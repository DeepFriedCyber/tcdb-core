//! Reasoner Constraints
//!
//! Lightweight constraint checking on topological summaries.
//! Acts as a "gate" before expensive LLM calls to catch invalid inputs early.
//!
//! This module provides fast validation of topological properties:
//! - Betti number constraints (non-negativity, monotonicity)
//! - Persistence diagram constraints (birth ≤ death, lifetime bounds)
//! - Physical units and bounds checking
//!
//! Use this to validate inputs before sending to LLM reasoning systems.

use serde::{Deserialize, Serialize};

/// Constraints on topological summaries
///
/// These constraints encode mathematical properties that must hold
/// for valid topological data. Violations indicate either:
/// - Computational errors in the TDA pipeline
/// - Invalid input data
/// - Physical impossibilities
///
/// # Examples
///
/// ```
/// use tcdb_core::reasoner::{Constraint, BettiCurve, PD, check};
///
/// // Check that Betti numbers are non-negative
/// let constraints = vec![Constraint::BettiNonNegative];
/// let bettis = vec![BettiCurve {
///     k: 0,
///     ts: vec![0.0, 1.0, 2.0],
///     values: vec![1, 2, 1],
/// }];
/// let pd = PD(vec![(0.0, 1.0)]);
///
/// let violations = check(&constraints, &bettis, &pd);
/// assert!(violations.is_empty());
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Constraint {
    /// Betti numbers must be non-negative: β_k(t) ≥ 0
    ///
    /// This is a fundamental mathematical property. Negative Betti numbers
    /// indicate a computational error.
    BettiNonNegative,
    
    /// For k=0, connected components do not increase after threshold t
    ///
    /// In a filtration, components can only merge (decrease), not split.
    /// After a threshold, no new components should appear.
    ///
    /// # Arguments
    /// * `t` - Threshold filtration value
    BettiMonotone0UpTo { t: f64 },
    
    /// Death time must be ≥ birth time: ∀(b,d)∈PD, d ≥ b
    ///
    /// Features cannot die before they are born. This is a fundamental
    /// property of persistence diagrams.
    DeathGeBirth,
    
    /// Maximum lifetime constraint: ∀(b,d), d-b ≤ max
    ///
    /// Useful for filtering noise or enforcing physical constraints.
    ///
    /// # Arguments
    /// * `max` - Maximum allowed lifetime
    MaxLifetime { max: f64 },
}

/// Betti curve: β_k(t) over filtration parameter t
///
/// Represents how the k-th Betti number changes as the filtration
/// parameter increases.
///
/// # Fields
/// * `k` - Homology dimension (0 = components, 1 = loops, 2 = voids, ...)
/// * `ts` - Filtration values (sorted, increasing)
/// * `values` - Betti numbers at each filtration value
///
/// # Invariants
/// * `ts.len() == values.len()`
/// * `ts` is sorted in increasing order
/// * `values[i]` is β_k at filtration value `ts[i]`
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BettiCurve {
    pub k: usize,
    pub ts: Vec<f64>,
    pub values: Vec<i64>,
}

impl BettiCurve {
    /// Create a new Betti curve
    pub fn new(k: usize, ts: Vec<f64>, values: Vec<i64>) -> Self {
        assert_eq!(ts.len(), values.len(), "ts and values must have same length");
        Self { k, ts, values }
    }
    
    /// Check if the curve is monotone decreasing after threshold t
    pub fn is_monotone_decreasing_after(&self, t: f64) -> bool {
        let mut prev_value = None;
        for (&time, &value) in self.ts.iter().zip(self.values.iter()) {
            if time >= t {
                if let Some(prev) = prev_value {
                    if value > prev {
                        return false;
                    }
                }
                prev_value = Some(value);
            }
        }
        true
    }
}

/// Persistence diagram: collection of (birth, death) pairs
///
/// Each pair (b, d) represents a topological feature that:
/// - Appears at filtration value b (birth)
/// - Disappears at filtration value d (death)
/// - Has persistence (lifetime) d - b
///
/// # Invariants
/// * For all (b, d): d ≥ b (features cannot die before birth)
/// * Infinite features have d = f64::INFINITY
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PD(pub Vec<(f64, f64)>);

impl PD {
    /// Create a new persistence diagram
    pub fn new(pairs: Vec<(f64, f64)>) -> Self {
        Self(pairs)
    }
    
    /// Check if all death times are ≥ birth times
    pub fn all_death_ge_birth(&self) -> bool {
        self.0.iter().all(|(b, d)| d >= b || d.is_nan())
    }
    
    /// Get maximum lifetime (excluding infinite features)
    pub fn max_lifetime(&self) -> Option<f64> {
        self.0.iter()
            .filter(|(_, d)| d.is_finite())
            .map(|(b, d)| d - b)
            .max_by(|a, b| a.partial_cmp(b).unwrap())
    }
    
    /// Filter to finite features only
    pub fn finite_features(&self) -> Vec<(f64, f64)> {
        self.0.iter()
            .filter(|(_, d)| d.is_finite())
            .copied()
            .collect()
    }
}

/// Constraint violation
///
/// Describes a specific violation of a constraint, including:
/// - Which constraint was violated
/// - Where the violation occurred (if applicable)
/// - Details about the violation
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Violation {
    pub constraint: Constraint,
    pub index: Option<usize>,
    pub detail: String,
}

impl Violation {
    /// Create a new violation
    pub fn new(constraint: Constraint, index: Option<usize>, detail: String) -> Self {
        Self { constraint, index, detail }
    }
}

/// Check constraints on topological summaries
///
/// This is the main entry point for constraint checking. It validates
/// Betti curves and persistence diagrams against a set of constraints.
///
/// # Arguments
/// * `constraints` - Constraints to check
/// * `bettis` - Betti curves to validate
/// * `pd` - Persistence diagram to validate
///
/// # Returns
/// Vector of violations (empty if all constraints satisfied)
///
/// # Examples
///
/// ```
/// use tcdb_core::reasoner::{Constraint, BettiCurve, PD, check};
///
/// let constraints = vec![
///     Constraint::BettiNonNegative,
///     Constraint::DeathGeBirth,
/// ];
///
/// let bettis = vec![BettiCurve::new(0, vec![0.0, 1.0], vec![1, 1])];
/// let pd = PD::new(vec![(0.0, 1.0), (0.5, 2.0)]);
///
/// let violations = check(&constraints, &bettis, &pd);
/// assert!(violations.is_empty());
/// ```
pub fn check(constraints: &[Constraint], bettis: &[BettiCurve], pd: &PD) -> Vec<Violation> {
    let mut violations = Vec::new();
    
    for constraint in constraints {
        match constraint {
            Constraint::BettiNonNegative => {
                for (i, betti) in bettis.iter().enumerate() {
                    if let Some(&negative_value) = betti.values.iter().find(|&&v| v < 0) {
                        violations.push(Violation::new(
                            constraint.clone(),
                            Some(i),
                            format!("Betti curve {} has negative value: {}", betti.k, negative_value),
                        ));
                    }
                }
            }
            
            Constraint::BettiMonotone0UpTo { t } => {
                for (i, betti) in bettis.iter().enumerate().filter(|(_, b)| b.k == 0) {
                    if !betti.is_monotone_decreasing_after(*t) {
                        violations.push(Violation::new(
                            constraint.clone(),
                            Some(i),
                            format!("β₀ increased after threshold t={}", t),
                        ));
                    }
                }
            }
            
            Constraint::DeathGeBirth => {
                for (b, d) in pd.0.iter().filter(|(b, d)| d < b && d.is_finite()) {
                    violations.push(Violation::new(
                        constraint.clone(),
                        None,
                        format!("Found death < birth: ({}, {})", b, d),
                    ));
                }
            }
            
            Constraint::MaxLifetime { max } => {
                for (b, d) in pd.0.iter()
                    .filter(|(_, d)| d.is_finite())
                    .filter(|(b, d)| (d - b) > *max)
                {
                    violations.push(Violation::new(
                        constraint.clone(),
                        None,
                        format!("Lifetime {} exceeds max {}: ({}, {})", d - b, max, b, d),
                    ));
                }
            }
        }
    }
    
    violations
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_betti_curve_creation() {
        let curve = BettiCurve::new(0, vec![0.0, 1.0, 2.0], vec![1, 2, 1]);
        assert_eq!(curve.k, 0);
        assert_eq!(curve.ts.len(), 3);
        assert_eq!(curve.values.len(), 3);
    }

    #[test]
    #[should_panic(expected = "ts and values must have same length")]
    fn test_betti_curve_length_mismatch() {
        BettiCurve::new(0, vec![0.0, 1.0], vec![1, 2, 3]);
    }

    #[test]
    fn test_pd_creation() {
        let pd = PD::new(vec![(0.0, 1.0), (0.5, 2.0)]);
        assert_eq!(pd.0.len(), 2);
    }

    #[test]
    fn test_pd_all_death_ge_birth() {
        let pd1 = PD::new(vec![(0.0, 1.0), (0.5, 2.0)]);
        assert!(pd1.all_death_ge_birth());
        
        let pd2 = PD::new(vec![(0.0, 1.0), (2.0, 1.5)]);
        assert!(!pd2.all_death_ge_birth());
    }

    #[test]
    fn test_pd_max_lifetime() {
        let pd = PD::new(vec![(0.0, 1.0), (0.5, 3.0), (1.0, f64::INFINITY)]);
        assert_eq!(pd.max_lifetime(), Some(2.5));
    }

    #[test]
    fn test_constraint_betti_non_negative_pass() {
        let constraints = vec![Constraint::BettiNonNegative];
        let bettis = vec![BettiCurve::new(0, vec![0.0, 1.0], vec![1, 2])];
        let pd = PD::new(vec![]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_constraint_betti_non_negative_fail() {
        let constraints = vec![Constraint::BettiNonNegative];
        let bettis = vec![BettiCurve::new(0, vec![0.0, 1.0], vec![1, -1])];
        let pd = PD::new(vec![]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert_eq!(violations.len(), 1);
        assert!(violations[0].detail.contains("negative"));
    }

    #[test]
    fn test_constraint_death_ge_birth_pass() {
        let constraints = vec![Constraint::DeathGeBirth];
        let bettis = vec![];
        let pd = PD::new(vec![(0.0, 1.0), (0.5, 2.0)]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_constraint_death_ge_birth_fail() {
        let constraints = vec![Constraint::DeathGeBirth];
        let bettis = vec![];
        let pd = PD::new(vec![(0.0, 1.0), (2.0, 1.5)]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert_eq!(violations.len(), 1);
        assert!(violations[0].detail.contains("death < birth"));
    }

    #[test]
    fn test_constraint_max_lifetime_pass() {
        let constraints = vec![Constraint::MaxLifetime { max: 2.0 }];
        let bettis = vec![];
        let pd = PD::new(vec![(0.0, 1.0), (0.5, 2.0)]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_constraint_max_lifetime_fail() {
        let constraints = vec![Constraint::MaxLifetime { max: 1.0 }];
        let bettis = vec![];
        let pd = PD::new(vec![(0.0, 1.0), (0.5, 2.0)]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert_eq!(violations.len(), 1);
        assert!(violations[0].detail.contains("exceeds max"));
    }

    #[test]
    fn test_betti_monotone_0_pass() {
        let constraints = vec![Constraint::BettiMonotone0UpTo { t: 1.0 }];
        let bettis = vec![BettiCurve::new(0, vec![0.0, 1.0, 2.0], vec![3, 2, 1])];
        let pd = PD::new(vec![]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_betti_monotone_0_fail() {
        let constraints = vec![Constraint::BettiMonotone0UpTo { t: 1.0 }];
        let bettis = vec![BettiCurve::new(0, vec![0.0, 1.0, 2.0], vec![1, 2, 3])];
        let pd = PD::new(vec![]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert_eq!(violations.len(), 1);
        assert!(violations[0].detail.contains("increased after threshold"));
    }

    #[test]
    fn test_multiple_constraints() {
        let constraints = vec![
            Constraint::BettiNonNegative,
            Constraint::DeathGeBirth,
            Constraint::MaxLifetime { max: 2.0 },
        ];
        let bettis = vec![BettiCurve::new(0, vec![0.0, 1.0], vec![1, 1])];
        let pd = PD::new(vec![(0.0, 1.0), (0.5, 2.0)]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert!(violations.is_empty());
    }

    #[test]
    fn test_multiple_violations() {
        let constraints = vec![
            Constraint::BettiNonNegative,
            Constraint::DeathGeBirth,
        ];
        let bettis = vec![BettiCurve::new(0, vec![0.0, 1.0], vec![1, -1])];
        let pd = PD::new(vec![(2.0, 1.0)]);
        
        let violations = check(&constraints, &bettis, &pd);
        assert_eq!(violations.len(), 2);
    }
}

