//! Bayesian Inference over Topological Evidence
//!
//! This module provides Bayesian updating using topological features as evidence.
//! It enables probabilistic reasoning about hypotheses based on persistence diagrams,
//! Betti numbers, and other topological summaries.
//!
//! # Use Cases
//!
//! - **Hypothesis testing**: Update beliefs based on topological evidence
//! - **Model selection**: Compare models using topological features
//! - **Anomaly detection**: Compute probability of anomaly given topology
//! - **Classification**: Bayesian classification using TDA features
//!
//! # Key Concepts
//!
//! - **Prior**: Initial belief P(H) before seeing evidence
//! - **Likelihood**: P(E|H) - probability of evidence given hypothesis
//! - **Posterior**: P(H|E) - updated belief after seeing evidence
//! - **Bayes' Rule**: P(H|E) = P(E|H) × P(H) / P(E)

use serde::{Deserialize, Serialize};

/// Evidence for Bayesian updating
///
/// Represents the likelihood of observing evidence E under two scenarios:
/// - Hypothesis H is true: P(E|H)
/// - Hypothesis H is false: P(E|¬H)
///
/// # Examples
///
/// ```
/// use tcdb_core::bayes::Evidence;
///
/// // Strong evidence for H: E is much more likely if H is true
/// let strong_evidence = Evidence {
///     like_h: 0.9,      // P(E|H) = 0.9
///     like_not_h: 0.1,  // P(E|¬H) = 0.1
/// };
///
/// // Weak evidence: E is equally likely under both scenarios
/// let weak_evidence = Evidence {
///     like_h: 0.5,
///     like_not_h: 0.5,
/// };
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Evidence {
    /// Likelihood P(E | H): probability of evidence given hypothesis is true
    pub like_h: f64,
    
    /// Likelihood P(E | ¬H): probability of evidence given hypothesis is false
    pub like_not_h: f64,
}

impl Evidence {
    /// Create new evidence
    ///
    /// # Arguments
    ///
    /// * `like_h` - P(E|H)
    /// * `like_not_h` - P(E|¬H)
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::bayes::Evidence;
    ///
    /// let ev = Evidence::new(0.9, 0.1);
    /// ```
    pub fn new(like_h: f64, like_not_h: f64) -> Self {
        assert!(like_h >= 0.0 && like_h <= 1.0, "like_h must be in [0,1]");
        assert!(like_not_h >= 0.0 && like_not_h <= 1.0, "like_not_h must be in [0,1]");
        Self { like_h, like_not_h }
    }
    
    /// Compute likelihood ratio: P(E|H) / P(E|¬H)
    ///
    /// Measures how much more likely the evidence is under H vs ¬H.
    ///
    /// # Returns
    ///
    /// - > 1: Evidence supports H
    /// - = 1: Evidence is neutral
    /// - < 1: Evidence supports ¬H
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::bayes::Evidence;
    ///
    /// let ev = Evidence::new(0.9, 0.1);
    /// assert_eq!(ev.likelihood_ratio(), 9.0); // Strong support for H
    /// ```
    pub fn likelihood_ratio(&self) -> f64 {
        if self.like_not_h == 0.0 {
            f64::INFINITY
        } else {
            self.like_h / self.like_not_h
        }
    }
    
    /// Check if evidence supports hypothesis H
    ///
    /// Returns true if P(E|H) > P(E|¬H)
    pub fn supports_h(&self) -> bool {
        self.like_h > self.like_not_h
    }
    
    /// Check if evidence is neutral
    ///
    /// Returns true if P(E|H) ≈ P(E|¬H)
    pub fn is_neutral(&self, epsilon: f64) -> bool {
        (self.like_h - self.like_not_h).abs() < epsilon
    }
}

/// Posterior distribution after Bayesian update
///
/// Contains the prior, evidence, and computed posterior probability.
///
/// # Examples
///
/// ```
/// use tcdb_core::bayes::{Evidence, posterior};
///
/// let prior = 0.5;
/// let ev = Evidence::new(0.9, 0.1);
/// let post = posterior(prior, ev);
///
/// assert!(post.posterior > post.prior); // Belief increased
/// ```
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Posterior {
    /// Prior probability P(H)
    pub prior: f64,
    
    /// Evidence used for update
    pub evidence: Evidence,
    
    /// Posterior probability P(H|E)
    pub posterior: f64,
}

impl Posterior {
    /// Compute change in belief: posterior - prior
    ///
    /// # Returns
    ///
    /// - > 0: Belief increased
    /// - = 0: Belief unchanged
    /// - < 0: Belief decreased
    pub fn belief_change(&self) -> f64 {
        self.posterior - self.prior
    }
    
    /// Compute odds ratio: P(H|E) / P(¬H|E)
    pub fn posterior_odds(&self) -> f64 {
        if self.posterior == 1.0 {
            f64::INFINITY
        } else {
            self.posterior / (1.0 - self.posterior)
        }
    }
    
    /// Compute prior odds: P(H) / P(¬H)
    pub fn prior_odds(&self) -> f64 {
        if self.prior == 1.0 {
            f64::INFINITY
        } else {
            self.prior / (1.0 - self.prior)
        }
    }
    
    /// Compute Bayes factor: posterior_odds / prior_odds
    ///
    /// Measures strength of evidence:
    /// - > 1: Evidence supports H
    /// - = 1: Evidence is neutral
    /// - < 1: Evidence supports ¬H
    pub fn bayes_factor(&self) -> f64 {
        let prior_odds = self.prior_odds();
        let posterior_odds = self.posterior_odds();
        
        if prior_odds.is_infinite() || posterior_odds.is_infinite() {
            return f64::NAN;
        }
        
        posterior_odds / prior_odds
    }
}

/// Compute posterior probability using Bayes' rule
///
/// Applies Bayes' rule: P(H|E) = P(E|H) × P(H) / P(E)
///
/// where P(E) = P(E|H) × P(H) + P(E|¬H) × P(¬H)
///
/// # Arguments
///
/// * `prior` - Prior probability P(H), must be in (0, 1)
/// * `ev` - Evidence with likelihoods P(E|H) and P(E|¬H)
///
/// # Returns
///
/// Posterior distribution with updated probability
///
/// # Examples
///
/// ```
/// use tcdb_core::bayes::{Evidence, posterior};
///
/// // Prior: 50% chance hypothesis is true
/// let prior = 0.5;
///
/// // Evidence strongly supports hypothesis
/// let ev = Evidence::new(0.9, 0.1);
///
/// let post = posterior(prior, ev);
/// assert!(post.posterior > 0.8); // Belief increased significantly
/// ```
pub fn posterior(prior: f64, ev: Evidence) -> Posterior {
    assert!(
        prior > 0.0 && prior < 1.0,
        "Prior must be in (0, 1), got {}",
        prior
    );
    assert!(
        ev.like_h >= 0.0 && ev.like_not_h >= 0.0,
        "Likelihoods must be non-negative"
    );
    
    // Bayes' rule: P(H|E) = P(E|H) × P(H) / P(E)
    let numerator = ev.like_h * prior;
    let denominator = numerator + ev.like_not_h * (1.0 - prior);
    
    let posterior_prob = if denominator == 0.0 {
        // Both likelihoods are zero - no information
        0.5
    } else {
        numerator / denominator
    };
    
    Posterior {
        prior,
        evidence: ev,
        posterior: posterior_prob,
    }
}

/// Sequential Bayesian updating with multiple pieces of evidence
///
/// Applies Bayes' rule sequentially, using the posterior from one
/// update as the prior for the next.
///
/// # Arguments
///
/// * `prior` - Initial prior probability
/// * `evidence` - Sequence of evidence to incorporate
///
/// # Returns
///
/// Final posterior after all updates
///
/// # Examples
///
/// ```
/// use tcdb_core::bayes::{Evidence, sequential_update};
///
/// let prior = 0.5;
/// let evidence = vec![
///     Evidence::new(0.8, 0.2),
///     Evidence::new(0.9, 0.1),
///     Evidence::new(0.7, 0.3),
/// ];
///
/// let final_post = sequential_update(prior, &evidence);
/// assert!(final_post.posterior > prior);
/// ```
pub fn sequential_update(prior: f64, evidence: &[Evidence]) -> Posterior {
    let mut current_prior = prior;
    let mut last_posterior = None;
    
    for ev in evidence {
        let post = posterior(current_prior, ev.clone());
        current_prior = post.posterior;
        last_posterior = Some(post);
    }
    
    last_posterior.unwrap_or_else(|| Posterior {
        prior,
        evidence: Evidence::new(0.5, 0.5),
        posterior: prior,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_evidence_creation() {
        let ev = Evidence::new(0.9, 0.1);
        assert_eq!(ev.like_h, 0.9);
        assert_eq!(ev.like_not_h, 0.1);
    }

    #[test]
    fn test_likelihood_ratio() {
        let ev = Evidence::new(0.9, 0.1);
        assert_eq!(ev.likelihood_ratio(), 9.0);
    }

    #[test]
    fn test_supports_h() {
        let ev1 = Evidence::new(0.9, 0.1);
        assert!(ev1.supports_h());
        
        let ev2 = Evidence::new(0.1, 0.9);
        assert!(!ev2.supports_h());
    }

    #[test]
    fn test_posterior_basic() {
        let prior = 0.5;
        let ev = Evidence::new(0.9, 0.1);
        let post = posterior(prior, ev);
        
        assert!(post.posterior > prior);
        assert!(post.posterior > 0.8);
    }

    #[test]
    fn test_belief_change() {
        let prior = 0.5;
        let ev = Evidence::new(0.9, 0.1);
        let post = posterior(prior, ev);
        
        assert!(post.belief_change() > 0.0);
    }

    #[test]
    fn test_sequential_update() {
        let prior = 0.5;
        let evidence = vec![
            Evidence::new(0.8, 0.2),
            Evidence::new(0.9, 0.1),
        ];
        
        let final_post = sequential_update(prior, &evidence);
        assert!(final_post.posterior > prior);
    }

    #[test]
    #[should_panic(expected = "Prior must be in (0, 1)")]
    fn test_invalid_prior() {
        let ev = Evidence::new(0.9, 0.1);
        posterior(1.5, ev);
    }

    #[test]
    #[should_panic(expected = "like_h must be in [0,1]")]
    fn test_invalid_likelihood() {
        Evidence::new(1.5, 0.1);
    }
}

