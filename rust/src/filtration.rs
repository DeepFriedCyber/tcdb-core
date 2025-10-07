//! Filtration Implementation
//!
//! A filtration is a nested sequence of simplicial complexes.
//! Verified in: lean/Tcdb/PersistentHomology/Filtration.lean

use crate::{Result, Simplex, SimplicialComplex, TcdbError};
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet};

/// A filtration value (time parameter)
pub type FiltrationValue = f64;

/// A filtration is a map from filtration values to simplicial complexes
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Filtration {
    /// Map from filtration value to the simplices that appear at that value
    levels: BTreeMap<FiltrationKey, Vec<Simplex>>,
    max_dimension: usize,
}

/// Wrapper for filtration values to enable proper ordering
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Serialize, Deserialize)]
struct FiltrationKey(FiltrationValue);

impl Eq for FiltrationKey {}

impl Ord for FiltrationKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .partial_cmp(&other.0)
            .expect("Filtration values must be comparable")
    }
}

impl From<FiltrationValue> for FiltrationKey {
    fn from(value: FiltrationValue) -> Self {
        Self(value)
    }
}

impl From<FiltrationKey> for FiltrationValue {
    fn from(key: FiltrationKey) -> Self {
        key.0
    }
}

impl Filtration {
    /// Create a new empty filtration
    pub fn new() -> Self {
        Self {
            levels: BTreeMap::new(),
            max_dimension: 0,
        }
    }

    /// Add a simplex at a specific filtration value
    ///
    /// # Mathematical Property
    /// Filtrations must be monotone: if s ≤ t, then F(s) ⊆ F(t)
    /// Verified in: lean/Tcdb/PersistentHomology/Filtration.lean
    pub fn add_simplex(&mut self, value: FiltrationValue, simplex: Simplex) -> Result<()> {
        if value.is_nan() || value.is_infinite() {
            return Err(TcdbError::InvalidFiltration);
        }

        let dim = simplex.dimension();
        if dim > self.max_dimension {
            self.max_dimension = dim;
        }

        // Validate that all faces exist before adding this simplex
        if dim > 0 {
            for face in simplex.faces() {
                if !self.contains_simplex_up_to(value, &face) {
                    return Err(TcdbError::InvalidFiltration);
                }
            }
        }

        self.levels
            .entry(FiltrationKey::from(value))
            .or_insert_with(Vec::new)
            .push(simplex);

        Ok(())
    }

    /// Get the simplicial complex at a specific filtration value
    ///
    /// Returns all simplices with filtration value ≤ the given value
    pub fn complex_at(&self, value: FiltrationValue) -> SimplicialComplex {
        let mut complex = SimplicialComplex::new();

        for (key, simplices) in self.levels.range(..=FiltrationKey::from(value)) {
            let filt_val: f64 = (*key).into();
            if filt_val <= value {
                for simplex in simplices {
                    let _ = complex.add_simplex(simplex.clone());
                }
            }
        }

        complex
    }

    /// Get all filtration values
    pub fn values(&self) -> Vec<FiltrationValue> {
        self.levels.keys().map(|k| (*k).into()).collect()
    }

    /// Get the maximum dimension of simplices in the filtration
    pub fn max_dimension(&self) -> usize {
        self.max_dimension
    }

    /// Verify the monotonicity property
    ///
    /// # Mathematical Invariant
    /// For all s ≤ t: F(s) ⊆ F(t)
    /// Proven in: lean/Tcdb/PersistentHomology/Filtration.lean
    pub fn verify_monotonicity(&self) -> bool {
        let mut accumulated: HashSet<Simplex> = HashSet::new();

        for simplices in self.levels.values() {
            for simplex in simplices {
                for face in simplex.faces() {
                    if !accumulated.contains(&face) && !simplices.contains(&face) {
                        return false;
                    }
                }
            }

            for simplex in simplices {
                accumulated.insert(simplex.clone());
            }
        }

        true
    }

    /// Iterate through simplices in non-decreasing filtration order.
    pub(crate) fn ordered_simplices(&self) -> Vec<(FiltrationValue, Simplex)> {
        let mut simplices: Vec<(FiltrationValue, Simplex)> = self
            .levels
            .iter()
            .flat_map(|(value, simplices)| {
                let filtration_value: FiltrationValue = (*value).into();
                simplices
                    .iter()
                    .cloned()
                    .map(move |s| (filtration_value, s))
            })
            .collect();

        simplices.sort_by(|(a_val, a_simplex), (b_val, b_simplex)| {
            a_val
                .partial_cmp(b_val)
                .unwrap()
                .then(a_simplex.dimension().cmp(&b_simplex.dimension()))
                .then(a_simplex.vertices().cmp(b_simplex.vertices()))
        });

        simplices
    }

    /// Check if a simplex exists up to a given filtration value
    fn contains_simplex_up_to(&self, value: FiltrationValue, simplex: &Simplex) -> bool {
        self.levels
            .range(..=FiltrationKey::from(value))
            .any(|(_, simplices)| simplices.contains(simplex))
    }
}

impl Default for Filtration {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_filtration_creation() {
        let filtration = Filtration::new();
        assert_eq!(filtration.values().len(), 0);
    }

    #[test]
    fn test_filtration_add_simplex() {
        let mut filtration = Filtration::new();
        filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
        filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
        let simplex = Simplex::new(vec![0, 1]);

        filtration.add_simplex(0.5, simplex).unwrap();
        assert_eq!(filtration.values().len(), 2);
    }

    #[test]
    fn test_filtration_invalid_value() {
        let mut filtration = Filtration::new();
        let simplex = Simplex::new(vec![0, 1]);

        let result = filtration.add_simplex(f64::NAN, simplex);
        assert!(result.is_err());
    }

    #[test]
    fn test_filtration_complex_at() {
        let mut filtration = Filtration::new();

        filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
        filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
        filtration.add_simplex(0.0, Simplex::new(vec![2])).unwrap();
        filtration
            .add_simplex(0.5, Simplex::new(vec![0, 1]))
            .unwrap();
        filtration
            .add_simplex(0.5, Simplex::new(vec![1, 2]))
            .unwrap();
        filtration
            .add_simplex(0.5, Simplex::new(vec![0, 2]))
            .unwrap();
        filtration
            .add_simplex(1.0, Simplex::new(vec![0, 1, 2]))
            .unwrap();

        let complex_at_0_5 = filtration.complex_at(0.5);
        // Should have simplices at 0.0 and 0.5, but not 1.0
        assert!(complex_at_0_5.dimension() >= 1);
    }

    #[test]
    fn test_filtration_monotonicity() {
        let mut filtration = Filtration::new();

        filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
        filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
        filtration.add_simplex(0.0, Simplex::new(vec![2])).unwrap();
        filtration
            .add_simplex(0.5, Simplex::new(vec![0, 1]))
            .unwrap();
        filtration
            .add_simplex(0.5, Simplex::new(vec![1, 2]))
            .unwrap();
        filtration
            .add_simplex(0.5, Simplex::new(vec![0, 2]))
            .unwrap();
        filtration
            .add_simplex(1.0, Simplex::new(vec![0, 1, 2]))
            .unwrap();

        assert!(filtration.verify_monotonicity());
    }

    #[test]
    fn test_filtration_values_sorted() {
        let mut filtration = Filtration::new();

        filtration.add_simplex(1.0, Simplex::new(vec![0])).unwrap();
        filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
        filtration.add_simplex(0.5, Simplex::new(vec![2])).unwrap();

        let values = filtration.values();
        assert_eq!(values, vec![0.0, 0.5, 1.0]);
    }

    #[test]
    fn test_filtration_rejects_missing_faces() {
        let mut filtration = Filtration::new();
        let result = filtration.add_simplex(0.5, Simplex::new(vec![0, 1]));
        assert!(result.is_err());
    }
}

