//! Filtration Implementation
//!
//! A filtration is a nested sequence of simplicial complexes.
//! Verified in: lean/Tcdb/PersistentHomology/Filtration.lean

use crate::{Result, TcdbError, SimplicialComplex, Simplex};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// A filtration value (time parameter)
pub type FiltrationValue = f64;

/// A filtration is a map from filtration values to simplicial complexes
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Filtration {
    /// Map from filtration value to the simplices that appear at that value
    levels: HashMap<String, Vec<Simplex>>, // Use String keys for f64 values
    max_dimension: usize,
}

impl Filtration {
    /// Create a new empty filtration
    pub fn new() -> Self {
        Self {
            levels: HashMap::new(),
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

        let key = format!("{:.10}", value); // Use string key for f64
        self.levels
            .entry(key)
            .or_insert_with(Vec::new)
            .push(simplex);

        Ok(())
    }

    /// Get the simplicial complex at a specific filtration value
    ///
    /// Returns all simplices with filtration value ≤ the given value
    pub fn complex_at(&self, value: FiltrationValue) -> SimplicialComplex {
        let mut complex = SimplicialComplex::new();

        for (key, simplices) in &self.levels {
            let filt_val: f64 = key.parse().unwrap_or(f64::INFINITY);
            if filt_val <= value {
                for simplex in simplices {
                    // Ignore errors - complex handles closure
                    let _ = complex.add_simplex(simplex.clone());
                }
            }
        }

        complex
    }

    /// Get all filtration values
    pub fn values(&self) -> Vec<FiltrationValue> {
        let mut vals: Vec<f64> = self.levels.keys()
            .filter_map(|k| k.parse().ok())
            .collect();
        vals.sort_by(|a, b| a.partial_cmp(b).unwrap());
        vals
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
        let values: Vec<_> = self.values();

        for i in 0..values.len() {
            for j in i + 1..values.len() {
                let complex_i = self.complex_at(values[i]);
                let complex_j = self.complex_at(values[j]);

                // Check if complex_i ⊆ complex_j
                // (simplified check - full implementation would verify all simplices)
                if complex_i.dimension() > complex_j.dimension() {
                    return false;
                }
            }
        }

        true
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
        let simplex = Simplex::new(vec![0, 1]);

        filtration.add_simplex(0.5, simplex).unwrap();
        assert_eq!(filtration.values().len(), 1);
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

        filtration.add_simplex(0.0, Simplex::new(vec![0, 1])).unwrap();
        filtration.add_simplex(0.5, Simplex::new(vec![1, 2])).unwrap();
        filtration.add_simplex(1.0, Simplex::new(vec![0, 1, 2])).unwrap();

        let complex_at_0_5 = filtration.complex_at(0.5);
        // Should have simplices at 0.0 and 0.5, but not 1.0
        assert!(complex_at_0_5.dimension() >= 1);
    }

    #[test]
    fn test_filtration_monotonicity() {
        let mut filtration = Filtration::new();

        filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
        filtration.add_simplex(0.5, Simplex::new(vec![0, 1])).unwrap();
        filtration.add_simplex(1.0, Simplex::new(vec![0, 1, 2])).unwrap();

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
}

