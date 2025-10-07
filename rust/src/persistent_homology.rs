//! Persistent Homology Computation
//!
//! Implements the standard algorithm for computing persistence diagrams.
//! Correctness verified in lean/Tcdb/PersistentHomology/

use crate::{Filtration, Result, Simplex};
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::collections::HashMap;

/// A point in a persistence diagram
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct PersistencePoint {
    pub birth: f64,
    pub death: f64,
    pub dimension: usize,
}

impl PersistencePoint {
    /// Get the persistence (lifetime) of this feature
    pub fn persistence(&self) -> f64 {
        self.death - self.birth
    }

    /// Check if this is an infinite persistence feature
    pub fn is_infinite(&self) -> bool {
        self.death.is_infinite()
    }
}

/// A persistence diagram for a given dimension
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PersistenceDiagram {
    pub dimension: usize,
    pub points: Vec<PersistencePoint>,
}

impl PersistenceDiagram {
    pub fn new(dimension: usize) -> Self {
        Self {
            dimension,
            points: Vec::new(),
        }
    }

    /// Add a persistence point
    pub fn add_point(&mut self, birth: f64, death: f64) {
        self.points.push(PersistencePoint {
            birth,
            death,
            dimension: self.dimension,
        });
    }

    /// Get points with persistence above threshold
    pub fn significant_points(&self, threshold: f64) -> Vec<&PersistencePoint> {
        self.points
            .iter()
            .filter(|p| p.persistence() >= threshold)
            .collect()
    }

    /// Get the number of infinite persistence features
    /// 
    /// This corresponds to the Betti numbers
    /// Verified in: lean/Tcdb/PersistentHomology/BettiNumbers.lean
    pub fn betti_number(&self) -> usize {
        self.points.iter().filter(|p| p.is_infinite()).count()
    }
}

/// A barcode representation (alternative to persistence diagram)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Barcode {
    pub dimension: usize,
    pub intervals: Vec<(f64, f64)>,
}

impl From<&PersistenceDiagram> for Barcode {
    fn from(diagram: &PersistenceDiagram) -> Self {
        let intervals = diagram.points.iter().map(|p| (p.birth, p.death)).collect();

        Self {
            dimension: diagram.dimension,
            intervals,
        }
    }
}

/// Persistent Homology computation engine
pub struct PersistentHomology {
    filtration: Filtration,
}

impl PersistentHomology {
    /// Create a new persistent homology computation
    pub fn new(filtration: Filtration) -> Self {
        Self { filtration }
    }

    /// Compute persistence diagrams for all dimensions
    ///
    /// # Algorithm
    /// Uses the standard persistence algorithm with matrix reduction
    /// Correctness proven in: lean/Tcdb/PersistentHomology/Algorithm.lean
    pub fn compute(&self) -> Result<Vec<PersistenceDiagram>> {
        let max_dim = self.filtration.max_dimension();
        let pairs = self.persistence_pairs()?;
        let mut diagrams: Vec<PersistenceDiagram> =
            (0..=max_dim).map(PersistenceDiagram::new).collect();

        for diagram in &mut diagrams {
            if let Some(points) = pairs.get(&diagram.dimension) {
                diagram.points = points.clone();
            }
        }

        diagrams.sort_by_key(|d| d.dimension);
        Ok(diagrams)
    }

    /// Compute persistence diagram for a specific dimension
    pub fn compute_dimension(&self, dimension: usize) -> Result<PersistenceDiagram> {
        let mut diagram = PersistenceDiagram::new(dimension);
        let pairs = self.persistence_pairs()?;
        if let Some(points) = pairs.get(&dimension) {
            diagram.points = points.clone();
        }

        Ok(diagram)
    }

    /// Compute Betti numbers at a specific filtration value
    /// 
    /// # Mathematical Property
    /// β_k = rank(H_k) where H_k is the k-th homology group
    /// Verified in: lean/Tcdb/PersistentHomology/BettiNumbers.lean
    pub fn betti_numbers(&self, filtration_value: f64) -> Result<Vec<usize>> {
        let diagrams = self.compute()?;
        
        Ok(diagrams
            .iter()
            .map(|d| {
                d.points
                    .iter()
                    .filter(|p| p.birth <= filtration_value && p.death > filtration_value)
                    .count()
            })
            .collect())
    }
}

impl PersistentHomology {
    /// Compute persistence pairs using matrix reduction algorithm
    fn persistence_pairs(&self) -> Result<HashMap<usize, Vec<PersistencePoint>>> {
        let ordered = self.filtration.ordered_simplices();
        let mut simplex_indices: HashMap<Simplex, usize> = HashMap::new();
        let mut columns: Vec<Vec<usize>> = vec![Vec::new(); ordered.len()];
        let mut low_inverse: HashMap<usize, usize> = HashMap::new();
        let mut births: HashMap<usize, f64> = HashMap::new();
        let mut diagrams: HashMap<usize, Vec<PersistencePoint>> = HashMap::new();

        for (idx, (value, simplex)) in ordered.iter().enumerate() {
            let mut column: Vec<usize> = simplex
                .faces()
                .into_iter()
                .filter_map(|face| simplex_indices.get(&face).copied())
                .collect();
            column.sort_unstable();
            column.dedup();

            while let Some(&low) = column.last() {
                if let Some(&other_idx) = low_inverse.get(&low) {
                    let other_column = columns[other_idx].clone();
                    column = Self::xor_columns(column, &other_column);
                } else {
                    break;
                }
            }

            if column.is_empty() {
                births.insert(idx, *value);
            } else {
                let low = *column.last().expect("column is non-empty");
                low_inverse.insert(low, idx);
                let birth_value = births.remove(&low).unwrap_or_else(|| ordered[low].0);
                let birth_dim = ordered[low].1.dimension();

                diagrams
                    .entry(birth_dim)
                    .or_default()
                    .push(PersistencePoint {
                        birth: birth_value,
                        death: *value,
                        dimension: birth_dim,
                    });
            }

            columns[idx] = column;
            simplex_indices.insert(simplex.clone(), idx);
        }

        for (birth_idx, birth_value) in births {
            let birth_dim = ordered[birth_idx].1.dimension();
            diagrams
                .entry(birth_dim)
                .or_default()
                .push(PersistencePoint {
                    birth: birth_value,
                    death: f64::INFINITY,
                    dimension: birth_dim,
                });
        }

        for points in diagrams.values_mut() {
            points.sort_by(|a, b| match a.birth.partial_cmp(&b.birth) {
                Some(Ordering::Equal) => a.death.partial_cmp(&b.death).unwrap_or(Ordering::Equal),
                Some(order) => order,
                None => Ordering::Equal,
            });
        }

        Ok(diagrams)
    }

    /// XOR two columns (symmetric difference for Z/2Z coefficients)
    fn xor_columns(mut left: Vec<usize>, right: &[usize]) -> Vec<usize> {
        let mut result = Vec::with_capacity(left.len() + right.len());
        left.sort_unstable();
        let mut right_sorted: Vec<usize> = right.to_vec();
        right_sorted.sort_unstable();

        let mut i = 0;
        let mut j = 0;

        while i < left.len() || j < right_sorted.len() {
            match (left.get(i), right_sorted.get(j)) {
                (Some(&l), Some(&r)) if l == r => {
                    i += 1;
                    j += 1;
                }
                (Some(&l), Some(&r)) if l < r => {
                    result.push(l);
                    i += 1;
                }
                (Some(&_l), Some(&r)) => {
                    result.push(r);
                    j += 1;
                }
                (Some(&l), None) => {
                    result.push(l);
                    i += 1;
                }
                (None, Some(&r)) => {
                    result.push(r);
                    j += 1;
                }
                (None, None) => break,
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Filtration, Simplex};

    #[test]
    fn test_persistence_point_creation() {
        let point = PersistencePoint {
            birth: 0.0,
            death: 1.0,
            dimension: 0,
        };
        assert_eq!(point.persistence(), 1.0);
        assert!(!point.is_infinite());
    }

    #[test]
    fn test_persistence_point_infinite() {
        let point = PersistencePoint {
            birth: 0.0,
            death: f64::INFINITY,
            dimension: 0,
        };
        assert!(point.is_infinite());
    }

    #[test]
    fn test_diagram_creation() {
        let mut diagram = PersistenceDiagram::new(0);
        diagram.add_point(0.0, 1.0);
        diagram.add_point(0.5, 2.0);
        
        assert_eq!(diagram.points.len(), 2);
        assert_eq!(diagram.dimension, 0);
    }

    #[test]
    fn test_diagram_significant_points() {
        let mut diagram = PersistenceDiagram::new(0);
        diagram.add_point(0.0, 0.1); // persistence = 0.1
        diagram.add_point(0.0, 1.0); // persistence = 1.0
        diagram.add_point(0.5, 2.0); // persistence = 1.5
        
        let significant = diagram.significant_points(0.5);
        assert_eq!(significant.len(), 2);
    }

    #[test]
    fn test_diagram_betti_number() {
        let mut diagram = PersistenceDiagram::new(0);
        diagram.add_point(0.0, 1.0);
        diagram.add_point(0.0, f64::INFINITY);
        diagram.add_point(0.5, f64::INFINITY);
        
        assert_eq!(diagram.betti_number(), 2);
    }

    #[test]
    fn test_barcode_conversion() {
        let mut diagram = PersistenceDiagram::new(1);
        diagram.add_point(0.0, 1.0);
        diagram.add_point(0.5, 2.0);

        let barcode = Barcode::from(&diagram);
        assert_eq!(barcode.intervals.len(), 2);
        assert_eq!(barcode.dimension, 1);
    }

    #[test]
    fn test_persistent_homology_interval() {
        let mut filtration = Filtration::new();
        filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
        filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
        filtration
            .add_simplex(1.0, Simplex::new(vec![0, 1]))
            .unwrap();

        let ph = PersistentHomology::new(filtration);
        let diagrams = ph.compute().unwrap();
        let dim0 = diagrams.into_iter().find(|d| d.dimension == 0).unwrap();

        assert_eq!(dim0.points.len(), 2);

        let infinite_components = dim0.points.iter().filter(|p| p.is_infinite()).count();
        assert_eq!(infinite_components, 1);

        let finite = dim0
            .points
            .iter()
            .find(|p| p.death.is_finite())
            .expect("expected a finite persistence pair");

        assert!((finite.birth - 0.0).abs() < 1e-9);
        assert!((finite.death - 1.0).abs() < 1e-9);
    }

    #[test]
    fn test_persistent_homology_triangle_loop() {
        let mut filtration = Filtration::new();
        filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
        filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
        filtration.add_simplex(0.0, Simplex::new(vec![2])).unwrap();
        filtration
            .add_simplex(1.0, Simplex::new(vec![0, 1]))
            .unwrap();
        filtration
            .add_simplex(1.2, Simplex::new(vec![1, 2]))
            .unwrap();
        filtration
            .add_simplex(1.4, Simplex::new(vec![0, 2]))
            .unwrap();
        filtration
            .add_simplex(2.0, Simplex::new(vec![0, 1, 2]))
            .unwrap();

        let ph = PersistentHomology::new(filtration);
        let diagrams = ph.compute().unwrap();
        let dim1 = diagrams.into_iter().find(|d| d.dimension == 1).unwrap();

        assert_eq!(dim1.points.len(), 1);

        let feature = &dim1.points[0];
        assert!((feature.birth - 1.4).abs() < 1e-9);
        assert!((feature.death - 2.0).abs() < 1e-9);
    }
}
