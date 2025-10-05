//! Simplicial Complex Implementation
//! 
//! Verified against Lean proofs in lean/Tcdb/Topology/SimplicialComplex.lean

use crate::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

/// A simplex is a set of vertices
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Simplex {
    vertices: Vec<usize>,
}

impl Simplex {
    /// Create a new simplex from vertices
    /// 
    /// # TDD: Test-Driven Development
    /// See tests::test_simplex_creation
    pub fn new(mut vertices: Vec<usize>) -> Self {
        vertices.sort_unstable();
        vertices.dedup();
        Self { vertices }
    }

    /// Get the dimension of the simplex
    /// 
    /// Dimension = number of vertices - 1
    /// Verified in: lean/Tcdb/Topology/SimplicialComplex.lean
    pub fn dimension(&self) -> usize {
        self.vertices.len().saturating_sub(1)
    }

    /// Get all faces of this simplex
    ///
    /// # Mathematical Property
    /// A k-simplex has (k+1) faces of dimension (k-1)
    /// Proven in Lean: Simplex.faces_count_correct
    pub fn faces(&self) -> Vec<Simplex> {
        // A 0-simplex (vertex) has no faces
        if self.vertices.len() <= 1 {
            return vec![];
        }

        let mut faces = Vec::new();
        for i in 0..self.vertices.len() {
            let mut face_vertices = self.vertices.clone();
            face_vertices.remove(i);
            faces.push(Simplex::new(face_vertices));
        }
        faces
    }

    /// Check if this simplex is a face of another
    pub fn is_face_of(&self, other: &Simplex) -> bool {
        self.vertices.iter().all(|v| other.vertices.contains(v))
    }

    pub fn vertices(&self) -> &[usize] {
        &self.vertices
    }
}

/// A simplicial complex is a collection of simplices
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimplicialComplex {
    simplices: HashSet<Simplex>,
    max_dimension: usize,
}

impl SimplicialComplex {
    /// Create an empty simplicial complex
    pub fn new() -> Self {
        Self {
            simplices: HashSet::new(),
            max_dimension: 0,
        }
    }

    /// Add a simplex to the complex
    ///
    /// # Closure Property
    /// When adding a simplex, all its faces must also be in the complex
    /// This is verified in Lean: SimplicialComplex.closure_property
    pub fn add_simplex(&mut self, simplex: Simplex) -> Result<()> {
        let dim = simplex.dimension();

        // Recursively add all faces (closure property)
        self.add_simplex_recursive(simplex.clone());

        if dim > self.max_dimension {
            self.max_dimension = dim;
        }

        Ok(())
    }

    /// Helper function to recursively add a simplex and all its faces
    fn add_simplex_recursive(&mut self, simplex: Simplex) {
        // Add the simplex itself
        if self.simplices.contains(&simplex) {
            return; // Already added
        }

        self.simplices.insert(simplex.clone());

        // Recursively add all faces
        for face in simplex.faces() {
            self.add_simplex_recursive(face);
        }
    }

    /// Get all simplices of a given dimension
    pub fn simplices_of_dimension(&self, dim: usize) -> Vec<&Simplex> {
        self.simplices
            .iter()
            .filter(|s| s.dimension() == dim)
            .collect()
    }

    /// Get the maximum dimension
    pub fn dimension(&self) -> usize {
        self.max_dimension
    }

    /// Verify the closure property holds
    /// 
    /// # Mathematical Invariant
    /// For every simplex σ in the complex, all faces of σ must be in the complex
    /// Proven in: lean/Tcdb/Topology/SimplicialComplex.lean
    pub fn verify_closure(&self) -> bool {
        for simplex in &self.simplices {
            for face in simplex.faces() {
                if !self.simplices.contains(&face) {
                    return false;
                }
            }
        }
        true
    }

    /// Compute the Euler characteristic
    /// 
    /// χ = Σ(-1)^k * n_k where n_k is the number of k-simplices
    /// Verified in Lean: SimplicialComplex.euler_characteristic_correct
    pub fn euler_characteristic(&self) -> i64 {
        let mut chi = 0i64;
        for dim in 0..=self.max_dimension {
            let count = self.simplices_of_dimension(dim).len() as i64;
            chi += if dim % 2 == 0 { count } else { -count };
        }
        chi
    }
}

impl Default for SimplicialComplex {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplex_creation() {
        let s = Simplex::new(vec![0, 1, 2]);
        assert_eq!(s.dimension(), 2);
        assert_eq!(s.vertices(), &[0, 1, 2]);
    }

    #[test]
    fn test_simplex_deduplication() {
        let s = Simplex::new(vec![0, 1, 1, 2]);
        assert_eq!(s.vertices(), &[0, 1, 2]);
    }

    #[test]
    fn test_simplex_faces() {
        let s = Simplex::new(vec![0, 1, 2]);
        let faces = s.faces();
        assert_eq!(faces.len(), 3);
        
        // Check all faces are present
        assert!(faces.contains(&Simplex::new(vec![0, 1])));
        assert!(faces.contains(&Simplex::new(vec![0, 2])));
        assert!(faces.contains(&Simplex::new(vec![1, 2])));
    }

    #[test]
    fn test_simplex_is_face_of() {
        let face = Simplex::new(vec![0, 1]);
        let simplex = Simplex::new(vec![0, 1, 2]);
        assert!(face.is_face_of(&simplex));
        assert!(!simplex.is_face_of(&face));
    }

    #[test]
    fn test_complex_creation() {
        let complex = SimplicialComplex::new();
        assert_eq!(complex.dimension(), 0);
    }

    #[test]
    fn test_complex_add_simplex() {
        let mut complex = SimplicialComplex::new();
        let simplex = Simplex::new(vec![0, 1, 2]);
        
        complex.add_simplex(simplex).unwrap();
        
        // Check closure property - all faces should be added
        assert_eq!(complex.simplices_of_dimension(0).len(), 3); // vertices
        assert_eq!(complex.simplices_of_dimension(1).len(), 3); // edges
        assert_eq!(complex.simplices_of_dimension(2).len(), 1); // triangle
    }

    #[test]
    fn test_complex_closure_property() {
        let mut complex = SimplicialComplex::new();
        complex.add_simplex(Simplex::new(vec![0, 1, 2])).unwrap();
        assert!(complex.verify_closure());
    }

    #[test]
    fn test_euler_characteristic_triangle() {
        let mut complex = SimplicialComplex::new();
        complex.add_simplex(Simplex::new(vec![0, 1, 2])).unwrap();
        
        // Triangle: 3 vertices - 3 edges + 1 face = 1
        assert_eq!(complex.euler_characteristic(), 1);
    }

    #[test]
    fn test_euler_characteristic_sphere() {
        // Create a tetrahedron (topologically a 2-sphere)
        let mut complex = SimplicialComplex::new();
        complex.add_simplex(Simplex::new(vec![0, 1, 2])).unwrap();
        complex.add_simplex(Simplex::new(vec![0, 1, 3])).unwrap();
        complex.add_simplex(Simplex::new(vec![0, 2, 3])).unwrap();
        complex.add_simplex(Simplex::new(vec![1, 2, 3])).unwrap();
        
        // Sphere: χ = 2
        assert_eq!(complex.euler_characteristic(), 2);
    }
}

