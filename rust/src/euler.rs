//! Euler Characteristic Computation
//!
//! This module provides computation of the Euler characteristic,
//! a fundamental topological invariant.
//!
//! # Mathematical Background
//!
//! The Euler characteristic χ is defined as:
//!
//! χ = Σ_k (-1)^k f_k
//!
//! where f_k is the number of k-dimensional faces.
//!
//! # Key Properties
//!
//! 1. **Additivity**: χ(A ⊔ B) = χ(A) + χ(B)
//! 2. **Topological invariant**: Homeomorphic spaces have same χ
//! 3. **Computable**: Can be computed from f-vector
//!
//! # Examples
//!
//! - Point: χ = 1
//! - Interval: χ = 1
//! - Triangle: χ = 1
//! - Sphere: χ = 2
//! - Torus: χ = 0

use serde::{Deserialize, Serialize};

/// f-vector: counts of k-dimensional faces
///
/// # Examples
///
/// ```
/// use tcdb_core::euler::FVector;
///
/// // Triangle: 3 vertices, 3 edges, 1 face
/// let triangle = FVector::new(vec![3, 3, 1]);
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FVector {
    /// faces[k] = number of k-dimensional faces
    pub faces: Vec<usize>,
}

impl FVector {
    /// Create new f-vector
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let fvec = FVector::new(vec![3, 3, 1]); // Triangle
    /// ```
    pub fn new(faces: Vec<usize>) -> Self {
        Self { faces }
    }
    
    /// Create empty complex
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let empty = FVector::empty();
    /// assert_eq!(empty.euler_characteristic(), 0);
    /// ```
    pub fn empty() -> Self {
        Self { faces: vec![] }
    }
    
    /// Create point (0-simplex)
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let point = FVector::point();
    /// assert_eq!(point.euler_characteristic(), 1);
    /// ```
    pub fn point() -> Self {
        Self { faces: vec![1] }
    }
    
    /// Create interval (1-simplex)
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let interval = FVector::interval();
    /// assert_eq!(interval.euler_characteristic(), 1);
    /// ```
    pub fn interval() -> Self {
        Self { faces: vec![2, 1] }
    }
    
    /// Create triangle (2-simplex)
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let triangle = FVector::triangle();
    /// assert_eq!(triangle.euler_characteristic(), 1);
    /// ```
    pub fn triangle() -> Self {
        Self { faces: vec![3, 3, 1] }
    }
    
    /// Create tetrahedron (3-simplex)
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let tet = FVector::tetrahedron();
    /// assert_eq!(tet.euler_characteristic(), 1);
    /// ```
    pub fn tetrahedron() -> Self {
        Self { faces: vec![4, 6, 4, 1] }
    }
    
    /// Compute Euler characteristic
    ///
    /// χ = Σ_k (-1)^k f_k
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let triangle = FVector::triangle();
    /// assert_eq!(triangle.euler_characteristic(), 1); // 3 - 3 + 1 = 1
    /// ```
    pub fn euler_characteristic(&self) -> i64 {
        self.faces
            .iter()
            .enumerate()
            .map(|(k, &count)| {
                if k % 2 == 0 {
                    count as i64
                } else {
                    -(count as i64)
                }
            })
            .sum()
    }
    
    /// Compute disjoint union
    ///
    /// (A ⊔ B)_k = A_k + B_k
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let t1 = FVector::triangle();
    /// let t2 = FVector::triangle();
    /// let union = t1.disjoint_union(&t2);
    ///
    /// assert_eq!(union.euler_characteristic(), 2); // χ(T) + χ(T) = 1 + 1 = 2
    /// ```
    pub fn disjoint_union(&self, other: &Self) -> Self {
        let max_dim = self.faces.len().max(other.faces.len());
        let mut faces = vec![0; max_dim];
        
        for k in 0..max_dim {
            let a_k = self.faces.get(k).copied().unwrap_or(0);
            let b_k = other.faces.get(k).copied().unwrap_or(0);
            faces[k] = a_k + b_k;
        }
        
        Self { faces }
    }
    
    /// Get number of k-faces
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let triangle = FVector::triangle();
    /// assert_eq!(triangle.get_face_count(0), 3); // 3 vertices
    /// assert_eq!(triangle.get_face_count(1), 3); // 3 edges
    /// assert_eq!(triangle.get_face_count(2), 1); // 1 face
    /// ```
    pub fn get_face_count(&self, k: usize) -> usize {
        self.faces.get(k).copied().unwrap_or(0)
    }
    
    /// Get maximum dimension
    ///
    /// # Examples
    ///
    /// ```
    /// use tcdb_core::euler::FVector;
    ///
    /// let triangle = FVector::triangle();
    /// assert_eq!(triangle.max_dimension(), 2);
    /// ```
    pub fn max_dimension(&self) -> usize {
        if self.faces.is_empty() {
            0
        } else {
            self.faces.len() - 1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_euler_characteristic() {
        let empty = FVector::empty();
        assert_eq!(empty.euler_characteristic(), 0);
    }

    #[test]
    fn test_point_euler_characteristic() {
        let point = FVector::point();
        assert_eq!(point.euler_characteristic(), 1);
    }

    #[test]
    fn test_interval_euler_characteristic() {
        let interval = FVector::interval();
        assert_eq!(interval.euler_characteristic(), 1); // 2 - 1 = 1
    }

    #[test]
    fn test_triangle_euler_characteristic() {
        let triangle = FVector::triangle();
        assert_eq!(triangle.euler_characteristic(), 1); // 3 - 3 + 1 = 1
    }

    #[test]
    fn test_tetrahedron_euler_characteristic() {
        let tet = FVector::tetrahedron();
        assert_eq!(tet.euler_characteristic(), 1); // 4 - 6 + 4 - 1 = 1
    }

    #[test]
    fn test_euler_characteristic_additive() {
        let t1 = FVector::triangle();
        let t2 = FVector::triangle();
        let union = t1.disjoint_union(&t2);
        
        let chi_union = union.euler_characteristic();
        let chi_sum = t1.euler_characteristic() + t2.euler_characteristic();
        
        assert_eq!(chi_union, chi_sum); // χ(A ⊔ B) = χ(A) + χ(B)
    }

    #[test]
    fn test_disjoint_union_commutative() {
        let a = FVector::triangle();
        let b = FVector::interval();
        
        let ab = a.disjoint_union(&b);
        let ba = b.disjoint_union(&a);
        
        assert_eq!(ab.euler_characteristic(), ba.euler_characteristic());
    }

    #[test]
    fn test_disjoint_union_associative() {
        let a = FVector::point();
        let b = FVector::interval();
        let c = FVector::triangle();
        
        let ab_c = a.disjoint_union(&b).disjoint_union(&c);
        let a_bc = a.disjoint_union(&b.disjoint_union(&c));
        
        assert_eq!(ab_c.euler_characteristic(), a_bc.euler_characteristic());
    }

    #[test]
    fn test_disjoint_union_identity() {
        let a = FVector::triangle();
        let empty = FVector::empty();
        
        let union = a.disjoint_union(&empty);
        
        assert_eq!(union.euler_characteristic(), a.euler_characteristic());
    }

    #[test]
    fn test_multiple_disjoint_unions() {
        let point = FVector::point();
        
        // 5 points
        let mut result = FVector::empty();
        for _ in 0..5 {
            result = result.disjoint_union(&point);
        }
        
        assert_eq!(result.euler_characteristic(), 5); // 5 × χ(point) = 5 × 1 = 5
    }

    #[test]
    fn test_get_face_count() {
        let triangle = FVector::triangle();
        
        assert_eq!(triangle.get_face_count(0), 3);
        assert_eq!(triangle.get_face_count(1), 3);
        assert_eq!(triangle.get_face_count(2), 1);
        assert_eq!(triangle.get_face_count(3), 0);
    }

    #[test]
    fn test_max_dimension() {
        assert_eq!(FVector::empty().max_dimension(), 0);
        assert_eq!(FVector::point().max_dimension(), 0);
        assert_eq!(FVector::interval().max_dimension(), 1);
        assert_eq!(FVector::triangle().max_dimension(), 2);
        assert_eq!(FVector::tetrahedron().max_dimension(), 3);
    }
}

