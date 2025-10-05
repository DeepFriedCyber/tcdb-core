//! Integration tests for tcdb-core

use tcdb_core::{Simplex, SimplicialComplex, Filtration, PersistentHomology};

#[test]
fn test_triangle_complex() {
    let mut complex = SimplicialComplex::new();
    let triangle = Simplex::new(vec![0, 1, 2]);
    
    complex.add_simplex(triangle).unwrap();
    
    // Check dimensions
    assert_eq!(complex.dimension(), 2);
    
    // Check Euler characteristic (3 vertices - 3 edges + 1 face = 1)
    assert_eq!(complex.euler_characteristic(), 1);
    
    // Verify closure property
    assert!(complex.verify_closure());
}

#[test]
fn test_tetrahedron_complex() {
    let mut complex = SimplicialComplex::new();
    
    // Add all faces of a tetrahedron
    complex.add_simplex(Simplex::new(vec![0, 1, 2])).unwrap();
    complex.add_simplex(Simplex::new(vec![0, 1, 3])).unwrap();
    complex.add_simplex(Simplex::new(vec![0, 2, 3])).unwrap();
    complex.add_simplex(Simplex::new(vec![1, 2, 3])).unwrap();
    
    // Tetrahedron is topologically a 2-sphere, so χ = 2
    assert_eq!(complex.euler_characteristic(), 2);
    assert!(complex.verify_closure());
}

#[test]
fn test_filtration_monotonicity() {
    let mut complex = SimplicialComplex::new();
    complex.add_simplex(Simplex::new(vec![0, 1, 2])).unwrap();
    
    let mut filtration = Filtration::new(complex);
    
    // Set values respecting monotonicity
    filtration.set_value(Simplex::new(vec![0]), 0.0).unwrap();
    filtration.set_value(Simplex::new(vec![1]), 0.0).unwrap();
    filtration.set_value(Simplex::new(vec![2]), 0.0).unwrap();
    filtration.set_value(Simplex::new(vec![0, 1]), 1.0).unwrap();
    filtration.set_value(Simplex::new(vec![0, 2]), 1.0).unwrap();
    filtration.set_value(Simplex::new(vec![1, 2]), 1.0).unwrap();
    filtration.set_value(Simplex::new(vec![0, 1, 2]), 2.0).unwrap();
    
    assert!(filtration.verify_monotonicity());
}

#[test]
fn test_rips_complex_construction() {
    // Simulate building a Rips complex from a point cloud
    let mut complex = SimplicialComplex::new();
    
    // Add vertices
    for i in 0..4 {
        complex.add_simplex(Simplex::new(vec![i])).unwrap();
    }
    
    // Add edges (simulating distance threshold)
    complex.add_simplex(Simplex::new(vec![0, 1])).unwrap();
    complex.add_simplex(Simplex::new(vec![1, 2])).unwrap();
    complex.add_simplex(Simplex::new(vec![2, 3])).unwrap();
    complex.add_simplex(Simplex::new(vec![3, 0])).unwrap();
    
    assert_eq!(complex.dimension(), 1);
    assert!(complex.verify_closure());
}

#[test]
fn test_empty_complex() {
    let complex = SimplicialComplex::new();
    assert_eq!(complex.dimension(), 0);
    assert_eq!(complex.euler_characteristic(), 0);
}

#[test]
fn test_single_vertex() {
    let mut complex = SimplicialComplex::new();
    complex.add_simplex(Simplex::new(vec![0])).unwrap();
    
    assert_eq!(complex.dimension(), 0);
    assert_eq!(complex.euler_characteristic(), 1);
}

#[test]
fn test_single_edge() {
    let mut complex = SimplicialComplex::new();
    complex.add_simplex(Simplex::new(vec![0, 1])).unwrap();
    
    // Should have 2 vertices and 1 edge
    assert_eq!(complex.dimension(), 1);
    // χ = 2 - 1 = 1
    assert_eq!(complex.euler_characteristic(), 1);
}

#[test]
fn test_disconnected_components() {
    let mut complex = SimplicialComplex::new();
    
    // Two separate edges
    complex.add_simplex(Simplex::new(vec![0, 1])).unwrap();
    complex.add_simplex(Simplex::new(vec![2, 3])).unwrap();
    
    assert_eq!(complex.dimension(), 1);
    // χ = 4 vertices - 2 edges = 2 (two components)
    assert_eq!(complex.euler_characteristic(), 2);
}

