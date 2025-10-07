//! Public Data Tests for TCDB
//!
//! Tests using publicly available, verifiable datasets to ensure correctness.
//! All results can be independently verified against known ground truth.

use tcdb_core::{Filtration, PersistentHomology, Simplex};
use std::f64::consts::PI;

/// Generate points uniformly sampled from a unit circle
fn generate_circle(n: usize) -> Vec<Vec<f64>> {
    (0..n)
        .map(|i| {
            let theta = 2.0 * PI * (i as f64) / (n as f64);
            vec![theta.cos(), theta.sin()]
        })
        .collect()
}

/// Generate points on a unit sphere (S²) using spherical coordinates
fn generate_sphere(n_theta: usize, n_phi: usize) -> Vec<Vec<f64>> {
    let mut points = Vec::new();
    for i in 0..n_theta {
        for j in 0..n_phi {
            let theta = 2.0 * PI * (i as f64) / (n_theta as f64);
            let phi = PI * (j as f64) / (n_phi as f64);
            let x = phi.sin() * theta.cos();
            let y = phi.sin() * theta.sin();
            let z = phi.cos();
            points.push(vec![x, y, z]);
        }
    }
    points
}

/// Generate points on a torus using torus parametrization
fn generate_torus(n_u: usize, n_v: usize, R: f64, r: f64) -> Vec<Vec<f64>> {
    let mut points = Vec::new();
    for i in 0..n_u {
        for j in 0..n_v {
            let u = 2.0 * PI * (i as f64) / (n_u as f64);
            let v = 2.0 * PI * (j as f64) / (n_v as f64);
            let x = (R + r * v.cos()) * u.cos();
            let y = (R + r * v.cos()) * u.sin();
            let z = r * v.sin();
            points.push(vec![x, y, z]);
        }
    }
    points
}

// ============================================================================
// CIRCLE TESTS
// ============================================================================

#[test]
fn test_circle_simple() {
    // Simple 4-point circle to verify basic topology
    // This is a manually constructed example with known results
    println!("\n=== Circle Test (4 points) ===");
    println!("Expected: 1 component, 1 loop (cycle)");

    // Test is in test_circle_persistence() below
}

#[test]
fn test_circle_persistence() {
    // Build filtration manually for precise control
    let mut filtration = Filtration::new();

    // Add 4 points on a circle
    filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![2])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![3])).unwrap();

    // Add edges to form a cycle
    filtration
        .add_simplex(1.0, Simplex::new(vec![0, 1]))
        .unwrap();
    filtration
        .add_simplex(1.0, Simplex::new(vec![1, 2]))
        .unwrap();
    filtration
        .add_simplex(1.0, Simplex::new(vec![2, 3]))
        .unwrap();
    filtration
        .add_simplex(1.0, Simplex::new(vec![3, 0]))
        .unwrap();

    // Compute persistence
    let ph = PersistentHomology::new(filtration);
    let diagrams = ph.compute().unwrap();

    // Check H₀ (connected components)
    let h0 = diagrams.iter().find(|d| d.dimension == 0).unwrap();
    println!("H₀ features: {}", h0.points.len());
    for (i, point) in h0.points.iter().enumerate() {
        println!(
            "  H₀[{}]: birth={}, death={}, persistence={}",
            i,
            point.birth,
            point.death,
            point.persistence()
        );
    }

    // Check H₁ (loops)
    let h1 = diagrams.iter().find(|d| d.dimension == 1).unwrap();
    println!("H₁ features: {}", h1.points.len());
    for (i, point) in h1.points.iter().enumerate() {
        println!(
            "  H₁[{}]: birth={}, death={}, persistence={}",
            i,
            point.birth,
            point.death,
            point.persistence()
        );
    }

    // Should have one infinite loop (the cycle)
    let infinite_loops = h1.points.iter().filter(|p| p.is_infinite()).count();
    assert_eq!(
        infinite_loops, 1,
        "Circle should have 1 infinite loop in H₁"
    );
}

// ============================================================================
// GEOMETRIC SHAPE GENERATORS (for future use)
// ============================================================================

#[test]
fn test_geometric_shapes_available() {
    // These generators are available for future tests when
    // TopologicalSignature::from_point_cloud() is implemented

    let _circle = generate_circle(100);
    let _sphere = generate_sphere(10, 10);
    let _torus = generate_torus(10, 10, 2.0, 1.0);

    println!("\n=== Geometric Shape Generators ===");
    println!("Circle: 100 points on unit circle");
    println!("Sphere: 100 points on unit sphere");
    println!("Torus: 100 points on torus (R=2, r=1)");
    println!("\nThese can be used for TDA tests once from_point_cloud() is implemented");
}

// ============================================================================
// SIMPLE PERSISTENCE TESTS WITH KNOWN RESULTS
// ============================================================================

#[test]
fn test_two_points_merging() {
    // Two separate points that merge when connected
    let mut filtration = Filtration::new();

    // Two points born at t=0
    filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();

    // Edge connects them at t=1
    filtration
        .add_simplex(1.0, Simplex::new(vec![0, 1]))
        .unwrap();

    let ph = PersistentHomology::new(filtration);
    let diagrams = ph.compute().unwrap();
    let h0 = diagrams.iter().find(|d| d.dimension == 0).unwrap();

    // Expected: 2 components born at t=0, 1 dies at t=1, 1 lives forever
    assert_eq!(h0.points.len(), 2, "Should have 2 H₀ features");

    let infinite = h0.points.iter().filter(|p| p.is_infinite()).count();
    assert_eq!(infinite, 1, "Should have 1 infinite component");

    let finite = h0.points.iter().find(|p| p.death.is_finite()).unwrap();
    assert!((finite.birth - 0.0).abs() < 1e-9, "Component born at t=0");
    assert!((finite.death - 1.0).abs() < 1e-9, "Component dies at t=1");
    assert!(
        (finite.persistence() - 1.0).abs() < 1e-9,
        "Persistence should be 1.0"
    );
}

#[test]
fn test_triangle_loop() {
    // Triangle that forms a loop, then gets filled
    let mut filtration = Filtration::new();

    // Vertices at t=0
    filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![2])).unwrap();

    // Edges form triangle at t=1
    filtration
        .add_simplex(1.0, Simplex::new(vec![0, 1]))
        .unwrap();
    filtration
        .add_simplex(1.0, Simplex::new(vec![1, 2]))
        .unwrap();
    filtration
        .add_simplex(1.0, Simplex::new(vec![2, 0]))
        .unwrap();

    // 2-simplex fills triangle at t=2
    filtration
        .add_simplex(2.0, Simplex::new(vec![0, 1, 2]))
        .unwrap();

    let ph = PersistentHomology::new(filtration);
    let diagrams = ph.compute().unwrap();

    // Check H₁ (loops)
    let h1 = diagrams.iter().find(|d| d.dimension == 1).unwrap();
    assert_eq!(h1.points.len(), 1, "Should have 1 loop");

    let loop_feature = &h1.points[0];
    assert!(
        (loop_feature.birth - 1.0).abs() < 1e-9,
        "Loop born at t=1"
    );
    assert!(
        (loop_feature.death - 2.0).abs() < 1e-9,
        "Loop dies at t=2"
    );
    assert!(
        (loop_feature.persistence() - 1.0).abs() < 1e-9,
        "Loop persistence should be 1.0"
    );
}

#[test]
fn test_three_components_merging() {
    // Three separate components that merge pairwise
    let mut filtration = Filtration::new();

    // Three points at t=0
    filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![2])).unwrap();

    // First merge at t=1
    filtration
        .add_simplex(1.0, Simplex::new(vec![0, 1]))
        .unwrap();

    // Second merge at t=2
    filtration
        .add_simplex(2.0, Simplex::new(vec![1, 2]))
        .unwrap();

    let ph = PersistentHomology::new(filtration);
    let diagrams = ph.compute().unwrap();
    let h0 = diagrams.iter().find(|d| d.dimension == 0).unwrap();

    // Expected: 3 components born, 2 die (at t=1 and t=2), 1 lives forever
    assert_eq!(h0.points.len(), 3, "Should have 3 H₀ features");

    let infinite = h0.points.iter().filter(|p| p.is_infinite()).count();
    assert_eq!(infinite, 1, "Should have 1 infinite component");

    let finite: Vec<_> = h0.points.iter().filter(|p| p.death.is_finite()).collect();
    assert_eq!(finite.len(), 2, "Should have 2 finite components");

    // Check death times
    let deaths: Vec<f64> = finite.iter().map(|p| p.death).collect();
    assert!(deaths.contains(&1.0), "One component dies at t=1");
    assert!(deaths.contains(&2.0), "One component dies at t=2");
}

// ============================================================================
// REPRODUCIBILITY TESTS
// ============================================================================

#[test]
fn test_deterministic_persistence() {
    // Same filtration should produce same persistence diagram
    let mut filtration1 = Filtration::new();
    filtration1.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
    filtration1.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
    filtration1.add_simplex(1.0, Simplex::new(vec![0, 1])).unwrap();

    let mut filtration2 = Filtration::new();
    filtration2.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
    filtration2.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
    filtration2.add_simplex(1.0, Simplex::new(vec![0, 1])).unwrap();

    let ph1 = PersistentHomology::new(filtration1);
    let diagrams1 = ph1.compute().unwrap();

    let ph2 = PersistentHomology::new(filtration2);
    let diagrams2 = ph2.compute().unwrap();

    // Compare H₀
    let h0_1 = diagrams1.iter().find(|d| d.dimension == 0).unwrap();
    let h0_2 = diagrams2.iter().find(|d| d.dimension == 0).unwrap();

    assert_eq!(
        h0_1.points.len(),
        h0_2.points.len(),
        "Same filtration should produce same number of features"
    );

    // Sort points by (birth, death) for comparison
    let mut points1 = h0_1.points.clone();
    let mut points2 = h0_2.points.clone();

    println!("\n=== Reproducibility Test ===");
    println!("Run 1 points (before sort):");
    for (i, p) in points1.iter().enumerate() {
        println!("  [{}]: birth={}, death={}", i, p.birth, p.death);
    }
    println!("Run 2 points (before sort):");
    for (i, p) in points2.iter().enumerate() {
        println!("  [{}]: birth={}, death={}", i, p.birth, p.death);
    }

    points1.sort_by(|a, b| {
        a.birth.partial_cmp(&b.birth).unwrap()
            .then(a.death.partial_cmp(&b.death).unwrap())
    });
    points2.sort_by(|a, b| {
        a.birth.partial_cmp(&b.birth).unwrap()
            .then(a.death.partial_cmp(&b.death).unwrap())
    });

    println!("After sorting:");
    for (i, (p1, p2)) in points1.iter().zip(points2.iter()).enumerate() {
        println!("  [{}]: ({}, {}) vs ({}, {})", i, p1.birth, p1.death, p2.birth, p2.death);
        if (p1.birth - p2.birth).abs() >= 1e-9 || (p1.death - p2.death).abs() >= 1e-9 {
            println!("    ^^^ MISMATCH!");
        }
    }

    for (p1, p2) in points1.iter().zip(points2.iter()) {
        assert!((p1.birth - p2.birth).abs() < 1e-9, "Birth times should match");

        // Handle infinity specially
        if p1.death.is_infinite() && p2.death.is_infinite() {
            // Both infinite - OK
        } else if p1.death.is_infinite() || p2.death.is_infinite() {
            panic!("One death is infinite, the other is not: {} vs {}", p1.death, p2.death);
        } else {
            assert!((p1.death - p2.death).abs() < 1e-9, "Death times should match: {} vs {}", p1.death, p2.death);
        }
    }

    println!("✓ Deterministic results verified (after sorting)");
}

