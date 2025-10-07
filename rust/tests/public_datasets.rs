//! Tests using publicly available datasets and known TDA results
//!
//! These tests use synthetic data that mimics real-world TDA datasets
//! and verify against known topological properties.

use tcdb_core::euler::FVector;
use tcdb_core::bayes::{Evidence, posterior, sequential_update};
use tcdb_core::streaming::Streamer;
use tcdb_core::embed::{landscape_features_auto, landscape_distance};

/// Generate points on a circle (S^1)
/// Known topology: β₀ = 1, β₁ = 1, χ = 0
fn generate_circle(n: usize, radius: f64) -> Vec<(f64, f64)> {
    (0..n)
        .map(|i| {
            let theta = 2.0 * std::f64::consts::PI * (i as f64) / (n as f64);
            (radius * theta.cos(), radius * theta.sin())
        })
        .collect()
}

/// Generate points on a sphere (S^2) - using spherical coordinates
/// Known topology: β₀ = 1, β₁ = 0, β₂ = 1, χ = 2
fn generate_sphere_points(n: usize) -> Vec<(f64, f64, f64)> {
    let mut points = Vec::new();
    let golden_ratio = (1.0 + 5.0_f64.sqrt()) / 2.0;
    
    for i in 0..n {
        let theta = 2.0 * std::f64::consts::PI * (i as f64) / golden_ratio;
        let phi = ((1.0 - 2.0 * (i as f64) / (n as f64)).acos());
        
        let x = phi.sin() * theta.cos();
        let y = phi.sin() * theta.sin();
        let z = phi.cos();
        
        points.push((x, y, z));
    }
    
    points
}

/// Generate points on a torus
/// Known topology: β₀ = 1, β₁ = 2, β₂ = 1, χ = 0
fn generate_torus(n: usize, R: f64, r: f64) -> Vec<(f64, f64, f64)> {
    let mut points = Vec::new();
    let samples_per_dim = (n as f64).sqrt() as usize;
    
    for i in 0..samples_per_dim {
        for j in 0..samples_per_dim {
            let u = 2.0 * std::f64::consts::PI * (i as f64) / (samples_per_dim as f64);
            let v = 2.0 * std::f64::consts::PI * (j as f64) / (samples_per_dim as f64);
            
            let x = (R + r * v.cos()) * u.cos();
            let y = (R + r * v.cos()) * u.sin();
            let z = r * v.sin();
            
            points.push((x, y, z));
        }
    }
    
    points
}

/// Generate noisy circle with outliers
fn generate_noisy_circle(n: usize, radius: f64, noise: f64, outliers: usize) -> Vec<(f64, f64)> {
    let mut points = generate_circle(n, radius);
    
    // Add noise
    for point in points.iter_mut() {
        point.0 += (rand::random::<f64>() - 0.5) * noise;
        point.1 += (rand::random::<f64>() - 0.5) * noise;
    }
    
    // Add outliers
    for _ in 0..outliers {
        points.push((
            (rand::random::<f64>() - 0.5) * radius * 3.0,
            (rand::random::<f64>() - 0.5) * radius * 3.0,
        ));
    }
    
    points
}

// Use a simple random number generator for reproducibility
mod rand {
    static mut SEED: u64 = 12345;
    
    pub fn random<T>() -> T
    where
        T: From<f64>,
    {
        unsafe {
            SEED = SEED.wrapping_mul(1103515245).wrapping_add(12345);
            let val = ((SEED / 65536) % 32768) as f64 / 32768.0;
            T::from(val)
        }
    }
}

#[test]
fn test_circle_topology() {
    // Circle has χ = 0 (1 component - 1 loop)
    let circle_fvec = FVector::new(vec![100, 100, 0]); // 100 vertices, 100 edges, 0 faces
    assert_eq!(circle_fvec.euler_characteristic(), 0);
}

#[test]
fn test_sphere_topology() {
    // Sphere has χ = 2
    // Octahedron approximation: 6 vertices, 12 edges, 8 faces
    let sphere = FVector::new(vec![6, 12, 8]);
    assert_eq!(sphere.euler_characteristic(), 2);
    
    // Icosahedron: 12 vertices, 30 edges, 20 faces
    let icosahedron = FVector::new(vec![12, 30, 20]);
    assert_eq!(icosahedron.euler_characteristic(), 2);
}

#[test]
fn test_torus_topology() {
    // Torus has χ = 0
    let torus = FVector::new(vec![9, 27, 18]);
    assert_eq!(torus.euler_characteristic(), 0);
}

#[test]
fn test_projective_plane_topology() {
    // Projective plane has χ = 1
    let proj_plane = FVector::new(vec![6, 15, 10]);
    assert_eq!(proj_plane.euler_characteristic(), 1);
}

#[test]
fn test_klein_bottle_topology() {
    // Klein bottle has χ = 0
    let klein = FVector::new(vec![8, 24, 16]);
    assert_eq!(klein.euler_characteristic(), 0);
}

#[test]
fn test_multiple_components() {
    // 5 disconnected triangles
    let mut complex = FVector::triangle();
    for _ in 1..5 {
        complex = complex.disjoint_union(&FVector::triangle());
    }
    
    // Each triangle has χ = 1, so 5 triangles have χ = 5
    assert_eq!(complex.euler_characteristic(), 5);
}

#[test]
fn test_streaming_sine_wave() {
    // Stream a sine wave and verify persistence
    let mut streamer = Streamer::new(100);
    
    // Generate one period of sine wave
    for i in 0..200 {
        let t = i as f64 * 0.1;
        let value = t.sin();
        streamer.push((t, value));
    }
    
    // Should have some persistent features
    let pd = streamer.pd();
    assert!(!pd.is_empty(), "Sine wave should have persistent features");
    
    // Check statistics
    let stats = streamer.statistics();
    assert!(stats.is_some(), "Should have statistics");
    
    if let Some((min, max, mean, _)) = stats {
        assert!(min >= -1.0 && min <= 1.0, "Min should be in [-1, 1]");
        assert!(max >= -1.0 && max <= 1.0, "Max should be in [-1, 1]");
        assert!(mean.abs() < 1.0, "Mean should be reasonable");
    }
}

#[test]
fn test_streaming_step_function() {
    // Stream a step function (should show clear topological change)
    let mut streamer = Streamer::new(50);
    
    // First half: constant at 0
    for i in 0..25 {
        streamer.push((i as f64, 0.0));
    }
    
    let pd_before = streamer.pd();
    
    // Second half: constant at 1
    for i in 25..50 {
        streamer.push((i as f64, 1.0));
    }
    
    let pd_after = streamer.pd();
    
    // The step should create different topology
    assert!(
        pd_before.len() != pd_after.len() || pd_before != pd_after,
        "Step function should change topology"
    );
}

#[test]
fn test_landscape_circle_vs_two_circles() {
    // One circle
    let pd_one = vec![(0.0, 1.0)];
    
    // Two circles (same size)
    let pd_two = vec![(0.0, 1.0), (0.0, 1.0)];
    
    let f1 = landscape_features_auto(&pd_one, 2, 10);
    let f2 = landscape_features_auto(&pd_two, 2, 10);
    
    let dist = landscape_distance(&f1, &f2);
    
    // Should be distinguishable
    assert!(dist > 0.1, "One circle vs two circles should be distinguishable");
}

#[test]
fn test_landscape_persistence_matters() {
    // Short-lived feature
    let pd_short = vec![(0.0, 0.1)];
    
    // Long-lived feature
    let pd_long = vec![(0.0, 1.0)];
    
    let f_short = landscape_features_auto(&pd_short, 2, 10);
    let f_long = landscape_features_auto(&pd_long, 2, 10);
    
    let dist = landscape_distance(&f_short, &f_long);
    
    // Persistence should matter
    assert!(dist > 0.5, "Persistence should affect landscape features");
}

#[test]
fn test_bayesian_anomaly_detection() {
    // Simulate anomaly detection scenario
    let base_rate = 0.01; // 1% of data are anomalies
    
    // Normal data: low persistence
    let normal_evidence = Evidence::new(0.1, 0.9);
    let post_normal = posterior(base_rate, normal_evidence);
    
    // Should stay low
    assert!(
        post_normal.posterior < 0.05,
        "Normal data should keep anomaly probability low"
    );
    
    // Anomalous data: high persistence
    let anomaly_evidence = Evidence::new(0.9, 0.05);
    let post_anomaly = posterior(base_rate, anomaly_evidence);
    
    // Should increase significantly
    assert!(
        post_anomaly.posterior > 0.1,
        "Anomalous data should increase anomaly probability"
    );
}

#[test]
fn test_bayesian_sequential_classification() {
    // Multi-feature classification
    let prior = 0.5;
    
    // Collect evidence from multiple topological features
    let evidence = vec![
        Evidence::new(0.8, 0.2), // Betti numbers support class 1
        Evidence::new(0.9, 0.1), // Persistence supports class 1
        Evidence::new(0.7, 0.3), // Landscape features support class 1
    ];
    
    let final_post = sequential_update(prior, &evidence);
    
    // Should be confident in class 1
    assert!(
        final_post.posterior > 0.9,
        "Multiple supporting features should give high confidence"
    );
}

#[test]
fn test_workflow_time_series_anomaly() {
    // Realistic workflow: streaming time series with anomaly detection
    let mut streamer = Streamer::new(50);
    
    // Normal data: sine wave
    for i in 0..40 {
        let t = i as f64 * 0.1;
        streamer.push((t, t.sin()));
    }
    
    let pd_normal = streamer.pd();
    let features_normal = landscape_features_auto(&pd_normal, 2, 10);
    
    // Inject anomaly: spike
    streamer.push((4.0, 10.0));
    
    let pd_anomaly = streamer.pd();
    let features_anomaly = landscape_features_auto(&pd_anomaly, 2, 10);
    
    // Compute distance
    let dist = landscape_distance(&features_normal, &features_anomaly);
    
    // Use distance as evidence
    let evidence = if dist > 0.5 {
        Evidence::new(0.9, 0.1) // High distance suggests anomaly
    } else {
        Evidence::new(0.1, 0.9)
    };
    
    let post = posterior(0.01, evidence);
    
    // Should detect anomaly
    assert!(
        post.posterior > 0.05 || dist > 0.3,
        "Should detect anomaly in time series"
    );
}

#[test]
fn test_workflow_shape_classification() {
    // Classify shapes based on Euler characteristic
    
    // Dataset: mix of spheres and tori
    let shapes = vec![
        ("sphere1", FVector::new(vec![6, 12, 8])),
        ("sphere2", FVector::new(vec![12, 30, 20])),
        ("torus1", FVector::new(vec![9, 27, 18])),
        ("torus2", FVector::new(vec![16, 48, 32])),
    ];
    
    // Classify based on χ
    for (name, fvec) in shapes {
        let chi = fvec.euler_characteristic();
        
        // Prior: 50% sphere, 50% torus
        let prior = 0.5;
        
        // Evidence: χ = 2 strongly suggests sphere
        let evidence = if chi == 2 {
            Evidence::new(0.95, 0.05)
        } else if chi == 0 {
            Evidence::new(0.05, 0.95)
        } else {
            Evidence::new(0.5, 0.5)
        };
        
        let post = posterior(prior, evidence);
        
        if name.starts_with("sphere") {
            assert!(
                post.posterior > 0.9,
                "Should classify {} as sphere with high confidence",
                name
            );
        } else {
            assert!(
                post.posterior < 0.1,
                "Should classify {} as torus (not sphere) with high confidence",
                name
            );
        }
    }
}

