//! Embedding Tests
//!
//! Integration tests for topology-aware embeddings using persistence landscapes.

use tcdb_core::embed::*;

#[test]
fn identical_pd_gives_identical_features() {
    // Test permutation invariance
    let pd1 = vec![(0.0, 1.0), (0.2, 0.9)];
    let mut pd2 = pd1.clone();
    pd2.reverse();

    let f1 = landscape_features(&pd1, 3, 16, 0.0, 1.0);
    let f2 = landscape_features(&pd2, 3, 16, 0.0, 1.0);

    assert_eq!(f1, f2, "Permutation should not change features");
}

#[test]
fn adding_far_apart_interval_changes_local_region_only() {
    // Test locality property
    let base = vec![(0.2, 0.4)];
    let far = vec![(0.2, 0.4), (10.0, 11.0)];

    let f1 = landscape_features(&base, 2, 32, 0.0, 1.0);
    let f2 = landscape_features(&far, 2, 32, 0.0, 1.0);

    // Features sampled on [0,1] shouldn't change when adding [10,11]
    assert_eq!(
        f1, f2,
        "Distant intervals should not affect local features"
    );
}

#[test]
fn empty_pd_gives_zero_features() {
    let pd = vec![];
    let features = landscape_features(&pd, 3, 16, 0.0, 1.0);

    assert_eq!(features.len(), 3 * 16);
    assert!(
        features.iter().all(|&x| x == 0.0),
        "Empty PD should give zero features"
    );
}

#[test]
fn single_interval_tent_shape() {
    // Test that a single interval creates a tent-shaped landscape
    let pd = vec![(0.0, 1.0)];
    let features = landscape_features(&pd, 1, 11, 0.0, 1.0);

    // Should have 11 samples
    assert_eq!(features.len(), 11);

    // Values should rise then fall (tent shape)
    // At t=0.0: value = 0
    // At t=0.5: value = 0.5 (peak)
    // At t=1.0: value = 0
    assert_eq!(features[0], 0.0); // t=0.0
    assert!(features[5] > 0.0); // t=0.5 (peak)
    assert_eq!(features[10], 0.0); // t=1.0

    // Peak should be at midpoint
    let max_val = features.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    assert!((max_val - 0.5).abs() < 1e-10, "Peak should be 0.5");
}

#[test]
fn multiple_levels_sorted_descending() {
    // Test that levels are sorted in descending order
    let pd = vec![(0.0, 1.0), (0.1, 0.9), (0.2, 0.8)];
    let features = landscape_features(&pd, 3, 1, 0.5, 0.5);

    // At t=0.5, all three intervals contribute
    // Level 0 should be >= Level 1 >= Level 2
    assert!(features[0] >= features[1]);
    assert!(features[1] >= features[2]);
}

#[test]
fn deterministic_features() {
    // Test that same input gives same output
    let pd = vec![(0.0, 1.0), (0.5, 2.0)];

    let f1 = landscape_features(&pd, 3, 16, 0.0, 2.0);
    let f2 = landscape_features(&pd, 3, 16, 0.0, 2.0);

    assert_eq!(f1, f2, "Features should be deterministic");
}

#[test]
fn auto_range_detection() {
    // Test automatic range detection
    let pd = vec![(0.5, 2.0), (1.0, 3.0)];
    let features = landscape_features_auto(&pd, 3, 16);

    assert_eq!(features.len(), 3 * 16);
    assert!(
        features.iter().any(|&x| x > 0.0),
        "Should have non-zero features"
    );
}

#[test]
fn auto_range_empty_pd() {
    // Test auto range with empty PD
    let pd = vec![];
    let features = landscape_features_auto(&pd, 3, 16);

    assert_eq!(features.len(), 3 * 16);
    assert!(
        features.iter().all(|&x| x == 0.0),
        "Empty PD should give zero features"
    );
}

#[test]
fn distance_identical_features() {
    let f1 = vec![1.0, 2.0, 3.0];
    let f2 = vec![1.0, 2.0, 3.0];

    let dist = landscape_distance(&f1, &f2);
    assert_eq!(dist, 0.0, "Identical features should have zero distance");
}

#[test]
fn distance_different_features() {
    let f1 = vec![1.0, 2.0, 3.0];
    let f2 = vec![4.0, 5.0, 6.0];

    let dist = landscape_distance(&f1, &f2);
    assert!(dist > 0.0, "Different features should have positive distance");

    // Check actual value: sqrt((3^2 + 3^2 + 3^2)) = sqrt(27) ≈ 5.196
    let expected = (27.0_f64).sqrt();
    assert!((dist - expected).abs() < 1e-10);
}

#[test]
fn similarity_identical_features() {
    let f1 = vec![1.0, 0.0, 0.0];
    let f2 = vec![1.0, 0.0, 0.0];

    let sim = landscape_similarity(&f1, &f2);
    assert!((sim - 1.0).abs() < 1e-10, "Identical features should have similarity 1.0");
}

#[test]
fn similarity_orthogonal_features() {
    let f1 = vec![1.0, 0.0, 0.0];
    let f2 = vec![0.0, 1.0, 0.0];

    let sim = landscape_similarity(&f1, &f2);
    assert!((sim - 0.0).abs() < 1e-10, "Orthogonal features should have similarity 0.0");
}

#[test]
fn similarity_opposite_features() {
    let f1 = vec![1.0, 0.0, 0.0];
    let f2 = vec![-1.0, 0.0, 0.0];

    let sim = landscape_similarity(&f1, &f2);
    assert!((sim - (-1.0)).abs() < 1e-10, "Opposite features should have similarity -1.0");
}

#[test]
fn permutation_invariance_comprehensive() {
    // Test permutation invariance with many permutations
    let pd = vec![(0.0, 1.0), (0.2, 0.9), (0.5, 1.5), (0.1, 0.8)];

    let f1 = landscape_features(&pd, 3, 16, 0.0, 2.0);

    // Try different permutations
    let mut pd2 = pd.clone();
    pd2.reverse();
    let f2 = landscape_features(&pd2, 3, 16, 0.0, 2.0);
    assert_eq!(f1, f2);

    let pd3 = vec![pd[2], pd[0], pd[3], pd[1]];
    let f3 = landscape_features(&pd3, 3, 16, 0.0, 2.0);
    assert_eq!(f1, f3);
}

#[test]
fn locality_property_detailed() {
    // Test that features are local
    let base = vec![(0.0, 0.5)];

    // Add interval far to the right
    let far_right = vec![(0.0, 0.5), (10.0, 10.5)];

    // Add interval far to the left
    let far_left = vec![(-10.0, -9.5), (0.0, 0.5)];

    let f_base = landscape_features(&base, 2, 32, 0.0, 1.0);
    let f_right = landscape_features(&far_right, 2, 32, 0.0, 1.0);
    let f_left = landscape_features(&far_left, 2, 32, 0.0, 1.0);

    assert_eq!(f_base, f_right, "Far right interval should not affect features");
    assert_eq!(f_base, f_left, "Far left interval should not affect features");
}

#[test]
fn stability_under_small_perturbations() {
    // Test that small changes in PD lead to small changes in features
    let pd1 = vec![(0.0, 1.0), (0.5, 1.5)];
    let pd2 = vec![(0.01, 1.01), (0.51, 1.51)]; // Small perturbation

    let f1 = landscape_features(&pd1, 3, 16, 0.0, 2.0);
    let f2 = landscape_features(&pd2, 3, 16, 0.0, 2.0);

    let dist = landscape_distance(&f1, &f2);
    assert!(dist < 0.1, "Small perturbation should lead to small change in features");
}

#[test]
fn different_levels_capture_different_features() {
    // Test that different levels capture different aspects
    let pd = vec![(0.0, 1.0), (0.1, 0.9), (0.2, 0.8)];

    let f_1level = landscape_features(&pd, 1, 16, 0.0, 1.0);
    let f_3level = landscape_features(&pd, 3, 16, 0.0, 1.0);

    assert_eq!(f_1level.len(), 16);
    assert_eq!(f_3level.len(), 48);

    // More levels should capture more information
    assert!(f_3level.iter().filter(|&&x| x > 0.0).count() > f_1level.iter().filter(|&&x| x > 0.0).count());
}

#[test]
fn infinite_death_handled() {
    // Test that infinite death times are handled correctly
    let pd = vec![(0.0, 1.0), (0.5, f64::INFINITY)];

    // Should not panic
    let features = landscape_features(&pd, 3, 16, 0.0, 2.0);
    assert_eq!(features.len(), 3 * 16);
}

#[test]
fn single_sample_point() {
    // Test with single sample point
    let pd = vec![(0.0, 1.0)];
    let features = landscape_features(&pd, 2, 1, 0.5, 0.5);

    assert_eq!(features.len(), 2);
    assert!(features[0] > 0.0); // Should have value at t=0.5
}

#[test]
fn zero_levels() {
    // Test with zero levels
    let pd = vec![(0.0, 1.0)];
    let features = landscape_features(&pd, 0, 16, 0.0, 1.0);

    assert_eq!(features.len(), 0);
}

#[test]
fn large_pd_performance() {
    // Test with large persistence diagram
    let pd: Vec<(f64, f64)> = (0..1000)
        .map(|i| {
            let b = i as f64 * 0.01;
            let d = b + 0.1;
            (b, d)
        })
        .collect();

    let features = landscape_features(&pd, 5, 50, 0.0, 10.0);
    assert_eq!(features.len(), 5 * 50);
}

#[test]
fn realistic_circle_example() {
    // Test with realistic persistence diagram from a circle
    let pd = vec![
        (0.0, f64::INFINITY), // Infinite component
        (1.0, f64::INFINITY), // Infinite loop
        (0.0, 0.5),           // Noise
        (0.0, 0.3),           // Noise
    ];

    let features = landscape_features(&pd, 3, 32, 0.0, 2.0);
    assert_eq!(features.len(), 3 * 32);

    // Should have non-zero features
    assert!(features.iter().any(|&x| x > 0.0));
}

#[test]
fn feature_vector_for_ml() {
    // Test that features are suitable for ML
    let pd1 = vec![(0.0, 1.0), (0.5, 1.5)];
    let pd2 = vec![(0.0, 1.0), (0.5, 1.5), (0.2, 0.8)];

    let f1 = landscape_features(&pd1, 5, 20, 0.0, 2.0);
    let f2 = landscape_features(&pd2, 5, 20, 0.0, 2.0);

    // Same dimensions
    assert_eq!(f1.len(), f2.len());

    // Can compute distance
    let dist = landscape_distance(&f1, &f2);
    assert!(dist >= 0.0);

    // Can compute similarity
    let sim = landscape_similarity(&f1, &f2);
    assert!(sim >= -1.0 && sim <= 1.0);
}

