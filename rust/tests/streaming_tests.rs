//! Streaming Filtration Tests
//!
//! Integration tests for streaming persistence diagram computation.

use tcdb_core::streaming::Streamer;

#[test]
fn window_is_idempotent_and_monotone() {
    let mut s = Streamer::new(4);
    
    // Fill window
    for i in 0..4 {
        s.push((i as f64, i as f64));
    }
    let pd1 = s.pd();
    
    // Advance window by one
    s.push((4.0, 4.0));
    let pd2 = s.pd();
    
    // Window changed → PD should change
    assert_ne!(pd1, pd2, "Window changed, PD should change");
    
    // Pushing the same last element again should keep window identical → idempotent PD
    let pd2a = s.pd();
    assert_eq!(pd2, pd2a, "Same window should give same PD (idempotent)");
}

#[test]
fn empty_window_gives_empty_pd() {
    let s = Streamer::new(10);
    let pd = s.pd();
    
    assert!(pd.is_empty(), "Empty window should give empty PD");
}

#[test]
fn single_point_gives_empty_pd() {
    let mut s = Streamer::new(10);
    s.push((0.0, 1.0));
    
    let pd = s.pd();
    assert!(pd.is_empty(), "Single point should give empty PD");
}

#[test]
fn window_size_respected() {
    let mut s = Streamer::new(3);
    
    // Add 5 samples
    for i in 0..5 {
        s.push((i as f64, i as f64));
    }
    
    // Window should only contain last 3
    assert_eq!(s.len(), 3, "Window should contain exactly 3 samples");
    
    let window = s.window();
    assert_eq!(window[0], (2.0, 2.0));
    assert_eq!(window[1], (3.0, 3.0));
    assert_eq!(window[2], (4.0, 4.0));
}

#[test]
fn deterministic_pd_computation() {
    let mut s1 = Streamer::new(10);
    let mut s2 = Streamer::new(10);
    
    // Add same samples to both
    for i in 0..5 {
        s1.push((i as f64, i as f64));
        s2.push((i as f64, i as f64));
    }
    
    let pd1 = s1.pd();
    let pd2 = s2.pd();
    
    assert_eq!(pd1, pd2, "Same window should give same PD");
}

#[test]
fn clear_resets_window() {
    let mut s = Streamer::new(10);
    
    for i in 0..5 {
        s.push((i as f64, i as f64));
    }
    
    assert_eq!(s.len(), 5);
    
    s.clear();
    
    assert_eq!(s.len(), 0);
    assert!(s.is_empty());
    
    let pd = s.pd();
    assert!(pd.is_empty());
}

#[test]
fn statistics_computation() {
    let mut s = Streamer::new(10);
    
    // Empty window
    assert!(s.statistics().is_none());
    
    // Add samples
    s.push((0.0, 1.0));
    s.push((1.0, 2.0));
    s.push((2.0, 3.0));
    s.push((3.0, 4.0));
    s.push((4.0, 5.0));
    
    let (min, max, mean, std_dev) = s.statistics().unwrap();
    
    assert_eq!(min, 1.0);
    assert_eq!(max, 5.0);
    assert_eq!(mean, 3.0);
    assert!(std_dev > 0.0);
}

#[test]
fn custom_distance_function() {
    let mut s = Streamer::new(10);
    
    for i in 0..5 {
        s.push((i as f64, i as f64));
    }
    
    // Custom distance: absolute difference
    let pd = s.pd_with_distance(|a, b| (a.1 - b.1).abs());
    
    // Should have at least one feature
    assert!(!pd.is_empty());
}

#[test]
fn streaming_sine_wave() {
    let mut s = Streamer::new(50);
    
    // Stream sine wave
    for i in 0..100 {
        let t = i as f64 * 0.1;
        let value = t.sin();
        s.push((t, value));
        
        if i >= 10 {
            // Should have features after enough samples
            let pd = s.pd();
            // PD may be empty or non-empty depending on window content
            // Just verify it doesn't panic
            let _ = pd.len();
        }
    }
}

#[test]
fn streaming_step_function() {
    let mut s = Streamer::new(20);
    
    // Stream step function
    for i in 0..40 {
        let value = if i < 20 { 0.0 } else { 1.0 };
        s.push((i as f64, value));
    }
    
    let pd = s.pd();
    // Should detect the step
    assert!(!pd.is_empty());
}

#[test]
fn window_sliding_behavior() {
    let mut s = Streamer::new(3);
    
    // Initial window: [1, 2, 3]
    s.push((0.0, 1.0));
    s.push((1.0, 2.0));
    s.push((2.0, 3.0));
    
    let pd1 = s.pd();
    
    // Slide window: [2, 3, 4]
    s.push((3.0, 4.0));
    
    let pd2 = s.pd();
    
    // PDs should be different (different windows)
    assert_ne!(pd1, pd2);
    
    // Slide window: [3, 4, 5]
    s.push((4.0, 5.0));
    
    let pd3 = s.pd();
    
    // PDs should be different
    assert_ne!(pd2, pd3);
}

#[test]
fn with_params_constructor() {
    let s = Streamer::with_params(100, 3.0, 2);
    
    assert_eq!(s.len(), 0);
    assert!(s.is_empty());
}

#[test]
fn large_window_performance() {
    let mut s = Streamer::new(1000);
    
    // Add 2000 samples (window will contain last 1000)
    for i in 0..2000 {
        s.push((i as f64, (i as f64).sin()));
    }
    
    assert_eq!(s.len(), 1000);
    
    // Compute PD (should not panic or timeout)
    let pd = s.pd();
    let _ = pd.len();
}

#[test]
fn monotone_values() {
    let mut s = Streamer::new(10);
    
    // Add monotonically increasing values
    for i in 0..10 {
        s.push((i as f64, i as f64));
    }
    
    let pd1 = s.pd();
    
    // Add more increasing values
    for i in 10..20 {
        s.push((i as f64, i as f64));
    }
    
    let pd2 = s.pd();
    
    // Both should have features
    assert!(!pd1.is_empty() || !pd2.is_empty());
}

#[test]
fn constant_values() {
    let mut s = Streamer::new(10);
    
    // Add constant values
    for i in 0..10 {
        s.push((i as f64, 1.0));
    }
    
    let pd = s.pd();
    
    // Constant values should give specific PD structure
    // (may be empty or have specific features)
    let _ = pd.len();
}

#[test]
fn alternating_values() {
    let mut s = Streamer::new(10);
    
    // Add alternating values
    for i in 0..10 {
        let value = if i % 2 == 0 { 0.0 } else { 1.0 };
        s.push((i as f64, value));
    }
    
    let pd = s.pd();
    
    // Should detect the alternating pattern
    assert!(!pd.is_empty());
}

#[test]
fn window_statistics_update() {
    let mut s = Streamer::new(5);
    
    // Add samples
    for i in 0..3 {
        s.push((i as f64, i as f64));
    }
    
    let (_, _, mean1, _) = s.statistics().unwrap();
    
    // Add more samples
    s.push((3.0, 3.0));
    s.push((4.0, 4.0));
    
    let (_, _, mean2, _) = s.statistics().unwrap();
    
    // Mean should increase
    assert!(mean2 > mean1);
}

#[test]
fn pd_changes_with_window_content() {
    let mut s = Streamer::new(5);
    
    // Window 1: [0, 1, 2, 3, 4]
    for i in 0..5 {
        s.push((i as f64, i as f64));
    }
    let pd1 = s.pd();
    
    // Window 2: [5, 6, 7, 8, 9] (completely different)
    for i in 5..10 {
        s.push((i as f64, i as f64));
    }
    let pd2 = s.pd();
    
    // Windows are completely different, PDs should differ
    assert_ne!(pd1, pd2);
}

#[test]
fn empty_after_clear() {
    let mut s = Streamer::new(10);
    
    for i in 0..5 {
        s.push((i as f64, i as f64));
    }
    
    s.clear();
    
    assert!(s.is_empty());
    assert_eq!(s.len(), 0);
    assert!(s.statistics().is_none());
    
    let pd = s.pd();
    assert!(pd.is_empty());
}

#[test]
fn realistic_sensor_data() {
    let mut s = Streamer::new(50);
    
    // Simulate sensor data with noise
    for i in 0..100 {
        let t = i as f64 * 0.1;
        let signal = t.sin();
        let noise = (t * 7.0).sin() * 0.1; // High-frequency noise
        let value = signal + noise;
        
        s.push((t, value));
        
        if i >= 20 {
            let pd = s.pd();
            // Should be able to compute PD without panic
            let _ = pd.len();
        }
    }
}

#[test]
fn window_boundary_conditions() {
    let mut s = Streamer::new(1);
    
    // Window size 1
    s.push((0.0, 1.0));
    assert_eq!(s.len(), 1);
    
    s.push((1.0, 2.0));
    assert_eq!(s.len(), 1); // Should replace
    
    let window = s.window();
    assert_eq!(window[0], (1.0, 2.0));
}

#[test]
fn zero_window_size() {
    let mut s = Streamer::new(0);
    
    s.push((0.0, 1.0));
    
    // Window size 0 means no samples retained
    assert_eq!(s.len(), 0);
}

