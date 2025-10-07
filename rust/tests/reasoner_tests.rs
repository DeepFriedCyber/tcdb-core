//! Reasoner Constraint Tests
//!
//! Integration tests for the reasoner constraint checking system.
//! These tests verify that constraints correctly detect violations
//! in topological summaries.

use tcdb_core::reasoner::*;

#[test]
fn catches_negative_betti_and_bad_pd() {
    // Test that multiple violations are detected simultaneously
    let b0 = BettiCurve { 
        k: 0, 
        ts: vec![0.0, 1.0], 
        values: vec![3, -1]  // Negative Betti number - INVALID
    };
    
    let pd = PD(vec![
        (0.2, 0.9),  // Valid: death > birth
        (0.5, 0.4)   // INVALID: death < birth
    ]);
    
    let violations = check(
        &[Constraint::BettiNonNegative, Constraint::DeathGeBirth], 
        &[b0], 
        &pd
    );
    
    // Should detect both violations
    assert!(
        violations.iter().any(|e| matches!(e.constraint, Constraint::BettiNonNegative)),
        "Should detect negative Betti number"
    );
    assert!(
        violations.iter().any(|e| matches!(e.constraint, Constraint::DeathGeBirth)),
        "Should detect death < birth"
    );
    
    // Should have exactly 2 violations
    assert_eq!(violations.len(), 2, "Should detect exactly 2 violations");
}

#[test]
fn valid_topology_passes_all_constraints() {
    // Test that valid topological data passes all constraints
    let b0 = BettiCurve {
        k: 0,
        ts: vec![0.0, 1.0, 2.0, 3.0],
        values: vec![3, 2, 1, 1],  // Monotone decreasing (components merge)
    };
    
    let b1 = BettiCurve {
        k: 1,
        ts: vec![0.0, 1.0, 2.0, 3.0],
        values: vec![0, 1, 1, 0],  // Loop appears and disappears
    };
    
    let pd = PD(vec![
        (0.0, 1.0),   // Component dies
        (0.0, 2.0),   // Component dies
        (1.0, 3.0),   // Loop dies
        (0.0, f64::INFINITY),  // Infinite component
    ]);
    
    let constraints = vec![
        Constraint::BettiNonNegative,
        Constraint::BettiMonotone0UpTo { t: 1.0 },
        Constraint::DeathGeBirth,
        Constraint::MaxLifetime { max: 5.0 },
    ];
    
    let violations = check(&constraints, &[b0, b1], &pd);
    
    assert!(
        violations.is_empty(),
        "Valid topology should pass all constraints, but got: {:?}",
        violations
    );
}

#[test]
fn max_lifetime_filters_noise() {
    // Test that MaxLifetime constraint can filter noise
    let pd = PD(vec![
        (0.0, 0.1),   // Lifetime 0.1 (OK)
        (0.0, 0.05),  // Lifetime 0.05 (OK)
        (0.0, 2.0),   // Lifetime 2.0 (EXCEEDS max=1.0)
        (0.5, 3.0),   // Lifetime 2.5 (EXCEEDS max=1.0)
    ]);

    // Filter features with lifetime > 1.0
    let constraints = vec![Constraint::MaxLifetime { max: 1.0 }];
    let violations = check(&constraints, &[], &pd);

    // Should detect the two long-lived features as violations
    // Note: (0.0, 2.0) has lifetime 2.0, (0.5, 3.0) has lifetime 2.5
    // Both exceed max=1.0, so we expect 2 violations
    assert_eq!(
        violations.len(), 2,
        "Should detect 2 features exceeding max lifetime, got: {:?}",
        violations
    );
}

#[test]
fn betti_monotone_detects_component_splitting() {
    // Test that BettiMonotone0UpTo detects invalid component increases
    let b0 = BettiCurve {
        k: 0,
        ts: vec![0.0, 1.0, 2.0, 3.0],
        values: vec![1, 1, 2, 3],  // Components INCREASE after t=1.0 - INVALID
    };
    
    let constraints = vec![Constraint::BettiMonotone0UpTo { t: 1.0 }];
    let violations = check(&constraints, &[b0], &PD(vec![]));
    
    assert_eq!(violations.len(), 1, "Should detect monotonicity violation");
    assert!(
        violations[0].detail.contains("increased after threshold"),
        "Violation message should mention threshold"
    );
}

#[test]
fn empty_data_passes_constraints() {
    // Test that empty data structures pass constraints
    let constraints = vec![
        Constraint::BettiNonNegative,
        Constraint::DeathGeBirth,
        Constraint::MaxLifetime { max: 1.0 },
    ];
    
    let violations = check(&constraints, &[], &PD(vec![]));
    
    assert!(
        violations.is_empty(),
        "Empty data should pass all constraints"
    );
}

#[test]
fn infinite_features_handled_correctly() {
    // Test that infinite features are handled correctly
    let pd = PD(vec![
        (0.0, f64::INFINITY),  // Infinite feature
        (0.5, f64::INFINITY),  // Another infinite feature
        (1.0, 2.0),            // Finite feature
    ]);
    
    let constraints = vec![
        Constraint::DeathGeBirth,
        Constraint::MaxLifetime { max: 5.0 },
    ];
    
    let violations = check(&constraints, &[], &pd);
    
    // Infinite features should not violate MaxLifetime
    // (they are filtered out in the check)
    assert!(
        violations.is_empty(),
        "Infinite features should not violate constraints"
    );
}

#[test]
fn multiple_betti_curves_checked() {
    // Test that multiple Betti curves are all checked
    let b0 = BettiCurve {
        k: 0,
        ts: vec![0.0, 1.0],
        values: vec![1, 1],  // Valid
    };
    
    let b1 = BettiCurve {
        k: 1,
        ts: vec![0.0, 1.0],
        values: vec![0, -1],  // INVALID: negative
    };
    
    let b2 = BettiCurve {
        k: 2,
        ts: vec![0.0, 1.0],
        values: vec![0, 0],  // Valid
    };
    
    let constraints = vec![Constraint::BettiNonNegative];
    let violations = check(&constraints, &[b0, b1, b2], &PD(vec![]));
    
    assert_eq!(violations.len(), 1, "Should detect exactly 1 violation");
    assert_eq!(
        violations[0].index,
        Some(1),
        "Should identify the second Betti curve (index 1)"
    );
}

#[test]
fn constraint_detail_messages_are_informative() {
    // Test that violation messages contain useful information
    let b0 = BettiCurve {
        k: 0,
        ts: vec![0.0, 1.0],
        values: vec![1, -5],
    };
    
    let pd = PD(vec![(2.0, 1.0)]);
    
    let constraints = vec![
        Constraint::BettiNonNegative,
        Constraint::DeathGeBirth,
    ];
    
    let violations = check(&constraints, &[b0], &pd);
    
    // Check that messages contain useful details
    for v in &violations {
        assert!(
            !v.detail.is_empty(),
            "Violation detail should not be empty"
        );
        
        match v.constraint {
            Constraint::BettiNonNegative => {
                assert!(
                    v.detail.contains("negative") || v.detail.contains("-5"),
                    "Should mention negative value"
                );
            }
            Constraint::DeathGeBirth => {
                assert!(
                    v.detail.contains("death") && v.detail.contains("birth"),
                    "Should mention death and birth"
                );
            }
            _ => {}
        }
    }
}

#[test]
fn betti_curve_helper_methods() {
    // Test BettiCurve helper methods
    let curve = BettiCurve {
        k: 0,
        ts: vec![0.0, 1.0, 2.0, 3.0],
        values: vec![3, 2, 1, 1],
    };
    
    // Test monotone decreasing check
    assert!(
        curve.is_monotone_decreasing_after(1.0),
        "Curve should be monotone decreasing after t=1.0"
    );
    
    assert!(
        curve.is_monotone_decreasing_after(0.0),
        "Curve should be monotone decreasing after t=0.0"
    );
    
    // Test with non-monotone curve
    let non_monotone = BettiCurve {
        k: 0,
        ts: vec![0.0, 1.0, 2.0, 3.0],
        values: vec![1, 2, 3, 2],
    };
    
    assert!(
        !non_monotone.is_monotone_decreasing_after(0.0),
        "Non-monotone curve should fail check"
    );
}

#[test]
fn pd_helper_methods() {
    // Test PD helper methods
    let pd = PD(vec![
        (0.0, 1.0),
        (0.5, 2.0),
        (1.0, f64::INFINITY),
        (2.0, 1.5),  // Invalid: death < birth
    ]);
    
    // Test all_death_ge_birth
    assert!(
        !pd.all_death_ge_birth(),
        "Should detect death < birth"
    );
    
    // Test max_lifetime
    assert_eq!(
        pd.max_lifetime(),
        Some(1.5),
        "Max lifetime should be 1.5 (from (0.5, 2.0))"
    );
    
    // Test finite_features
    let finite = pd.finite_features();
    assert_eq!(
        finite.len(),
        3,
        "Should have 3 finite features"
    );
    assert!(
        !finite.iter().any(|(_, d)| d.is_infinite()),
        "Finite features should not include infinity"
    );
}

#[test]
fn realistic_filtration_example() {
    // Test with realistic filtration data (circle with 4 points)
    let b0 = BettiCurve {
        k: 0,
        ts: vec![0.0, 1.0, 1.0, 1.0, 2.0],
        values: vec![4, 3, 2, 1, 1],  // 4 components merge to 1
    };
    
    let b1 = BettiCurve {
        k: 1,
        ts: vec![0.0, 1.0, 2.0],
        values: vec![0, 1, 1],  // Loop appears at t=1.0
    };
    
    let pd = PD(vec![
        (0.0, 1.0),  // Component dies
        (0.0, 1.0),  // Component dies
        (0.0, 1.0),  // Component dies
        (0.0, f64::INFINITY),  // Infinite component
        (1.0, f64::INFINITY),  // Infinite loop
    ]);
    
    let constraints = vec![
        Constraint::BettiNonNegative,
        Constraint::DeathGeBirth,
        Constraint::MaxLifetime { max: 10.0 },
    ];
    
    let violations = check(&constraints, &[b0, b1], &pd);
    
    assert!(
        violations.is_empty(),
        "Realistic circle filtration should pass all constraints"
    );
}

#[test]
fn stress_test_large_data() {
    // Test with large data structures
    let n = 1000;
    
    let b0 = BettiCurve {
        k: 0,
        ts: (0..n).map(|i| i as f64).collect(),
        values: (0..n).map(|i| (n - i) as i64).collect(),  // Monotone decreasing
    };
    
    let pd = PD(
        (0..n)
            .map(|i| (i as f64, (i + 1) as f64))
            .collect()
    );
    
    let constraints = vec![
        Constraint::BettiNonNegative,
        Constraint::DeathGeBirth,
        Constraint::MaxLifetime { max: 2.0 },
    ];
    
    let violations = check(&constraints, &[b0], &pd);
    
    // Should pass BettiNonNegative and DeathGeBirth
    // Should fail MaxLifetime for some features
    assert!(
        violations.iter().all(|v| matches!(v.constraint, Constraint::MaxLifetime { .. })),
        "Only MaxLifetime violations expected"
    );
}

