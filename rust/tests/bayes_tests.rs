//! Bayesian Inference Tests
//!
//! Integration tests for Bayesian updating with topological evidence.

use tcdb_core::bayes::*;

#[test]
fn posterior_updates_in_right_direction() {
    // Evidence supports H
    let ev = Evidence { like_h: 0.9, like_not_h: 0.1 };
    let p = posterior(0.5, ev);
    assert!(p.posterior > 0.5, "Supportive evidence should increase belief");

    // Evidence supports ¬H
    let ev2 = Evidence { like_h: 0.1, like_not_h: 0.9 };
    let p2 = posterior(0.5, ev2);
    assert!(p2.posterior < 0.5, "Contradictory evidence should decrease belief");
}

#[test]
fn neutral_evidence_preserves_prior() {
    let prior = 0.5;
    let ev = Evidence::new(0.5, 0.5); // Neutral evidence
    let post = posterior(prior, ev);
    
    assert!((post.posterior - prior).abs() < 1e-10, "Neutral evidence should preserve prior");
}

#[test]
fn strong_evidence_high_posterior() {
    let prior = 0.5;
    let ev = Evidence::new(0.99, 0.01); // Very strong evidence
    let post = posterior(prior, ev);
    
    assert!(post.posterior > 0.95, "Very strong evidence should give high posterior");
}

#[test]
fn weak_prior_strong_evidence() {
    let prior = 0.1; // Low initial belief
    let ev = Evidence::new(0.9, 0.1); // Strong evidence
    let post = posterior(prior, ev);
    
    assert!(post.posterior > prior, "Strong evidence should increase even weak prior");
    assert!(post.posterior > 0.4, "Should significantly increase belief");
}

#[test]
fn strong_prior_weak_evidence() {
    let prior = 0.9; // High initial belief
    let ev = Evidence::new(0.6, 0.4); // Weak evidence
    let post = posterior(prior, ev);
    
    assert!(post.posterior > prior, "Supportive evidence should increase belief");
    assert!(post.posterior < 0.95, "Weak evidence shouldn't increase much");
}

#[test]
fn likelihood_ratio_interpretation() {
    let ev1 = Evidence::new(0.9, 0.1);
    assert_eq!(ev1.likelihood_ratio(), 9.0, "LR = 9 means 9x more likely under H");
    
    let ev2 = Evidence::new(0.5, 0.5);
    assert_eq!(ev2.likelihood_ratio(), 1.0, "LR = 1 means neutral evidence");
    
    let ev3 = Evidence::new(0.1, 0.9);
    assert!((ev3.likelihood_ratio() - 1.0/9.0).abs() < 1e-10, "LR < 1 means evidence against H");
}

#[test]
fn supports_h_detection() {
    let ev1 = Evidence::new(0.9, 0.1);
    assert!(ev1.supports_h(), "Should support H");
    
    let ev2 = Evidence::new(0.1, 0.9);
    assert!(!ev2.supports_h(), "Should not support H");
    
    let ev3 = Evidence::new(0.5, 0.5);
    assert!(!ev3.supports_h(), "Neutral evidence doesn't support H");
}

#[test]
fn is_neutral_detection() {
    let ev1 = Evidence::new(0.5, 0.5);
    assert!(ev1.is_neutral(0.01), "Should be neutral");
    
    let ev2 = Evidence::new(0.51, 0.49);
    assert!(ev2.is_neutral(0.05), "Should be approximately neutral");
    
    let ev3 = Evidence::new(0.9, 0.1);
    assert!(!ev3.is_neutral(0.01), "Should not be neutral");
}

#[test]
fn belief_change_computation() {
    let prior = 0.5;
    let ev = Evidence::new(0.9, 0.1);
    let post = posterior(prior, ev);
    
    let change = post.belief_change();
    assert!(change > 0.0, "Belief should increase");
    assert!(change > 0.3, "Should increase significantly");
}

#[test]
fn posterior_odds_computation() {
    let prior = 0.5;
    let ev = Evidence::new(0.9, 0.1);
    let post = posterior(prior, ev);
    
    let odds = post.posterior_odds();
    assert!(odds > 1.0, "Posterior odds should favor H");
}

#[test]
fn bayes_factor_interpretation() {
    let prior = 0.5;
    let ev = Evidence::new(0.9, 0.1);
    let post = posterior(prior, ev);
    
    let bf = post.bayes_factor();
    assert!(bf > 1.0, "Bayes factor should be > 1 for supportive evidence");
    assert!((bf - 9.0).abs() < 1e-10, "Bayes factor should equal likelihood ratio");
}

#[test]
fn sequential_update_accumulates_evidence() {
    let prior = 0.5;
    let evidence = vec![
        Evidence::new(0.8, 0.2),
        Evidence::new(0.9, 0.1),
        Evidence::new(0.7, 0.3),
    ];
    
    let final_post = sequential_update(prior, &evidence);
    
    assert!(final_post.posterior > prior, "Sequential evidence should increase belief");
    assert!(final_post.posterior > 0.9, "Multiple pieces of evidence should strongly increase belief");
}

#[test]
fn sequential_update_order_matters() {
    let prior = 0.5;
    
    // Same evidence, different order
    let evidence1 = vec![
        Evidence::new(0.9, 0.1),
        Evidence::new(0.8, 0.2),
    ];
    
    let evidence2 = vec![
        Evidence::new(0.8, 0.2),
        Evidence::new(0.9, 0.1),
    ];
    
    let post1 = sequential_update(prior, &evidence1);
    let post2 = sequential_update(prior, &evidence2);
    
    // Order shouldn't matter for final posterior (Bayes is commutative)
    assert!((post1.posterior - post2.posterior).abs() < 1e-10, "Order shouldn't affect final posterior");
}

#[test]
fn sequential_update_empty_evidence() {
    let prior = 0.5;
    let evidence: Vec<Evidence> = vec![];
    
    let post = sequential_update(prior, &evidence);
    
    assert_eq!(post.posterior, prior, "No evidence should preserve prior");
}

#[test]
fn zero_likelihood_edge_case() {
    let prior = 0.5;
    let ev = Evidence::new(0.0, 0.0); // Both likelihoods zero
    let post = posterior(prior, ev);
    
    assert_eq!(post.posterior, 0.5, "Zero likelihoods should give 0.5");
}

#[test]
fn extreme_prior_low() {
    let prior = 0.01; // Very low prior
    let ev = Evidence::new(0.9, 0.1);
    let post = posterior(prior, ev);
    
    assert!(post.posterior > prior, "Should increase belief");
    assert!(post.posterior < 0.5, "But shouldn't overcome very low prior completely");
}

#[test]
fn extreme_prior_high() {
    let prior = 0.99; // Very high prior
    let ev = Evidence::new(0.1, 0.9); // Contradictory evidence
    let post = posterior(prior, ev);
    
    assert!(post.posterior < prior, "Should decrease belief");
    assert!(post.posterior > 0.5, "But shouldn't overcome very high prior completely");
}

#[test]
fn multiple_weak_evidence_accumulates() {
    let prior = 0.5;
    
    // Many pieces of weak evidence
    let evidence: Vec<Evidence> = (0..10)
        .map(|_| Evidence::new(0.6, 0.4))
        .collect();
    
    let final_post = sequential_update(prior, &evidence);
    
    assert!(final_post.posterior > 0.9, "Many weak pieces should accumulate to strong belief");
}

#[test]
fn contradictory_evidence_sequence() {
    let prior = 0.5;
    
    // Alternating supportive and contradictory evidence
    let evidence = vec![
        Evidence::new(0.9, 0.1), // Support
        Evidence::new(0.1, 0.9), // Contradict
        Evidence::new(0.9, 0.1), // Support
        Evidence::new(0.1, 0.9), // Contradict
    ];
    
    let final_post = sequential_update(prior, &evidence);
    
    // Should end up close to prior (evidence cancels out)
    assert!((final_post.posterior - prior).abs() < 0.1, "Contradictory evidence should roughly cancel");
}

#[test]
fn evidence_serialization() {
    let ev = Evidence::new(0.9, 0.1);
    
    // Serialize to JSON
    let json = serde_json::to_string(&ev).unwrap();
    
    // Deserialize back
    let ev2: Evidence = serde_json::from_str(&json).unwrap();
    
    assert_eq!(ev, ev2, "Serialization should preserve evidence");
}

#[test]
fn posterior_serialization() {
    let prior = 0.5;
    let ev = Evidence::new(0.9, 0.1);
    let post = posterior(prior, ev);
    
    // Serialize to JSON
    let json = serde_json::to_string(&post).unwrap();
    
    // Deserialize back
    let post2: Posterior = serde_json::from_str(&json).unwrap();
    
    assert_eq!(post, post2, "Serialization should preserve posterior");
}

#[test]
fn realistic_anomaly_detection() {
    // Scenario: Detecting anomalies using topological features
    
    let prior = 0.01; // 1% base rate of anomalies
    
    // Topological feature (e.g., high persistence) observed
    // P(high_persistence | anomaly) = 0.8
    // P(high_persistence | normal) = 0.05
    let ev = Evidence::new(0.8, 0.05);
    
    let post = posterior(prior, ev);
    
    // Posterior should be much higher than prior
    assert!(post.posterior > 0.1, "Anomaly probability should increase significantly");
    assert!(post.posterior < 0.5, "But still not certain given low base rate");
}

#[test]
fn realistic_classification() {
    // Scenario: Classifying data using TDA features
    
    let prior = 0.5; // Equal prior for two classes
    
    // Multiple topological features observed
    let evidence = vec![
        Evidence::new(0.7, 0.3), // Feature 1: moderate support
        Evidence::new(0.8, 0.2), // Feature 2: strong support
        Evidence::new(0.6, 0.4), // Feature 3: weak support
    ];
    
    let final_post = sequential_update(prior, &evidence);
    
    assert!(final_post.posterior > 0.8, "Combined features should give high confidence");
}

#[test]
fn realistic_model_selection() {
    // Scenario: Selecting between two models based on topological fit
    
    let prior = 0.5; // No preference initially
    
    // Model 1 fits topological features better
    let ev = Evidence::new(0.9, 0.3);
    
    let post = posterior(prior, ev);
    
    assert!(post.posterior > 0.7, "Better fit should favor model 1");
}

#[test]
#[should_panic(expected = "Prior must be in (0, 1)")]
fn invalid_prior_zero() {
    let ev = Evidence::new(0.9, 0.1);
    posterior(0.0, ev);
}

#[test]
#[should_panic(expected = "Prior must be in (0, 1)")]
fn invalid_prior_one() {
    let ev = Evidence::new(0.9, 0.1);
    posterior(1.0, ev);
}

#[test]
#[should_panic(expected = "Prior must be in (0, 1)")]
fn invalid_prior_negative() {
    let ev = Evidence::new(0.9, 0.1);
    posterior(-0.1, ev);
}

#[test]
#[should_panic(expected = "Prior must be in (0, 1)")]
fn invalid_prior_greater_than_one() {
    let ev = Evidence::new(0.9, 0.1);
    posterior(1.5, ev);
}

#[test]
#[should_panic(expected = "like_h must be in [0,1]")]
fn invalid_likelihood_h_negative() {
    Evidence::new(-0.1, 0.5);
}

#[test]
#[should_panic(expected = "like_h must be in [0,1]")]
fn invalid_likelihood_h_greater_than_one() {
    Evidence::new(1.5, 0.5);
}

#[test]
#[should_panic(expected = "like_not_h must be in [0,1]")]
fn invalid_likelihood_not_h_negative() {
    Evidence::new(0.5, -0.1);
}

#[test]
#[should_panic(expected = "like_not_h must be in [0,1]")]
fn invalid_likelihood_not_h_greater_than_one() {
    Evidence::new(0.5, 1.5);
}

