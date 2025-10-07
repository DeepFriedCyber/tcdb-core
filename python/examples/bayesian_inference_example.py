"""
Bayesian Inference Example

Demonstrates probabilistic reasoning over topological evidence.
"""

import tcdb_core


def main():
    print("=" * 60)
    print("Bayesian Inference Examples")
    print("=" * 60)
    
    # Basic posterior computation
    print("\n1. Basic Posterior Computation:")
    print("-" * 40)
    
    prior = 0.5
    evidence = tcdb_core.Evidence(0.9, 0.1)
    posterior = tcdb_core.py_posterior(prior, evidence)
    
    print(f"Prior: {prior:.2f}")
    print(f"Evidence: P(E|H) = {evidence.like_h:.2f}, P(E|¬H) = {evidence.like_not_h:.2f}")
    print(f"Likelihood Ratio: {evidence.likelihood_ratio():.2f}")
    print(f"Posterior: {posterior.posterior:.2f}")
    print(f"Belief Change: {posterior.belief_change():+.2f}")
    
    # Supportive vs contradictory evidence
    print("\n2. Supportive vs Contradictory Evidence:")
    print("-" * 40)
    
    prior = 0.5
    
    # Supportive evidence
    ev_support = tcdb_core.Evidence(0.9, 0.1)
    post_support = tcdb_core.py_posterior(prior, ev_support)
    print(f"Supportive evidence: {prior:.2f} → {post_support.posterior:.2f}")
    
    # Contradictory evidence
    ev_contra = tcdb_core.Evidence(0.1, 0.9)
    post_contra = tcdb_core.py_posterior(prior, ev_contra)
    print(f"Contradictory evidence: {prior:.2f} → {post_contra.posterior:.2f}")
    
    # Neutral evidence
    ev_neutral = tcdb_core.Evidence(0.5, 0.5)
    post_neutral = tcdb_core.py_posterior(prior, ev_neutral)
    print(f"Neutral evidence: {prior:.2f} → {post_neutral.posterior:.2f}")
    
    # Sequential updating
    print("\n3. Sequential Updating:")
    print("-" * 40)
    
    prior = 0.5
    evidence_list = [
        tcdb_core.Evidence(0.8, 0.2),
        tcdb_core.Evidence(0.9, 0.1),
        tcdb_core.Evidence(0.7, 0.3),
    ]
    
    print(f"Initial prior: {prior:.2f}")
    
    # Manual sequential update
    current = prior
    for i, ev in enumerate(evidence_list, 1):
        post = tcdb_core.py_posterior(current, ev)
        print(f"After evidence {i}: {post.posterior:.2f}")
        current = post.posterior
    
    # Automatic sequential update
    final_post = tcdb_core.py_sequential_update(prior, evidence_list)
    print(f"Final posterior (automatic): {final_post.posterior:.2f}")
    
    # Anomaly detection
    print("\n4. Anomaly Detection:")
    print("-" * 40)
    
    # Base rate: 1% of data are anomalies
    prior_anomaly = 0.01
    
    # Topological feature observed (high persistence)
    # P(high_persistence | anomaly) = 0.8
    # P(high_persistence | normal) = 0.05
    ev_anomaly = tcdb_core.Evidence(0.8, 0.05)
    
    post_anomaly = tcdb_core.py_posterior(prior_anomaly, ev_anomaly)
    
    print(f"Prior probability of anomaly: {prior_anomaly:.1%}")
    print(f"Observed: high persistence feature")
    print(f"Posterior probability of anomaly: {post_anomaly.posterior:.1%}")
    
    if post_anomaly.posterior > 0.5:
        print("→ ANOMALY DETECTED!")
    else:
        print(f"→ Likely normal (anomaly probability: {post_anomaly.posterior:.1%})")
    
    # Model selection
    print("\n5. Model Selection:")
    print("-" * 40)
    
    # Two competing models: Model A vs Model B
    prior_a = 0.5
    
    # Topological features fit Model A better
    # P(features | Model A) = 0.9
    # P(features | Model B) = 0.3
    ev_model = tcdb_core.Evidence(0.9, 0.3)
    
    post_model = tcdb_core.py_posterior(prior_a, ev_model)
    
    print(f"P(Model A) = {prior_a:.2f}")
    print(f"P(Model B) = {1 - prior_a:.2f}")
    print(f"Observed topological features")
    print(f"P(Model A | features) = {post_model.posterior:.2f}")
    print(f"P(Model B | features) = {1 - post_model.posterior:.2f}")
    print(f"Bayes Factor: {post_model.bayes_factor():.2f}")
    
    if post_model.posterior > 0.7:
        print("→ Strong evidence for Model A")
    elif post_model.posterior < 0.3:
        print("→ Strong evidence for Model B")
    else:
        print("→ Weak evidence")
    
    # Classification
    print("\n6. Classification with Multiple Features:")
    print("-" * 40)
    
    # Binary classification: Class 0 vs Class 1
    prior_class1 = 0.5
    
    # Multiple topological features observed
    features = [
        tcdb_core.Evidence(0.7, 0.3),  # Betti numbers
        tcdb_core.Evidence(0.8, 0.2),  # Persistence
        tcdb_core.Evidence(0.6, 0.4),  # Landscape features
    ]
    
    final_class = tcdb_core.py_sequential_update(prior_class1, features)
    
    print(f"Prior: P(Class 1) = {prior_class1:.2f}")
    print(f"Observed {len(features)} topological features")
    print(f"Posterior: P(Class 1 | features) = {final_class.posterior:.2f}")
    
    if final_class.posterior > 0.5:
        confidence = final_class.posterior
        print(f"→ Predicted: Class 1 (confidence: {confidence:.1%})")
    else:
        confidence = 1 - final_class.posterior
        print(f"→ Predicted: Class 0 (confidence: {confidence:.1%})")
    
    print("\n" + "=" * 60)


if __name__ == "__main__":
    main()

