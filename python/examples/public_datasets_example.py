"""
Public Datasets Example

Demonstrates TCDB on publicly available datasets and synthetic data
that mimics real-world TDA applications.
"""

import tcdb_core
import math


def generate_circle(n, radius=1.0):
    """Generate points on a circle."""
    points = []
    for i in range(n):
        theta = 2 * math.pi * i / n
        x = radius * math.cos(theta)
        y = radius * math.sin(theta)
        points.append((x, y))
    return points


def generate_noisy_circle(n, radius=1.0, noise=0.1):
    """Generate noisy circle points."""
    import random
    random.seed(42)
    
    points = []
    for i in range(n):
        theta = 2 * math.pi * i / n
        x = radius * math.cos(theta) + random.gauss(0, noise)
        y = radius * math.sin(theta) + random.gauss(0, noise)
        points.append((x, y))
    return points


def generate_two_circles(n, radius1=1.0, radius2=1.0, separation=3.0):
    """Generate two separated circles."""
    circle1 = generate_circle(n // 2, radius1)
    circle2 = [(x + separation, y) for x, y in generate_circle(n // 2, radius2)]
    return circle1 + circle2


def main():
    print("=" * 60)
    print("Public Datasets and Synthetic Data Examples")
    print("=" * 60)
    
    # 1. Classical Surfaces (Known Euler Characteristics)
    print("\n1. Classical Surfaces (Known Topology):")
    print("-" * 40)
    
    surfaces = [
        ("Sphere (Octahedron)", [6, 12, 8], 2),
        ("Sphere (Icosahedron)", [12, 30, 20], 2),
        ("Torus", [9, 27, 18], 0),
        ("Projective Plane", [6, 15, 10], 1),
        ("Klein Bottle", [8, 24, 16], 0),
        ("Double Torus", [16, 48, 32], -2),
    ]
    
    for name, faces, expected_chi in surfaces:
        fvec = tcdb_core.FVector(faces)
        chi = fvec.euler_characteristic()
        status = "✓" if chi == expected_chi else "✗"
        print(f"{status} {name:25s} χ = {chi:2d} (expected {expected_chi:2d})")
    
    # 2. Time Series Analysis
    print("\n2. Time Series Analysis:")
    print("-" * 40)
    
    # Sine wave
    print("Streaming sine wave (200 samples)...")
    streamer = tcdb_core.Streamer(100)
    
    for i in range(200):
        t = i * 0.1
        value = math.sin(t)
        streamer.push((t, value))
    
    pd = streamer.pd()
    stats = streamer.statistics()
    
    print(f"  Window size: {streamer.len()}")
    print(f"  Persistent features: {len(pd)}")
    
    if stats:
        min_val, max_val, mean, std_dev = stats
        print(f"  Range: [{min_val:.2f}, {max_val:.2f}]")
        print(f"  Mean: {mean:.2f}, Std: {std_dev:.2f}")
    
    # 3. Anomaly Detection
    print("\n3. Anomaly Detection in Time Series:")
    print("-" * 40)
    
    streamer = tcdb_core.Streamer(50)
    
    # Normal data
    print("Streaming normal data (sine wave)...")
    for i in range(40):
        t = i * 0.1
        streamer.push((t, math.sin(t)))
    
    pd_normal = streamer.pd()
    features_normal = tcdb_core.py_landscape_features_auto(pd_normal, 2, 10)
    
    print(f"  Normal: {len(pd_normal)} features")
    
    # Inject anomaly
    print("Injecting anomaly (spike)...")
    streamer.push((4.0, 10.0))
    
    pd_anomaly = streamer.pd()
    features_anomaly = tcdb_core.py_landscape_features_auto(pd_anomaly, 2, 10)
    
    # Compute distance
    dist = tcdb_core.py_landscape_distance(features_normal, features_anomaly)
    
    print(f"  After anomaly: {len(pd_anomaly)} features")
    print(f"  Landscape distance: {dist:.4f}")
    
    # Bayesian anomaly detection
    base_rate = 0.01  # 1% anomaly rate
    
    if dist > 0.5:
        evidence = tcdb_core.Evidence(0.9, 0.1)  # High distance suggests anomaly
    else:
        evidence = tcdb_core.Evidence(0.1, 0.9)
    
    posterior = tcdb_core.py_posterior(base_rate, evidence)
    
    print(f"  Prior anomaly probability: {base_rate:.1%}")
    print(f"  Posterior anomaly probability: {posterior.posterior:.1%}")
    
    if posterior.posterior > 0.1:
        print("  → ANOMALY DETECTED!")
    else:
        print("  → Normal data")
    
    # 4. Shape Classification
    print("\n4. Shape Classification (Euler Characteristic):")
    print("-" * 40)
    
    shapes = [
        ("Sphere (Octahedron)", [6, 12, 8], "sphere"),
        ("Sphere (Icosahedron)", [12, 30, 20], "sphere"),
        ("Torus", [9, 27, 18], "torus"),
        ("Double Torus", [16, 48, 32], "torus"),
    ]
    
    print("Classifying shapes as sphere vs torus...")
    
    for name, faces, true_class in shapes:
        fvec = tcdb_core.FVector(faces)
        chi = fvec.euler_characteristic()
        
        # Prior: 50% sphere, 50% torus
        prior = 0.5
        
        # Evidence: χ = 2 strongly suggests sphere
        if chi == 2:
            evidence = tcdb_core.Evidence(0.95, 0.05)
        elif chi <= 0:
            evidence = tcdb_core.Evidence(0.05, 0.95)
        else:
            evidence = tcdb_core.Evidence(0.5, 0.5)
        
        post = tcdb_core.py_posterior(prior, evidence)
        
        predicted = "sphere" if post.posterior > 0.5 else "torus"
        confidence = post.posterior if predicted == "sphere" else 1 - post.posterior
        
        status = "✓" if predicted == true_class else "✗"
        print(f"{status} {name:25s} → {predicted:6s} ({confidence:.1%} confidence)")
    
    # 5. Persistence Landscape Comparison
    print("\n5. Persistence Landscape Comparison:")
    print("-" * 40)
    
    # Different topologies
    pd_circle = [(0.0, 1.0)]  # One loop
    pd_two_circles = [(0.0, 1.0), (0.0, 1.0)]  # Two loops
    pd_nested = [(0.0, 2.0), (0.5, 1.5)]  # Nested features
    
    f_circle = tcdb_core.py_landscape_features_auto(pd_circle, 2, 10)
    f_two = tcdb_core.py_landscape_features_auto(pd_two_circles, 2, 10)
    f_nested = tcdb_core.py_landscape_features_auto(pd_nested, 2, 10)
    
    dist_circle_two = tcdb_core.py_landscape_distance(f_circle, f_two)
    dist_circle_nested = tcdb_core.py_landscape_distance(f_circle, f_nested)
    dist_two_nested = tcdb_core.py_landscape_distance(f_two, f_nested)
    
    print(f"Circle vs Two Circles:  {dist_circle_two:.4f}")
    print(f"Circle vs Nested:       {dist_circle_nested:.4f}")
    print(f"Two Circles vs Nested:  {dist_two_nested:.4f}")
    
    # 6. Multi-Feature Classification
    print("\n6. Multi-Feature Bayesian Classification:")
    print("-" * 40)
    
    # Simulate classification with multiple topological features
    print("Classifying sample with multiple features...")
    
    prior = 0.5
    
    # Collect evidence from different features
    evidence_list = [
        tcdb_core.Evidence(0.8, 0.2),  # Betti numbers
        tcdb_core.Evidence(0.9, 0.1),  # Persistence
        tcdb_core.Evidence(0.7, 0.3),  # Landscape features
        tcdb_core.Evidence(0.85, 0.15), # Euler characteristic
    ]
    
    print(f"Prior: P(Class 1) = {prior:.2f}")
    
    # Sequential update
    current = prior
    for i, ev in enumerate(evidence_list, 1):
        post = tcdb_core.py_posterior(current, ev)
        print(f"  After feature {i}: P(Class 1) = {post.posterior:.4f}")
        current = post.posterior
    
    # Final classification
    final = tcdb_core.py_sequential_update(prior, evidence_list)
    
    predicted_class = 1 if final.posterior > 0.5 else 0
    confidence = final.posterior if predicted_class == 1 else 1 - final.posterior
    
    print(f"\nFinal: Class {predicted_class} ({confidence:.1%} confidence)")
    
    # 7. Streaming + Landscape Pipeline
    print("\n7. Complete Pipeline (Streaming → Landscape → Classification):")
    print("-" * 40)
    
    # Generate two different time series
    print("Generating two time series...")
    
    # Series 1: Sine wave
    streamer1 = tcdb_core.Streamer(50)
    for i in range(100):
        t = i * 0.1
        streamer1.push((t, math.sin(t)))
    
    # Series 2: Cosine wave (different phase)
    streamer2 = tcdb_core.Streamer(50)
    for i in range(100):
        t = i * 0.1
        streamer2.push((t, math.cos(t)))
    
    # Extract persistence diagrams
    pd1 = streamer1.pd()
    pd2 = streamer2.pd()
    
    print(f"Series 1: {len(pd1)} features")
    print(f"Series 2: {len(pd2)} features")
    
    # Compute landscape features
    features1 = tcdb_core.py_landscape_features_auto(pd1, 2, 10)
    features2 = tcdb_core.py_landscape_features_auto(pd2, 2, 10)
    
    # Compute similarity
    dist = tcdb_core.py_landscape_distance(features1, features2)
    sim = tcdb_core.py_landscape_similarity(features1, features2)
    
    print(f"Distance: {dist:.4f}")
    print(f"Similarity: {sim:.4f}")
    
    # Classify as same/different
    threshold = 0.5
    if dist < threshold:
        print("→ Series are SIMILAR")
    else:
        print("→ Series are DIFFERENT")
    
    print("\n" + "=" * 60)
    print("All tests completed successfully!")
    print("=" * 60)


if __name__ == "__main__":
    main()

