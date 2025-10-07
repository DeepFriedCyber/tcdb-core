"""
Landscape Embeddings Example

Demonstrates topology-aware embeddings for machine learning.
"""

import tcdb_core


def main():
    print("=" * 60)
    print("Landscape Embeddings Examples")
    print("=" * 60)
    
    # Basic landscape features
    print("\n1. Basic Landscape Features:")
    print("-" * 40)
    
    # Simple persistence diagram
    pd = [(0.0, 1.0), (0.5, 1.5), (1.0, 2.0)]
    
    # Compute landscape features
    # 2 levels, 10 samples, range [0, 2]
    features = tcdb_core.py_landscape_features(pd, 2, 10, 0.0, 2.0)
    
    print(f"Persistence diagram: {len(pd)} points")
    print(f"Landscape features: {len(features)} dimensions (2 levels × 10 samples)")
    print(f"First 5 features: {[f'{f:.2f}' for f in features[:5]]}")
    
    # Automatic range detection
    print("\n2. Automatic Range Detection:")
    print("-" * 40)
    
    pd = [(0.2, 0.9), (0.5, 1.5), (1.0, 2.5)]
    
    # Auto-detect range from data
    features_auto = tcdb_core.py_landscape_features_auto(pd, 3, 20)
    
    print(f"Persistence diagram: {len(pd)} points")
    print(f"Landscape features (auto): {len(features_auto)} dimensions (3 levels × 20 samples)")
    
    # Distance computation
    print("\n3. Distance Between Landscapes:")
    print("-" * 40)
    
    pd1 = [(0.0, 1.0), (0.5, 1.5)]
    pd2 = [(0.0, 1.1), (0.5, 1.6)]
    
    f1 = tcdb_core.py_landscape_features_auto(pd1, 2, 10)
    f2 = tcdb_core.py_landscape_features_auto(pd2, 2, 10)
    
    distance = tcdb_core.py_landscape_distance(f1, f2)
    
    print(f"PD 1: {pd1}")
    print(f"PD 2: {pd2}")
    print(f"Landscape distance: {distance:.4f}")
    
    # Similarity computation
    print("\n4. Similarity Between Landscapes:")
    print("-" * 40)
    
    similarity = tcdb_core.py_landscape_similarity(f1, f2)
    
    print(f"Landscape similarity: {similarity:.4f}")
    print(f"(1.0 = identical, 0.0 = completely different)")
    
    # Identical features
    print("\n5. Identical Features:")
    print("-" * 40)
    
    pd_same = [(0.0, 1.0), (0.5, 1.5), (1.0, 2.0)]
    
    f_same1 = tcdb_core.py_landscape_features_auto(pd_same, 2, 10)
    f_same2 = tcdb_core.py_landscape_features_auto(pd_same, 2, 10)
    
    dist_same = tcdb_core.py_landscape_distance(f_same1, f_same2)
    sim_same = tcdb_core.py_landscape_similarity(f_same1, f_same2)
    
    print(f"Distance (identical): {dist_same:.10f}")
    print(f"Similarity (identical): {sim_same:.10f}")
    
    # Different topologies
    print("\n6. Different Topologies:")
    print("-" * 40)
    
    # Circle (1 loop)
    pd_circle = [(0.0, 0.5), (0.1, 0.9)]
    
    # Two circles (2 loops)
    pd_two_circles = [(0.0, 0.5), (0.0, 0.5), (0.1, 0.9), (0.1, 0.9)]
    
    f_circle = tcdb_core.py_landscape_features_auto(pd_circle, 2, 10)
    f_two = tcdb_core.py_landscape_features_auto(pd_two_circles, 2, 10)
    
    dist_diff = tcdb_core.py_landscape_distance(f_circle, f_two)
    sim_diff = tcdb_core.py_landscape_similarity(f_circle, f_two)
    
    print(f"Circle vs Two Circles:")
    print(f"  Distance: {dist_diff:.4f}")
    print(f"  Similarity: {sim_diff:.4f}")
    
    # Classification example
    print("\n7. Classification Example:")
    print("-" * 40)
    
    # Training data (simplified)
    class_a_pds = [
        [(0.0, 1.0), (0.5, 1.5)],
        [(0.1, 1.1), (0.6, 1.6)],
        [(0.0, 0.9), (0.4, 1.4)],
    ]
    
    class_b_pds = [
        [(0.0, 2.0), (1.0, 3.0)],
        [(0.1, 2.1), (1.1, 3.1)],
        [(0.0, 1.9), (0.9, 2.9)],
    ]
    
    # Compute landscape features for training data
    class_a_features = [tcdb_core.py_landscape_features_auto(pd, 2, 10) for pd in class_a_pds]
    class_b_features = [tcdb_core.py_landscape_features_auto(pd, 2, 10) for pd in class_b_pds]
    
    # Test sample
    test_pd = [(0.05, 1.05), (0.55, 1.55)]
    test_features = tcdb_core.py_landscape_features_auto(test_pd, 2, 10)
    
    # Compute distances to each class
    dist_to_a = [tcdb_core.py_landscape_distance(test_features, f) for f in class_a_features]
    dist_to_b = [tcdb_core.py_landscape_distance(test_features, f) for f in class_b_features]
    
    avg_dist_a = sum(dist_to_a) / len(dist_to_a)
    avg_dist_b = sum(dist_to_b) / len(dist_to_b)
    
    print(f"Test sample: {test_pd}")
    print(f"Average distance to Class A: {avg_dist_a:.4f}")
    print(f"Average distance to Class B: {avg_dist_b:.4f}")
    
    if avg_dist_a < avg_dist_b:
        print("→ Predicted: Class A")
    else:
        print("→ Predicted: Class B")
    
    # Clustering example
    print("\n8. Clustering Example:")
    print("-" * 40)
    
    # Multiple persistence diagrams
    pds = [
        [(0.0, 1.0), (0.5, 1.5)],      # Group 1
        [(0.1, 1.1), (0.6, 1.6)],      # Group 1
        [(0.0, 2.0), (1.0, 3.0)],      # Group 2
        [(0.1, 2.1), (1.1, 3.1)],      # Group 2
    ]
    
    # Compute all features
    all_features = [tcdb_core.py_landscape_features_auto(pd, 2, 10) for pd in pds]
    
    # Compute pairwise distances
    print("Pairwise distances:")
    for i in range(len(all_features)):
        for j in range(i + 1, len(all_features)):
            dist = tcdb_core.py_landscape_distance(all_features[i], all_features[j])
            print(f"  PD {i} ↔ PD {j}: {dist:.4f}")
    
    print("\n" + "=" * 60)


if __name__ == "__main__":
    main()

