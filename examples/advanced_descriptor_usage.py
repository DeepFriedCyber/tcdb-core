"""
Advanced Descriptor Usage Examples

Demonstrates advanced features:
1. DGD with efficient trace estimation (Lanczos, stochastic)
2. KME-Δ with attention weights
3. Pre-computed Laplacians
4. Large-scale optimizations
"""

import numpy as np
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'python'))

from tcdb_api.descriptors import (
    DiffusionGeometryDescriptor,
    KernelMeanEmbeddingDelta
)
from tcdb_api.pipelines.build_graph import (
    build_knn_graph,
    compute_graph_laplacian
)


def example_dgd_efficient_methods():
    """
    Example: DGD with different trace estimation methods
    
    Demonstrates automatic selection based on matrix size:
    - Small (n ≤ 100): Exact eigendecomposition
    - Medium (100 < n ≤ 500): Lanczos method
    - Large (n > 500): Stochastic trace estimator
    """
    print("\n" + "="*70)
    print("DGD: Efficient Heat Trace Estimation")
    print("="*70)
    
    dgd = DiffusionGeometryDescriptor(
        k_neighbors=5,
        n_time_samples=20
    )
    
    # Small dataset: exact method
    print("\n1. Small dataset (n=50) - Exact eigendecomposition")
    small_data = np.random.randn(50, 3)
    result_small = dgd.compute(small_data)
    print(f"   DGD_F: {result_small['DGD_F']:.4f}")
    print(f"   Method: Exact (full eigendecomposition)")
    
    # Medium dataset: Lanczos method
    print("\n2. Medium dataset (n=200) - Lanczos method")
    medium_data = np.random.randn(200, 3)
    result_medium = dgd.compute(medium_data)
    print(f"   DGD_F: {result_medium['DGD_F']:.4f}")
    print(f"   Method: Lanczos (sparse eigendecomposition)")
    
    # Large dataset: stochastic estimator
    print("\n3. Large dataset (n=600) - Stochastic trace estimator")
    large_data = np.random.randn(600, 3)
    result_large = dgd.compute(large_data)
    print(f"   DGD_F: {result_large['DGD_F']:.4f}")
    print(f"   Method: Stochastic (Hutchinson estimator)")


def example_dgd_precomputed_laplacian():
    """
    Example: DGD with pre-computed Laplacian
    
    Useful when you want to:
    - Reuse the same graph structure
    - Use custom graph construction
    - Avoid redundant computation
    """
    print("\n" + "="*70)
    print("DGD: Pre-computed Laplacian")
    print("="*70)
    
    # Generate data
    np.random.seed(42)
    points = np.random.randn(100, 3)
    
    # Build graph and Laplacian once
    print("\n1. Building graph and Laplacian...")
    adj_matrix = build_knn_graph(points, k=5, weighted=True)
    laplacian = compute_graph_laplacian(adj_matrix, normalized=True)
    print(f"   Graph: {adj_matrix.shape[0]} nodes")
    print(f"   Laplacian: {laplacian.shape}")
    
    # Compute DGD multiple times with different parameters
    print("\n2. Computing DGD with different time ranges...")
    
    dgd1 = DiffusionGeometryDescriptor(n_time_samples=10)
    result1 = dgd1.compute({'laplacian': laplacian})
    print(f"   10 time samples: DGD_F = {result1['DGD_F']:.4f}")
    
    dgd2 = DiffusionGeometryDescriptor(n_time_samples=30)
    result2 = dgd2.compute({'laplacian': laplacian})
    print(f"   30 time samples: DGD_F = {result2['DGD_F']:.4f}")


def example_dgd_custom_times():
    """
    Example: DGD with custom time grid
    
    Instead of automatic logspace, specify exact times.
    """
    print("\n" + "="*70)
    print("DGD: Custom Time Grid")
    print("="*70)
    
    points = np.random.randn(50, 3)
    dgd = DiffusionGeometryDescriptor()
    
    # Custom time points (e.g., focus on specific scales)
    custom_times = np.array([0.01, 0.05, 0.1, 0.5, 1.0, 2.0, 5.0])
    
    print(f"\nCustom times: {custom_times}")
    result = dgd.compute(points, times=custom_times)
    
    print(f"DGD_F: {result['DGD_F']:.4f}")
    print(f"φ1 mean: {result['DGD_phi1_mean']:.4f}")
    print(f"φ2 q90: {result['DGD_phi2_q90']:.4f}")


def example_kme_attention_weights():
    """
    Example: KME-Δ with attention weights
    
    Simulates transformer attention weights for weighted MMD.
    """
    print("\n" + "="*70)
    print("KME-Δ: Attention-Weighted Embeddings")
    print("="*70)
    
    # Simulate transformer embeddings
    n_tokens = 20
    embedding_dim = 64
    
    np.random.seed(42)
    embeddings = np.random.randn(n_tokens, embedding_dim)
    
    # Simulate attention weights (e.g., from self-attention)
    # Higher weights = more important tokens
    attention_weights = np.random.dirichlet(np.ones(n_tokens))
    
    print(f"\nEmbeddings: {embeddings.shape}")
    print(f"Attention weights: {attention_weights.shape}")
    print(f"Top 3 attention weights: {sorted(attention_weights, reverse=True)[:3]}")
    
    # Compute KME-Δ with attention weights
    kme = KernelMeanEmbeddingDelta(
        sigma_scales=[0.5, 1.0, 2.0],
        reference_type='gaussian'
    )
    
    # Method 1: Dict input
    print("\n1. Using dict input:")
    result1 = kme.compute({
        'embeddings': embeddings,
        'attention_weights': attention_weights
    })
    print(f"   KME_delta_F: {result1['KME_delta_F']:.4f}")
    
    # Method 2: Kwargs
    print("\n2. Using kwargs:")
    result2 = kme.compute(embeddings, attention_weights=attention_weights)
    print(f"   KME_delta_F: {result2['KME_delta_F']:.4f}")
    
    # Compare with uniform weights
    print("\n3. Comparison with uniform weights:")
    result_uniform = kme.compute(embeddings)
    print(f"   KME_delta_F (uniform): {result_uniform['KME_delta_F']:.4f}")
    print(f"   KME_delta_F (weighted): {result1['KME_delta_F']:.4f}")
    print(f"   Difference: {abs(result1['KME_delta_F'] - result_uniform['KME_delta_F']):.4f}")


def example_kme_multiscale_analysis():
    """
    Example: KME-Δ multi-scale analysis
    
    Shows how different scales capture different aspects.
    """
    print("\n" + "="*70)
    print("KME-Δ: Multi-Scale Analysis")
    print("="*70)
    
    # Create data with structure at different scales
    np.random.seed(42)
    
    # Fine-scale structure
    cluster1 = np.random.randn(30, 2) * 0.1 + [0, 0]
    cluster2 = np.random.randn(30, 2) * 0.1 + [2, 0]
    
    # Coarse-scale structure
    data = np.vstack([cluster1, cluster2])
    
    # Test different scale ranges
    scale_configs = [
        ([0.01, 0.05, 0.1], "Fine scales"),
        ([0.5, 1.0, 2.0], "Medium scales"),
        ([5.0, 10.0, 20.0], "Coarse scales"),
        ([0.1, 1.0, 10.0], "Multi-scale")
    ]
    
    for scales, description in scale_configs:
        kme = KernelMeanEmbeddingDelta(
            sigma_scales=scales,
            reference_type='uniform'
        )
        result = kme.compute(data)
        
        print(f"\n{description} (σ = {scales}):")
        print(f"  KME_delta_F: {result['KME_delta_F']:.4f}")
        
        for sigma in scales:
            key = f'KME_sigma_{sigma}'
            print(f"  {key}: {result[key]:.4f}")


def example_performance_comparison():
    """
    Example: Performance comparison of different methods
    """
    print("\n" + "="*70)
    print("Performance Comparison")
    print("="*70)
    
    import time
    
    sizes = [50, 100, 200, 500]
    
    print("\nDGD computation time vs. dataset size:")
    print(f"{'Size':<10} {'Time (s)':<12} {'Method':<20}")
    print("-" * 45)
    
    for n in sizes:
        data = np.random.randn(n, 3)
        dgd = DiffusionGeometryDescriptor(k_neighbors=5, n_time_samples=10)
        
        start = time.time()
        result = dgd.compute(data)
        elapsed = time.time() - start
        
        # Determine method used
        if n <= 100:
            method = "Exact"
        elif n <= 500:
            method = "Lanczos"
        else:
            method = "Stochastic"
        
        print(f"{n:<10} {elapsed:<12.4f} {method:<20}")


def example_layer_comparison():
    """
    Example: Compare embeddings from different layers

    Simulates comparing neural network layers (same dimension).
    """
    print("\n" + "="*70)
    print("Layer-wise Embedding Comparison")
    print("="*70)

    # Simulate embeddings from different layers (same dimension for comparison)
    n_samples = 50
    embedding_dim = 64

    np.random.seed(42)
    layers = {
        'layer_1': np.random.randn(n_samples, embedding_dim),
        'layer_2': np.random.randn(n_samples, embedding_dim) * 0.8,  # Slightly different scale
        'layer_3': np.random.randn(n_samples, embedding_dim) * 1.2,
        'layer_4': np.random.randn(n_samples, embedding_dim) * 0.9,
    }

    # Use first layer as reference
    reference = layers['layer_1']

    kme = KernelMeanEmbeddingDelta(
        sigma_scales=[1.0, 2.0],
        reference_type='data',
        reference_data=reference
    )

    print("\nComparing layers to layer_1 (reference):")
    for layer_name, embeddings in layers.items():
        result = kme.compute(embeddings)
        print(f"  {layer_name}: KME_delta_F = {result['KME_delta_F']:.4f}")


if __name__ == "__main__":
    print("\n" + "="*70)
    print("Advanced Descriptor Examples")
    print("="*70)
    
    # Run all examples
    example_dgd_efficient_methods()
    example_dgd_precomputed_laplacian()
    example_dgd_custom_times()
    example_kme_attention_weights()
    example_kme_multiscale_analysis()
    example_performance_comparison()
    example_layer_comparison()
    
    print("\n" + "="*70)
    print("Examples complete!")
    print("="*70 + "\n")

