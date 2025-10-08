"""
Descriptor Usage Examples

Demonstrates how to use the four descriptor modules:
1. TID (Topological-Information Descriptor)
2. DGD (Diffusion-Geometry Descriptor)
3. KME-Δ (Kernel Mean Embedding Divergence)
4. GSER (Graph-Scattering Energy Ratio)
"""

import numpy as np
import sys
sys.path.insert(0, '../python')

from tcdb_api.descriptors import (
    TopologicalInformationDescriptor,
    DiffusionGeometryDescriptor,
    KernelMeanEmbeddingDelta,
    GraphScatteringEnergyRatio,
    DescriptorRegistry
)


def create_sample_data():
    """Create sample point clouds for demonstration"""
    
    # 1. Simple square
    square = np.array([
        [0.0, 0.0],
        [1.0, 0.0],
        [1.0, 1.0],
        [0.0, 1.0],
        [0.5, 0.5]
    ])
    
    # 2. Circle
    n = 30
    theta = np.linspace(0, 2 * np.pi, n, endpoint=False)
    circle = np.column_stack([np.cos(theta), np.sin(theta)])
    
    # 3. Random cloud
    np.random.seed(42)
    random_cloud = np.random.randn(50, 3)
    
    return {
        'square': square,
        'circle': circle,
        'random': random_cloud
    }


def example_tid():
    """Example: Topological-Information Descriptor"""
    print("\n" + "="*60)
    print("TID (Topological-Information Descriptor)")
    print("="*60)
    
    data = create_sample_data()
    
    # Create TID descriptor
    tid = TopologicalInformationDescriptor(
        max_dimension=2,
        max_edge_length=None,  # Auto-computed
        n_bins=100
    )
    
    # Compute on circle (should detect 1-cycle)
    print("\nComputing TID on circle...")
    result = tid.compute(data['circle'])
    
    print(f"F_TID (combined): {result['F_TID']:.4f}")
    
    for key, value in sorted(result.items()):
        if key != 'F_TID':
            print(f"  {key}: {value:.4f}")
    
    # Compute Betti numbers
    betti = tid.compute_betti_numbers(data['circle'])
    print(f"\nBetti numbers: {betti}")


def example_dgd():
    """Example: Diffusion-Geometry Descriptor"""
    print("\n" + "="*60)
    print("DGD (Diffusion-Geometry Descriptor)")
    print("="*60)

    data = create_sample_data()

    # Create DGD descriptor
    dgd = DiffusionGeometryDescriptor(
        graph_type='knn',
        k_neighbors=5,
        n_time_samples=20,
        time_range=(0.01, 10.0)
    )

    # Compute on random cloud
    print("\nComputing DGD on random cloud...")
    result = dgd.compute(data['random'], times='logspace')

    print(f"DGD_F (weighted integral): {result['DGD_F']:.4f}")
    print(f"  φ1 mean (curvature ratio): {result['DGD_phi1_mean']:.4f}")
    print(f"  φ2 q90 (trace ratio): {result['DGD_phi2_q90']:.4f}")
    print(f"  Spectral decay: {result['DGD_spectral_decay']:.4f}")

    # Example with pre-computed Laplacian
    print("\nComputing DGD from pre-computed Laplacian...")
    from tcdb_api.pipelines.build_graph import build_knn_graph, compute_graph_laplacian

    adj = build_knn_graph(data['circle'], k=5)
    laplacian = compute_graph_laplacian(adj, normalized=True)

    result2 = dgd.compute({'laplacian': laplacian})
    print(f"DGD_F (from Laplacian): {result2['DGD_F']:.4f}")


def example_kme_delta():
    """Example: Kernel Mean Embedding Divergence"""
    print("\n" + "="*60)
    print("KME-Δ (Kernel Mean Embedding Divergence)")
    print("="*60)

    data = create_sample_data()

    # Create KME-Δ descriptor
    kme = KernelMeanEmbeddingDelta(
        kernel_type='rbf',
        sigma_scales=[0.1, 0.5, 1.0, 2.0, 5.0],
        reference_type='uniform'
    )

    # Compute on square
    print("\nComputing KME-Δ on square...")
    result = kme.compute(data['square'])

    print(f"KME_delta_F (combined): {result['KME_delta_F']:.4f}")
    print(f"  Mean divergence: {result['KME_mean']:.4f}")
    print(f"  Max divergence: {result['KME_max']:.4f}")

    print("\nDivergence at each scale:")
    for sigma in [0.1, 0.5, 1.0, 2.0, 5.0]:
        key = f'KME_sigma_{sigma}'
        if key in result:
            print(f"  σ={sigma}: {result[key]:.4f}")

    # Example with attention weights (e.g., from transformer)
    print("\nComputing KME-Δ with attention weights...")
    attention_weights = np.array([0.1, 0.2, 0.3, 0.2, 0.2])

    result_weighted = kme.compute({
        'embeddings': data['square'],
        'attention_weights': attention_weights
    })

    print(f"KME_delta_F (weighted): {result_weighted['KME_delta_F']:.4f}")


def example_gser():
    """Example: Graph-Scattering Energy Ratio"""
    print("\n" + "="*60)
    print("GSER (Graph-Scattering Energy Ratio)")
    print("="*60)
    
    data = create_sample_data()
    
    # Create GSER descriptor
    gser = GraphScatteringEnergyRatio(
        n_scales=4,
        graph_type='knn',
        k_neighbors=5,
        signal_type='coordinates'
    )
    
    # Compute on circle
    print("\nComputing GSER on circle...")
    result = gser.compute(data['circle'])
    
    print(f"F_GSER (combined): {result['F_GSER']:.4f}")
    print(f"  Energy concentration: {result['energy_concentration']:.4f}")
    
    print("\nFirst-order scattering:")
    for key in sorted(result.keys()):
        if key.startswith('S1_'):
            print(f"  {key}: {result[key]:.4f}")
    
    print("\nSecond-order scattering (sample):")
    count = 0
    for key in sorted(result.keys()):
        if key.startswith('S2_') and count < 3:
            print(f"  {key}: {result[key]:.4f}")
            count += 1


def example_registry():
    """Example: Using the descriptor registry"""
    print("\n" + "="*60)
    print("Descriptor Registry")
    print("="*60)
    
    # Create registry
    registry = DescriptorRegistry()
    
    # Register descriptors
    registry.register('tid', TopologicalInformationDescriptor)
    registry.register('dgd', DiffusionGeometryDescriptor)
    registry.register('kme_delta', KernelMeanEmbeddingDelta)
    registry.register('gser', GraphScatteringEnergyRatio)
    
    print(f"\nAvailable descriptors: {registry.list()}")
    
    # Get and use a descriptor
    data = create_sample_data()
    
    print("\nComputing all descriptors on circle...")
    for name in registry.list():
        descriptor = registry.get(name)
        result = descriptor.compute(data['circle'])
        
        # Get the main combined feature
        main_key = f'F_{name.upper()}'
        if main_key in result:
            print(f"  {name}: {result[main_key]:.4f}")


def example_batch_comparison():
    """Example: Compare all descriptors on different datasets"""
    print("\n" + "="*60)
    print("Batch Comparison")
    print("="*60)
    
    data = create_sample_data()
    
    # Create all descriptors
    descriptors = {
        'TID': TopologicalInformationDescriptor(max_dimension=1),
        'DGD': DiffusionGeometryDescriptor(k_neighbors=5, n_time_samples=10),
        'KME-Δ': KernelMeanEmbeddingDelta(sigma_scales=[0.5, 1.0, 2.0]),
        'GSER': GraphScatteringEnergyRatio(n_scales=3, k_neighbors=5)
    }
    
    # Compute on each dataset
    for dataset_name, dataset in data.items():
        print(f"\n{dataset_name.upper()}:")
        
        for desc_name, descriptor in descriptors.items():
            try:
                result = descriptor.compute(dataset)
                
                # Get main feature
                main_key = f'F_{descriptor.name.upper()}'
                if main_key in result:
                    print(f"  {desc_name:8s}: {result[main_key]:.4f}")
            except Exception as e:
                print(f"  {desc_name:8s}: Error - {str(e)[:40]}")


def example_scale_invariance():
    """Example: Demonstrate scale invariance"""
    print("\n" + "="*60)
    print("Scale Invariance Test")
    print("="*60)
    
    # Create data at different scales
    base_data = np.array([
        [0.0, 0.0],
        [1.0, 0.0],
        [0.0, 1.0],
        [1.0, 1.0],
        [0.5, 0.5]
    ])
    
    scales = [1.0, 10.0, 100.0]
    
    # Test each descriptor
    descriptors = {
        'TID': TopologicalInformationDescriptor(max_dimension=1),
        'DGD': DiffusionGeometryDescriptor(k_neighbors=3),
        'KME-Δ': KernelMeanEmbeddingDelta(sigma_scales=[0.5, 1.0]),
        'GSER': GraphScatteringEnergyRatio(n_scales=2, k_neighbors=3)
    }
    
    for desc_name, descriptor in descriptors.items():
        print(f"\n{desc_name}:")
        
        results = []
        for scale in scales:
            scaled_data = base_data * scale
            result = descriptor.compute(scaled_data)
            
            main_key = f'F_{descriptor.name.upper()}'
            value = result.get(main_key, 0.0)
            results.append(value)
            
            print(f"  Scale {scale:6.1f}: {value:.4f}")
        
        # Check relative variation
        if max(results) > 0:
            variation = (max(results) - min(results)) / max(results)
            print(f"  Relative variation: {variation:.2%}")


if __name__ == "__main__":
    print("\n" + "="*60)
    print("TCDB Descriptor Examples")
    print("="*60)
    
    # Run all examples
    example_tid()
    example_dgd()
    example_kme_delta()
    example_gser()
    example_registry()
    example_batch_comparison()
    example_scale_invariance()
    
    print("\n" + "="*60)
    print("Examples complete!")
    print("="*60 + "\n")

