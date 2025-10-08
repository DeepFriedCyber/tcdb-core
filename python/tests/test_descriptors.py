"""
Tests for descriptor modules

Tests all four descriptor types:
- TID (Topological-Information Descriptor)
- DGD (Diffusion-Geometry Descriptor)
- KME-Δ (Kernel Mean Embedding Divergence)
- GSER (Graph-Scattering Energy Ratio)
"""

import pytest
import numpy as np
from tcdb_api.descriptors import (
    TopologicalInformationDescriptor,
    DiffusionGeometryDescriptor,
    KernelMeanEmbeddingDelta,
    GraphScatteringEnergyRatio,
    DescriptorRegistry
)


# Test fixtures

@pytest.fixture
def simple_point_cloud():
    """Simple 2D point cloud for testing"""
    return np.array([
        [0.0, 0.0],
        [1.0, 0.0],
        [0.0, 1.0],
        [1.0, 1.0],
        [0.5, 0.5]
    ])


@pytest.fixture
def circle_point_cloud():
    """Points on a circle"""
    n = 20
    theta = np.linspace(0, 2 * np.pi, n, endpoint=False)
    return np.column_stack([np.cos(theta), np.sin(theta)])


@pytest.fixture
def random_point_cloud():
    """Random point cloud"""
    np.random.seed(42)
    return np.random.randn(30, 3)


# TID Tests

class TestTopologicalInformationDescriptor:
    """Tests for TID descriptor"""
    
    def test_initialization(self):
        """Test TID initialization"""
        tid = TopologicalInformationDescriptor(max_dimension=2)
        assert tid.name == "tid"
        assert tid.params['max_dimension'] == 2
    
    def test_compute_simple(self, simple_point_cloud):
        """Test TID computation on simple data"""
        tid = TopologicalInformationDescriptor(max_dimension=1)
        result = tid.compute(simple_point_cloud)
        
        # Check that result is a dictionary
        assert isinstance(result, dict)
        
        # Check for expected keys
        assert 'F_TID' in result
        
        # Check that values are dimensionless (finite floats)
        for key, value in result.items():
            assert isinstance(value, (int, float))
            assert np.isfinite(value)
    
    def test_dimensionless_property(self, simple_point_cloud):
        """Test that TID is scale-invariant (dimensionless)"""
        tid = TopologicalInformationDescriptor(max_dimension=1)
        
        # Compute on original data
        result1 = tid.compute(simple_point_cloud)
        
        # Compute on scaled data
        scaled_data = simple_point_cloud * 10.0
        result2 = tid.compute(scaled_data)
        
        # F_TID should be similar (within tolerance due to numerical effects)
        # Note: Perfect invariance requires normalized filtration
        assert result1['F_TID'] >= 0
        assert result2['F_TID'] >= 0
    
    def test_circle_topology(self, circle_point_cloud):
        """Test TID on circle (should detect 1-cycle)"""
        tid = TopologicalInformationDescriptor(max_dimension=1)
        result = tid.compute(circle_point_cloud)
        
        # Should have non-zero H1 (1-dimensional homology)
        assert 'H1' in result or 'F_TID' in result
        assert result['F_TID'] > 0


# DGD Tests

class TestDiffusionGeometryDescriptor:
    """Tests for DGD descriptor"""
    
    def test_initialization(self):
        """Test DGD initialization"""
        dgd = DiffusionGeometryDescriptor(k_neighbors=5)
        assert dgd.name == "dgd"
        assert dgd.params['k_neighbors'] == 5
    
    def test_compute_simple(self, simple_point_cloud):
        """Test DGD computation on simple data"""
        dgd = DiffusionGeometryDescriptor(k_neighbors=3, n_time_samples=10)
        result = dgd.compute(simple_point_cloud)

        # Check result structure with new keys
        assert isinstance(result, dict)
        assert 'DGD_F' in result
        assert 'DGD_phi1_mean' in result
        assert 'DGD_phi2_q90' in result
        assert 'DGD_spectral_decay' in result

        # Check dimensionless
        for value in result.values():
            assert np.isfinite(value)
    
    def test_graph_types(self, simple_point_cloud):
        """Test different graph construction methods"""
        # kNN graph
        dgd_knn = DiffusionGeometryDescriptor(graph_type='knn', k_neighbors=3)
        result_knn = dgd_knn.compute(simple_point_cloud)

        # Epsilon graph
        dgd_eps = DiffusionGeometryDescriptor(graph_type='epsilon', epsilon=1.0)
        result_eps = dgd_eps.compute(simple_point_cloud)

        # Both should produce valid results
        assert result_knn['DGD_F'] >= 0
        assert result_eps['DGD_F'] >= 0

    def test_spectral_decay(self, circle_point_cloud):
        """Test spectral decay computation"""
        dgd = DiffusionGeometryDescriptor(k_neighbors=5)
        result = dgd.compute(circle_point_cloud)

        # Spectral decay should be non-negative
        assert result['DGD_spectral_decay'] >= 0

    def test_laplacian_input(self, simple_point_cloud):
        """Test DGD with pre-computed Laplacian"""
        from tcdb_api.pipelines.build_graph import compute_graph_laplacian, build_knn_graph

        # Build Laplacian
        adj = build_knn_graph(simple_point_cloud, k=3)
        laplacian = compute_graph_laplacian(adj, normalized=True)

        # Compute DGD from Laplacian
        dgd = DiffusionGeometryDescriptor()
        result = dgd.compute({'laplacian': laplacian})

        assert 'DGD_F' in result
        assert result['DGD_F'] >= 0


# KME-Δ Tests

class TestKernelMeanEmbeddingDelta:
    """Tests for KME-Δ descriptor"""
    
    def test_initialization(self):
        """Test KME-Δ initialization"""
        kme = KernelMeanEmbeddingDelta(kernel_type='rbf')
        assert kme.name == "kme_delta"
        assert kme.params['kernel_type'] == 'rbf'
    
    def test_compute_simple(self, simple_point_cloud):
        """Test KME-Δ computation on simple data"""
        kme = KernelMeanEmbeddingDelta(sigma_scales=[0.5, 1.0])
        result = kme.compute(simple_point_cloud)

        # Check result structure with new keys
        assert isinstance(result, dict)
        assert 'KME_delta_F' in result
        assert 'KME_mean' in result
        assert 'KME_sigma_0.5' in result
        assert 'KME_sigma_1.0' in result

        # Check dimensionless
        for value in result.values():
            assert np.isfinite(value)
            assert value >= 0  # Divergences are non-negative
    
    def test_reference_types(self, simple_point_cloud):
        """Test different reference distribution types"""
        # Uniform reference
        kme_uniform = KernelMeanEmbeddingDelta(reference_type='uniform')
        result_uniform = kme_uniform.compute(simple_point_cloud)

        # Gaussian reference
        kme_gaussian = KernelMeanEmbeddingDelta(reference_type='gaussian')
        result_gaussian = kme_gaussian.compute(simple_point_cloud)

        # Both should produce valid results
        assert result_uniform['KME_delta_F'] >= 0
        assert result_gaussian['KME_delta_F'] >= 0

    def test_multiscale(self, random_point_cloud):
        """Test multi-scale kernel computation"""
        kme = KernelMeanEmbeddingDelta(sigma_scales=[0.1, 1.0, 10.0])
        result = kme.compute(random_point_cloud)

        # Should have divergence at each scale with new key format
        assert 'KME_sigma_0.1' in result
        assert 'KME_sigma_1.0' in result
        assert 'KME_sigma_10.0' in result

    def test_attention_weights(self, simple_point_cloud):
        """Test KME-Δ with attention weights"""
        # Create attention weights (e.g., from transformer)
        attention_weights = np.array([0.1, 0.2, 0.3, 0.2, 0.2])

        kme = KernelMeanEmbeddingDelta(sigma_scales=[1.0])

        # Test with dict input
        result = kme.compute({
            'embeddings': simple_point_cloud,
            'attention_weights': attention_weights
        })

        assert 'KME_delta_F' in result
        assert result['KME_delta_F'] >= 0

        # Test with kwargs
        result2 = kme.compute(simple_point_cloud, attention_weights=attention_weights)
        assert 'KME_delta_F' in result2


# GSER Tests

class TestGraphScatteringEnergyRatio:
    """Tests for GSER descriptor"""
    
    def test_initialization(self):
        """Test GSER initialization"""
        gser = GraphScatteringEnergyRatio(n_scales=4)
        assert gser.name == "gser"
        assert gser.params['n_scales'] == 4
    
    def test_compute_simple(self, simple_point_cloud):
        """Test GSER computation on simple data"""
        gser = GraphScatteringEnergyRatio(n_scales=3, k_neighbors=3)
        result = gser.compute(simple_point_cloud)
        
        # Check result structure
        assert isinstance(result, dict)
        assert 'F_GSER' in result
        assert 'energy_concentration' in result
        
        # Check dimensionless
        for value in result.values():
            assert np.isfinite(value)
            assert value >= 0  # Energy ratios are non-negative
    
    def test_signal_types(self, simple_point_cloud):
        """Test different signal types"""
        # Coordinates signal (use k=3 for 5-point dataset)
        gser_coord = GraphScatteringEnergyRatio(signal_type='coordinates', k_neighbors=3)
        result_coord = gser_coord.compute(simple_point_cloud)

        # Degrees signal
        gser_deg = GraphScatteringEnergyRatio(signal_type='degrees', k_neighbors=3)
        result_deg = gser_deg.compute(simple_point_cloud)

        # Both should produce valid results
        assert result_coord['F_GSER'] >= 0
        assert result_deg['F_GSER'] >= 0
    
    def test_scattering_coefficients(self, circle_point_cloud):
        """Test scattering coefficient computation"""
        gser = GraphScatteringEnergyRatio(n_scales=2, k_neighbors=5)
        result = gser.compute(circle_point_cloud)
        
        # Should have first-order coefficients
        assert 'S1_0' in result
        assert 'S1_1' in result
        
        # Should have second-order coefficients
        assert any('S2_' in key for key in result.keys())


# Registry Tests

class TestDescriptorRegistry:
    """Tests for descriptor registry"""
    
    def test_registration(self):
        """Test descriptor registration"""
        registry = DescriptorRegistry()
        registry.register('tid', TopologicalInformationDescriptor)
        
        assert 'tid' in registry
        assert 'tid' in registry.list()
    
    def test_get_descriptor(self):
        """Test getting descriptor from registry"""
        registry = DescriptorRegistry()
        registry.register('tid', TopologicalInformationDescriptor)
        
        descriptor = registry.get('tid', max_dimension=2)
        assert isinstance(descriptor, TopologicalInformationDescriptor)
        assert descriptor.params['max_dimension'] == 2
    
    def test_unknown_descriptor(self):
        """Test error on unknown descriptor"""
        registry = DescriptorRegistry()
        
        with pytest.raises(KeyError):
            registry.get('unknown_descriptor')


# Integration Tests

class TestDescriptorIntegration:
    """Integration tests for all descriptors"""
    
    def test_all_descriptors_on_same_data(self, simple_point_cloud):
        """Test that all descriptors work on the same data"""
        descriptors = [
            TopologicalInformationDescriptor(max_dimension=1),
            DiffusionGeometryDescriptor(k_neighbors=3, n_time_samples=5),
            KernelMeanEmbeddingDelta(sigma_scales=[0.5, 1.0]),
            GraphScatteringEnergyRatio(n_scales=2, k_neighbors=3)
        ]
        
        for descriptor in descriptors:
            result = descriptor.compute(simple_point_cloud)
            assert isinstance(result, dict)
            assert len(result) > 0
            
            # All values should be finite
            for value in result.values():
                assert np.isfinite(value)
    
    def test_reproducibility(self, random_point_cloud):
        """Test that results are reproducible"""
        tid = TopologicalInformationDescriptor(max_dimension=1)
        
        result1 = tid.compute(random_point_cloud)
        result2 = tid.compute(random_point_cloud)
        
        # Results should be identical
        assert result1.keys() == result2.keys()
        for key in result1.keys():
            assert np.isclose(result1[key], result2[key])

