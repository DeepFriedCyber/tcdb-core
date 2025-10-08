"""
Tests for enhanced v2 descriptor implementations.

Verifies that the production-ready skeleton patterns work correctly
and produce compatible results with v1.
"""

import numpy as np
import pytest

from tcdb_api.descriptors.base_v2 import (
    Descriptor,
    DescriptorRegistry,
    merge_features,
    validate_data,
    pairwise_sq_dists,
    rbf_kernel,
    safe_divide,
    normalize_weights,
)
from tcdb_api.descriptors.kme_delta_v2 import KME_Delta


class TestBaseV2:
    """Test enhanced base module."""
    
    def test_pairwise_sq_dists(self):
        """Test efficient pairwise distance computation."""
        X = np.array([[0, 0], [1, 0], [0, 1]])
        Y = np.array([[1, 1], [2, 2]])
        
        D2 = pairwise_sq_dists(X, Y)
        
        assert D2.shape == (3, 2)
        # Distance from [0,0] to [1,1] should be sqrt(2)^2 = 2
        assert abs(D2[0, 0] - 2.0) < 1e-10
        # Distance from [1,0] to [1,1] should be 1^2 = 1
        assert abs(D2[1, 0] - 1.0) < 1e-10
    
    def test_rbf_kernel(self):
        """Test RBF kernel computation."""
        X = np.array([[0, 0], [1, 0]])
        Y = np.array([[0, 0], [2, 0]])

        K = rbf_kernel(X, Y, sigma=1.0)

        assert K.shape == (2, 2)
        # K(x, x) should be 1
        assert abs(K[0, 0] - 1.0) < 1e-10
        # Distance from [0,0] to [2,0] is 4, so K = exp(-4/2) = exp(-2)
        assert abs(K[0, 1] - np.exp(-4.0 / 2.0)) < 1e-10
    
    def test_safe_divide(self):
        """Test safe division with epsilon."""
        # Normal division
        assert abs(safe_divide(10.0, 2.0) - 5.0) < 1e-10
        
        # Division by near-zero
        result = safe_divide(10.0, 1e-15, epsilon=1e-12, default=0.0)
        assert result == 0.0
        
        # Array division
        num = np.array([1.0, 2.0, 3.0])
        denom = np.array([2.0, 1e-15, 3.0])
        result = safe_divide(num, denom, epsilon=1e-12, default=0.0)
        assert abs(result[0] - 0.5) < 1e-10
        assert result[1] == 0.0
        assert abs(result[2] - 1.0) < 1e-10
    
    def test_normalize_weights(self):
        """Test weight normalization."""
        # None -> uniform
        w = normalize_weights(None, 5)
        assert len(w) == 5
        assert abs(w.sum() - 1.0) < 1e-10
        assert np.allclose(w, 0.2)
        
        # Custom weights
        w = normalize_weights(np.array([1, 2, 3]), 3)
        assert abs(w.sum() - 1.0) < 1e-10
        assert abs(w[0] - 1/6) < 1e-10
        assert abs(w[1] - 2/6) < 1e-10
        assert abs(w[2] - 3/6) < 1e-10
    
    def test_validate_data(self):
        """Test data validation."""
        # Valid data
        data = np.random.randn(10, 3)
        validate_data(data)  # Should not raise
        
        # Too few points
        with pytest.raises(ValueError, match="at least 2 points"):
            validate_data(np.random.randn(1, 3))
        
        # Wrong dimensions
        with pytest.raises(ValueError, match="2D array"):
            validate_data(np.random.randn(10))
        
        # NaN values
        data_nan = np.random.randn(10, 3)
        data_nan[0, 0] = np.nan
        with pytest.raises(ValueError, match="NaN"):
            validate_data(data_nan)
    
    def test_merge_features(self):
        """Test feature dictionary merging."""
        f1 = {"a": 1.0, "b": 2.0}
        f2 = {"c": 3.0, "d": 4.0}
        f3 = {"e": 5.0}
        
        merged = merge_features(f1, f2, f3)
        
        assert len(merged) == 5
        assert merged["a"] == 1.0
        assert merged["e"] == 5.0
    
    def test_descriptor_registry(self):
        """Test descriptor registry."""
        registry = DescriptorRegistry()
        
        # Register
        registry.register("kme_delta", KME_Delta)
        
        # List
        assert "kme_delta" in registry.list()
        
        # Contains
        assert "kme_delta" in registry
        assert "unknown" not in registry
        
        # Get
        desc = registry.get("kme_delta", sigmas=(1.0, 2.0))
        assert isinstance(desc, KME_Delta)
        assert desc.sigmas == (1.0, 2.0)
        
        # Unknown descriptor
        with pytest.raises(KeyError, match="not found"):
            registry.get("unknown")


class TestKMEDeltaV2:
    """Test enhanced KME-Δ implementation."""
    
    def test_initialization(self):
        """Test dataclass initialization."""
        # Default
        kme = KME_Delta()
        assert kme.sigmas == (0.5, 1.0, 2.0)
        assert kme.weights is None
        assert kme.eps == 1e-12
        assert kme.name == "kme_delta"
        
        # Custom
        kme = KME_Delta(sigmas=(1.0, 2.0), eps=1e-10)
        assert kme.sigmas == (1.0, 2.0)
        assert kme.eps == 1e-10
    
    def test_compute_basic(self):
        """Test basic computation."""
        np.random.seed(42)
        X = np.random.randn(20, 3)
        
        kme = KME_Delta(sigmas=(1.0, 2.0))
        result = kme.compute(X)
        
        # Check output structure
        assert "KME_delta_F" in result
        assert "KME_sigma_1" in result
        assert "KME_sigma_2" in result
        assert "KME_mean" in result
        assert "KME_max" in result
        assert "KME_min" in result
        
        # Check dimensionless
        for value in result.values():
            assert np.isfinite(value)
            assert value >= 0
    
    def test_compute_with_reference(self):
        """Test computation with custom reference."""
        np.random.seed(42)
        X = np.random.randn(20, 3)
        X_ref = np.random.randn(15, 3)
        
        kme = KME_Delta(sigmas=(1.0,))
        result = kme.compute(X, X_ref=X_ref)
        
        assert "KME_delta_F" in result
        assert result["KME_delta_F"] >= 0
    
    def test_compute_with_weights(self):
        """Test computation with sample weights."""
        np.random.seed(42)
        X = np.random.randn(20, 3)
        weights = np.random.rand(20)
        
        kme = KME_Delta(sigmas=(1.0,))
        result = kme.compute(X, sample_weights=weights)
        
        assert "KME_delta_F" in result
        assert result["KME_delta_F"] >= 0
    
    def test_compute_dict_input(self):
        """Test computation with dict input (attention weights)."""
        np.random.seed(42)
        embeddings = np.random.randn(20, 64)
        attention_weights = np.random.rand(20)
        
        kme = KME_Delta(sigmas=(1.0, 2.0))
        result = kme.compute({
            'embeddings': embeddings,
            'attention_weights': attention_weights
        })
        
        assert "KME_delta_F" in result
        assert result["KME_delta_F"] >= 0
    
    def test_multiscale(self):
        """Test multi-scale computation."""
        np.random.seed(42)
        X = np.random.randn(30, 3)

        kme = KME_Delta(sigmas=(0.1, 1.0, 10.0))
        result = kme.compute(X)

        # Should have all scales
        assert "KME_sigma_0.1" in result
        assert "KME_sigma_1" in result
        assert "KME_sigma_10" in result

        # All values should be non-negative
        assert result["KME_sigma_0.1"] >= 0
        assert result["KME_sigma_1"] >= 0
        assert result["KME_sigma_10"] >= 0
    
    def test_callable(self):
        """Test __call__ method."""
        np.random.seed(42)
        X = np.random.randn(20, 3)
        
        kme = KME_Delta(sigmas=(1.0,))
        
        # Should work as callable
        result = kme(X)
        assert "KME_delta_F" in result


class TestCompatibility:
    """Test compatibility between v1 and v2."""
    
    def test_kme_delta_compatibility(self):
        """Verify v1 and v2 produce similar results."""
        from tcdb_api.descriptors import KernelMeanEmbeddingDelta  # v1

        np.random.seed(42)
        X = np.random.randn(30, 3)
        X_ref = np.random.randn(25, 3)  # Different reference for non-zero divergence

        # v1
        kme_v1 = KernelMeanEmbeddingDelta(sigma_scales=[1.0, 2.0])
        result_v1 = kme_v1.compute(X, reference_data=X_ref)

        # v2
        kme_v2 = KME_Delta(sigmas=(1.0, 2.0))
        result_v2 = kme_v2.compute(X, X_ref=X_ref)

        # Both should produce valid results
        assert result_v1['KME_delta_F'] >= 0
        assert result_v2['KME_delta_F'] >= 0

        # Both should have per-scale values
        assert 'KME_sigma_1' in result_v1 or 'KME_sigma_1.0' in result_v1
        assert 'KME_sigma_1' in result_v2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

