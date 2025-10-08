"""
Simple tests following production skeleton pattern.

Focused on basic functionality and dimensionless properties.
Complements the comprehensive tests in test_descriptors.py.
"""

from __future__ import annotations

import numpy as np
import scipy.sparse as sp
import pytest

from tcdb_api.descriptors.kme_delta_v2 import KME_Delta
from tcdb_api.descriptors.dgd import DiffusionGeometryDescriptor as DGD
from tcdb_api.descriptors.tid import TopologicalInformationDescriptor as TID
from tcdb_api.descriptors.gser import GraphScatteringEnergyRatio as GSER


def test_kme_delta_basic():
    """Test KME-Δ basic computation."""
    X = np.random.RandomState(0).randn(64, 8)
    X_ref = np.random.RandomState(1).randn(64, 8)
    
    desc = KME_Delta(sigmas=(0.5, 1.0))
    feats = desc.compute(X, X_ref=X_ref)
    
    assert "KME_delta_F" in feats
    assert feats["KME_delta_F"] >= 0.0
    assert np.isfinite(feats["KME_delta_F"])


def _toy_graph(n: int = 32) -> sp.csr_matrix:
    """Create simple ring graph for testing."""
    rows, cols, data = [], [], []
    for i in range(n):
        j = (i + 1) % n
        rows += [i, j]
        cols += [j, i]
        data += [1.0, 1.0]
    return sp.csr_matrix((data, (rows, cols)), shape=(n, n))


def test_dgd_runs():
    """Test DGD runs without errors."""
    # DGD expects point cloud, not adjacency matrix
    X = np.random.RandomState(0).randn(32, 3)

    desc = DGD(n_time_samples=8)
    feats = desc.compute(X)

    assert "DGD_F" in feats
    assert np.isfinite(feats["DGD_F"])


def test_tid_runs_without_gudhi():
    """Test TID graceful fallback without Gudhi."""
    X = np.random.RandomState(0).randn(64, 3)
    
    desc = TID(max_dimension=1)
    feats = desc.compute(X)
    
    assert "TID_F" in feats or "F_TID" in feats
    # May be 0.0 if Gudhi/Ripser not available
    f_tid = feats.get("TID_F", feats.get("F_TID", 0.0))
    assert f_tid >= 0.0


def test_gser_runs():
    """Test GSER basic computation."""
    # GSER expects point cloud with signal
    X = np.random.RandomState(0).randn(32, 3)

    desc = GSER(n_scales=2, k_neighbors=3)
    feats = desc.compute(X)

    assert "GSER_F" in feats or "F_GSER" in feats
    f_gser = feats.get("GSER_F", feats.get("F_GSER", 0.0))
    assert 0.0 <= f_gser <= 1.0 or np.isfinite(f_gser)


def test_all_descriptors_return_dict():
    """Test that all descriptors return dict[str, float]."""
    X = np.random.RandomState(0).randn(32, 3)

    descriptors = [
        (KME_Delta(sigmas=(1.0,)), lambda d: d.compute(X)),
        (DGD(n_time_samples=4), lambda d: d.compute(X)),
        (TID(max_dimension=1), lambda d: d.compute(X)),
        (GSER(n_scales=2, k_neighbors=3), lambda d: d.compute(X)),
    ]

    for desc, compute_fn in descriptors:
        result = compute_fn(desc)
        assert isinstance(result, dict)
        assert all(isinstance(k, str) for k in result.keys())
        assert all(isinstance(v, (int, float)) for v in result.values())


def test_all_descriptors_finite_values():
    """Test that all descriptors return finite values."""
    X = np.random.RandomState(0).randn(32, 3)

    descriptors = [
        (KME_Delta(sigmas=(1.0,)), lambda d: d.compute(X)),
        (DGD(n_time_samples=4), lambda d: d.compute(X)),
        (TID(max_dimension=1), lambda d: d.compute(X)),
        (GSER(n_scales=2, k_neighbors=3), lambda d: d.compute(X)),
    ]

    for desc, compute_fn in descriptors:
        result = compute_fn(desc)
        for key, value in result.items():
            assert np.isfinite(value), f"{desc.name}.{key} is not finite: {value}"


def test_all_descriptors_non_negative():
    """Test that main descriptor values are non-negative."""
    X = np.random.RandomState(0).randn(32, 3)

    descriptors_and_keys = [
        (KME_Delta(sigmas=(1.0,)), lambda d: d.compute(X), "KME_delta_F"),
        (DGD(n_time_samples=4), lambda d: d.compute(X), "DGD_F"),
        (TID(max_dimension=1), lambda d: d.compute(X), ["TID_F", "F_TID"]),
        (GSER(n_scales=2, k_neighbors=3), lambda d: d.compute(X), ["GSER_F", "F_GSER"]),
    ]

    for desc, compute_fn, keys in descriptors_and_keys:
        result = compute_fn(desc)

        # Handle both single key and list of possible keys
        if isinstance(keys, str):
            keys = [keys]

        # Check at least one key exists and is non-negative
        found = False
        for key in keys:
            if key in result:
                assert result[key] >= 0.0, f"{desc.name}.{key} is negative: {result[key]}"
                found = True
                break

        assert found, f"None of {keys} found in {desc.name} result"


@pytest.mark.parametrize("n_points", [10, 50, 100])
def test_kme_delta_scales_with_data_size(n_points):
    """Test KME-Δ works with different data sizes."""
    X = np.random.RandomState(0).randn(n_points, 5)
    
    desc = KME_Delta(sigmas=(1.0,))
    result = desc.compute(X)
    
    assert "KME_delta_F" in result
    assert np.isfinite(result["KME_delta_F"])


@pytest.mark.parametrize("n_points", [10, 32, 64])
def test_dgd_scales_with_data_size(n_points):
    """Test DGD works with different data sizes."""
    X = np.random.RandomState(0).randn(n_points, 3)

    desc = DGD(n_time_samples=4)
    result = desc.compute(X)

    assert "DGD_F" in result
    assert np.isfinite(result["DGD_F"])


def test_reproducibility():
    """Test that descriptors produce reproducible results."""
    np.random.seed(42)
    X = np.random.randn(32, 3)
    
    desc = KME_Delta(sigmas=(1.0,))
    result1 = desc.compute(X)
    result2 = desc.compute(X)
    
    assert result1["KME_delta_F"] == result2["KME_delta_F"]


def test_kme_delta_self_comparison_is_zero():
    """Test that KME-Δ comparing data to itself gives zero."""
    X = np.random.RandomState(0).randn(32, 3)
    
    desc = KME_Delta(sigmas=(1.0,))
    result = desc.compute(X, X_ref=X)
    
    # Self-comparison should give very small divergence
    assert result["KME_delta_F"] < 1e-6


def test_dgd_point_cloud():
    """Test DGD on point cloud."""
    # Create point cloud
    X = np.random.RandomState(0).randn(16, 3)

    desc = DGD(n_time_samples=4)
    result = desc.compute(X)

    assert np.isfinite(result["DGD_F"])


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

