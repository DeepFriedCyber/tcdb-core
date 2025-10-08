"""
API tests for simple unified descriptor endpoint.

Tests the /descriptor/compute endpoint following skeleton pattern.
"""

from __future__ import annotations

import pytest
from fastapi.testclient import TestClient

from tcdb_api.app import app

client = TestClient(app)


def test_list_descriptors():
    """Test listing available descriptors."""
    response = client.get("/descriptor/list")
    
    assert response.status_code == 200
    data = response.json()
    
    assert "descriptors" in data
    assert "count" in data
    assert isinstance(data["descriptors"], list)
    assert len(data["descriptors"]) == data["count"]
    
    # Check expected descriptors are present
    expected = {"kme_delta", "dgd", "tid", "gser"}
    assert expected.issubset(set(data["descriptors"]))


def test_health_check():
    """Test health check endpoint."""
    response = client.get("/descriptor/health")
    
    assert response.status_code == 200
    data = response.json()
    
    assert data["status"] == "healthy"
    assert "descriptors_available" in data


def test_kme_delta_basic():
    """Test KME-Δ computation via API."""
    payload = {
        "name": "kme_delta",
        "params": {"sigmas": [1.0, 2.0]},
        "X": [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0], [1.0, 1.0]],
        "X_ref": [[2.0, 2.0], [3.0, 3.0]]
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 200
    data = response.json()
    
    assert "KME_delta_F" in data
    assert data["KME_delta_F"] >= 0.0


def test_kme_delta_without_reference():
    """Test KME-Δ without reference (uses Gaussian baseline)."""
    payload = {
        "name": "kme_delta",
        "params": {"sigmas": [1.0]},
        "X": [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]]
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 200
    data = response.json()
    
    assert "KME_delta_F" in data


def test_dgd_ring_graph():
    """Test DGD on ring graph."""
    # Create ring graph: 0-1-2-3-0
    n = 4
    edges = [(0, 1), (1, 2), (2, 3), (3, 0)]
    
    # Make symmetric
    adj_indices = []
    adj_data = []
    for i, j in edges:
        adj_indices.extend([(i, j), (j, i)])
        adj_data.extend([1.0, 1.0])
    
    payload = {
        "name": "dgd",
        "params": {"n_time_samples": 8},
        "adj_indices": adj_indices,
        "adj_data": adj_data,
        "n_nodes": n
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 200
    data = response.json()
    
    assert "DGD_F" in data
    assert isinstance(data["DGD_F"], (int, float))


def test_tid_point_cloud():
    """Test TID on point cloud."""
    payload = {
        "name": "tid",
        "params": {"max_dimension": 1},
        "X": [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0], [1.0, 1.0]]
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 200
    data = response.json()
    
    # TID may return TID_F or F_TID depending on implementation
    assert "TID_F" in data or "F_TID" in data


def test_gser_with_signal():
    """Test GSER with node signal."""
    # Simple graph
    n = 4
    adj_indices = [(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)]
    adj_data = [1.0] * len(adj_indices)
    signal = [1.0, 0.5, -0.5, -1.0]
    
    payload = {
        "name": "gser",
        "params": {"n_scales": 2, "k_neighbors": 2},
        "adj_indices": adj_indices,
        "adj_data": adj_data,
        "n_nodes": n,
        "signal": signal
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 200
    data = response.json()
    
    assert "GSER_F" in data or "F_GSER" in data


def test_unknown_descriptor():
    """Test error handling for unknown descriptor."""
    payload = {
        "name": "unknown_descriptor",
        "X": [[0.0, 0.0]]
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 400
    assert "Unknown descriptor" in response.json()["detail"]


def test_missing_required_field():
    """Test error handling for missing required field."""
    payload = {
        "name": "kme_delta",
        "params": {"sigmas": [1.0]}
        # Missing X
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 400


def test_dgd_missing_graph_data():
    """Test DGD error when graph data is missing."""
    payload = {
        "name": "dgd",
        "params": {},
        "n_nodes": 10
        # Missing adj_indices and adj_data
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 400
    assert "requires" in response.json()["detail"].lower()


def test_gser_missing_signal():
    """Test GSER error when signal is missing."""
    payload = {
        "name": "gser",
        "adj_indices": [(0, 1), (1, 0)],
        "adj_data": [1.0, 1.0],
        "n_nodes": 2
        # Missing signal
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 400
    assert "signal" in response.json()["detail"].lower()


def test_invalid_parameters():
    """Test error handling for invalid parameters."""
    payload = {
        "name": "kme_delta",
        "params": {"sigmas": "invalid"},  # Should be list/tuple
        "X": [[0.0, 0.0]]
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 400


def test_multiple_descriptors_same_data():
    """Test computing multiple descriptors on same data."""
    X = [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0], [1.0, 1.0]]
    
    # Compute KME-Δ
    response1 = client.post("/descriptor/compute", json={
        "name": "kme_delta",
        "params": {"sigmas": [1.0]},
        "X": X
    })
    
    # Compute TID
    response2 = client.post("/descriptor/compute", json={
        "name": "tid",
        "params": {"max_dimension": 1},
        "X": X
    })
    
    assert response1.status_code == 200
    assert response2.status_code == 200
    
    data1 = response1.json()
    data2 = response2.json()
    
    assert "KME_delta_F" in data1
    assert "TID_F" in data2 or "F_TID" in data2


def test_large_point_cloud():
    """Test with larger point cloud."""
    import numpy as np
    
    np.random.seed(42)
    X = np.random.randn(100, 5).tolist()
    
    payload = {
        "name": "kme_delta",
        "params": {"sigmas": [1.0, 2.0]},
        "X": X
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 200
    data = response.json()
    
    assert "KME_delta_F" in data
    assert "KME_sigma_1" in data
    assert "KME_sigma_2" in data


def test_response_format():
    """Test that response format is consistent."""
    payload = {
        "name": "kme_delta",
        "params": {"sigmas": [1.0]},
        "X": [[0.0, 0.0], [1.0, 1.0]]
    }
    
    response = client.post("/descriptor/compute", json=payload)
    
    assert response.status_code == 200
    data = response.json()
    
    # Should be dict[str, float]
    assert isinstance(data, dict)
    for key, value in data.items():
        assert isinstance(key, str)
        assert isinstance(value, (int, float))


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

