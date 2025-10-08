"""
API tests for descriptor endpoints

Tests the FastAPI endpoints for descriptor computation.
"""

import pytest
from fastapi.testclient import TestClient
from tcdb_api.app import create_app


@pytest.fixture
def client():
    """Create test client"""
    app = create_app()
    return TestClient(app)


@pytest.fixture
def sample_data():
    """Sample point cloud data for testing"""
    return {
        "data": [
            [0.0, 0.0],
            [1.0, 0.0],
            [0.0, 1.0],
            [1.0, 1.0],
            [0.5, 0.5]
        ]
    }


class TestDescriptorListEndpoint:
    """Tests for /api/v1/descriptors/list endpoint"""
    
    def test_list_descriptors(self, client):
        """Test listing available descriptors"""
        response = client.get("/api/v1/descriptors/list")
        
        assert response.status_code == 200
        data = response.json()
        
        assert "descriptors" in data
        assert len(data["descriptors"]) == 4
        
        # Check that all four descriptors are present
        names = [d["name"] for d in data["descriptors"]]
        assert "tid" in names
        assert "dgd" in names
        assert "kme_delta" in names
        assert "gser" in names


class TestDescriptorComputeEndpoint:
    """Tests for /api/v1/descriptors/compute endpoint"""
    
    def test_compute_tid(self, client, sample_data):
        """Test computing TID descriptor"""
        request_data = {
            **sample_data,
            "descriptor_type": "tid",
            "parameters": {"max_dimension": 1}
        }
        
        response = client.post("/api/v1/descriptors/compute", json=request_data)
        
        assert response.status_code == 200
        data = response.json()
        
        assert data["descriptor_type"] == "tid"
        assert "features" in data
        assert "F_TID" in data["features"]
        assert "metadata" in data
        assert data["metadata"]["n_points"] == 5
    
    def test_compute_dgd(self, client, sample_data):
        """Test computing DGD descriptor"""
        request_data = {
            **sample_data,
            "descriptor_type": "dgd",
            "parameters": {"k_neighbors": 3, "n_time_samples": 10}
        }

        response = client.post("/api/v1/descriptors/compute", json=request_data)

        assert response.status_code == 200
        data = response.json()

        assert data["descriptor_type"] == "dgd"
        assert "DGD_F" in data["features"]
        assert "DGD_phi1_mean" in data["features"]
        assert "DGD_phi2_q90" in data["features"]
    
    def test_compute_kme_delta(self, client, sample_data):
        """Test computing KME-Δ descriptor"""
        request_data = {
            **sample_data,
            "descriptor_type": "kme_delta",
            "parameters": {"sigma_scales": [0.5, 1.0]}
        }

        response = client.post("/api/v1/descriptors/compute", json=request_data)

        assert response.status_code == 200
        data = response.json()

        assert data["descriptor_type"] == "kme_delta"
        assert "KME_delta_F" in data["features"]
        assert "KME_mean" in data["features"]
        assert "KME_sigma_0.5" in data["features"]
        assert "KME_sigma_1.0" in data["features"]
    
    def test_compute_gser(self, client, sample_data):
        """Test computing GSER descriptor"""
        request_data = {
            **sample_data,
            "descriptor_type": "gser",
            "parameters": {"n_scales": 2, "k_neighbors": 3}
        }
        
        response = client.post("/api/v1/descriptors/compute", json=request_data)
        
        assert response.status_code == 200
        data = response.json()
        
        assert data["descriptor_type"] == "gser"
        assert "F_GSER" in data["features"]
        assert "energy_concentration" in data["features"]
    
    def test_invalid_descriptor_type(self, client, sample_data):
        """Test error on invalid descriptor type"""
        request_data = {
            **sample_data,
            "descriptor_type": "invalid_descriptor"
        }
        
        response = client.post("/api/v1/descriptors/compute", json=request_data)
        
        assert response.status_code == 400
        assert "Unknown descriptor type" in response.json()["detail"]
    
    def test_insufficient_points(self, client):
        """Test error on insufficient points"""
        request_data = {
            "data": [[0.0, 0.0], [1.0, 1.0]],  # Only 2 points
            "descriptor_type": "tid"
        }
        
        response = client.post("/api/v1/descriptors/compute", json=request_data)
        
        assert response.status_code == 400
        assert "at least 3 points" in response.json()["detail"]
    
    def test_default_parameters(self, client, sample_data):
        """Test computation with default parameters"""
        request_data = {
            **sample_data,
            "descriptor_type": "tid"
            # No parameters specified - should use defaults
        }
        
        response = client.post("/api/v1/descriptors/compute", json=request_data)
        
        assert response.status_code == 200
        data = response.json()
        assert "features" in data


class TestBatchDescriptorEndpoint:
    """Tests for /api/v1/descriptors/compute/batch endpoint"""
    
    def test_batch_compute(self, client, sample_data):
        """Test computing multiple descriptors"""
        request_data = {
            **sample_data,
            "descriptor_types": ["tid", "dgd"],
            "parameters": {
                "tid": {"max_dimension": 1},
                "dgd": {"k_neighbors": 3, "n_time_samples": 5}
            }
        }
        
        response = client.post("/api/v1/descriptors/compute/batch", json=request_data)
        
        assert response.status_code == 200
        data = response.json()
        
        assert "results" in data
        assert "tid" in data["results"]
        assert "dgd" in data["results"]
        
        # Check TID results
        assert "F_TID" in data["results"]["tid"]
        
        # Check DGD results
        assert "F_DGD" in data["results"]["dgd"]
        
        # Check metadata
        assert "metadata" in data
        assert data["metadata"]["n_points"] == 5
    
    def test_batch_all_descriptors(self, client, sample_data):
        """Test computing all four descriptors at once"""
        request_data = {
            **sample_data,
            "descriptor_types": ["tid", "dgd", "kme_delta", "gser"],
            "parameters": {
                "tid": {"max_dimension": 1},
                "dgd": {"n_time_samples": 5},
                "kme_delta": {"sigma_scales": [0.5, 1.0]},
                "gser": {"n_scales": 2}
            }
        }
        
        response = client.post("/api/v1/descriptors/compute/batch", json=request_data)
        
        assert response.status_code == 200
        data = response.json()
        
        # All four descriptors should be in results
        assert len(data["results"]) == 4
        assert all(desc in data["results"] for desc in ["tid", "dgd", "kme_delta", "gser"])
    
    def test_batch_partial_parameters(self, client, sample_data):
        """Test batch with parameters for only some descriptors"""
        request_data = {
            **sample_data,
            "descriptor_types": ["tid", "dgd"],
            "parameters": {
                "tid": {"max_dimension": 1}
                # dgd will use defaults
            }
        }
        
        response = client.post("/api/v1/descriptors/compute/batch", json=request_data)
        
        assert response.status_code == 200
        data = response.json()
        
        assert "tid" in data["results"]
        assert "dgd" in data["results"]


class TestDescriptorConfigEndpoint:
    """Tests for /api/v1/descriptors/config/{descriptor_type} endpoint"""
    
    def test_get_tid_config(self, client):
        """Test getting TID configuration"""
        response = client.get("/api/v1/descriptors/config/tid")
        
        assert response.status_code == 200
        data = response.json()
        
        assert data["descriptor_type"] == "tid"
        assert "configuration" in data
        assert "max_dimension" in data["configuration"]
    
    def test_get_dgd_config(self, client):
        """Test getting DGD configuration"""
        response = client.get("/api/v1/descriptors/config/dgd")
        
        assert response.status_code == 200
        data = response.json()
        
        assert data["descriptor_type"] == "dgd"
        assert "k_neighbors" in data["configuration"]
    
    def test_get_unknown_config(self, client):
        """Test error on unknown descriptor type"""
        response = client.get("/api/v1/descriptors/config/unknown")
        
        assert response.status_code == 404


class TestDescriptorValidation:
    """Tests for input validation"""
    
    def test_empty_data(self, client):
        """Test error on empty data"""
        request_data = {
            "data": [],
            "descriptor_type": "tid"
        }
        
        response = client.post("/api/v1/descriptors/compute", json=request_data)
        
        assert response.status_code == 400
    
    def test_invalid_data_format(self, client):
        """Test error on invalid data format"""
        request_data = {
            "data": "not a list",
            "descriptor_type": "tid"
        }
        
        response = client.post("/api/v1/descriptors/compute", json=request_data)
        
        assert response.status_code == 422  # Validation error
    
    def test_mixed_dimension_data(self, client):
        """Test handling of mixed-dimension data"""
        request_data = {
            "data": [
                [0.0, 0.0],
                [1.0, 0.0, 0.0],  # Different dimension
                [0.0, 1.0]
            ],
            "descriptor_type": "tid"
        }
        
        response = client.post("/api/v1/descriptors/compute", json=request_data)
        
        # Should fail during numpy array conversion or validation
        assert response.status_code in [400, 500]

