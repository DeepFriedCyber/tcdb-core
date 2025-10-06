"""
TDD Integration Tests for TCDB API
Tests the live API endpoints with real HTTP requests
"""

import pytest
import requests
import os
import json
from typing import Dict, Any

# Get API key from environment or prompt
API_KEY = os.getenv('TCDB_API_KEY', '')
BASE_URL = "https://tcdb.uk/api/v1"

# Skip tests if no API key provided
pytestmark = pytest.mark.skipif(
    not API_KEY,
    reason="TCDB_API_KEY environment variable not set"
)


class TestAPIAuthentication:
    """Test API authentication and authorization"""
    
    def test_missing_api_key_returns_401(self):
        """Test that requests without API key are rejected"""
        response = requests.get(f"{BASE_URL}/health")
        assert response.status_code == 401
        assert 'error' in response.json()
    
    def test_invalid_api_key_returns_401(self):
        """Test that requests with invalid API key are rejected"""
        headers = {"Authorization": "Bearer invalid_key_12345"}
        response = requests.get(f"{BASE_URL}/health", headers=headers)
        assert response.status_code == 401
    
    def test_valid_api_key_returns_200(self):
        """Test that requests with valid API key are accepted"""
        headers = {"Authorization": f"Bearer {API_KEY}"}
        response = requests.get(f"{BASE_URL}/health", headers=headers)
        assert response.status_code == 200


class TestHealthEndpoint:
    """Test health check endpoint"""
    
    @pytest.fixture
    def headers(self):
        return {"Authorization": f"Bearer {API_KEY}"}
    
    def test_health_returns_status(self, headers):
        """Test that health endpoint returns status"""
        response = requests.get(f"{BASE_URL}/health", headers=headers)
        data = response.json()
        
        assert response.status_code == 200
        assert data['status'] == 'healthy'
        assert 'version' in data
    
    def test_health_lists_endpoints(self, headers):
        """Test that health endpoint lists all available endpoints"""
        response = requests.get(f"{BASE_URL}/health", headers=headers)
        data = response.json()
        
        assert 'endpoints' in data
        assert isinstance(data['endpoints'], list)
        assert '/api/v1/topology/signature' in data['endpoints']
        assert '/api/v1/provenance/track' in data['endpoints']
        assert '/api/v1/data/proof' in data['endpoints']
        assert '/api/v1/cross-domain/reason' in data['endpoints']


class TestTopologySignatureEndpoint:
    """Test topological signature generation endpoint"""
    
    @pytest.fixture
    def headers(self):
        return {
            "Authorization": f"Bearer {API_KEY}",
            "Content-Type": "application/json"
        }
    
    def test_topology_signature_with_valid_data(self, headers):
        """Test topological signature generation with valid data"""
        payload = {
            "data": [1.0, 2.5, 3.2, 4.1, 5.0],
            "method": "vietoris_rips",
            "max_dimension": 2
        }
        
        response = requests.post(
            f"{BASE_URL}/topology/signature",
            headers=headers,
            json=payload
        )
        data = response.json()
        
        assert response.status_code == 200
        assert data['success'] is True
        assert 'signature' in data
        assert 'persistence_diagram' in data['signature']
        assert 'betti_numbers' in data['signature']
        assert data['data_points'] == 5
    
    def test_topology_signature_without_data_returns_400(self, headers):
        """Test that missing data returns 400 error"""
        response = requests.post(
            f"{BASE_URL}/topology/signature",
            headers=headers,
            json={}
        )
        
        assert response.status_code == 400
        assert 'error' in response.json()
    
    def test_topology_signature_with_invalid_data_type(self, headers):
        """Test that invalid data type returns 400 error"""
        payload = {"data": "not an array"}
        
        response = requests.post(
            f"{BASE_URL}/topology/signature",
            headers=headers,
            json=payload
        )
        
        assert response.status_code == 400
    
    def test_topology_signature_uses_default_method(self, headers):
        """Test that default method is used when not specified"""
        payload = {"data": [1, 2, 3, 4, 5]}
        
        response = requests.post(
            f"{BASE_URL}/topology/signature",
            headers=headers,
            json=payload
        )
        data = response.json()
        
        assert data['method'] == 'vietoris_rips'
    
    def test_topology_signature_respects_max_dimension(self, headers):
        """Test that max_dimension parameter is respected"""
        payload = {
            "data": [1, 2, 3, 4, 5],
            "max_dimension": 3
        }
        
        response = requests.post(
            f"{BASE_URL}/topology/signature",
            headers=headers,
            json=payload
        )
        data = response.json()
        
        assert data['max_dimension'] == 3
    
    def test_topology_signature_with_large_dataset(self, headers):
        """Test topological signature with larger dataset"""
        payload = {
            "data": list(range(100)),
            "max_dimension": 2
        }
        
        response = requests.post(
            f"{BASE_URL}/topology/signature",
            headers=headers,
            json=payload
        )
        
        assert response.status_code == 200
        data = response.json()
        assert data['data_points'] == 100


class TestProvenanceTrackingEndpoint:
    """Test provenance tracking endpoint"""
    
    @pytest.fixture
    def headers(self):
        return {
            "Authorization": f"Bearer {API_KEY}",
            "Content-Type": "application/json"
        }
    
    def test_provenance_track_with_valid_data(self, headers):
        """Test provenance tracking with valid data"""
        payload = {
            "operation": "model_inference",
            "inputs": ["embedding_data", "model_weights"],
            "outputs": ["prediction", "confidence_score"],
            "metadata": {"model": "gpt-4", "version": "1.0"}
        }
        
        response = requests.post(
            f"{BASE_URL}/provenance/track",
            headers=headers,
            json=payload
        )
        data = response.json()
        
        assert response.status_code == 200
        assert data['success'] is True
        assert 'provenance_id' in data
        assert 'record' in data
        assert data['record']['operation'] == 'model_inference'
        assert 'signature' in data['record']
    
    def test_provenance_track_without_required_fields(self, headers):
        """Test that missing required fields returns 400"""
        payload = {"operation": "test"}
        
        response = requests.post(
            f"{BASE_URL}/provenance/track",
            headers=headers,
            json=payload
        )
        
        assert response.status_code == 400
    
    def test_provenance_track_includes_metadata(self, headers):
        """Test that metadata is included in provenance record"""
        metadata = {"custom_field": "custom_value", "version": "2.0"}
        payload = {
            "operation": "test_op",
            "inputs": ["a"],
            "outputs": ["b"],
            "metadata": metadata
        }
        
        response = requests.post(
            f"{BASE_URL}/provenance/track",
            headers=headers,
            json=payload
        )
        data = response.json()
        
        assert data['record']['metadata'] == metadata
    
    def test_provenance_generates_unique_ids(self, headers):
        """Test that each provenance record gets unique ID"""
        payload = {
            "operation": "test",
            "inputs": ["x"],
            "outputs": ["y"]
        }
        
        response1 = requests.post(
            f"{BASE_URL}/provenance/track",
            headers=headers,
            json=payload
        )
        response2 = requests.post(
            f"{BASE_URL}/provenance/track",
            headers=headers,
            json=payload
        )
        
        id1 = response1.json()['provenance_id']
        id2 = response2.json()['provenance_id']
        
        assert id1 != id2


class TestDataProofEndpoint:
    """Test data proof generation endpoint"""
    
    @pytest.fixture
    def headers(self):
        return {
            "Authorization": f"Bearer {API_KEY}",
            "Content-Type": "application/json"
        }
    
    def test_data_proof_with_valid_data(self, headers):
        """Test data proof generation with valid data"""
        payload = {
            "data": ["item1", "item2", "item3"],
            "proof_type": "membership"
        }
        
        response = requests.post(
            f"{BASE_URL}/data/proof",
            headers=headers,
            json=payload
        )
        data = response.json()
        
        assert response.status_code == 200
        assert data['success'] is True
        assert 'fingerprint' in data
        assert 'proof' in data
        assert data['proof']['type'] == 'membership'
        assert data['data_size'] == 3
    
    def test_data_proof_without_data_returns_400(self, headers):
        """Test that missing data returns 400"""
        response = requests.post(
            f"{BASE_URL}/data/proof",
            headers=headers,
            json={}
        )
        
        assert response.status_code == 400
    
    def test_data_proof_uses_default_type(self, headers):
        """Test that default proof type is used"""
        payload = {"data": ["a", "b", "c"]}
        
        response = requests.post(
            f"{BASE_URL}/data/proof",
            headers=headers,
            json=payload
        )
        data = response.json()
        
        assert data['proof_type'] == 'membership'


class TestCrossDomainReasoningEndpoint:
    """Test cross-domain reasoning endpoint"""
    
    @pytest.fixture
    def headers(self):
        return {
            "Authorization": f"Bearer {API_KEY}",
            "Content-Type": "application/json"
        }
    
    def test_cross_domain_with_valid_data(self, headers):
        """Test cross-domain reasoning with valid data"""
        payload = {
            "domain_a": "neural_networks",
            "domain_b": "power_grids",
            "data_a": [0.5, 0.8, 0.3, 0.9],
            "data_b": [0.6, 0.7, 0.4, 0.8]
        }
        
        response = requests.post(
            f"{BASE_URL}/cross-domain/reason",
            headers=headers,
            json=payload
        )
        data = response.json()
        
        assert response.status_code == 200
        assert data['success'] is True
        assert 'similarity_score' in data
        assert isinstance(data['similarity_score'], (int, float))
        assert 'connections' in data
        assert isinstance(data['connections'], list)
        assert 'transferable' in data
    
    def test_cross_domain_without_required_fields(self, headers):
        """Test that missing required fields returns 400"""
        payload = {"domain_a": "test"}
        
        response = requests.post(
            f"{BASE_URL}/cross-domain/reason",
            headers=headers,
            json=payload
        )
        
        assert response.status_code == 400
    
    def test_cross_domain_similarity_in_valid_range(self, headers):
        """Test that similarity score is in valid range [0, 1]"""
        payload = {
            "domain_a": "a",
            "domain_b": "b",
            "data_a": [1, 2, 3],
            "data_b": [1, 2, 3]
        }
        
        response = requests.post(
            f"{BASE_URL}/cross-domain/reason",
            headers=headers,
            json=payload
        )
        data = response.json()
        
        similarity = data['similarity_score']
        assert -1 <= similarity <= 1  # Cosine similarity range


class TestCORSSupport:
    """Test CORS support for browser requests"""
    
    def test_options_request_returns_cors_headers(self):
        """Test that OPTIONS preflight requests return CORS headers"""
        response = requests.options(f"{BASE_URL}/health")
        
        assert 'Access-Control-Allow-Origin' in response.headers
        assert 'Access-Control-Allow-Methods' in response.headers
    
    def test_api_responses_include_cors_headers(self):
        """Test that API responses include CORS headers"""
        headers = {"Authorization": f"Bearer {API_KEY}"}
        response = requests.get(f"{BASE_URL}/health", headers=headers)
        
        assert 'Access-Control-Allow-Origin' in response.headers


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])

