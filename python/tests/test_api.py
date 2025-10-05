"""
Tests for Python API endpoints
"""

import pytest
import json
from tcdb_api.app import create_app


@pytest.fixture
def client():
    """Create test client"""
    app = create_app({'TESTING': True})
    with app.test_client() as client:
        yield client


class TestHealthEndpoints:
    """Test health check endpoints"""
    
    def test_root_endpoint(self, client):
        """Test root endpoint"""
        response = client.get('/')
        assert response.status_code == 200
        data = json.loads(response.data)
        assert data['name'] == 'TCDB Core API'
        assert data['version'] == '1.0.0'
    
    def test_health_check(self, client):
        """Test health check endpoint"""
        response = client.get('/api/v1/health')
        assert response.status_code == 200
        data = json.loads(response.data)
        assert data['status'] == 'healthy'
        assert 'rust_available' in data
        assert 'components' in data


class TestTDAEndpoints:
    """Test TDA-specific endpoints"""
    
    def test_create_simplex(self, client):
        """Test simplex creation endpoint"""
        response = client.post(
            '/api/v1/tda/simplex',
            data=json.dumps({'vertices': [0, 1, 2]}),
            content_type='application/json'
        )
        
        # May fail if Rust not available
        if response.status_code == 503:
            pytest.skip("Rust bindings not available")
        
        assert response.status_code == 200
        data = json.loads(response.data)
        assert data['dimension'] == 2
        assert data['vertices'] == [0, 1, 2]
    
    def test_create_complex(self, client):
        """Test complex creation endpoint"""
        response = client.post(
            '/api/v1/tda/complex',
            data=json.dumps({
                'simplices': [[0], [1], [2], [0, 1], [1, 2], [0, 2], [0, 1, 2]]
            }),
            content_type='application/json'
        )
        
        if response.status_code == 503:
            pytest.skip("Rust bindings not available")
        
        assert response.status_code == 200
        data = json.loads(response.data)
        assert data['dimension'] == 2
        assert data['euler_characteristic'] == 1
        assert data['closure_verified'] is True
    
    def test_compute_rips(self, client):
        """Test Rips complex computation"""
        response = client.post(
            '/api/v1/tda/rips',
            data=json.dumps({
                'points': [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]],
                'max_edge_length': 1.5,
                'max_dimension': 2
            }),
            content_type='application/json'
        )
        
        if response.status_code == 503:
            pytest.skip("Rust bindings not available")
        
        assert response.status_code == 200
        data = json.loads(response.data)
        assert data['num_vertices'] == 3
        assert data['verified'] is True


class TestPipelineEndpoints:
    """Test pipeline endpoints"""
    
    def test_run_pipeline(self, client):
        """Test running a complete pipeline"""
        response = client.post(
            '/api/v1/pipeline/run',
            data=json.dumps({
                'data': [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0], [1.0, 1.0]],
                'max_dimension': 2,
                'max_edge_length': 1.5
            }),
            content_type='application/json'
        )
        
        if response.status_code == 503:
            pytest.skip("Rust bindings not available")
        
        assert response.status_code == 200
        data = json.loads(response.data)
        assert 'job_id' in data
        assert data['status'] == 'completed'
        assert 'results' in data
    
    def test_list_jobs(self, client):
        """Test listing jobs"""
        response = client.get('/api/v1/pipeline/jobs')
        assert response.status_code == 200
        data = json.loads(response.data)
        assert 'jobs' in data


class TestErrorHandling:
    """Test error handling"""
    
    def test_missing_data(self, client):
        """Test missing data field"""
        response = client.post(
            '/api/v1/pipeline/run',
            data=json.dumps({}),
            content_type='application/json'
        )
        assert response.status_code == 400
    
    def test_invalid_data_shape(self, client):
        """Test invalid data shape"""
        response = client.post(
            '/api/v1/pipeline/run',
            data=json.dumps({'data': [1, 2, 3]}),  # 1D instead of 2D
            content_type='application/json'
        )
        assert response.status_code == 400
    
    def test_job_not_found(self, client):
        """Test getting non-existent job"""
        response = client.get('/api/v1/pipeline/status/nonexistent')
        assert response.status_code == 404


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

