import pytest
import numpy as np
from api.app import create_app

@pytest.fixture
def client():
    app = create_app({'TESTING': True})
    with app.test_client() as client:
        yield client

@pytest.fixture
def auth_headers():
    return {'Authorization': 'Bearer test_token_12345'}

def test_run_pipeline_success(client, auth_headers):
    """Test successful pipeline execution"""
    data = {
        'data': np.random.rand(20, 3).tolist(),
        'embedding_module': 'standard',
        'tda_module': 'rips'
    }

    response = client.post('/api/v1/pipeline/run',
                          json=data,
                          headers=auth_headers)

    assert response.status_code == 200
    result = response.get_json()
    assert 'job_id' in result
    assert result['status'] == 'completed'
    assert result['validation_passed'] is True
    assert 'features' in result

def test_run_pipeline_with_labels(client, auth_headers):
    """Test pipeline with downstream task"""
    np.random.seed(42)
    X = np.random.rand(50, 3).tolist()
    y = np.random.randint(0, 2, 50).tolist()

    data = {
        'data': X,
        'labels': y,
        'embedding_module': 'standard',
        'tda_module': 'rips',
        'downstream_module': 'classifier'
    }

    response = client.post('/api/v1/pipeline/run',
                          json=data,
                          headers=auth_headers)

    assert response.status_code == 200
    result = response.get_json()
    assert 'downstream_scores' in result
    assert result['downstream_scores'] is not None

def test_run_pipeline_invalid_data(client, auth_headers):
    """Test pipeline with invalid data"""
    data = {
        'data': [[1.0, float('nan'), 3.0]],
        'embedding_module': 'standard',
        'tda_module': 'rips'
    }

    response = client.post('/api/v1/pipeline/run',
                          json=data,
                          headers=auth_headers)

    assert response.status_code == 400

def test_get_results(client, auth_headers):
    """Test retrieving results"""
    # First run a pipeline
    data = {
        'data': np.random.rand(20, 3).tolist(),
        'embedding_module': 'standard',
        'tda_module': 'rips'
    }

    response = client.post('/api/v1/pipeline/run',
                          json=data,
                          headers=auth_headers)

    job_id = response.get_json()['job_id']

    # Now get results
    response = client.get(f'/api/v1/results/{job_id}',
                         headers=auth_headers)

    assert response.status_code == 200
    result = response.get_json()
    assert result['job_id'] == job_id

def test_get_results_not_found(client, auth_headers):
    """Test retrieving non-existent results"""
    response = client.get('/api/v1/results/nonexistent',
                         headers=auth_headers)

    assert response.status_code == 404
