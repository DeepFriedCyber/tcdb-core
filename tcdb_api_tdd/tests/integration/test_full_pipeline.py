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

def test_full_workflow(client, auth_headers):
    """Test complete workflow: list modules -> run pipeline -> get results"""

    # Step 1: List available modules
    response = client.get('/api/v1/modules', headers=auth_headers)
    assert response.status_code == 200
    modules = response.get_json()

    # Step 2: Run pipeline
    np.random.seed(42)
    data = {
        'data': np.random.rand(30, 4).tolist(),
        'labels': np.random.randint(0, 2, 30).tolist(),
        'embedding_module': modules['embedding_modules'][0]['name'],
        'tda_module': modules['tda_modules'][0]['name'],
        'downstream_module': modules['downstream_modules'][0]['name']
    }

    response = client.post('/api/v1/pipeline/run',
                          json=data,
                          headers=auth_headers)
    assert response.status_code == 200
    result = response.get_json()
    job_id = result['job_id']

    # Step 3: Retrieve results
    response = client.get(f'/api/v1/results/{job_id}',
                         headers=auth_headers)
    assert response.status_code == 200
    final_result = response.get_json()

    # Verify complete result
    assert final_result['validation_passed'] is True
    assert 'features' in final_result
    assert 'downstream_scores' in final_result
    assert final_result['downstream_scores'] is not None
