import pytest
from api.app import create_app

@pytest.fixture
def client():
    app = create_app({'TESTING': True})
    with app.test_client() as client:
        yield client

@pytest.fixture
def auth_headers():
    return {'Authorization': 'Bearer test_token_12345'}

def test_list_modules(client, auth_headers):
    """Test listing available modules"""
    response = client.get('/api/v1/modules', headers=auth_headers)

    assert response.status_code == 200
    data = response.get_json()
    assert 'embedding_modules' in data
    assert 'tda_modules' in data
    assert 'downstream_modules' in data
    assert len(data['embedding_modules']) > 0
    assert len(data['tda_modules']) > 0
