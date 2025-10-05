import pytest
import os
from unittest.mock import patch
from api.app import create_app

@pytest.fixture
def client():
    # Set development mode for testing
    os.environ['FLASK_ENV'] = 'development'
    app = create_app({'TESTING': True})
    with app.test_client() as client:
        yield client

@pytest.fixture
def mock_clerk_auth():
    """Mock Clerk authentication for testing"""
    with patch('api.middleware.auth.verify_clerk_token') as mock:
        mock.return_value = {
            'sub': 'test_user_id',
            'email': 'test@example.com',
            'email_verified': True,
            'metadata': {'tier': 'free'},
            'iat': 1234567890,
            'exp': 1234571490
        }
        yield mock

def test_missing_auth_header(client):
    """Test request without auth header"""
    response = client.get('/api/v1/modules')
    assert response.status_code == 401
    data = response.get_json()
    assert 'error' in data
    assert 'authorization header' in data['error'].lower()

def test_invalid_auth_format(client):
    """Test request with invalid auth header format"""
    response = client.get('/api/v1/modules',
                         headers={'Authorization': 'InvalidFormat'})
    assert response.status_code == 401
    data = response.get_json()
    assert 'error' in data

def test_invalid_token(client):
    """Test request with invalid token (not in development mode)"""
    # Temporarily disable development mode
    original_env = os.environ.get('FLASK_ENV')
    os.environ['FLASK_ENV'] = 'production'

    response = client.get('/api/v1/modules',
                         headers={'Authorization': 'Bearer invalid_token'})
    assert response.status_code == 401

    # Restore environment
    if original_env:
        os.environ['FLASK_ENV'] = original_env

def test_valid_token_dev_mode(client):
    """Test request with test token in development mode"""
    # In development mode, tokens starting with 'test_' are accepted
    response = client.get('/api/v1/modules',
                         headers={'Authorization': 'Bearer test_dev_token'})
    assert response.status_code == 200

def test_clerk_config_endpoint(client):
    """Test getting Clerk configuration"""
    # Set a test publishable key
    os.environ['CLERK_PUBLISHABLE_KEY'] = 'pk_test_example'

    response = client.get('/api/v1/auth/config')
    assert response.status_code == 200
    data = response.get_json()
    assert 'publishable_key' in data
    assert data['publishable_key'] == 'pk_test_example'

def test_verify_token_endpoint(client, mock_clerk_auth):
    """Test token verification endpoint"""
    response = client.post('/api/v1/auth/verify',
                          json={'token': 'test_token'})
    assert response.status_code == 200
    data = response.get_json()
    assert data['valid'] is True
    assert 'user' in data
    assert data['user']['id'] == 'test_user_id'

def test_verify_token_missing_token(client):
    """Test token verification without token"""
    response = client.post('/api/v1/auth/verify', json={})
    assert response.status_code == 400
    data = response.get_json()
    assert 'error' in data

def test_get_current_user(client, mock_clerk_auth):
    """Test getting current user info"""
    response = client.get('/api/v1/auth/me',
                         headers={'Authorization': 'Bearer test_token'})
    assert response.status_code == 200
    data = response.get_json()
    assert 'user' in data
    assert data['user']['email'] == 'test@example.com'

def test_get_session_info(client, mock_clerk_auth):
    """Test getting session information"""
    response = client.get('/api/v1/auth/session',
                         headers={'Authorization': 'Bearer test_token'})
    assert response.status_code == 200
    data = response.get_json()
    assert 'session' in data
    assert data['session']['active'] is True
