"""
Smoke tests for API entrypoint

Basic tests to ensure the application starts correctly and core endpoints work.
"""

import pytest
from fastapi.testclient import TestClient
from tcdb_api.app import create_app


def test_health():
    """Test health endpoint returns 200 OK"""
    app = create_app()
    client = TestClient(app)
    r = client.get("/api/v1/health")
    assert r.status_code == 200
    data = r.json()
    assert data["status"] == "healthy"


def test_api_root():
    """Test API root endpoint returns correct structure"""
    app = create_app()
    client = TestClient(app)
    r = client.get("/api")
    assert r.status_code == 200
    data = r.json()
    assert "name" in data
    assert "version" in data
    assert "status" in data
    assert data["status"] == "operational"


def test_docs_available():
    """Test that OpenAPI docs are accessible"""
    app = create_app()
    client = TestClient(app)
    r = client.get("/docs")
    assert r.status_code == 200


def test_openapi_schema():
    """Test that OpenAPI schema is valid"""
    app = create_app()
    client = TestClient(app)
    r = client.get("/openapi.json")
    assert r.status_code == 200
    schema = r.json()
    assert "openapi" in schema
    assert "info" in schema
    assert "paths" in schema


def test_404_handler():
    """Test 404 handler works"""
    app = create_app()
    client = TestClient(app)
    r = client.get("/nonexistent-endpoint")
    assert r.status_code == 404


def test_cors_headers():
    """Test CORS headers are present"""
    app = create_app()
    client = TestClient(app)
    r = client.options("/api/v1/health", headers={"Origin": "http://localhost:3000"})
    assert "access-control-allow-origin" in r.headers


@pytest.mark.parametrize("endpoint", [
    "/api/v1/health",
    "/api",
])
def test_core_endpoints(endpoint):
    """Test core endpoints are accessible"""
    app = create_app()
    client = TestClient(app)
    r = client.get(endpoint)
    assert r.status_code == 200

