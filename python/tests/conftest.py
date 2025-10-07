"""
Pytest configuration and fixtures for FastAPI tests
"""

import pytest
from fastapi.testclient import TestClient
from tcdb_api.app import app


@pytest.fixture
def client():
    """Create FastAPI test client"""
    return TestClient(app)


@pytest.fixture(autouse=True)
def _no_edge_hmac(monkeypatch):
    """Keep EDGE_HMAC_SECRET empty during unit tests so auth is bypassed"""
    monkeypatch.setenv("EDGE_HMAC_SECRET", "")

