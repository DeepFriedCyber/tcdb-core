"""
Tests for certificate/provenance functionality
"""

import pytest
from fastapi.testclient import TestClient


def test_certificate_deterministic(client):
    """
    Test that certificate generation is deterministic

    The same input should always produce the same result hash and audit token.
    This is critical for reproducibility and verification.
    """
    body = {
        "data_cid": "cid:demo",
        "code_rev": "rev:abc",
        "pd": [[0.1, 0.9], [0.2, 0.7]]
    }

    # Call twice with same input
    r1 = client.post("/evidence/certificate", json=body)
    r2 = client.post("/evidence/certificate", json=body)

    assert r1.status_code == 200
    assert r2.status_code == 200

    j1 = r1.json()
    j2 = r2.json()

    # Should be identical (deterministic)
    assert j1["result_hash"] == j2["result_hash"]
    assert j1["audit_token"] == j2["audit_token"]

    # Verify structure
    assert "data_cid" in j1
    assert "code_rev" in j1
    assert "result_hash" in j1
    assert "audit_token" in j1

    # Verify values match input
    assert j1["data_cid"] == "cid:demo"
    assert j1["code_rev"] == "rev:abc"

