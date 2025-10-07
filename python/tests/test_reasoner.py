"""
Tests for reasoner/constraint checking functionality
"""

import pytest
from fastapi.testclient import TestClient


def test_reasoner_catches_bad_pd(client):
    """
    Test that reasoner catches violations in persistence diagrams

    Death < Birth violates the fundamental constraint that features
    must be born before they die.
    """
    body = {
        "constraints": ["DeathGeBirth", "MaxLifetime:1.5"],
        "pd": [[0.2, 0.9], [0.5, 0.4]],  # Second point violates: death < birth
        "betti": None
    }

    r = client.post("/reasoner/check", json=body)
    assert r.status_code == 200

    j = r.json()
    assert not j["ok"]  # Should fail
    assert len(j["violations"]) > 0
    assert any("DeathGeBirth" in v["constraint"] for v in j["violations"])

    # Verify structure
    assert "checked_constraints" in j
    assert "DeathGeBirth" in j["checked_constraints"]


def test_reasoner_passes_good_pd(client):
    """
    Test that reasoner passes valid persistence diagrams

    All points satisfy Death >= Birth and lifetime constraints.
    """
    body = {
        "constraints": ["DeathGeBirth", "MaxLifetime:1.5"],
        "pd": [[0.2, 0.9], [0.5, 1.0]],  # All valid
        "betti": None
    }

    r = client.post("/reasoner/check", json=body)
    assert r.status_code == 200

    j = r.json()
    assert j["ok"]  # Should pass
    assert len(j["violations"]) == 0
    assert "checked_constraints" in j

