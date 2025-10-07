"""
Tests for evaluation/hallucination detection functionality
"""

import pytest
from fastapi.testclient import TestClient


def test_eval_run_basic(client):
    """
    Test basic evaluation run with multiple items

    Tests the evaluation pipeline that checks for:
    - Claim support
    - Hallucination detection
    - Citation verification
    - Topological constraints
    """
    payload = {
        "items": [
            {
                "id": "ex1",
                "question": "Does X form β-sheets at pH<6?",
                "answer_text": "Yes, X forms beta-sheets at pH<6 per Smith 2019.",
                "claims": ["X forms beta-sheets at pH<6"],
                "citations": ["doc://smith2019#p3"],
                "pd": [[0.1, 0.9]],
                "constraints": ["DeathGeBirth", "MaxLifetime:1.5"],
                "data_cid": "cid:abc",
                "code_rev": "rev:123"
            },
            {
                "id": "ex2",
                "question": "Is CVE-2021-44228 exploitable here?",
                "answer_text": "[ABSTAIN] insufficient evidence",
                "claims": [],
                "citations": []
            }
        ],
        "require_tcdb": False
    }

    r = client.post("/eval/run", json=payload)
    assert r.status_code == 200

    j = r.json()
    assert "items" in j
    assert "summary" in j

    # First item should be supported & non-hallucinating with our simple entailment
    ex1 = next(i for i in j["items"] if i["id"] == "ex1")
    assert ex1["hallucinated"] is False
    assert ex1["supported"] is True

    # Second item (abstention) should not be hallucinated
    ex2 = next(i for i in j["items"] if i["id"] == "ex2")
    assert ex2["hallucinated"] is False

    # Check summary
    assert j["summary"]["total_items"] == 2
    assert j["summary"]["hallucinated_count"] == 0

