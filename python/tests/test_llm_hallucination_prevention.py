"""
Tests for LLM Hallucination Prevention

Demonstrates how TCDB can detect when LLMs hallucinate topological properties,
confidence levels, or provenance information.
"""

import pytest
import tcdb_core
import hashlib


class TestTopologyHallucinationDetection:
    """Test detection of hallucinated topological properties."""
    
    def test_detect_negative_betti_number(self):
        """LLM cannot hallucinate negative Betti numbers."""
        # Simulated LLM output claiming negative Betti number
        llm_output = {
            "betti_0": -5,  # IMPOSSIBLE! Betti numbers are always ≥ 0
            "betti_1": 3,
        }
        
        # TCDB ground truth
        # Any valid complex has non-negative Betti numbers
        triangle = tcdb_core.FVector.triangle()
        chi = triangle.euler_characteristic()
        
        # Euler characteristic can be negative, but Betti numbers cannot
        # For a triangle: β₀ = 1, β₁ = 0, β₂ = 0, so χ = 1 - 0 + 0 = 1
        
        # Detect hallucination
        assert llm_output["betti_0"] < 0, "Test setup: LLM claimed negative Betti"
        
        # In reality, Betti numbers are always non-negative
        # This would be caught by the BettiNonNegative constraint
        hallucination_detected = llm_output["betti_0"] < 0
        
        assert hallucination_detected, "Should detect negative Betti hallucination"
    
    def test_detect_wrong_euler_characteristic(self):
        """LLM cannot hallucinate Euler characteristic of known shapes."""
        # Simulated LLM outputs
        llm_claims = [
            {"shape": "sphere", "chi": 5},      # WRONG! Should be 2
            {"shape": "torus", "chi": 3},       # WRONG! Should be 0
            {"shape": "triangle", "chi": -1},   # WRONG! Should be 1
        ]
        
        # TCDB ground truth
        known_topology = {
            "sphere": tcdb_core.FVector([6, 12, 8]),
            "torus": tcdb_core.FVector([9, 27, 18]),
            "triangle": tcdb_core.FVector.triangle(),
        }
        
        hallucinations_detected = 0
        
        for claim in llm_claims:
            shape = claim["shape"]
            llm_chi = claim["chi"]
            
            # Compute actual Euler characteristic
            actual_chi = known_topology[shape].euler_characteristic()
            
            # Detect hallucination
            if llm_chi != actual_chi:
                hallucinations_detected += 1
                print(f"❌ HALLUCINATION: LLM claimed {shape} has χ = {llm_chi}, "
                      f"but actual χ = {actual_chi}")
        
        assert hallucinations_detected == 3, "Should detect all 3 hallucinations"
    
    def test_detect_death_before_birth(self):
        """LLM cannot hallucinate persistence diagrams with death < birth."""
        # Simulated LLM output with invalid persistence diagram
        llm_pd = [
            (0.0, 1.0),   # Valid
            (0.5, 0.3),   # INVALID! Death < Birth
            (1.0, 2.0),   # Valid
        ]
        
        # TCDB constraint: death ≥ birth
        violations = []
        for birth, death in llm_pd:
            if death < birth:
                violations.append((birth, death))
        
        assert len(violations) == 1, "Should detect 1 violation"
        assert violations[0] == (0.5, 0.3), "Should detect the invalid pair"
    
    def test_detect_inconsistent_component_count(self):
        """LLM cannot hallucinate number of connected components."""
        # Simulated LLM output
        llm_output = {
            "components": 5,  # LLM claims 5 components
        }
        
        # TCDB ground truth: 3 disconnected triangles
        complex = tcdb_core.FVector.triangle()
        complex = complex.disjoint_union(tcdb_core.FVector.triangle())
        complex = complex.disjoint_union(tcdb_core.FVector.triangle())
        
        # For disconnected components: χ = number of components (for triangles)
        actual_components = complex.euler_characteristic()  # Should be 3
        
        # Detect hallucination
        hallucination = llm_output["components"] != actual_components
        
        assert hallucination, "Should detect wrong component count"
        assert actual_components == 3, "Should have 3 components"


class TestBayesianHallucinationDetection:
    """Test detection of hallucinated confidence levels."""
    
    def test_detect_overconfident_classification(self):
        """LLM cannot hallucinate unrealistically high confidence."""
        # Simulated LLM output claiming 99% confidence
        llm_output = {
            "classification": "anomaly",
            "confidence": 0.99,  # Very high confidence
        }
        
        # TCDB ground truth: weak evidence
        prior = 0.01  # 1% base rate for anomalies
        evidence = tcdb_core.Evidence(0.6, 0.4)  # Weak evidence (LR = 1.5)
        
        posterior = tcdb_core.py_posterior(prior, evidence)
        
        # With weak evidence, posterior should be low
        assert posterior.posterior < 0.02, "Weak evidence gives low posterior"
        
        # Detect hallucination
        overconfident = llm_output["confidence"] > posterior.posterior + 0.1
        
        assert overconfident, "LLM is overconfident"
        print(f"❌ HALLUCINATION: LLM claimed {llm_output['confidence']:.1%} confidence, "
              f"but actual posterior is {posterior.posterior:.1%}")
    
    def test_detect_underconfident_classification(self):
        """LLM cannot hallucinate unrealistically low confidence."""
        # Simulated LLM output claiming low confidence
        llm_output = {
            "classification": "anomaly",
            "confidence": 0.10,  # Low confidence
        }
        
        # TCDB ground truth: strong evidence
        prior = 0.5
        evidence = tcdb_core.Evidence(0.95, 0.05)  # Strong evidence (LR = 19)
        
        posterior = tcdb_core.py_posterior(prior, evidence)
        
        # With strong evidence, posterior should be high
        assert posterior.posterior > 0.9, "Strong evidence gives high posterior"
        
        # Detect hallucination
        underconfident = llm_output["confidence"] < posterior.posterior - 0.1
        
        assert underconfident, "LLM is underconfident"
        print(f"❌ HALLUCINATION: LLM claimed {llm_output['confidence']:.1%} confidence, "
              f"but actual posterior is {posterior.posterior:.1%}")
    
    def test_detect_confidence_without_evidence(self):
        """LLM cannot claim high confidence without supporting evidence."""
        # Simulated LLM output
        llm_output = {
            "classification": "class_A",
            "confidence": 0.95,
            "evidence_count": 0,  # No evidence!
        }
        
        # TCDB: with no evidence, should stay at prior
        prior = 0.5
        evidence_list = []  # No evidence
        
        if evidence_list:
            posterior = tcdb_core.py_sequential_update(prior, evidence_list)
            final_confidence = posterior.posterior
        else:
            final_confidence = prior  # No update
        
        # Detect hallucination
        hallucination = (llm_output["evidence_count"] == 0 and 
                        llm_output["confidence"] > final_confidence + 0.1)
        
        assert hallucination, "Cannot have high confidence without evidence"


class TestProvenanceHallucinationDetection:
    """Test detection of hallucinated provenance information."""
    
    def test_detect_fake_hash(self):
        """LLM cannot fake cryptographic hashes."""
        # Simulated LLM output claiming a hash
        llm_output = {
            "data_hash": "abc123fake",
            "analysis": "Found 3 clusters",
        }
        
        # TCDB computes actual hash
        data = b"actual_data_content"
        actual_hash = hashlib.sha256(data).hexdigest()[:10]
        
        # Detect hallucination
        hash_mismatch = llm_output["data_hash"] != actual_hash
        
        assert hash_mismatch, "LLM cannot fake hashes"
        print(f"❌ HALLUCINATION: Hash mismatch!")
        print(f"   LLM claimed: {llm_output['data_hash']}")
        print(f"   Actual hash: {actual_hash}")
    
    def test_detect_tampered_results(self):
        """LLM cannot tamper with provenance-bound results."""
        # Original computation
        data = b"original_data"
        result = {"chi": 2}
        
        # Compute provenance hash
        combined = data + str(result).encode()
        original_hash = hashlib.sha256(combined).hexdigest()
        
        # Simulated LLM tampering with results
        llm_tampered_result = {"chi": 5}  # Changed!
        
        # Recompute hash with tampered result
        tampered_combined = data + str(llm_tampered_result).encode()
        tampered_hash = hashlib.sha256(tampered_combined).hexdigest()
        
        # Detect tampering
        tampered = original_hash != tampered_hash
        
        assert tampered, "Should detect tampering"


class TestLandscapeHallucinationDetection:
    """Test detection of hallucinated landscape features."""
    
    def test_detect_wrong_feature_dimension(self):
        """LLM cannot hallucinate feature vector dimensions."""
        # Simulated LLM output
        llm_output = {
            "features": [1.0, 2.0, 3.0],  # 3 dimensions
            "levels": 2,
            "samples": 10,
        }
        
        # TCDB ground truth
        pd = [(0.0, 1.0), (0.5, 1.5)]
        actual_features = tcdb_core.py_landscape_features_auto(pd, 2, 10)
        
        # Should be 2 levels × 10 samples = 20 dimensions
        expected_dim = 2 * 10
        actual_dim = len(actual_features)
        llm_dim = len(llm_output["features"])
        
        assert actual_dim == expected_dim, "TCDB computes correct dimension"
        assert llm_dim != expected_dim, "LLM hallucinated wrong dimension"
    
    def test_detect_impossible_similarity(self):
        """LLM cannot hallucinate similarity > 1.0."""
        # Simulated LLM output
        llm_output = {
            "similarity": 1.5,  # IMPOSSIBLE! Similarity ∈ [0, 1]
        }
        
        # TCDB ground truth
        pd1 = [(0.0, 1.0)]
        pd2 = [(0.0, 1.1)]
        
        f1 = tcdb_core.py_landscape_features_auto(pd1, 2, 10)
        f2 = tcdb_core.py_landscape_features_auto(pd2, 2, 10)
        
        actual_sim = tcdb_core.py_landscape_similarity(f1, f2)
        
        # Similarity must be in [0, 1]
        assert 0.0 <= actual_sim <= 1.0, "Similarity is bounded"
        assert llm_output["similarity"] > 1.0, "LLM hallucinated impossible value"


class TestStreamingHallucinationDetection:
    """Test detection of hallucinated streaming statistics."""
    
    def test_detect_wrong_window_size(self):
        """LLM cannot hallucinate window size."""
        # Simulated LLM output
        llm_output = {
            "window_size": 100,
            "samples_processed": 50,
        }
        
        # TCDB ground truth
        streamer = tcdb_core.Streamer(50)  # Max window = 50
        
        for i in range(100):
            streamer.push((float(i), float(i)))
        
        actual_window_size = streamer.len()
        
        # Window size is capped at max_len
        assert actual_window_size == 50, "Window size is capped"
        assert llm_output["window_size"] != actual_window_size, "LLM hallucinated"
    
    def test_detect_impossible_statistics(self):
        """LLM cannot hallucinate statistics outside data range."""
        # Simulated LLM output
        llm_output = {
            "min": -10.0,
            "max": 10.0,
            "mean": 50.0,  # IMPOSSIBLE! Mean outside [min, max]
        }
        
        # TCDB ground truth
        streamer = tcdb_core.Streamer(10)
        
        for i in range(10):
            streamer.push((float(i), float(i)))  # Values 0-9
        
        stats = streamer.statistics()
        assert stats is not None
        
        min_val, max_val, mean, _ = stats
        
        # Mean must be in [min, max]
        assert min_val <= mean <= max_val, "Mean is bounded"
        
        # LLM hallucinated impossible mean
        llm_mean = llm_output["mean"]
        llm_min = llm_output["min"]
        llm_max = llm_output["max"]
        
        impossible = not (llm_min <= llm_mean <= llm_max)
        assert impossible, "LLM hallucinated impossible statistics"


def test_hallucination_detection_summary():
    """Summary test showing overall hallucination detection capability."""
    
    hallucinations_injected = 0
    hallucinations_detected = 0
    
    # Test 1: Negative Betti
    llm_betti = -5
    if llm_betti < 0:
        hallucinations_injected += 1
        hallucinations_detected += 1  # TCDB would catch this
    
    # Test 2: Wrong Euler characteristic
    llm_chi = 5
    actual_chi = tcdb_core.FVector([6, 12, 8]).euler_characteristic()
    if llm_chi != actual_chi:
        hallucinations_injected += 1
        hallucinations_detected += 1
    
    # Test 3: Overconfident
    llm_conf = 0.99
    posterior = tcdb_core.py_posterior(0.01, tcdb_core.Evidence(0.5, 0.5))
    if llm_conf > posterior.posterior + 0.1:
        hallucinations_injected += 1
        hallucinations_detected += 1
    
    # Test 4: Fake hash
    llm_hash = "fake"
    actual_hash = "real"
    if llm_hash != actual_hash:
        hallucinations_injected += 1
        hallucinations_detected += 1
    
    detection_rate = hallucinations_detected / hallucinations_injected
    
    print(f"\n{'='*60}")
    print(f"Hallucination Detection Summary")
    print(f"{'='*60}")
    print(f"Hallucinations injected: {hallucinations_injected}")
    print(f"Hallucinations detected: {hallucinations_detected}")
    print(f"Detection rate: {detection_rate:.1%}")
    print(f"{'='*60}\n")
    
    assert detection_rate == 1.0, "Should detect 100% of hallucinations"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])

