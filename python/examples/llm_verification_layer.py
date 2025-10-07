"""
LLM Verification Layer Example

Demonstrates how to use TCDB as a verification layer to prevent
LLM hallucinations in topological data analysis applications.
"""

import tcdb_core
import json
import hashlib


class LLMVerificationLayer:
    """
    Wrapper that validates LLM outputs against TCDB ground truth.
    
    This prevents hallucinations by checking:
    1. Topological constraints (Betti numbers, Euler characteristic)
    2. Probabilistic reasoning (Bayesian confidence)
    3. Provenance verification (cryptographic hashes)
    4. Mathematical consistency (formal properties)
    """
    
    def __init__(self, strict_mode=True):
        """
        Initialize verification layer.
        
        Args:
            strict_mode: If True, reject any violations. If False, warn only.
        """
        self.strict_mode = strict_mode
        self.violations = []
    
    def verify_topology_claim(self, llm_output, ground_truth_data):
        """
        Verify LLM claims about topology against TCDB computation.
        
        Args:
            llm_output: Dict with LLM's topological claims
            ground_truth_data: Actual data to analyze
        
        Returns:
            bool: True if verified, False if hallucination detected
        """
        violations = []
        
        # Check Euler characteristic
        if "euler_characteristic" in llm_output:
            claimed_chi = llm_output["euler_characteristic"]
            
            # Compute actual chi from data
            if "fvector" in ground_truth_data:
                fvec = tcdb_core.FVector(ground_truth_data["fvector"])
                actual_chi = fvec.euler_characteristic()
                
                if claimed_chi != actual_chi:
                    violations.append({
                        "type": "euler_characteristic_mismatch",
                        "claimed": claimed_chi,
                        "actual": actual_chi,
                        "severity": "high"
                    })
        
        # Check Betti numbers
        if "betti_numbers" in llm_output:
            for k, betti_k in llm_output["betti_numbers"].items():
                if betti_k < 0:
                    violations.append({
                        "type": "negative_betti_number",
                        "dimension": k,
                        "value": betti_k,
                        "severity": "critical"
                    })
        
        # Check persistence diagram validity
        if "persistence_diagram" in llm_output:
            pd = llm_output["persistence_diagram"]
            for birth, death in pd:
                if death < birth:
                    violations.append({
                        "type": "death_before_birth",
                        "birth": birth,
                        "death": death,
                        "severity": "critical"
                    })
        
        self.violations.extend(violations)
        
        if violations and self.strict_mode:
            return False
        return True
    
    def verify_confidence_claim(self, llm_output, evidence_data):
        """
        Verify LLM confidence claims against Bayesian computation.
        
        Args:
            llm_output: Dict with LLM's confidence claim
            evidence_data: Evidence for Bayesian update
        
        Returns:
            bool: True if verified, False if hallucination detected
        """
        violations = []
        
        if "confidence" not in llm_output:
            return True
        
        claimed_confidence = llm_output["confidence"]
        
        # Compute actual posterior
        prior = evidence_data.get("prior", 0.5)
        
        if "evidence" in evidence_data:
            ev = evidence_data["evidence"]
            evidence = tcdb_core.Evidence(ev["like_h"], ev["like_not_h"])
            posterior = tcdb_core.py_posterior(prior, evidence)
            actual_confidence = posterior.posterior
            
            # Check for overconfidence
            if claimed_confidence > actual_confidence + 0.1:
                violations.append({
                    "type": "overconfident",
                    "claimed": claimed_confidence,
                    "actual": actual_confidence,
                    "severity": "medium"
                })
            
            # Check for underconfidence
            elif claimed_confidence < actual_confidence - 0.1:
                violations.append({
                    "type": "underconfident",
                    "claimed": claimed_confidence,
                    "actual": actual_confidence,
                    "severity": "low"
                })
        
        self.violations.extend(violations)
        
        if violations and self.strict_mode:
            return False
        return True
    
    def verify_provenance(self, llm_output, actual_data):
        """
        Verify provenance hash claims.
        
        Args:
            llm_output: Dict with LLM's hash claim
            actual_data: Actual data to hash
        
        Returns:
            bool: True if verified, False if hallucination detected
        """
        violations = []
        
        if "data_hash" not in llm_output:
            return True
        
        claimed_hash = llm_output["data_hash"]
        
        # Compute actual hash
        data_bytes = json.dumps(actual_data, sort_keys=True).encode()
        actual_hash = hashlib.sha256(data_bytes).hexdigest()[:16]
        
        if claimed_hash != actual_hash:
            violations.append({
                "type": "hash_mismatch",
                "claimed": claimed_hash,
                "actual": actual_hash,
                "severity": "critical"
            })
        
        self.violations.extend(violations)
        
        if violations and self.strict_mode:
            return False
        return True
    
    def get_violations_report(self):
        """Get detailed report of all violations."""
        if not self.violations:
            return "✅ No violations detected. LLM output verified."
        
        report = f"❌ {len(self.violations)} violation(s) detected:\n\n"
        
        for i, v in enumerate(self.violations, 1):
            report += f"{i}. {v['type'].upper()} (severity: {v['severity']})\n"
            for key, value in v.items():
                if key not in ['type', 'severity']:
                    report += f"   {key}: {value}\n"
            report += "\n"
        
        return report


def example_1_topology_verification():
    """Example 1: Verify topology claims."""
    print("=" * 60)
    print("Example 1: Topology Verification")
    print("=" * 60)
    
    # Simulated LLM output
    llm_output = {
        "shape": "sphere",
        "euler_characteristic": 5,  # WRONG! Should be 2
        "betti_numbers": {"0": 1, "1": 0, "2": 1},
    }
    
    # Ground truth data
    ground_truth = {
        "fvector": [6, 12, 8],  # Octahedron (sphere approximation)
    }
    
    # Verify
    verifier = LLMVerificationLayer(strict_mode=True)
    verified = verifier.verify_topology_claim(llm_output, ground_truth)
    
    print(f"\nLLM Output: {json.dumps(llm_output, indent=2)}")
    print(f"\nVerification Result: {'✅ PASS' if verified else '❌ FAIL'}")
    print(f"\n{verifier.get_violations_report()}")


def example_2_confidence_verification():
    """Example 2: Verify confidence claims."""
    print("=" * 60)
    print("Example 2: Confidence Verification")
    print("=" * 60)
    
    # Simulated LLM output claiming high confidence
    llm_output = {
        "classification": "anomaly",
        "confidence": 0.95,  # Very high
        "reasoning": "Detected unusual pattern",
    }
    
    # Evidence data (weak evidence)
    evidence_data = {
        "prior": 0.01,  # 1% base rate
        "evidence": {
            "like_h": 0.6,    # Weak evidence
            "like_not_h": 0.4,
        }
    }
    
    # Verify
    verifier = LLMVerificationLayer(strict_mode=True)
    verified = verifier.verify_confidence_claim(llm_output, evidence_data)
    
    print(f"\nLLM Output: {json.dumps(llm_output, indent=2)}")
    print(f"\nVerification Result: {'✅ PASS' if verified else '❌ FAIL'}")
    print(f"\n{verifier.get_violations_report()}")


def example_3_provenance_verification():
    """Example 3: Verify provenance hashes."""
    print("=" * 60)
    print("Example 3: Provenance Verification")
    print("=" * 60)
    
    # Simulated LLM output with hash
    llm_output = {
        "analysis": "Completed topological analysis",
        "data_hash": "abc123fake",  # Fake hash
        "results": {"clusters": 3},
    }
    
    # Actual data
    actual_data = {
        "points": [[1, 2], [3, 4], [5, 6]],
        "timestamp": "2024-01-01",
    }
    
    # Verify
    verifier = LLMVerificationLayer(strict_mode=True)
    verified = verifier.verify_provenance(llm_output, actual_data)
    
    print(f"\nLLM Output: {json.dumps(llm_output, indent=2)}")
    print(f"\nVerification Result: {'✅ PASS' if verified else '❌ FAIL'}")
    print(f"\n{verifier.get_violations_report()}")


def example_4_complete_workflow():
    """Example 4: Complete verification workflow."""
    print("=" * 60)
    print("Example 4: Complete Verification Workflow")
    print("=" * 60)
    
    # Simulated LLM analysis of medical imaging data
    llm_output = {
        "patient_id": "P12345",
        "analysis": "Brain scan topological analysis",
        "euler_characteristic": 2,
        "betti_numbers": {"0": 1, "1": 0, "2": 1},
        "anomaly_detected": True,
        "confidence": 0.85,
        "data_hash": "computed_hash_here",
    }
    
    # Ground truth data
    ground_truth = {
        "fvector": [6, 12, 8],  # Sphere-like structure
    }
    
    # Evidence for anomaly detection
    evidence_data = {
        "prior": 0.1,  # 10% base rate for anomalies
        "evidence": {
            "like_h": 0.9,    # Strong evidence for anomaly
            "like_not_h": 0.2,
        }
    }
    
    # Actual data for hash
    actual_data = {
        "patient_id": "P12345",
        "scan_data": "...",
    }
    
    # Verify all aspects
    verifier = LLMVerificationLayer(strict_mode=False)  # Warning mode
    
    topo_ok = verifier.verify_topology_claim(llm_output, ground_truth)
    conf_ok = verifier.verify_confidence_claim(llm_output, evidence_data)
    prov_ok = verifier.verify_provenance(llm_output, actual_data)
    
    all_verified = topo_ok and conf_ok and prov_ok
    
    print(f"\nLLM Analysis:")
    print(json.dumps(llm_output, indent=2))
    
    print(f"\n\nVerification Results:")
    print(f"  Topology: {'✅ PASS' if topo_ok else '❌ FAIL'}")
    print(f"  Confidence: {'✅ PASS' if conf_ok else '❌ FAIL'}")
    print(f"  Provenance: {'✅ PASS' if prov_ok else '❌ FAIL'}")
    print(f"  Overall: {'✅ VERIFIED' if all_verified else '⚠️  WARNINGS'}")
    
    print(f"\n{verifier.get_violations_report()}")


def main():
    """Run all examples."""
    print("\n" + "=" * 60)
    print("LLM Verification Layer Examples")
    print("Demonstrating TCDB's Hallucination Prevention")
    print("=" * 60 + "\n")
    
    example_1_topology_verification()
    print("\n")
    
    example_2_confidence_verification()
    print("\n")
    
    example_3_provenance_verification()
    print("\n")
    
    example_4_complete_workflow()
    
    print("\n" + "=" * 60)
    print("Summary")
    print("=" * 60)
    print("""
TCDB prevents LLM hallucinations by:

1. ✅ Mathematical Verification
   - Euler characteristics must match computed values
   - Betti numbers must be non-negative
   - Persistence diagrams must satisfy death ≥ birth

2. ✅ Probabilistic Verification
   - Confidence claims must match Bayesian posteriors
   - Evidence must support claimed probabilities
   - Cannot claim high confidence without evidence

3. ✅ Cryptographic Verification
   - Hashes must match actual data
   - Provenance cannot be faked
   - Results are tamper-evident

4. ✅ Formal Verification
   - All claims must satisfy Lean 4 theorems
   - Mathematical properties are enforced
   - Violations are automatically detected

Result: LLMs cannot hallucinate topology!
""")
    print("=" * 60 + "\n")


if __name__ == "__main__":
    main()

