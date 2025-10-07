"""
Hallucination A/B Test Harness

Evaluates LLM outputs with and without TCDB verification gates.
Measures hallucination detection rate and false positive rate.
"""

import json
import sys
from pathlib import Path
from typing import Dict, List, Any, Tuple
from dataclasses import dataclass, asdict

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "python"))

import tcdb_core


@dataclass
class EvalItem:
    """Single evaluation item."""
    id: str
    description: str
    ground_truth: Dict[str, Any]
    llm_output: Dict[str, Any]
    expected_violation: bool
    violation_type: str


@dataclass
class EvalResult:
    """Result of evaluating one item."""
    item_id: str
    description: str
    expected_violation: bool
    detected_violation: bool
    violation_type: str
    violations: List[Dict[str, Any]]
    correct: bool
    
    def to_dict(self):
        return asdict(self)


class HallucinationEvaluator:
    """
    Evaluates LLM outputs against TCDB ground truth.
    
    Implements the verification gates:
    1. Topology constraints (Euler characteristic, Betti numbers)
    2. Bayesian confidence bounds
    3. Provenance verification
    4. Reasoner constraints
    """
    
    def __init__(self, strict_mode: bool = True):
        self.strict_mode = strict_mode
        self.results: List[EvalResult] = []
    
    def verify_topology(self, llm_output: Dict, ground_truth: Dict) -> List[Dict]:
        """Verify topological claims."""
        violations = []
        
        # Check Euler characteristic
        if "euler_characteristic" in llm_output and "fvector" in ground_truth:
            claimed = llm_output["euler_characteristic"]
            fvec = tcdb_core.FVector(ground_truth["fvector"])
            actual = fvec.euler_characteristic()
            
            if claimed != actual:
                violations.append({
                    "type": "euler_mismatch",
                    "claimed": claimed,
                    "actual": actual,
                    "severity": "high"
                })
        
        # Check Betti numbers
        if "betti_numbers" in llm_output:
            for dim, value in llm_output["betti_numbers"].items():
                if value < 0:
                    violations.append({
                        "type": "negative_betti",
                        "dimension": dim,
                        "value": value,
                        "severity": "critical"
                    })
        
        # Check persistence diagram
        if "persistence_diagram" in llm_output:
            for birth, death in llm_output["persistence_diagram"]:
                if death < birth:
                    violations.append({
                        "type": "death_before_birth",
                        "birth": birth,
                        "death": death,
                        "severity": "critical"
                    })
        
        return violations
    
    def verify_confidence(self, llm_output: Dict, ground_truth: Dict) -> List[Dict]:
        """Verify Bayesian confidence claims."""
        violations = []
        
        if "confidence" not in llm_output:
            return violations
        
        claimed = llm_output["confidence"]
        
        if "bayesian" in ground_truth:
            prior = ground_truth["bayesian"]["prior"]
            ev = ground_truth["bayesian"]["evidence"]
            evidence = tcdb_core.Evidence(ev["like_h"], ev["like_not_h"])
            posterior = tcdb_core.py_posterior(prior, evidence)
            actual = posterior.posterior
            
            # Check for overconfidence (>10% deviation)
            if claimed > actual + 0.1:
                violations.append({
                    "type": "overconfident",
                    "claimed": claimed,
                    "actual": actual,
                    "deviation": claimed - actual,
                    "severity": "medium"
                })
            
            # Check for underconfidence
            elif claimed < actual - 0.1:
                violations.append({
                    "type": "underconfident",
                    "claimed": claimed,
                    "actual": actual,
                    "deviation": actual - claimed,
                    "severity": "low"
                })
        
        return violations
    
    def verify_provenance(self, llm_output: Dict, ground_truth: Dict) -> List[Dict]:
        """Verify provenance hashes."""
        violations = []
        
        if "data_hash" in llm_output and "expected_hash" in ground_truth:
            claimed = llm_output["data_hash"]
            expected = ground_truth["expected_hash"]
            
            if claimed != expected:
                violations.append({
                    "type": "hash_mismatch",
                    "claimed": claimed,
                    "expected": expected,
                    "severity": "critical"
                })
        
        return violations
    
    def verify_reasoner_constraints(self, llm_output: Dict, ground_truth: Dict) -> List[Dict]:
        """Verify reasoner constraints."""
        violations = []
        
        # Check for impossible values
        if "similarity" in llm_output:
            sim = llm_output["similarity"]
            if sim < 0.0 or sim > 1.0:
                violations.append({
                    "type": "impossible_similarity",
                    "value": sim,
                    "severity": "critical"
                })
        
        # Check for impossible statistics
        if "statistics" in llm_output:
            stats = llm_output["statistics"]
            if "mean" in stats and "min" in stats and "max" in stats:
                mean = stats["mean"]
                min_val = stats["min"]
                max_val = stats["max"]
                
                if not (min_val <= mean <= max_val):
                    violations.append({
                        "type": "impossible_statistics",
                        "mean": mean,
                        "range": [min_val, max_val],
                        "severity": "critical"
                    })
        
        return violations
    
    def evaluate_item(self, item: EvalItem) -> EvalResult:
        """Evaluate a single item."""
        all_violations = []
        
        # Run all verification gates
        all_violations.extend(self.verify_topology(item.llm_output, item.ground_truth))
        all_violations.extend(self.verify_confidence(item.llm_output, item.ground_truth))
        all_violations.extend(self.verify_provenance(item.llm_output, item.ground_truth))
        all_violations.extend(self.verify_reasoner_constraints(item.llm_output, item.ground_truth))
        
        detected_violation = len(all_violations) > 0
        correct = detected_violation == item.expected_violation
        
        result = EvalResult(
            item_id=item.id,
            description=item.description,
            expected_violation=item.expected_violation,
            detected_violation=detected_violation,
            violation_type=item.violation_type,
            violations=all_violations,
            correct=correct
        )
        
        self.results.append(result)
        return result
    
    def compute_metrics(self) -> Dict[str, float]:
        """Compute evaluation metrics."""
        if not self.results:
            return {}
        
        total = len(self.results)
        correct = sum(1 for r in self.results if r.correct)
        
        # True positives: correctly detected hallucinations
        tp = sum(1 for r in self.results if r.expected_violation and r.detected_violation)
        
        # False positives: incorrectly flagged valid outputs
        fp = sum(1 for r in self.results if not r.expected_violation and r.detected_violation)
        
        # True negatives: correctly accepted valid outputs
        tn = sum(1 for r in self.results if not r.expected_violation and not r.detected_violation)
        
        # False negatives: missed hallucinations
        fn = sum(1 for r in self.results if r.expected_violation and not r.detected_violation)
        
        accuracy = correct / total if total > 0 else 0.0
        precision = tp / (tp + fp) if (tp + fp) > 0 else 0.0
        recall = tp / (tp + fn) if (tp + fn) > 0 else 0.0
        f1 = 2 * (precision * recall) / (precision + recall) if (precision + recall) > 0 else 0.0
        
        return {
            "total": total,
            "correct": correct,
            "accuracy": accuracy,
            "true_positives": tp,
            "false_positives": fp,
            "true_negatives": tn,
            "false_negatives": fn,
            "precision": precision,
            "recall": recall,
            "f1_score": f1,
        }
    
    def print_report(self):
        """Print evaluation report."""
        metrics = self.compute_metrics()
        
        print("\n" + "=" * 70)
        print("TCDB Hallucination Detection Evaluation Report")
        print("=" * 70)
        
        print(f"\nTotal Items: {metrics['total']}")
        print(f"Correct: {metrics['correct']}")
        print(f"Accuracy: {metrics['accuracy']:.1%}")
        
        print(f"\nConfusion Matrix:")
        print(f"  True Positives:  {metrics['true_positives']:3d} (hallucinations detected)")
        print(f"  False Positives: {metrics['false_positives']:3d} (false alarms)")
        print(f"  True Negatives:  {metrics['true_negatives']:3d} (valid outputs accepted)")
        print(f"  False Negatives: {metrics['false_negatives']:3d} (missed hallucinations)")
        
        print(f"\nPerformance Metrics:")
        print(f"  Precision: {metrics['precision']:.1%} (of flagged items, how many were actual hallucinations)")
        print(f"  Recall:    {metrics['recall']:.1%} (of actual hallucinations, how many were detected)")
        print(f"  F1 Score:  {metrics['f1_score']:.3f}")
        
        print("\n" + "=" * 70)
        
        # Print individual results
        print("\nDetailed Results:")
        print("-" * 70)
        
        for r in self.results:
            status = "✅ PASS" if r.correct else "❌ FAIL"
            print(f"\n{status} [{r.item_id}] {r.description}")
            print(f"  Expected violation: {r.expected_violation}")
            print(f"  Detected violation: {r.detected_violation}")
            
            if r.violations:
                print(f"  Violations found:")
                for v in r.violations:
                    print(f"    - {v['type']} (severity: {v['severity']})")
        
        print("\n" + "=" * 70 + "\n")


def load_eval_items(jsonl_path: Path) -> List[EvalItem]:
    """Load evaluation items from JSONL file."""
    items = []

    with open(jsonl_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line:  # Skip empty lines
                continue
            data = json.loads(line)
            items.append(EvalItem(**data))

    return items


def main():
    """Run hallucination evaluation."""
    # Path to evaluation data
    eval_file = Path(__file__).parent / "items.jsonl"
    
    if not eval_file.exists():
        print(f"Error: Evaluation file not found: {eval_file}")
        print("Creating sample evaluation file...")
        create_sample_eval_file(eval_file)
        print(f"Sample file created at {eval_file}")
        print("Please review and run again.")
        return
    
    # Load evaluation items
    items = load_eval_items(eval_file)
    
    print(f"Loaded {len(items)} evaluation items from {eval_file}")
    
    # Run evaluation
    evaluator = HallucinationEvaluator(strict_mode=True)
    
    for item in items:
        evaluator.evaluate_item(item)
    
    # Print report
    evaluator.print_report()
    
    # Save results
    results_file = Path(__file__).parent / "eval_results.json"
    with open(results_file, 'w') as f:
        json.dump({
            "metrics": evaluator.compute_metrics(),
            "results": [r.to_dict() for r in evaluator.results]
        }, f, indent=2)
    
    print(f"Results saved to {results_file}")


def create_sample_eval_file(path: Path):
    """Create sample evaluation file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    
    sample_items = [
        {
            "id": "topo_001",
            "description": "LLM claims wrong Euler characteristic for sphere",
            "ground_truth": {"fvector": [6, 12, 8]},
            "llm_output": {"euler_characteristic": 5},
            "expected_violation": True,
            "violation_type": "euler_mismatch"
        },
        {
            "id": "topo_002",
            "description": "LLM correctly identifies sphere topology",
            "ground_truth": {"fvector": [6, 12, 8]},
            "llm_output": {"euler_characteristic": 2},
            "expected_violation": False,
            "violation_type": "none"
        },
    ]
    
    with open(path, 'w') as f:
        for item in sample_items:
            f.write(json.dumps(item) + '\n')


if __name__ == "__main__":
    main()

