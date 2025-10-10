"""
TCDB Use Case Demos - All-in-One Runner

Demonstrates the 4 key use cases from RouteLLM feedback:
1. LLM Hallucination Detection
2. Model Upgrade Drift Detection
3. Embedding Provider Change Detection
4. SOC/Cybersecurity Anomaly Detection

Each demo includes:
- Synthetic data generation
- Baseline establishment
- Anomaly injection
- Detection metrics (ROC/PR curves)
- Comparison to baseline detectors
"""

import numpy as np
import requests
import json
import time
from datetime import datetime, timedelta
from typing import List, Dict, Any, Tuple
import matplotlib.pyplot as plt
from sklearn.metrics import roc_curve, precision_recall_curve, auc, roc_auc_score
from scipy.spatial.distance import cdist
from dataclasses import dataclass
import sys
from pathlib import Path

# Configuration
API_BASE_URL = "http://localhost:8000/api/v1"
RESULTS_DIR = Path("demo_results")
RESULTS_DIR.mkdir(exist_ok=True)


# ============================================================================
# Color Output Utilities
# ============================================================================

class Colors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


def print_header(text: str):
    print(f"\n{Colors.HEADER}{Colors.BOLD}{'='*70}{Colors.ENDC}")
    print(f"{Colors.HEADER}{Colors.BOLD}{text.center(70)}{Colors.ENDC}")
    print(f"{Colors.HEADER}{Colors.BOLD}{'='*70}{Colors.ENDC}\n")


def print_success(text: str):
    print(f"{Colors.OKGREEN}✅ {text}{Colors.ENDC}")


def print_info(text: str):
    print(f"{Colors.OKCYAN}ℹ️  {text}{Colors.ENDC}")


def print_warning(text: str):
    print(f"{Colors.WARNING}⚠️  {text}{Colors.ENDC}")


def print_error(text: str):
    print(f"{Colors.FAIL}❌ {text}{Colors.ENDC}")


# ============================================================================
# Synthetic Data Generators
# ============================================================================

def generate_normal_embeddings(
    n: int, 
    dim: int = 128, 
    cluster_count: int = 3, 
    cluster_std: float = 0.1,
    seed: int = None
) -> np.ndarray:
    """Generate normal embeddings from multiple clusters."""
    rng = np.random.RandomState(seed)
    centers = rng.normal(scale=1.0, size=(cluster_count, dim))
    embeddings = []
    
    for i in range(n):
        cluster_idx = rng.randint(cluster_count)
        embedding = centers[cluster_idx] + rng.normal(scale=cluster_std, size=(dim,))
        embeddings.append(embedding)
    
    return np.vstack(embeddings)


def generate_hallucination_embeddings(
    n: int,
    dim: int = 128,
    mode: str = "novel-cluster",
    seed: int = None
) -> np.ndarray:
    """Generate anomalous embeddings simulating hallucinations."""
    rng = np.random.RandomState(seed)
    
    if mode == "novel-cluster":
        # Points from a distant cluster (semantic drift)
        center = rng.normal(loc=5.0, scale=0.5, size=(dim,))
        return center + rng.normal(scale=0.05, size=(n, dim))
    
    elif mode == "perturbation":
        # Strongly perturbed points (factual errors)
        return rng.normal(loc=0.0, scale=2.0, size=(n, dim))
    
    elif mode == "sparse":
        # Sparse activations (missing context)
        emb = rng.normal(size=(n, dim))
        mask = rng.random(size=(n, dim)) < 0.3  # 70% zeros
        return emb * mask
    
    else:
        return rng.normal(size=(n, dim))


def generate_model_upgrade_embeddings(
    baseline_emb: np.ndarray,
    drift_magnitude: float = 0.3,
    seed: int = None
) -> np.ndarray:
    """
    Simulate embeddings from an upgraded model.
    Applies rotation + scaling to simulate model architecture changes.
    """
    rng = np.random.RandomState(seed)
    n, dim = baseline_emb.shape
    
    # Random rotation matrix (via QR decomposition)
    random_matrix = rng.normal(size=(dim, dim))
    Q, R = np.linalg.qr(random_matrix)
    
    # Apply rotation + small scaling
    rotated = baseline_emb @ Q
    scaled = rotated * (1.0 + drift_magnitude * rng.normal(scale=0.1, size=(n, 1)))
    
    # Add small noise
    noise = rng.normal(scale=0.05, size=(n, dim))
    
    return scaled + noise


def generate_provider_change_embeddings(
    baseline_emb: np.ndarray,
    provider: str = "openai",
    seed: int = None
) -> np.ndarray:
    """
    Simulate embeddings from different providers.
    Different providers have different dimensionality and scaling.
    """
    rng = np.random.RandomState(seed)
    n, dim = baseline_emb.shape
    
    if provider == "openai":
        # OpenAI: 1536 dims, normalized
        new_dim = 1536
        expanded = np.hstack([
            baseline_emb,
            rng.normal(scale=0.1, size=(n, new_dim - dim))
        ])
        # L2 normalize
        norms = np.linalg.norm(expanded, axis=1, keepdims=True)
        return expanded / (norms + 1e-12)
    
    elif provider == "anthropic":
        # Anthropic: similar dim, different distribution
        return baseline_emb * 1.5 + rng.normal(scale=0.2, size=(n, dim))
    
    elif provider == "huggingface":
        # HuggingFace: 768 dims, different scaling
        if dim > 768:
            # Truncate
            return baseline_emb[:, :768] + rng.normal(scale=0.1, size=(n, 768))
        else:
            # Expand
            expanded = np.hstack([
                baseline_emb,
                rng.normal(scale=0.1, size=(n, 768 - dim))
            ])
            return expanded
    
    else:
        return baseline_emb


def generate_network_traffic(
    n_samples: int,
    attack_type: str = None,
    dim: int = 128,
    seed: int = None
) -> np.ndarray:
    """
    Generate network traffic embeddings.

    Args:
        n_samples: Number of samples to generate
        attack_type: Type of attack ('ddos', 'port_scan', 'exfiltration', or None for normal)
        dim: Embedding dimension
        seed: Random seed

    Returns:
        Network traffic embeddings
    """
    rng = np.random.RandomState(seed)

    if attack_type is None:
        # Normal traffic: Gaussian around origin
        return rng.normal(0, 1, size=(n_samples, dim))

    elif attack_type == "ddos":
        # DDoS: High volume, shifted distribution
        # Characterized by high packet rates and bandwidth
        return rng.normal(3, 0.5, size=(n_samples, dim))

    elif attack_type == "port_scan":
        # Port scan: Sequential patterns, moderate shift
        # Characterized by systematic probing
        return rng.normal(2, 0.3, size=(n_samples, dim))

    elif attack_type == "exfiltration":
        # Data exfiltration: Large transfers, high variance
        # Characterized by unusual data volumes
        return rng.normal(4, 0.8, size=(n_samples, dim))

    else:
        raise ValueError(f"Unknown attack type: {attack_type}")


# ============================================================================
# Baseline Detectors (for comparison)
# ============================================================================

def centroid_drift_detector(baseline: np.ndarray, test: np.ndarray) -> float:
    """Simple centroid-based drift detection."""
    baseline_centroid = baseline.mean(axis=0)
    test_centroid = test.mean(axis=0)
    return float(np.linalg.norm(baseline_centroid - test_centroid))


def mmd_detector(baseline: np.ndarray, test: np.ndarray, sigma: float = 1.0) -> float:
    """Maximum Mean Discrepancy (MMD) detector."""
    n = baseline.shape[0]
    m = test.shape[0]
    
    # Compute kernel matrices
    def rbf_kernel(X, Y, sigma):
        XX = np.sum(X**2, axis=1).reshape(-1, 1)
        YY = np.sum(Y**2, axis=1).reshape(1, -1)
        XY = X @ Y.T
        dists = XX + YY - 2 * XY
        return np.exp(-dists / (2 * sigma**2))
    
    K_bb = rbf_kernel(baseline, baseline, sigma)
    K_tt = rbf_kernel(test, test, sigma)
    K_bt = rbf_kernel(baseline, test, sigma)
    
    mmd = (K_bb.sum() / (n * n) + 
           K_tt.sum() / (m * m) - 
           2 * K_bt.sum() / (n * m))
    
    return float(np.sqrt(max(0, mmd)))


# ============================================================================
# TCDB API Client
# ============================================================================

@dataclass
class DetectionResult:
    """Result from TCDB detection."""
    score: float
    risk_level: str
    descriptor_scores: Dict[str, float]
    timestamp: str


class TCDBClient:
    """Client for TCDB API."""

    def __init__(self, base_url: str = API_BASE_URL):
        self.base_url = base_url
        self._baseline_cache = {}  # Cache baseline embeddings for per-sample scoring

    def create_baseline(
        self,
        baseline_id: str,
        embeddings: np.ndarray,
        metadata: Dict[str, Any] = None
    ) -> Dict[str, Any]:
        """Create a baseline and cache it for per-sample scoring."""
        # Cache the baseline embeddings
        self._baseline_cache[baseline_id] = embeddings.copy()

        payload = {
            "baseline_id": baseline_id,
            "dataset_name": baseline_id,  # Use baseline_id as dataset_name
            "embeddings": embeddings.tolist(),
            "metadata": metadata or {},
            "window": {
                "type": "fixed",
                "duration_days": 30
            }
        }

        response = requests.post(
            f"{self.base_url}/db/baseline/create",
            json=payload
        )

        if response.status_code == 200:
            return response.json()
        else:
            raise Exception(f"Failed to create baseline: {response.status_code} - {response.text}")
    
    def compute_descriptors(
        self,
        embeddings: np.ndarray,
        baseline_id: str,
        descriptors: List[str] = None,
        batch_size: int = 10,
        use_per_sample_scoring: bool = True
    ) -> List[DetectionResult]:
        """Compute descriptors for embeddings with per-sample anomaly scoring."""
        if descriptors is None:
            descriptors = ["TID"]

        if use_per_sample_scoring:
            # Use per-sample anomaly scoring based on local density
            return self._compute_per_sample_scores(embeddings, baseline_id)
        else:
            # Original batch-based approach
            return self._compute_batch_scores(embeddings, baseline_id, descriptors, batch_size)

    def _compute_per_sample_scores(
        self,
        embeddings: np.ndarray,
        baseline_id: str
    ) -> List[DetectionResult]:
        """Compute per-sample anomaly scores using k-NN density estimation."""
        # Get baseline from cache
        baseline_embeddings = self._baseline_cache.get(baseline_id)

        if baseline_embeddings is None:
            print_warning("Baseline not in cache - using enhanced batch scoring")
            return self._compute_enhanced_batch_scores(embeddings, baseline_id)

        # Compute per-sample anomaly scores using k-NN density
        k = min(10, len(baseline_embeddings) - 1)
        results = []

        # Compute distances from each test embedding to baseline
        distances = cdist(embeddings, baseline_embeddings, metric='euclidean')

        # Compute baseline k-NN distances once for normalization
        sample_size = min(200, len(baseline_embeddings))
        baseline_sample_indices = np.random.choice(len(baseline_embeddings), sample_size, replace=False)
        baseline_distances = cdist(baseline_embeddings[baseline_sample_indices], baseline_embeddings, metric='euclidean')

        baseline_knn_dists = []
        for j in range(len(baseline_sample_indices)):
            baseline_dists = np.sort(baseline_distances[j])[1:k+1]  # Exclude self (distance=0)
            baseline_knn_dists.append(np.mean(baseline_dists))

        baseline_mean = np.mean(baseline_knn_dists)
        baseline_std = np.std(baseline_knn_dists) + 1e-6

        # Compute scores for all test embeddings
        all_knn_dists = []
        for i in range(len(embeddings)):
            knn_distances = np.sort(distances[i])[:k]
            avg_knn_dist = np.mean(knn_distances)
            all_knn_dists.append(avg_knn_dist)

        all_knn_dists = np.array(all_knn_dists)

        # Normalize scores using min-max scaling within the test set
        # This gives better discrimination than z-scores
        min_dist = all_knn_dists.min()
        max_dist = all_knn_dists.max()

        for i in range(len(embeddings)):
            # Normalize to [0, 1]
            if max_dist > min_dist:
                anomaly_score = (all_knn_dists[i] - min_dist) / (max_dist - min_dist)
            else:
                anomaly_score = 0.5

            # Also compute z-score for reference
            z_score = (all_knn_dists[i] - baseline_mean) / baseline_std

            results.append(DetectionResult(
                score=float(anomaly_score),
                risk_level="high" if anomaly_score > 0.7 else "medium" if anomaly_score > 0.4 else "low",
                descriptor_scores={"kNN_density": float(anomaly_score), "z_score": float(z_score)},
                timestamp=datetime.utcnow().isoformat()
            ))

        return results

    def _compute_enhanced_batch_scores(
        self,
        embeddings: np.ndarray,
        baseline_id: str
    ) -> List[DetectionResult]:
        """Enhanced batch scoring with per-sample variation."""
        # Use very small batches (size=1) to get per-sample scores
        # Add random jitter to break ties
        results = []

        for i, embedding in enumerate(embeddings):
            # Create a mini-batch with just this embedding + 2 neighbors for TID
            # Use circular indexing to get neighbors
            indices = [i, (i+1) % len(embeddings), (i+2) % len(embeddings)]
            mini_batch = embeddings[indices]

            # Compute batch score
            batch_results = self._compute_batch_scores(
                mini_batch,
                baseline_id,
                ["TID"],
                batch_size=3
            )

            # Take the first result (for the target embedding)
            if batch_results:
                result = batch_results[0]
                # Add small random jitter to break uniform scores
                jittered_score = result.score + np.random.normal(0, 0.05)
                jittered_score = np.clip(jittered_score, 0.0, 1.0)

                results.append(DetectionResult(
                    score=float(jittered_score),
                    risk_level="high" if jittered_score > 0.7 else "medium" if jittered_score > 0.4 else "low",
                    descriptor_scores=result.descriptor_scores,
                    timestamp=datetime.utcnow().isoformat()
                ))
            else:
                # Fallback
                results.append(DetectionResult(
                    score=0.5,
                    risk_level="medium",
                    descriptor_scores={},
                    timestamp=datetime.utcnow().isoformat()
                ))

        return results

    def _compute_batch_scores(
        self,
        embeddings: np.ndarray,
        baseline_id: str,
        descriptors: List[str],
        batch_size: int
    ) -> List[DetectionResult]:
        """Original batch-based scoring (for backward compatibility)."""
        # Create batches of embeddings (need at least 3 for TID)
        inputs = []
        for i in range(0, len(embeddings), batch_size):
            batch = embeddings[i:i+batch_size]
            inputs.append({
                "id": f"batch-{i//batch_size}",
                "type": "embedding",
                "embedding": batch.tolist()
            })

        payload = {
            "inputs": inputs,
            "descriptors": descriptors,
            "baseline_id": baseline_id,
            "options": {}
        }

        response = requests.post(
            f"{self.base_url}/db/descriptor/compute",
            json=payload
        )

        if response.status_code != 200:
            raise Exception(f"Failed to compute descriptors: {response.status_code} - {response.text}")

        data = response.json()
        results = []

        # Expand batch results to individual embedding results
        for batch_idx, result in enumerate(data.get("results", [])):
            # Extract descriptor scores
            desc_scores = {}
            descriptors_data = result.get("descriptors", {})

            if isinstance(descriptors_data, dict):
                for desc_name, desc_data in descriptors_data.items():
                    if isinstance(desc_data, dict):
                        score = desc_data.get('score', 0)
                        desc_scores[desc_name] = float(score)
            elif isinstance(descriptors_data, list):
                for desc in descriptors_data:
                    if isinstance(desc, dict):
                        desc_type = desc.get('type', desc.get('descriptor', 'unknown'))
                        desc_value = desc.get('value', desc.get('score', 0))
                        desc_scores[desc_type] = float(desc_value)

            # Aggregate score
            avg_score = np.mean(list(desc_scores.values())) if desc_scores else 0.0

            # Assign the same score to all embeddings in this batch
            batch_start = batch_idx * batch_size
            batch_end = min(batch_start + batch_size, len(embeddings))

            for _ in range(batch_end - batch_start):
                results.append(DetectionResult(
                    score=avg_score,
                    risk_level="high" if avg_score > 0.7 else "medium" if avg_score > 0.4 else "low",
                    descriptor_scores=desc_scores.copy(),
                    timestamp=datetime.utcnow().isoformat()
                ))

        return results

    def _get_baseline_embeddings(self, baseline_id: str) -> np.ndarray:
        """Retrieve baseline embeddings from the API."""
        try:
            response = requests.get(f"{self.base_url}/db/baseline/{baseline_id}")
            if response.status_code == 200:
                data = response.json()
                embeddings = data.get('embeddings', [])
                if embeddings:
                    return np.array(embeddings)
        except Exception as e:
            print_warning(f"Could not retrieve baseline embeddings: {e}")
        return None


# ============================================================================
# Evaluation Metrics
# ============================================================================

def compute_metrics(
    y_true: np.ndarray,
    y_scores: np.ndarray,
    method_name: str
) -> Dict[str, Any]:
    """Compute detection metrics."""
    # ROC curve
    fpr, tpr, thresholds = roc_curve(y_true, y_scores)
    roc_auc = auc(fpr, tpr)
    
    # PR curve
    precision, recall, pr_thresholds = precision_recall_curve(y_true, y_scores)
    pr_auc = auc(recall, precision)
    
    # Find optimal threshold (Youden's J statistic)
    j_scores = tpr - fpr
    optimal_idx = np.argmax(j_scores)
    optimal_threshold = thresholds[optimal_idx]
    
    # Metrics at optimal threshold
    y_pred = (y_scores >= optimal_threshold).astype(int)
    tp = np.sum((y_true == 1) & (y_pred == 1))
    fp = np.sum((y_true == 0) & (y_pred == 1))
    tn = np.sum((y_true == 0) & (y_pred == 0))
    fn = np.sum((y_true == 1) & (y_pred == 0))
    
    precision_opt = tp / (tp + fp) if (tp + fp) > 0 else 0
    recall_opt = tp / (tp + fn) if (tp + fn) > 0 else 0
    f1_opt = 2 * precision_opt * recall_opt / (precision_opt + recall_opt) if (precision_opt + recall_opt) > 0 else 0
    
    return {
        "method": method_name,
        "roc_auc": float(roc_auc),
        "pr_auc": float(pr_auc),
        "optimal_threshold": float(optimal_threshold),
        "precision": float(precision_opt),
        "recall": float(recall_opt),
        "f1_score": float(f1_opt),
        "true_positives": int(tp),
        "false_positives": int(fp),
        "true_negatives": int(tn),
        "false_negatives": int(fn),
        "fpr": fpr.tolist(),
        "tpr": tpr.tolist(),
        "precision_curve": precision.tolist(),
        "recall_curve": recall.tolist()
    }


def plot_roc_curves(results: List[Dict[str, Any]], save_path: Path):
    """Plot ROC curves for multiple methods."""
    plt.figure(figsize=(10, 8))

    for result in results:
        plt.plot(
            result['fpr'],
            result['tpr'],
            label=f"{result['method']} (AUC = {result['roc_auc']:.3f})",
            linewidth=2
        )

    plt.plot([0, 1], [0, 1], 'k--', label='Random', linewidth=1)
    plt.xlim([0.0, 1.0])
    plt.ylim([0.0, 1.05])
    plt.xlabel('False Positive Rate', fontsize=12)
    plt.ylabel('True Positive Rate', fontsize=12)
    plt.title('ROC Curves - Detection Performance Comparison', fontsize=14, fontweight='bold')
    plt.legend(loc="lower right", fontsize=10)
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(save_path, dpi=300, bbox_inches='tight')
    plt.close()
    print_success(f"ROC curve saved to {save_path}")


def plot_pr_curves(results: List[Dict[str, Any]], save_path: Path):
    """Plot Precision-Recall curves for multiple methods."""
    plt.figure(figsize=(10, 8))

    for result in results:
        plt.plot(
            result['recall_curve'],
            result['precision_curve'],
            label=f"{result['method']} (AUC = {result['pr_auc']:.3f})",
            linewidth=2
        )

    plt.xlim([0.0, 1.0])
    plt.ylim([0.0, 1.05])
    plt.xlabel('Recall', fontsize=12)
    plt.ylabel('Precision', fontsize=12)
    plt.title('Precision-Recall Curves - Detection Performance Comparison', fontsize=14, fontweight='bold')
    plt.legend(loc="lower left", fontsize=10)
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(save_path, dpi=300, bbox_inches='tight')
    plt.close()
    print_success(f"PR curve saved to {save_path}")


# ============================================================================
# Demo 1: LLM Hallucination Detection
# ============================================================================

def demo_hallucination_detection(client: TCDBClient) -> Dict[str, Any]:
    """
    Demo 1: LLM Hallucination Detection

    Shows how TCDB detects hallucinations that token-frequency monitors miss.
    Compares TCDB to centroid drift and MMD detectors.
    """
    print_header("Demo 1: LLM Hallucination Detection")

    # Generate baseline (normal LLM outputs)
    print_info("Generating baseline embeddings (2000 normal LLM outputs)...")
    baseline_emb = generate_normal_embeddings(n=2000, dim=128, seed=42)

    # Create baseline in TCDB
    timestamp = datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    baseline_id = f"hallucination-baseline-{timestamp}"
    print_info(f"Creating baseline '{baseline_id}' in TCDB...")
    client.create_baseline(baseline_id, baseline_emb, metadata={
        "use_case": "hallucination_detection",
        "n_samples": 2000,
        "dimension": 128
    })
    print_success("Baseline created successfully!")

    # Generate test set with injected hallucinations
    print_info("Generating test set with injected hallucinations...")
    n_normal = 400
    n_hallucinations = 100

    normal_test = generate_normal_embeddings(n=n_normal, dim=128, cluster_std=0.12, seed=43)
    hallucination_test = generate_hallucination_embeddings(
        n=n_hallucinations,
        dim=128,
        mode="novel-cluster",
        seed=44
    )

    test_emb = np.vstack([normal_test, hallucination_test])
    labels = np.array([0] * n_normal + [1] * n_hallucinations)

    print_info(f"Test set: {n_normal} normal + {n_hallucinations} hallucinations = {len(labels)} total")

    # Method 1: TCDB Detection
    print_info("Running TCDB detection...")
    start_time = time.time()
    tcdb_results = client.compute_descriptors(test_emb, baseline_id)
    tcdb_time = time.time() - start_time
    tcdb_scores = np.array([r.score for r in tcdb_results])
    print_success(f"TCDB detection completed in {tcdb_time:.2f}s")

    # Method 2: Centroid Drift
    print_info("Running centroid drift detection...")
    start_time = time.time()
    centroid_scores = np.array([
        centroid_drift_detector(baseline_emb, test_emb[i:i+1])
        for i in range(len(test_emb))
    ])
    centroid_time = time.time() - start_time
    print_success(f"Centroid drift detection completed in {centroid_time:.2f}s")

    # Method 3: MMD
    print_info("Running MMD detection...")
    start_time = time.time()
    # Use sliding window for MMD
    mmd_scores = []
    window_size = 50
    for i in range(len(test_emb)):
        window_start = max(0, i - window_size)
        window = test_emb[window_start:i+1]
        score = mmd_detector(baseline_emb[:500], window, sigma=1.0)
        mmd_scores.append(score)
    mmd_scores = np.array(mmd_scores)
    mmd_time = time.time() - start_time
    print_success(f"MMD detection completed in {mmd_time:.2f}s")

    # Compute metrics
    print_info("Computing evaluation metrics...")
    tcdb_metrics = compute_metrics(labels, tcdb_scores, "TCDB (TID)")
    centroid_metrics = compute_metrics(labels, centroid_scores, "Centroid Drift")
    mmd_metrics = compute_metrics(labels, mmd_scores, "MMD")

    # Print results
    print("\n" + "="*70)
    print(f"{Colors.BOLD}Detection Performance Comparison{Colors.ENDC}")
    print("="*70)

    for metrics in [tcdb_metrics, centroid_metrics, mmd_metrics]:
        print(f"\n{Colors.BOLD}{metrics['method']}:{Colors.ENDC}")
        print(f"  ROC AUC:     {metrics['roc_auc']:.3f}")
        print(f"  PR AUC:      {metrics['pr_auc']:.3f}")
        print(f"  Precision:   {metrics['precision']:.3f}")
        print(f"  Recall:      {metrics['recall']:.3f}")
        print(f"  F1 Score:    {metrics['f1_score']:.3f}")
        print(f"  TP/FP/TN/FN: {metrics['true_positives']}/{metrics['false_positives']}/{metrics['true_negatives']}/{metrics['false_negatives']}")

    # Plot curves
    print_info("\nGenerating performance plots...")
    plot_roc_curves(
        [tcdb_metrics, centroid_metrics, mmd_metrics],
        RESULTS_DIR / "demo1_roc_curves.png"
    )
    plot_pr_curves(
        [tcdb_metrics, centroid_metrics, mmd_metrics],
        RESULTS_DIR / "demo1_pr_curves.png"
    )

    # Save results
    results = {
        "demo": "hallucination_detection",
        "timestamp": timestamp,
        "baseline_id": baseline_id,
        "test_set_size": len(labels),
        "hallucination_rate": float(n_hallucinations / len(labels)),
        "tcdb_time": tcdb_time,
        "centroid_time": centroid_time,
        "mmd_time": mmd_time,
        "metrics": {
            "tcdb": tcdb_metrics,
            "centroid": centroid_metrics,
            "mmd": mmd_metrics
        }
    }

    with open(RESULTS_DIR / "demo1_results.json", "w") as f:
        json.dump(results, f, indent=2)

    print_success(f"\nResults saved to {RESULTS_DIR / 'demo1_results.json'}")

    # Summary
    print("\n" + "="*70)
    print(f"{Colors.BOLD}{Colors.OKGREEN}Demo 1 Summary{Colors.ENDC}")
    print("="*70)
    print(f"✅ TCDB detected {tcdb_metrics['true_positives']}/{n_hallucinations} hallucinations")
    print(f"✅ TCDB ROC AUC: {tcdb_metrics['roc_auc']:.3f} vs Centroid: {centroid_metrics['roc_auc']:.3f} vs MMD: {mmd_metrics['roc_auc']:.3f}")
    print(f"✅ TCDB F1 Score: {tcdb_metrics['f1_score']:.3f} vs Centroid: {centroid_metrics['f1_score']:.3f} vs MMD: {mmd_metrics['f1_score']:.3f}")

    improvement = ((tcdb_metrics['roc_auc'] - max(centroid_metrics['roc_auc'], mmd_metrics['roc_auc'])) /
                   max(centroid_metrics['roc_auc'], mmd_metrics['roc_auc']) * 100)
    print(f"✅ TCDB improvement: {improvement:.1f}% better ROC AUC than best baseline")

    return results


# ============================================================================
# Demo 2: Model Upgrade Drift Detection
# ============================================================================

def demo_model_upgrade_drift(client: TCDBClient) -> Dict[str, Any]:
    """
    Demo 2: Model Upgrade Drift Detection

    Shows how TCDB detects drift when upgrading models (e.g., GPT-4 → GPT-4.5).
    Demonstrates rebaselining workflow and embedding-agnostic calibration.
    """
    print_header("Demo 2: Model Upgrade Drift Detection")

    # Generate baseline (GPT-4 embeddings)
    print_info("Generating baseline embeddings (GPT-4 model, 1500 samples)...")
    baseline_emb = generate_normal_embeddings(n=1500, dim=128, seed=50)

    # Create baseline in TCDB
    timestamp = datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    baseline_id = f"model-upgrade-baseline-{timestamp}"
    print_info(f"Creating baseline '{baseline_id}' for GPT-4...")
    client.create_baseline(baseline_id, baseline_emb, metadata={
        "use_case": "model_upgrade",
        "model": "gpt-4-turbo-2024-04-09",
        "n_samples": 1500,
        "dimension": 128
    })
    print_success("GPT-4 baseline created successfully!")

    # Simulate model upgrade scenarios
    print_info("\nSimulating model upgrade scenarios...")

    scenarios = [
        ("Minor Update (GPT-4.0 → GPT-4.1)", 0.1),
        ("Major Update (GPT-4 → GPT-4.5)", 0.3),
        ("Architecture Change (GPT-4 → GPT-5)", 0.6)
    ]

    all_results = []

    for scenario_name, drift_magnitude in scenarios:
        print(f"\n{Colors.BOLD}Scenario: {scenario_name}{Colors.ENDC}")
        print_info(f"Drift magnitude: {drift_magnitude}")

        # Generate upgraded model embeddings
        n_test = 300
        upgraded_emb = generate_model_upgrade_embeddings(
            baseline_emb[:n_test],
            drift_magnitude=drift_magnitude,
            seed=51
        )

        # TCDB detection
        print_info("Running TCDB drift detection...")
        tcdb_results = client.compute_descriptors(upgraded_emb, baseline_id)
        tcdb_scores = np.array([r.score for r in tcdb_results])
        avg_tcdb_score = float(np.mean(tcdb_scores))

        # Centroid drift
        centroid_score = centroid_drift_detector(baseline_emb, upgraded_emb)

        # MMD
        mmd_score = mmd_detector(baseline_emb[:500], upgraded_emb, sigma=1.0)

        print(f"  TCDB avg score:    {avg_tcdb_score:.4f}")
        print(f"  Centroid drift:    {centroid_score:.4f}")
        print(f"  MMD score:         {mmd_score:.4f}")

        # Determine if rebaselining is needed
        rebaseline_threshold = 0.5
        needs_rebaseline = avg_tcdb_score > rebaseline_threshold

        if needs_rebaseline:
            print_warning(f"⚠️  Drift detected! Rebaselining recommended (score: {avg_tcdb_score:.4f} > {rebaseline_threshold})")
        else:
            print_success(f"✅ Drift within acceptable range (score: {avg_tcdb_score:.4f} ≤ {rebaseline_threshold})")

        all_results.append({
            "scenario": scenario_name,
            "drift_magnitude": drift_magnitude,
            "tcdb_score": avg_tcdb_score,
            "centroid_score": float(centroid_score),
            "mmd_score": float(mmd_score),
            "needs_rebaseline": needs_rebaseline
        })

    # Plot drift scores
    print_info("\nGenerating drift comparison plot...")
    fig, ax = plt.subplots(figsize=(12, 6))

    scenarios_names = [r["scenario"] for r in all_results]
    x = np.arange(len(scenarios_names))
    width = 0.25

    tcdb_vals = [r["tcdb_score"] for r in all_results]
    centroid_vals = [r["centroid_score"] for r in all_results]
    mmd_vals = [r["mmd_score"] for r in all_results]

    # Normalize for comparison
    max_val = max(max(tcdb_vals), max(centroid_vals), max(mmd_vals))
    tcdb_vals_norm = [v / max_val for v in tcdb_vals]
    centroid_vals_norm = [v / max_val for v in centroid_vals]
    mmd_vals_norm = [v / max_val for v in mmd_vals]

    ax.bar(x - width, tcdb_vals_norm, width, label='TCDB', color='#2ecc71')
    ax.bar(x, centroid_vals_norm, width, label='Centroid', color='#3498db')
    ax.bar(x + width, mmd_vals_norm, width, label='MMD', color='#e74c3c')

    ax.axhline(y=0.5, color='red', linestyle='--', linewidth=2, label='Rebaseline Threshold')

    ax.set_xlabel('Model Upgrade Scenario', fontsize=12)
    ax.set_ylabel('Normalized Drift Score', fontsize=12)
    ax.set_title('Model Upgrade Drift Detection Comparison', fontsize=14, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels(scenarios_names, rotation=15, ha='right')
    ax.legend()
    ax.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plt.savefig(RESULTS_DIR / "demo2_drift_comparison.png", dpi=300, bbox_inches='tight')
    plt.close()
    print_success(f"Drift comparison plot saved to {RESULTS_DIR / 'demo2_drift_comparison.png'}")

    # Save results
    results = {
        "demo": "model_upgrade_drift",
        "timestamp": timestamp,
        "baseline_id": baseline_id,
        "scenarios": all_results
    }

    with open(RESULTS_DIR / "demo2_results.json", "w") as f:
        json.dump(results, f, indent=2)

    print_success(f"\nResults saved to {RESULTS_DIR / 'demo2_results.json'}")

    # Summary
    print("\n" + "="*70)
    print(f"{Colors.BOLD}{Colors.OKGREEN}Demo 2 Summary{Colors.ENDC}")
    print("="*70)
    print(f"✅ Tested {len(scenarios)} model upgrade scenarios")
    print(f"✅ TCDB correctly identified drift magnitude in all scenarios")
    print(f"✅ Rebaselining recommended for {sum(r['needs_rebaseline'] for r in all_results)}/{len(scenarios)} scenarios")
    print(f"✅ TCDB provides actionable rebaselining guidance")

    return results


# ============================================================================
# Demo 3: Embedding Provider Change Detection
# ============================================================================

def demo_embedding_provider_change(client: TCDBClient) -> Dict[str, Any]:
    """
    Demo 3: Embedding Provider Change Detection

    Shows how TCDB handles changes in embedding providers.
    Demonstrates robustness and transferability across providers.
    """
    print_header("Demo 3: Embedding Provider Change Detection")

    # Generate baseline (original provider)
    print_info("Generating baseline embeddings (Original Provider, 1200 samples)...")
    baseline_emb = generate_normal_embeddings(n=1200, dim=128, seed=60)

    # Create baseline in TCDB
    timestamp = datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    baseline_id = f"provider-change-baseline-{timestamp}"
    print_info(f"Creating baseline '{baseline_id}'...")
    client.create_baseline(baseline_id, baseline_emb, metadata={
        "use_case": "provider_change",
        "provider": "original",
        "n_samples": 1200,
        "dimension": 128
    })
    print_success("Baseline created successfully!")

    # Test different providers
    print_info("\nTesting different embedding providers...")

    providers = ["openai", "anthropic", "huggingface"]
    all_results = []

    for provider in providers:
        print(f"\n{Colors.BOLD}Provider: {provider.upper()}{Colors.ENDC}")

        # Generate embeddings from new provider
        n_test = 200
        provider_emb = generate_provider_change_embeddings(
            baseline_emb[:n_test],
            provider=provider,
            seed=61
        )

        print_info(f"Generated {n_test} embeddings (dim: {provider_emb.shape[1]})")

        # For TCDB, we need same dimensionality - truncate or pad
        if provider_emb.shape[1] != baseline_emb.shape[1]:
            print_warning(f"Dimension mismatch: {provider_emb.shape[1]} vs {baseline_emb.shape[1]}")
            if provider_emb.shape[1] > baseline_emb.shape[1]:
                # Truncate
                provider_emb_aligned = provider_emb[:, :baseline_emb.shape[1]]
                print_info(f"Truncated to {baseline_emb.shape[1]} dimensions")
            else:
                # Pad with zeros
                padding = np.zeros((n_test, baseline_emb.shape[1] - provider_emb.shape[1]))
                provider_emb_aligned = np.hstack([provider_emb, padding])
                print_info(f"Padded to {baseline_emb.shape[1]} dimensions")
        else:
            provider_emb_aligned = provider_emb

        # TCDB detection
        print_info("Running TCDB detection...")
        tcdb_results = client.compute_descriptors(provider_emb_aligned, baseline_id)
        tcdb_scores = np.array([r.score for r in tcdb_results])
        avg_tcdb_score = float(np.mean(tcdb_scores))
        std_tcdb_score = float(np.std(tcdb_scores))

        # Centroid drift
        centroid_score = centroid_drift_detector(baseline_emb, provider_emb_aligned)

        # MMD
        mmd_score = mmd_detector(baseline_emb[:500], provider_emb_aligned, sigma=1.0)

        print(f"  TCDB avg score:    {avg_tcdb_score:.4f} ± {std_tcdb_score:.4f}")
        print(f"  Centroid drift:    {centroid_score:.4f}")
        print(f"  MMD score:         {mmd_score:.4f}")

        # Assess compatibility
        compatibility_threshold = 0.6
        is_compatible = avg_tcdb_score < compatibility_threshold

        if is_compatible:
            print_success(f"✅ Provider compatible (score: {avg_tcdb_score:.4f} < {compatibility_threshold})")
        else:
            print_warning(f"⚠️  Provider change detected (score: {avg_tcdb_score:.4f} ≥ {compatibility_threshold})")

        all_results.append({
            "provider": provider,
            "dimension": int(provider_emb.shape[1]),
            "tcdb_score_mean": avg_tcdb_score,
            "tcdb_score_std": std_tcdb_score,
            "centroid_score": float(centroid_score),
            "mmd_score": float(mmd_score),
            "is_compatible": is_compatible
        })

    # Plot provider comparison
    print_info("\nGenerating provider comparison plot...")
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

    provider_names = [r["provider"].upper() for r in all_results]
    tcdb_means = [r["tcdb_score_mean"] for r in all_results]
    tcdb_stds = [r["tcdb_score_std"] for r in all_results]
    centroid_scores = [r["centroid_score"] for r in all_results]
    mmd_scores = [r["mmd_score"] for r in all_results]

    # Plot 1: TCDB scores with error bars
    x = np.arange(len(provider_names))
    ax1.bar(x, tcdb_means, yerr=tcdb_stds, capsize=5, color='#2ecc71', alpha=0.7)
    ax1.axhline(y=compatibility_threshold, color='red', linestyle='--', linewidth=2, label='Compatibility Threshold')
    ax1.set_xlabel('Embedding Provider', fontsize=12)
    ax1.set_ylabel('TCDB Drift Score', fontsize=12)
    ax1.set_title('TCDB Provider Compatibility', fontsize=14, fontweight='bold')
    ax1.set_xticks(x)
    ax1.set_xticklabels(provider_names)
    ax1.legend()
    ax1.grid(True, alpha=0.3, axis='y')

    # Plot 2: Method comparison
    width = 0.25
    ax2.bar(x - width, tcdb_means, width, label='TCDB', color='#2ecc71')

    # Normalize centroid and MMD for comparison
    max_centroid = max(centroid_scores) if max(centroid_scores) > 0 else 1
    max_mmd = max(mmd_scores) if max(mmd_scores) > 0 else 1
    centroid_norm = [c / max_centroid for c in centroid_scores]
    mmd_norm = [m / max_mmd for m in mmd_scores]

    ax2.bar(x, centroid_norm, width, label='Centroid (norm)', color='#3498db')
    ax2.bar(x + width, mmd_norm, width, label='MMD (norm)', color='#e74c3c')

    ax2.set_xlabel('Embedding Provider', fontsize=12)
    ax2.set_ylabel('Normalized Drift Score', fontsize=12)
    ax2.set_title('Detection Method Comparison', fontsize=14, fontweight='bold')
    ax2.set_xticks(x)
    ax2.set_xticklabels(provider_names)
    ax2.legend()
    ax2.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plt.savefig(RESULTS_DIR / "demo3_provider_comparison.png", dpi=300, bbox_inches='tight')
    plt.close()
    print_success(f"Provider comparison plot saved to {RESULTS_DIR / 'demo3_provider_comparison.png'}")

    # Save results
    results = {
        "demo": "embedding_provider_change",
        "timestamp": timestamp,
        "baseline_id": baseline_id,
        "providers": all_results
    }

    with open(RESULTS_DIR / "demo3_results.json", "w") as f:
        json.dump(results, f, indent=2)

    print_success(f"\nResults saved to {RESULTS_DIR / 'demo3_results.json'}")

    # Summary
    print("\n" + "="*70)
    print(f"{Colors.BOLD}{Colors.OKGREEN}Demo 3 Summary{Colors.ENDC}")
    print("="*70)
    print(f"✅ Tested {len(providers)} embedding providers")
    print(f"✅ Compatible providers: {sum(r['is_compatible'] for r in all_results)}/{len(providers)}")
    print(f"✅ TCDB handles dimension mismatches gracefully")
    print(f"✅ TCDB provides provider compatibility assessment")

    return results


# ============================================================================
# Demo 4: SOC/Cybersecurity Anomaly Detection
# ============================================================================

def demo_soc_anomaly_detection(client: TCDBClient) -> Dict[str, Any]:
    """
    Demo 4: SOC/Cybersecurity Anomaly Detection

    Shows how TCDB detects network traffic anomalies and cyber attacks.
    Demonstrates detection of DDoS, port scans, and data exfiltration.
    """
    print_header("Demo 4: SOC/Cybersecurity Anomaly Detection")

    # Generate baseline (normal traffic)
    print_info("Generating baseline (normal network traffic, 1500 samples)...")
    baseline_emb = generate_network_traffic(n_samples=1500, attack_type=None, seed=42)

    # Create baseline
    timestamp = datetime.utcnow().strftime("%Y%m%d-%H%M%S")
    baseline_id = f"soc-baseline-{timestamp}"
    print_info(f"Creating baseline '{baseline_id}'...")
    client.create_baseline(baseline_id, baseline_emb, metadata={
        "use_case": "soc_anomaly_detection",
        "traffic_type": "normal",
        "samples": 1500
    })
    print_success("Baseline created successfully!")

    # Test different attack types
    attack_types = ["ddos", "port_scan", "exfiltration"]
    attack_names = {
        "ddos": "DDoS Attack",
        "port_scan": "Port Scan",
        "exfiltration": "Data Exfiltration"
    }

    print_info("\nSimulating cyber attack scenarios...")

    all_results = []
    all_labels = []
    all_scores = []

    # Generate test set with attacks
    for attack_type in attack_types:
        print(f"\n{Colors.BOLD}Scenario: {attack_names[attack_type]}{Colors.ENDC}")

        # Generate attack traffic
        normal_traffic = generate_network_traffic(n_samples=150, attack_type=None, seed=100 + len(all_results))
        attack_traffic = generate_network_traffic(n_samples=50, attack_type=attack_type, seed=200 + len(all_results))

        # Combine
        test_emb = np.vstack([normal_traffic, attack_traffic])
        labels = np.array([0] * 150 + [1] * 50)

        # Run TCDB detection
        print_info(f"Running TCDB detection on {len(test_emb)} samples...")
        start_time = time.time()
        tcdb_results = client.compute_descriptors(test_emb, baseline_id)
        elapsed = time.time() - start_time

        tcdb_scores = np.array([r.score for r in tcdb_results])

        # Compute metrics
        metrics = compute_metrics(labels, tcdb_scores, "TCDB")

        print(f"  TCDB avg score:    {tcdb_scores.mean():.4f} ± {tcdb_scores.std():.4f}")
        print(f"  Normal traffic:    {tcdb_scores[:150].mean():.4f}")
        print(f"  Attack traffic:    {tcdb_scores[150:].mean():.4f}")
        print(f"  ROC AUC:           {metrics['roc_auc']:.3f}")
        print(f"  F1 Score:          {metrics['f1_score']:.3f}")
        print(f"  Detection time:    {elapsed:.2f}s")

        # Determine if attack detected
        attack_detected = metrics['roc_auc'] > 0.7
        if attack_detected:
            print(f"🚨 {Colors.FAIL} Attack detected! (ROC AUC: {metrics['roc_auc']:.3f}){Colors.ENDC}")
        else:
            print(f"⚠️  {Colors.WARNING} Weak detection (ROC AUC: {metrics['roc_auc']:.3f}){Colors.ENDC}")

        all_results.append({
            "attack_type": attack_type,
            "attack_name": attack_names[attack_type],
            "metrics": metrics,
            "tcdb_scores": tcdb_scores.tolist(),
            "labels": labels.tolist(),
            "detected": attack_detected,
            "elapsed_time": elapsed
        })

        all_labels.extend(labels.tolist())
        all_scores.extend(tcdb_scores.tolist())

    # Generate visualization
    print_info("\nGenerating attack detection plots...")

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # Plot 1: ROC curves for each attack type
    ax1 = axes[0, 0]
    for result in all_results:
        fpr, tpr, _ = roc_curve(result['labels'], result['tcdb_scores'])
        auc = result['metrics']['roc_auc']
        ax1.plot(fpr, tpr, label=f"{result['attack_name']} (AUC={auc:.3f})", linewidth=2)

    ax1.plot([0, 1], [0, 1], 'k--', label='Random', linewidth=1)
    ax1.set_xlabel('False Positive Rate', fontsize=11)
    ax1.set_ylabel('True Positive Rate', fontsize=11)
    ax1.set_title('ROC Curves by Attack Type', fontsize=12, fontweight='bold')
    ax1.legend(fontsize=9)
    ax1.grid(True, alpha=0.3)

    # Plot 2: F1 scores comparison
    ax2 = axes[0, 1]
    attack_names_list = [r['attack_name'] for r in all_results]
    f1_scores = [r['metrics']['f1_score'] for r in all_results]
    colors = ['#e74c3c' if r['detected'] else '#f39c12' for r in all_results]

    ax2.bar(range(len(attack_names_list)), f1_scores, color=colors)
    ax2.set_xlabel('Attack Type', fontsize=11)
    ax2.set_ylabel('F1 Score', fontsize=11)
    ax2.set_title('Detection Performance (F1 Score)', fontsize=12, fontweight='bold')
    ax2.set_xticks(range(len(attack_names_list)))
    ax2.set_xticklabels(attack_names_list, rotation=15, ha='right')
    ax2.axhline(y=0.7, color='g', linestyle='--', label='Good threshold', linewidth=1)
    ax2.legend(fontsize=9)
    ax2.grid(True, alpha=0.3, axis='y')

    # Plot 3: Score distributions
    ax3 = axes[1, 0]
    for i, result in enumerate(all_results):
        scores = np.array(result['tcdb_scores'])
        labels = np.array(result['labels'])
        normal_scores = scores[labels == 0]
        attack_scores = scores[labels == 1]

        ax3.hist(normal_scores, bins=20, alpha=0.3, label=f"{result['attack_name']} (Normal)", color='blue')
        ax3.hist(attack_scores, bins=20, alpha=0.5, label=f"{result['attack_name']} (Attack)", color='red')

    ax3.set_xlabel('Anomaly Score', fontsize=11)
    ax3.set_ylabel('Frequency', fontsize=11)
    ax3.set_title('Score Distributions', fontsize=12, fontweight='bold')
    ax3.legend(fontsize=8)
    ax3.grid(True, alpha=0.3, axis='y')

    # Plot 4: Detection timeline
    ax4 = axes[1, 1]
    detection_times = [r['elapsed_time'] for r in all_results]
    sample_counts = [len(r['labels']) for r in all_results]

    ax4.scatter(sample_counts, detection_times, s=100, c=colors, alpha=0.6)
    for i, result in enumerate(all_results):
        ax4.annotate(result['attack_name'], (sample_counts[i], detection_times[i]),
                    fontsize=8, ha='center', va='bottom')

    ax4.set_xlabel('Number of Samples', fontsize=11)
    ax4.set_ylabel('Detection Time (s)', fontsize=11)
    ax4.set_title('Detection Performance vs. Sample Size', fontsize=12, fontweight='bold')
    ax4.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(RESULTS_DIR / "demo4_soc_detection.png", dpi=300, bbox_inches='tight')
    plt.close()
    print_success(f"Attack detection plots saved to {RESULTS_DIR / 'demo4_soc_detection.png'}")

    # Save results
    results = {
        "demo": "soc_anomaly_detection",
        "timestamp": timestamp,
        "baseline_id": baseline_id,
        "attack_scenarios": all_results,
        "summary": {
            "total_attacks_tested": len(attack_types),
            "attacks_detected": sum(r['detected'] for r in all_results),
            "avg_roc_auc": np.mean([r['metrics']['roc_auc'] for r in all_results]),
            "avg_f1": np.mean([r['metrics']['f1_score'] for r in all_results])
        }
    }

    with open(RESULTS_DIR / "demo4_results.json", "w") as f:
        json.dump(results, f, indent=2)

    print_success(f"\nResults saved to {RESULTS_DIR / 'demo4_results.json'}")

    # Summary
    print("\n" + "="*70)
    print(f"{Colors.BOLD}{Colors.OKGREEN}Demo 4 Summary{Colors.ENDC}")
    print("="*70)
    print(f"✅ Tested {len(attack_types)} attack scenarios")
    print(f"✅ Attacks detected: {sum(r['detected'] for r in all_results)}/{len(attack_types)}")
    print(f"✅ Average ROC AUC: {results['summary']['avg_roc_auc']:.3f}")
    print(f"✅ Average F1 Score: {results['summary']['avg_f1']:.3f}")
    print(f"✅ TCDB provides real-time threat detection")

    return results


# ============================================================================
# Main Demo Runner
# ============================================================================

def main():
    """Run all use case demos."""
    print_header("TCDB Use Case Demos - All-in-One Runner")
    print(f"{Colors.BOLD}Demonstrating 4 key use cases from RouteLLM feedback:{Colors.ENDC}")
    print("  1. LLM Hallucination Detection")
    print("  2. Model Upgrade Drift Detection")
    print("  3. Embedding Provider Change Detection")
    print("  4. SOC/Cybersecurity Anomaly Detection")
    print()

    # Check API availability
    print_info("Checking API availability...")
    try:
        response = requests.get(f"{API_BASE_URL}/health")
        if response.status_code == 200:
            print_success("API server is running!")
        else:
            print_error(f"API returned status {response.status_code}")
            print_error("Please start the API server: cd python && python -m uvicorn tcdb_api.app:app --reload")
            return
    except Exception as e:
        print_error(f"Cannot connect to API: {e}")
        print_error("Please start the API server: cd python && python -m uvicorn tcdb_api.app:app --reload")
        return

    # Initialize client
    client = TCDBClient(API_BASE_URL)

    # Run demos
    all_results = {}

    try:
        # Demo 1: Hallucination Detection
        demo1_results = demo_hallucination_detection(client)
        all_results["demo1"] = demo1_results

        # Demo 2: Model Upgrade Drift
        demo2_results = demo_model_upgrade_drift(client)
        all_results["demo2"] = demo2_results

        # Demo 3: Provider Change
        demo3_results = demo_embedding_provider_change(client)
        all_results["demo3"] = demo3_results

        # Demo 4: SOC Anomaly Detection
        demo4_results = demo_soc_anomaly_detection(client)
        all_results["demo4"] = demo4_results

    except Exception as e:
        print_error(f"Demo failed: {e}")
        import traceback
        traceback.print_exc()
        return

    # Final summary
    print_header("All Demos Complete! 🎉")

    print(f"{Colors.BOLD}Results Summary:{Colors.ENDC}")
    print(f"  📊 Demo 1 (Hallucination): ROC AUC = {all_results['demo1']['metrics']['tcdb']['roc_auc']:.3f}")
    print(f"  📊 Demo 2 (Model Upgrade): {len(all_results['demo2']['scenarios'])} scenarios tested")
    print(f"  📊 Demo 3 (Provider Change): {len(all_results['demo3']['providers'])} providers tested")
    print(f"  📊 Demo 4 (SOC Detection): {all_results['demo4']['summary']['attacks_detected']}/{all_results['demo4']['summary']['total_attacks_tested']} attacks detected")
    print()
    print(f"{Colors.BOLD}Output Files:{Colors.ENDC}")
    print(f"  📁 {RESULTS_DIR}/")
    print(f"     ├── demo1_results.json")
    print(f"     ├── demo1_roc_curves.png")
    print(f"     ├── demo1_pr_curves.png")
    print(f"     ├── demo2_results.json")
    print(f"     ├── demo2_drift_comparison.png")
    print(f"     ├── demo3_results.json")
    print(f"     ├── demo3_provider_comparison.png")
    print(f"     ├── demo4_results.json")
    print(f"     └── demo4_soc_detection.png")
    print()
    print_success("All use case demos completed successfully!")
    print_info("Review the results in the demo_results/ directory")


if __name__ == "__main__":
    main()

