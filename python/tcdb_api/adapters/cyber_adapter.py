"""
Cybersecurity adapter for TCDB descriptors.

Analyzes network flows and logs to detect:
- Network topology changes (DGD)
- Anomalous traffic patterns (GSER)
- Behavioral drift (KME-Δ)
"""

from __future__ import annotations

from typing import Dict, Iterable, List, Optional, Tuple

import numpy as np
import scipy.sparse as sp

from .common import DescriptorClient


class CyberAdapter:
    """
    Build windowed graphs from logs/flows and call descriptors.
    
    Minimal expected records:
    - edges: iterable of (src_id, dst_id, weight) within time window
    - node_signal (optional): per-node scalar like failed-login count
    
    Node ids should be 0..N-1; map your hostnames/users accordingly.
    
    Example:
        >>> adapter = CyberAdapter(DescriptorClient(), n_nodes=100)
        >>> edges = [(0, 1, 1.0), (1, 2, 2.0), ...]  # Network flows
        >>> signal = np.array([...])  # Failed login counts per node
        >>> results = adapter.compute_descriptors(edges, node_signal=signal)
        >>> print(results["dgd"]["DGD_F"])  # Network health score
    """
    
    def __init__(self, client: DescriptorClient, n_nodes: int) -> None:
        """
        Initialize cyber adapter.
        
        Args:
            client: DescriptorClient instance
            n_nodes: Number of nodes in the network
        """
        self.client = client
        self.n_nodes = n_nodes
    
    def _edges_to_csr(
        self,
        edges: Iterable[Tuple[int, int, float]]
    ) -> sp.csr_matrix:
        """
        Convert edge list to sparse adjacency matrix.
        
        Args:
            edges: Iterable of (src, dst, weight) tuples
            
        Returns:
            Symmetric sparse adjacency matrix
        """
        edge_list = list(edges)
        
        if not edge_list:
            # Empty graph
            return sp.csr_matrix((self.n_nodes, self.n_nodes))
        
        rows, cols, data = zip(*edge_list)
        
        # Create adjacency matrix
        A = sp.csr_matrix(
            (data, (rows, cols)),
            shape=(self.n_nodes, self.n_nodes)
        )
        
        # Symmetrize (take maximum for directed edges)
        A = A.maximum(A.T)
        
        return A
    
    def compute_descriptors(
        self,
        edges: Iterable[Tuple[int, int, float]],
        node_signal: Optional[np.ndarray] = None,
        baseline_embeddings: Optional[np.ndarray] = None,
        window_embeddings: Optional[np.ndarray] = None,
        dgd_params: Optional[dict] = None,
        gser_params: Optional[dict] = None,
        kme_params: Optional[dict] = None,
    ) -> Dict[str, Dict[str, float]]:
        """
        Compute descriptors for network security analysis.
        
        Args:
            edges: Network edges as (src, dst, weight) tuples
            node_signal: Optional per-node signal (e.g., failed logins)
            baseline_embeddings: Optional baseline feature embeddings
            window_embeddings: Optional current window feature embeddings
            dgd_params: Parameters for DGD
            gser_params: Parameters for GSER
            kme_params: Parameters for KME-Δ
            
        Returns:
            Dictionary mapping descriptor names to their results
        """
        out: Dict[str, Dict[str, float]] = {}
        
        # Build graph from edges
        A = self._edges_to_csr(edges)
        self.client.validate_graph(A, min_nodes=2)
        
        graph_payload = self.client.csr_to_coo_payload(A)
        
        # 1) DGD: Geometry health of the network
        out["dgd"] = self.client.compute(
            "dgd",
            params=dgd_params or {"n_time_samples": 16},
            **graph_payload
        )
        
        # 2) GSER: Multi-scale bursts and anomalies
        # Use provided node_signal or uniform
        if node_signal is None:
            node_signal = np.ones(self.n_nodes, dtype=float)
        
        if len(node_signal) != self.n_nodes:
            raise ValueError(
                f"Signal length {len(node_signal)} doesn't match "
                f"n_nodes {self.n_nodes}"
            )
        
        out["gser"] = self.client.compute(
            "gser",
            params=gser_params or {"n_scales": 3, "k_neighbors": 5},
            **graph_payload,
            signal=node_signal.tolist()
        )
        
        # 3) Optional drift on feature embeddings
        # (e.g., aggregated flow features per time window)
        if window_embeddings is not None:
            self.client.validate_point_cloud(window_embeddings, min_points=2)
            
            payload = {"X": window_embeddings.tolist()}
            
            if baseline_embeddings is not None:
                self.client.validate_point_cloud(baseline_embeddings, min_points=2)
                payload["X_ref"] = baseline_embeddings.tolist()
            
            out["kme_delta"] = self.client.compute(
                "kme_delta",
                params=kme_params or {"sigmas": [0.5, 1.0, 2.0]},
                **payload
            )
        
        return out
    
    def detect_anomaly(
        self,
        edges: Iterable[Tuple[int, int, float]],
        node_signal: Optional[np.ndarray] = None,
        gser_threshold: float = 0.8,
        dgd_threshold: float = 2.0
    ) -> Dict[str, any]:
        """
        Detect network anomalies using descriptor thresholds.
        
        Args:
            edges: Network edges
            node_signal: Optional per-node signal
            gser_threshold: GSER anomaly threshold
            dgd_threshold: DGD anomaly threshold
            
        Returns:
            Dictionary with anomaly detection results
        """
        results = self.compute_descriptors(edges, node_signal=node_signal)
        
        gser_score = results["gser"].get("GSER_F", results["gser"].get("F_GSER", 0.0))
        dgd_score = results["dgd"]["DGD_F"]
        
        gser_anomaly = gser_score > gser_threshold
        dgd_anomaly = dgd_score > dgd_threshold
        
        return {
            "anomaly_detected": gser_anomaly or dgd_anomaly,
            "gser_anomaly": gser_anomaly,
            "dgd_anomaly": dgd_anomaly,
            "gser_score": gser_score,
            "dgd_score": dgd_score,
            "thresholds": {
                "gser": gser_threshold,
                "dgd": dgd_threshold
            },
            "full_results": results
        }
    
    def analyze_time_window(
        self,
        edges: Iterable[Tuple[int, int, float]],
        node_signal: Optional[np.ndarray] = None,
        window_id: Optional[str] = None
    ) -> Dict[str, any]:
        """
        Analyze a single time window of network activity.
        
        Args:
            edges: Network edges in this window
            node_signal: Optional per-node signal
            window_id: Optional identifier for this window
            
        Returns:
            Dictionary with analysis results
        """
        results = self.compute_descriptors(edges, node_signal=node_signal)
        
        return {
            "window_id": window_id,
            "n_edges": len(list(edges)),
            "descriptors": results,
            "summary": {
                "network_health": results["dgd"]["DGD_F"],
                "burst_score": results["gser"].get("GSER_F", results["gser"].get("F_GSER", 0.0))
            }
        }


# Demo with toy ring and bursty node signal
if __name__ == "__main__":
    print("Cyber Adapter Demo")
    print("=" * 60)
    
    rng = np.random.default_rng(0)
    N = 64
    
    print(f"\nGenerating synthetic network:")
    print(f"  Number of nodes: {N}")
    
    # Create ring topology
    edges = [(i, (i + 1) % N, 1.0) for i in range(N)]
    print(f"  Number of edges: {len(edges)}")
    
    # Add some random edges (noise)
    for _ in range(10):
        src = rng.integers(0, N)
        dst = rng.integers(0, N)
        if src != dst:
            edges.append((src, dst, rng.random()))
    
    # Create bursty signal (simulating failed logins)
    signal = np.ones(N)
    signal[5:8] = 10.0  # Burst at nodes 5-7
    signal[20:22] = 5.0  # Smaller burst at nodes 20-21
    
    print(f"  Signal bursts at nodes: 5-7 (10.0), 20-21 (5.0)")
    
    # Create adapter
    client = DescriptorClient()
    adapter = CyberAdapter(client, n_nodes=N)
    
    print("\nComputing descriptors...")
    try:
        results = adapter.compute_descriptors(edges, node_signal=signal)
        
        print("\n✅ Results:")
        for desc_name, desc_results in results.items():
            print(f"\n{desc_name.upper()}:")
            for key, value in desc_results.items():
                print(f"  {key}: {value:.4f}")
        
        # Test anomaly detection
        print("\n" + "=" * 60)
        print("Anomaly Detection Test:")
        anomaly_result = adapter.detect_anomaly(
            edges,
            node_signal=signal,
            gser_threshold=0.8,
            dgd_threshold=2.0
        )
        print(f"  Anomaly detected: {anomaly_result['anomaly_detected']}")
        print(f"  GSER anomaly: {anomaly_result['gser_anomaly']}")
        print(f"  DGD anomaly: {anomaly_result['dgd_anomaly']}")
        print(f"  GSER score: {anomaly_result['gser_score']:.4f}")
        print(f"  DGD score: {anomaly_result['dgd_score']:.4f}")
        
    except Exception as e:
        print(f"\n❌ Error: {e}")
        print("\nMake sure the API is running:")
        print("  python run_api.py")

