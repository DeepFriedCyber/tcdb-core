"""
LLM adapter for TCDB descriptors.

Analyzes transformer internals (embeddings, attention) to detect:
- Semantic drift (KME-Δ)
- Topological structure of token space (TID)
- Attention graph geometry (DGD)
- Multi-scale attention patterns (GSER)
"""

from __future__ import annotations

from typing import Dict, Optional

import numpy as np
import scipy.sparse as sp

from .common import DescriptorClient


class LLMAdapter:
    """
    Turn LLM internals (embeddings/attention) into descriptor calls.
    
    Expected inputs per request:
    - token_embeddings: (T, D) float array for a turn (e.g., last hidden states)
    - attention: (H, T, T) OR (T, T) array averaged across heads
    
    Example:
        >>> adapter = LLMAdapter(DescriptorClient())
        >>> embeddings = model.get_hidden_states(tokens)  # (seq_len, hidden_dim)
        >>> attention = model.get_attention_weights(tokens)  # (n_heads, seq_len, seq_len)
        >>> results = adapter.compute_descriptors(embeddings, attention=attention)
        >>> print(results["kme_delta"]["KME_delta_F"])  # Drift score
    """
    
    def __init__(self, client: DescriptorClient) -> None:
        """
        Initialize LLM adapter.
        
        Args:
            client: DescriptorClient instance
        """
        self.client = client
    
    def _attention_to_graph(
        self,
        attn: np.ndarray,
        tau: float = 0.0
    ) -> sp.csr_matrix:
        """
        Convert attention matrix to sparse graph.
        
        Args:
            attn: Attention weights (H, T, T) or (T, T)
            tau: Threshold for edge creation (default: 0.0 = keep all)
            
        Returns:
            Sparse symmetric adjacency matrix
        """
        # Average over heads if multi-head
        if attn.ndim == 3:
            attn = attn.mean(axis=0)
        
        # Threshold and symmetrize
        M = np.where(attn >= tau, attn, 0.0)
        M = 0.5 * (M + M.T)
        
        # Convert to sparse
        rows, cols = np.nonzero(M)
        data = M[rows, cols]
        
        return sp.csr_matrix((data, (rows, cols)), shape=attn.shape)
    
    def compute_descriptors(
        self,
        token_embeddings: np.ndarray,
        attention: Optional[np.ndarray] = None,
        baseline_embeddings: Optional[np.ndarray] = None,
        tau: float = 0.0,
        kme_params: Optional[dict] = None,
        tid_params: Optional[dict] = None,
        dgd_params: Optional[dict] = None,
        gser_params: Optional[dict] = None,
    ) -> Dict[str, Dict[str, float]]:
        """
        Compute all relevant descriptors for LLM analysis.
        
        Args:
            token_embeddings: Token embeddings (T, D)
            attention: Optional attention weights (H, T, T) or (T, T)
            baseline_embeddings: Optional baseline embeddings for drift detection
            tau: Attention threshold for graph construction
            kme_params: Parameters for KME-Δ
            tid_params: Parameters for TID
            dgd_params: Parameters for DGD
            gser_params: Parameters for GSER
            
        Returns:
            Dictionary mapping descriptor names to their results
        """
        # Validate inputs
        self.client.validate_point_cloud(token_embeddings, min_points=2)
        
        if baseline_embeddings is not None:
            self.client.validate_point_cloud(baseline_embeddings, min_points=2)
            if baseline_embeddings.shape[1] != token_embeddings.shape[1]:
                raise ValueError(
                    f"Baseline dimension {baseline_embeddings.shape[1]} "
                    f"doesn't match embeddings dimension {token_embeddings.shape[1]}"
                )
        
        out: Dict[str, Dict[str, float]] = {}
        
        # 1) KME-Δ: Semantic drift vs baseline
        payload = {"X": token_embeddings.tolist()}
        if baseline_embeddings is not None:
            payload["X_ref"] = baseline_embeddings.tolist()
        
        out["kme_delta"] = self.client.compute(
            "kme_delta",
            params=kme_params or {"sigmas": [0.5, 1.0, 2.0]},
            **payload
        )
        
        # 2) TID: Topology of embedding cloud
        out["tid"] = self.client.compute(
            "tid",
            params=tid_params or {"max_dimension": 1},
            X=token_embeddings.tolist()
        )
        
        # 3) Attention-based descriptors (if attention provided)
        if attention is not None:
            A = self._attention_to_graph(attention, tau=tau)
            self.client.validate_graph(A, min_nodes=2)
            
            graph_payload = self.client.csr_to_coo_payload(A)
            
            # DGD: Diffusion geometry on attention graph
            out["dgd"] = self.client.compute(
                "dgd",
                params=dgd_params or {"n_time_samples": 16},
                **graph_payload
            )
            
            # GSER: Multi-scale attention patterns
            # Use uniform signal as placeholder (could use token probabilities)
            signal = np.ones(A.shape[0], dtype=float)
            
            out["gser"] = self.client.compute(
                "gser",
                params=gser_params or {"n_scales": 3, "k_neighbors": 5},
                **graph_payload,
                signal=signal.tolist()
            )
        
        return out
    
    def detect_drift(
        self,
        current_embeddings: np.ndarray,
        baseline_embeddings: np.ndarray,
        threshold: float = 0.5
    ) -> Dict[str, any]:
        """
        Detect semantic drift between current and baseline embeddings.
        
        Args:
            current_embeddings: Current token embeddings (T, D)
            baseline_embeddings: Baseline token embeddings (T', D)
            threshold: Drift threshold (default: 0.5)
            
        Returns:
            Dictionary with drift detection results
        """
        result = self.compute_descriptors(
            current_embeddings,
            baseline_embeddings=baseline_embeddings
        )
        
        drift_score = result["kme_delta"]["KME_delta_F"]
        
        return {
            "drift_detected": drift_score > threshold,
            "drift_score": drift_score,
            "threshold": threshold,
            "full_results": result
        }
    
    def analyze_attention_structure(
        self,
        attention: np.ndarray,
        tau: float = 0.1
    ) -> Dict[str, Dict[str, float]]:
        """
        Analyze attention graph structure.
        
        Args:
            attention: Attention weights (H, T, T) or (T, T)
            tau: Attention threshold
            
        Returns:
            Dictionary with DGD and GSER results
        """
        # Create dummy embeddings for graph-only analysis
        T = attention.shape[-1]
        dummy_embeddings = np.eye(T)
        
        result = self.compute_descriptors(
            dummy_embeddings,
            attention=attention,
            tau=tau
        )
        
        return {
            "dgd": result.get("dgd", {}),
            "gser": result.get("gser", {})
        }


# Quick demo with synthetic data
if __name__ == "__main__":
    print("LLM Adapter Demo")
    print("=" * 60)
    
    rng = np.random.default_rng(0)
    
    # Synthetic transformer outputs
    T, D, H = 64, 32, 4  # seq_len, hidden_dim, n_heads
    
    print(f"\nGenerating synthetic data:")
    print(f"  Sequence length: {T}")
    print(f"  Hidden dimension: {D}")
    print(f"  Number of heads: {H}")
    
    # Current embeddings
    X = rng.standard_normal((T, D))
    
    # Baseline embeddings (slightly different)
    X_ref = rng.standard_normal((T, D))
    
    # Attention weights
    attn = rng.random((H, T, T))
    # Normalize to make it look like real attention
    attn = attn / attn.sum(axis=-1, keepdims=True)
    
    # Create adapter
    client = DescriptorClient()
    adapter = LLMAdapter(client)
    
    print("\nComputing descriptors...")
    try:
        results = adapter.compute_descriptors(
            X,
            attention=attn,
            baseline_embeddings=X_ref,
            tau=0.1
        )
        
        print("\n✅ Results:")
        for desc_name, desc_results in results.items():
            print(f"\n{desc_name.upper()}:")
            for key, value in desc_results.items():
                print(f"  {key}: {value:.4f}")
        
        # Test drift detection
        print("\n" + "=" * 60)
        print("Drift Detection Test:")
        drift_result = adapter.detect_drift(X, X_ref, threshold=0.5)
        print(f"  Drift detected: {drift_result['drift_detected']}")
        print(f"  Drift score: {drift_result['drift_score']:.4f}")
        print(f"  Threshold: {drift_result['threshold']}")
        
    except Exception as e:
        print(f"\n❌ Error: {e}")
        print("\nMake sure the API is running:")
        print("  python run_api.py")

