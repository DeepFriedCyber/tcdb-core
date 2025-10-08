"""
Bioinformatics adapter for TCDB descriptors.

Analyzes protein structures and ensembles to detect:
- Conformational diversity (TID)
- Ensemble drift (KME-Δ)
- Contact network geometry (DGD)
- Residue flexibility patterns (GSER)
"""

from __future__ import annotations

from typing import Dict, List, Optional

import numpy as np
import scipy.sparse as sp

from .common import DescriptorClient


class BioAdapter:
    """
    Descriptors for protein ensembles & contact graphs.
    
    Inputs:
    - coords_list: list of (N_atoms, 3) arrays for MD frames or model samples
    - contact_graph: optional CSR adjacency for residue/atom contacts
    - ref_coords_list: optional reference ensemble (WT or known actives)
    
    Example:
        >>> adapter = BioAdapter(DescriptorClient())
        >>> coords = [frame1, frame2, ...]  # MD trajectory frames
        >>> ref_coords = [ref1, ref2, ...]  # Reference ensemble
        >>> results = adapter.compute_descriptors(coords, ref_coords_list=ref_coords)
        >>> print(results["kme_delta"]["KME_delta_F"])  # Conformational drift
    """
    
    def __init__(self, client: DescriptorClient) -> None:
        """
        Initialize bio adapter.
        
        Args:
            client: DescriptorClient instance
        """
        self.client = client
    
    def _coords_to_embedding(self, coords: np.ndarray) -> np.ndarray:
        """
        Convert 3D coordinates to alignment-agnostic embedding.
        
        Uses pairwise distance spectrum as a rotation/translation invariant
        representation of the structure.
        
        Args:
            coords: Atomic coordinates (N_atoms, 3)
            
        Returns:
            Spectral signature (N_atoms,)
        """
        # Compute pairwise distance matrix
        D = np.linalg.norm(
            coords[:, None, :] - coords[None, :, :],
            axis=-1
        )
        
        # Get eigenvalues (spectral signature)
        vals = np.linalg.eigvalsh(D)
        
        # Sort in descending order
        return np.sort(vals)[::-1]
    
    def _build_contact_graph(
        self,
        coords: np.ndarray,
        cutoff: float = 8.0
    ) -> sp.csr_matrix:
        """
        Build contact graph from coordinates.
        
        Args:
            coords: Atomic coordinates (N_atoms, 3)
            cutoff: Distance cutoff for contacts (Angstroms)
            
        Returns:
            Sparse contact adjacency matrix
        """
        # Compute pairwise distances
        D = np.linalg.norm(
            coords[:, None, :] - coords[None, :, :],
            axis=-1
        )
        
        # Create contact matrix
        contacts = (D < cutoff) & (D > 0)  # Exclude self-contacts
        
        # Convert to sparse
        rows, cols = np.nonzero(contacts)
        data = np.ones(len(rows))
        
        return sp.csr_matrix(
            (data, (rows, cols)),
            shape=coords.shape[:1] * 2
        )
    
    def compute_descriptors(
        self,
        coords_list: List[np.ndarray],
        contact_graph: Optional[sp.csr_matrix] = None,
        ref_coords_list: Optional[List[np.ndarray]] = None,
        contact_cutoff: float = 8.0,
        kme_params: Optional[dict] = None,
        tid_params: Optional[dict] = None,
        dgd_params: Optional[dict] = None,
        gser_params: Optional[dict] = None,
    ) -> Dict[str, Dict[str, float]]:
        """
        Compute descriptors for protein ensemble analysis.
        
        Args:
            coords_list: List of coordinate arrays (N_atoms, 3)
            contact_graph: Optional pre-computed contact graph
            ref_coords_list: Optional reference ensemble
            contact_cutoff: Distance cutoff for contact graph (Angstroms)
            kme_params: Parameters for KME-Δ
            tid_params: Parameters for TID
            dgd_params: Parameters for DGD
            gser_params: Parameters for GSER
            
        Returns:
            Dictionary mapping descriptor names to their results
        """
        if not coords_list:
            raise ValueError("coords_list cannot be empty")
        
        out: Dict[str, Dict[str, float]] = {}
        
        # Build ensemble embedding matrix
        embeddings = np.stack([
            self._coords_to_embedding(coords)
            for coords in coords_list
        ], axis=0)
        
        self.client.validate_point_cloud(embeddings, min_points=2)
        
        # 1) KME-Δ: Conformational drift
        payload = {"X": embeddings.tolist()}
        
        if ref_coords_list is not None:
            ref_embeddings = np.stack([
                self._coords_to_embedding(coords)
                for coords in ref_coords_list
            ], axis=0)
            
            self.client.validate_point_cloud(ref_embeddings, min_points=2)
            payload["X_ref"] = ref_embeddings.tolist()
        
        out["kme_delta"] = self.client.compute(
            "kme_delta",
            params=kme_params or {"sigmas": [0.5, 1.0, 2.0]},
            **payload
        )
        
        # 2) TID: Topological diversity of conformations
        # Use PCA to 3D for point cloud representation
        from sklearn.decomposition import PCA
        
        pca = PCA(n_components=min(3, embeddings.shape[1]))
        X_pca = pca.fit_transform(embeddings)
        
        out["tid"] = self.client.compute(
            "tid",
            params=tid_params or {"max_dimension": 1},
            X=X_pca.tolist()
        )
        
        # 3) Contact graph analysis (if provided or can be built)
        if contact_graph is None and coords_list:
            # Build from first frame
            contact_graph = self._build_contact_graph(
                coords_list[0],
                cutoff=contact_cutoff
            )
        
        if contact_graph is not None:
            self.client.validate_graph(contact_graph, min_nodes=2)
            
            graph_payload = self.client.csr_to_coo_payload(contact_graph)
            
            # DGD: Contact network geometry
            out["dgd"] = self.client.compute(
                "dgd",
                params=dgd_params or {"n_time_samples": 16},
                **graph_payload
            )
            
            # GSER: Residue flexibility patterns
            # Use per-residue B-factor-like signal (uniform as placeholder)
            signal = np.ones(contact_graph.shape[0], dtype=float)
            
            out["gser"] = self.client.compute(
                "gser",
                params=gser_params or {"n_scales": 3, "k_neighbors": 5},
                **graph_payload,
                signal=signal.tolist()
            )
        
        return out
    
    def analyze_conformational_change(
        self,
        coords_list: List[np.ndarray],
        ref_coords_list: List[np.ndarray],
        threshold: float = 0.5
    ) -> Dict[str, any]:
        """
        Analyze conformational changes relative to reference.
        
        Args:
            coords_list: Current ensemble coordinates
            ref_coords_list: Reference ensemble coordinates
            threshold: Change threshold
            
        Returns:
            Dictionary with analysis results
        """
        results = self.compute_descriptors(
            coords_list,
            ref_coords_list=ref_coords_list
        )
        
        drift_score = results["kme_delta"]["KME_delta_F"]
        
        return {
            "significant_change": drift_score > threshold,
            "drift_score": drift_score,
            "threshold": threshold,
            "full_results": results
        }


# Demo with synthetic coordinates (toy helix + noise)
if __name__ == "__main__":
    print("Bio Adapter Demo")
    print("=" * 60)
    
    rng = np.random.default_rng(0)
    
    def helix(n=60, pitch=1.5, radius=5.0):
        """Generate ideal helix coordinates."""
        t = np.linspace(0, 2*np.pi, n, endpoint=False)
        return np.stack([
            radius * np.cos(t),
            radius * np.sin(t),
            pitch * t / (2*np.pi)
        ], axis=1)
    
    print("\nGenerating synthetic protein ensemble:")
    print("  Structure: Alpha helix")
    print("  Number of atoms: 60")
    print("  Number of frames: 20")
    
    # Generate ensemble with thermal noise
    coords_list = [
        helix() + 0.1 * rng.standard_normal((60, 3))
        for _ in range(20)
    ]
    
    # Generate reference ensemble (less noise)
    ref_list = [
        helix() + 0.05 * rng.standard_normal((60, 3))
        for _ in range(20)
    ]
    
    print("  Current ensemble RMSD: ~0.1 Å")
    print("  Reference ensemble RMSD: ~0.05 Å")
    
    # Create adapter
    client = DescriptorClient()
    adapter = BioAdapter(client)
    
    print("\nComputing descriptors...")
    try:
        results = adapter.compute_descriptors(
            coords_list,
            ref_coords_list=ref_list,
            contact_cutoff=8.0
        )
        
        print("\n✅ Results:")
        for desc_name, desc_results in results.items():
            print(f"\n{desc_name.upper()}:")
            for key, value in desc_results.items():
                print(f"  {key}: {value:.4f}")
        
        # Test conformational change analysis
        print("\n" + "=" * 60)
        print("Conformational Change Analysis:")
        change_result = adapter.analyze_conformational_change(
            coords_list,
            ref_list,
            threshold=0.5
        )
        print(f"  Significant change: {change_result['significant_change']}")
        print(f"  Drift score: {change_result['drift_score']:.4f}")
        print(f"  Threshold: {change_result['threshold']}")
        
    except Exception as e:
        print(f"\n❌ Error: {e}")
        print("\nMake sure the API is running:")
        print("  python run_api.py")
        
        # Check if sklearn is available
        try:
            import sklearn
        except ImportError:
            print("\n⚠️  Note: sklearn is required for PCA in bio adapter")
            print("  pip install scikit-learn")

