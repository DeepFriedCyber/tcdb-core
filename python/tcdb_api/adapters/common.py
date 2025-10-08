"""
Common utilities for descriptor API adapters.

Provides a lightweight client for calling the FastAPI descriptor endpoints
without requiring the full tcdb_api package.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from typing import Any, Dict, List, Tuple

import numpy as np
import requests
import scipy.sparse as sp


@dataclass
class DescriptorClient:
    """
    Lightweight client for TCDB descriptor API.
    
    Can be used standalone with just requests, numpy, and scipy.
    
    Attributes:
        base_url: Base URL of the descriptor API
        timeout: Request timeout in seconds
    
    Example:
        >>> client = DescriptorClient("http://localhost:8000")
        >>> result = client.compute("kme_delta", X=[[0,0], [1,0], [0,1]])
        >>> print(result["KME_delta_F"])
    """
    
    base_url: str = "http://localhost:8000"
    timeout: int = 60
    
    def compute(self, name: str, params: dict | None = None, **payload) -> Dict[str, float]:
        """
        Call the unified descriptor compute endpoint.
        
        Args:
            name: Descriptor name (kme_delta, dgd, tid, gser)
            params: Optional descriptor parameters
            **payload: Descriptor-specific data (X, X_ref, graph, signal, etc.)
            
        Returns:
            Dictionary of computed features
            
        Raises:
            requests.HTTPError: If the API request fails
        """
        url = f"{self.base_url}/descriptor/compute"
        
        body = {
            "name": name,
            "params": params or {},
            **payload
        }
        
        response = requests.post(url, json=body, timeout=self.timeout)
        response.raise_for_status()
        
        return response.json()
    
    def list_descriptors(self) -> List[str]:
        """
        List available descriptors.
        
        Returns:
            List of descriptor names
        """
        url = f"{self.base_url}/descriptor/list"
        response = requests.get(url, timeout=self.timeout)
        response.raise_for_status()
        
        data = response.json()
        return data.get("descriptors", [])
    
    def health_check(self) -> bool:
        """
        Check if the descriptor API is healthy.
        
        Returns:
            True if healthy, False otherwise
        """
        try:
            url = f"{self.base_url}/descriptor/health"
            response = requests.get(url, timeout=5)
            response.raise_for_status()
            
            data = response.json()
            return data.get("status") == "healthy"
        except Exception:
            return False
    
    # Utility methods for packaging inputs
    
    @staticmethod
    def csr_to_coo_payload(A: sp.csr_matrix) -> Dict[str, Any]:
        """
        Convert sparse CSR matrix to COO format for API payload.
        
        Args:
            A: Sparse adjacency matrix
            
        Returns:
            Dictionary with n_nodes, adj_indices, and adj_data
        """
        A_coo = A.tocoo()
        indices: List[Tuple[int, int]] = list(zip(
            A_coo.row.tolist(),
            A_coo.col.tolist()
        ))
        
        return {
            "n_nodes": A.shape[0],
            "adj_indices": indices,
            "adj_data": A_coo.data.tolist()
        }
    
    @staticmethod
    def array_to_list(X: np.ndarray) -> List[List[float]]:
        """
        Convert numpy array to nested list for JSON serialization.
        
        Args:
            X: Numpy array (1D or 2D)
            
        Returns:
            Nested list representation
        """
        if X.ndim == 1:
            return X.tolist()
        elif X.ndim == 2:
            return X.tolist()
        else:
            raise ValueError(f"Expected 1D or 2D array, got {X.ndim}D")
    
    @staticmethod
    def validate_point_cloud(X: np.ndarray, min_points: int = 2) -> None:
        """
        Validate point cloud data.
        
        Args:
            X: Point cloud array (n_points, n_features)
            min_points: Minimum number of points required
            
        Raises:
            ValueError: If validation fails
        """
        if not isinstance(X, np.ndarray):
            raise ValueError(f"Expected numpy array, got {type(X)}")
        
        if X.ndim != 2:
            raise ValueError(f"Expected 2D array, got {X.ndim}D")
        
        if X.shape[0] < min_points:
            raise ValueError(
                f"Need at least {min_points} points, got {X.shape[0]}"
            )
        
        if np.any(np.isnan(X)):
            raise ValueError("Point cloud contains NaN values")
        
        if np.any(np.isinf(X)):
            raise ValueError("Point cloud contains infinite values")
    
    @staticmethod
    def validate_graph(A: sp.spmatrix, min_nodes: int = 2) -> None:
        """
        Validate sparse graph adjacency matrix.
        
        Args:
            A: Sparse adjacency matrix
            min_nodes: Minimum number of nodes required
            
        Raises:
            ValueError: If validation fails
        """
        if not sp.issparse(A):
            raise ValueError(f"Expected sparse matrix, got {type(A)}")
        
        if A.shape[0] != A.shape[1]:
            raise ValueError(f"Expected square matrix, got shape {A.shape}")
        
        if A.shape[0] < min_nodes:
            raise ValueError(
                f"Need at least {min_nodes} nodes, got {A.shape[0]}"
            )


# Convenience function for quick testing
def quick_test(base_url: str = "http://localhost:8000") -> None:
    """
    Quick test of the descriptor API.
    
    Args:
        base_url: Base URL of the API
    """
    client = DescriptorClient(base_url)
    
    print("Testing descriptor API...")
    print(f"Base URL: {base_url}")
    
    # Health check
    if not client.health_check():
        print("❌ API is not healthy")
        return
    print("✅ API is healthy")
    
    # List descriptors
    descriptors = client.list_descriptors()
    print(f"✅ Available descriptors: {descriptors}")
    
    # Test KME-Δ
    X = np.random.randn(20, 3).tolist()
    result = client.compute("kme_delta", X=X)
    print(f"✅ KME-Δ result: {result.get('KME_delta_F', 'N/A')}")
    
    print("\n✅ All tests passed!")


if __name__ == "__main__":
    quick_test()

