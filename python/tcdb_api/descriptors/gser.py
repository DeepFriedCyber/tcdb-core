"""
Graph-Scattering Energy Ratio (GSER)

Uses graph wavelet scattering to extract multiscale signal features.
Computes dimensionless energy ratios across wavelet scales.

Key idea: Pass signals through graph wavelet filters {ψ_j} and low-pass φ_J,
then compute energy ratios that are stable to deformations.
"""

import numpy as np
from typing import Dict, Any, Optional, List, Tuple
from scipy.linalg import expm
from .base import Descriptor, build_knn_graph


class GraphScatteringEnergyRatio(Descriptor):
    """
    Graph-Scattering Energy Ratio (GSER)
    
    Computes dimensionless features from graph wavelet scattering:
    - First-order scattering coefficients
    - Second-order scattering coefficients
    - Energy ratios across scales
    
    All features are scale-free and dimensionless.
    """
    
    name = "gser"
    
    def __init__(self,
                 n_scales: int = 4,
                 graph_type: str = 'knn',
                 k_neighbors: int = 5,
                 signal_type: str = 'coordinates',
                 scale_weights: Optional[List[float]] = None):
        """
        Initialize GSER descriptor.
        
        Args:
            n_scales: Number of wavelet scales
            graph_type: Type of graph ('knn' or 'epsilon')
            k_neighbors: Number of neighbors for kNN graph
            signal_type: Type of signal ('coordinates', 'degrees', 'random')
            scale_weights: Weights for each scale pair
        """
        super().__init__(
            n_scales=n_scales,
            graph_type=graph_type,
            k_neighbors=k_neighbors,
            signal_type=signal_type,
            scale_weights=scale_weights
        )
    
    def compute(self, data: np.ndarray, **kwargs) -> Dict[str, float]:
        """
        Compute GSER features from point cloud.
        
        Args:
            data: Point cloud (n_points, n_features)
            **kwargs: Additional parameters
            
        Returns:
            Dictionary with dimensionless features:
            - F_GSER: Combined descriptor value
            - S1_{j}: First-order scattering at scale j
            - S2_{j1}_{j2}: Second-order scattering at scales j1, j2
            - energy_concentration: Energy in low-pass vs wavelets
        """
        self.validate_data(data, min_points=3)
        
        # Build graph Laplacian
        laplacian = self._build_laplacian(data)
        
        # Generate or extract signal
        signal = self._get_signal(data)
        
        # Compute wavelet filters
        wavelets = self._compute_wavelets(laplacian)
        
        # Compute scattering coefficients
        S1, S2 = self._compute_scattering(signal, wavelets, laplacian)
        
        # Compute total energy
        total_energy = self._compute_total_energy(signal, wavelets, laplacian)
        
        # Build results
        results = {}
        
        # First-order coefficients (normalized)
        for j, s1 in enumerate(S1):
            results[f'S1_{j}'] = self.safe_divide(s1, total_energy)
        
        # Second-order coefficients (normalized)
        for (j1, j2), s2 in S2.items():
            results[f'S2_{j1}_{j2}'] = self.safe_divide(s2, total_energy)
        
        # Combined GSER value
        f_gser = sum(results.values())
        results['F_GSER'] = f_gser
        
        # Energy concentration (low-pass vs high-pass)
        low_pass_energy = self._compute_low_pass_energy(signal, laplacian)
        results['energy_concentration'] = self.safe_divide(
            low_pass_energy, total_energy
        )
        
        return results
    
    def _build_laplacian(self, data: np.ndarray) -> np.ndarray:
        """
        Build normalized graph Laplacian.
        
        Args:
            data: Point cloud
            
        Returns:
            Normalized Laplacian matrix
        """
        graph_type = self.params.get('graph_type', 'knn')
        k = self.params.get('k_neighbors', 5)
        
        # Build adjacency matrix
        adj_matrix = build_knn_graph(data, k=k, weighted=True)
        
        # Compute degree matrix
        degrees = np.sum(adj_matrix, axis=1)
        degrees[degrees == 0] = 1
        
        # Normalized Laplacian
        D_inv_sqrt = np.diag(1.0 / np.sqrt(degrees))
        L = np.eye(len(data)) - D_inv_sqrt @ adj_matrix @ D_inv_sqrt
        
        return L
    
    def _get_signal(self, data: np.ndarray) -> np.ndarray:
        """
        Get or generate signal on graph vertices.
        
        Args:
            data: Point cloud
            
        Returns:
            Signal vector (n_points,)
        """
        signal_type = self.params.get('signal_type', 'coordinates')
        
        if signal_type == 'coordinates':
            # Use first coordinate as signal
            if data.ndim == 1:
                signal = data
            else:
                signal = data[:, 0]
        
        elif signal_type == 'degrees':
            # Use node degrees as signal
            adj_matrix = build_knn_graph(
                data, 
                k=self.params.get('k_neighbors', 5),
                weighted=False
            )
            signal = np.sum(adj_matrix, axis=1)
        
        elif signal_type == 'random':
            # Random signal for testing
            signal = np.random.randn(len(data))
        
        else:
            raise ValueError(f"Unknown signal type: {signal_type}")
        
        # Normalize signal
        signal = signal - signal.mean()
        norm = np.linalg.norm(signal)
        if norm > 1e-10:
            signal = signal / norm
        
        return signal
    
    def _compute_wavelets(self, laplacian: np.ndarray) -> List[np.ndarray]:
        """
        Compute graph wavelet filters.
        
        Uses heat kernel wavelets: ψ_j = exp(-2^j L) - exp(-2^(j+1) L)
        
        Args:
            laplacian: Graph Laplacian
            
        Returns:
            List of wavelet filter matrices
        """
        n_scales = self.params.get('n_scales', 4)
        wavelets = []
        
        for j in range(n_scales):
            # Heat kernel at two scales
            t1 = 2**j
            t2 = 2**(j + 1)
            
            # Wavelet = difference of heat kernels
            # For efficiency, use eigendecomposition
            eigenvalues, eigenvectors = np.linalg.eigh(laplacian)
            
            heat1 = eigenvectors @ np.diag(np.exp(-t1 * eigenvalues)) @ eigenvectors.T
            heat2 = eigenvectors @ np.diag(np.exp(-t2 * eigenvalues)) @ eigenvectors.T
            
            wavelet = heat1 - heat2
            wavelets.append(wavelet)
        
        return wavelets
    
    def _compute_scattering(self, signal: np.ndarray, 
                           wavelets: List[np.ndarray],
                           laplacian: np.ndarray) -> Tuple[List[float], Dict]:
        """
        Compute first and second-order scattering coefficients.
        
        S1_j = ||x * ψ_j||_1
        S2_{j1,j2} = ||(|x * ψ_{j1}|) * ψ_{j2}||_1
        
        Args:
            signal: Input signal
            wavelets: Wavelet filters
            laplacian: Graph Laplacian
            
        Returns:
            (S1, S2) where S1 is list and S2 is dict
        """
        # First-order scattering
        S1 = []
        wavelet_responses = []
        
        for wavelet in wavelets:
            # Convolve signal with wavelet
            response = wavelet @ signal
            wavelet_responses.append(response)
            
            # L1 norm
            s1 = np.sum(np.abs(response))
            S1.append(s1)
        
        # Second-order scattering
        S2 = {}
        
        for j1, response1 in enumerate(wavelet_responses):
            # Take absolute value
            abs_response1 = np.abs(response1)
            
            for j2, wavelet2 in enumerate(wavelets):
                if j2 >= j1:  # Only compute for j2 >= j1 (symmetry)
                    # Convolve |response1| with wavelet2
                    response2 = wavelet2 @ abs_response1
                    
                    # L1 norm
                    s2 = np.sum(np.abs(response2))
                    S2[(j1, j2)] = s2
        
        return S1, S2
    
    def _compute_total_energy(self, signal: np.ndarray,
                             wavelets: List[np.ndarray],
                             laplacian: np.ndarray) -> float:
        """
        Compute total signal energy.
        
        E = ||x * φ_J||_1 + Σ S1_j + Σ S2_{j1,j2}
        
        Args:
            signal: Input signal
            wavelets: Wavelet filters
            laplacian: Graph Laplacian
            
        Returns:
            Total energy
        """
        # Low-pass energy
        low_pass = self._compute_low_pass_energy(signal, laplacian)
        
        # Wavelet energies (first-order)
        wavelet_energy = sum(
            np.sum(np.abs(wavelet @ signal))
            for wavelet in wavelets
        )
        
        # Total energy
        total = low_pass + wavelet_energy
        
        return max(total, 1e-10)  # Avoid division by zero
    
    def _compute_low_pass_energy(self, signal: np.ndarray,
                                 laplacian: np.ndarray) -> float:
        """
        Compute low-pass filtered energy.
        
        Uses heat kernel at large scale as low-pass filter.
        
        Args:
            signal: Input signal
            laplacian: Graph Laplacian
            
        Returns:
            Low-pass energy
        """
        # Large time scale for low-pass
        J = self.params.get('n_scales', 4)
        t_J = 2**J
        
        # Low-pass filter: φ_J = exp(-t_J L)
        eigenvalues, eigenvectors = np.linalg.eigh(laplacian)
        low_pass = eigenvectors @ np.diag(np.exp(-t_J * eigenvalues)) @ eigenvectors.T
        
        # Apply filter
        filtered = low_pass @ signal
        
        # L1 norm
        return np.sum(np.abs(filtered))

