"""
Diffusion-Geometry Descriptor (DGD)

Uses heat diffusion on data graphs to extract scale-free geometric features.
Computes dimensionless ratios from the heat trace across multiple time scales.

Key idea: Heat kernel K_t = exp(-tL) where L is the graph Laplacian.
The heat trace θ(t) = Tr(K_t) reveals multiscale geometry.

Input: graph Laplacian (normalized) or point cloud
Steps: heat kernel trace on log-time grid → ratios φ₁, φ₂ → weighted integral
Output keys: {'DGD_F', 'DGD_phi1_mean', 'DGD_phi2_q90'}
"""

import numpy as np
from typing import Dict, Any, Optional, Callable, Union
from scipy.linalg import expm
from scipy.sparse.linalg import eigsh
from scipy.sparse import issparse, csr_matrix
from .base import Descriptor, build_knn_graph, build_epsilon_graph


class DiffusionGeometryDescriptor(Descriptor):
    """
    Diffusion-Geometry Descriptor (DGD)
    
    Computes dimensionless features from heat diffusion on graphs:
    - Heat trace ratios across scales
    - Curvature-like quantities from trace derivatives
    - Spectral decay rates
    
    All features are scale-free and dimensionless.
    """
    
    name = "dgd"
    
    def __init__(self,
                 graph_type: str = 'knn',
                 k_neighbors: int = 5,
                 epsilon: Optional[float] = None,
                 n_time_samples: int = 20,
                 time_range: tuple = (0.01, 10.0),
                 weight_a: float = 1.0,
                 weight_b: float = 1.0,
                 use_sparse: bool = True):
        """
        Initialize DGD descriptor.
        
        Args:
            graph_type: Type of graph ('knn' or 'epsilon')
            k_neighbors: Number of neighbors for kNN graph
            epsilon: Distance threshold for epsilon graph
            n_time_samples: Number of time points to sample
            time_range: (min_time, max_time) for diffusion
            weight_a: Weight for φ1 (curvature ratio)
            weight_b: Weight for φ2 (trace ratio)
            use_sparse: Use sparse eigendecomposition for large graphs
        """
        super().__init__(
            graph_type=graph_type,
            k_neighbors=k_neighbors,
            epsilon=epsilon,
            n_time_samples=n_time_samples,
            time_range=time_range,
            weight_a=weight_a,
            weight_b=weight_b,
            use_sparse=use_sparse
        )
    
    def compute(self, data: Union[np.ndarray, Dict],
                times: str = 'logspace', **kwargs) -> Dict[str, float]:
        """
        Compute DGD features from point cloud or graph Laplacian.

        Args:
            data: Point cloud (n_points, n_features) OR dict with 'laplacian' key
            times: Time sampling strategy ('logspace' or array of times)
            **kwargs: Additional parameters

        Returns:
            Dictionary with dimensionless features:
            - DGD_F: Combined descriptor value (weighted integral)
            - DGD_phi1_mean: Mean curvature ratio φ₁
            - DGD_phi2_q90: 90th percentile of trace ratio φ₂
            - DGD_spectral_decay: Spectral decay rate
        """
        # Handle input: either point cloud or pre-computed Laplacian
        if isinstance(data, dict) and 'laplacian' in data:
            laplacian = data['laplacian']
            if issparse(laplacian):
                laplacian = laplacian.toarray()
        else:
            # Build from point cloud
            if isinstance(data, np.ndarray):
                self.validate_data(data, min_points=3)
                laplacian = self._build_laplacian(data)
            else:
                raise ValueError("Data must be numpy array or dict with 'laplacian' key")

        # Compute heat trace over time using efficient methods
        time_grid, heat_trace = self._compute_heat_trace_efficient(
            laplacian, times=times
        )

        # Compute dimensionless ratios
        phi1_values = self._compute_phi1(time_grid, heat_trace)
        phi2_values = self._compute_phi2(time_grid, heat_trace)

        # Aggregate with weighted integral
        phi1_mean = np.mean(phi1_values)
        phi2_q90 = np.percentile(phi2_values, 90)  # 90th percentile for robustness

        # Weighted integral (log-uniform weights)
        weight_a = self.params.get('weight_a', 1.0)
        weight_b = self.params.get('weight_b', 1.0)

        # Trapezoidal integration in log-space
        log_times = np.log(time_grid)
        weights = np.diff(log_times)
        weights = np.append(weights, weights[-1])  # Extend for last point
        weights = weights / weights.sum()  # Normalize

        dgd_f = np.sum(weights * (weight_a * phi1_values + weight_b * phi2_values))

        # Additional spectral feature
        spectral_decay = self._compute_spectral_decay(laplacian)

        return {
            'DGD_F': dgd_f,
            'DGD_phi1_mean': phi1_mean,
            'DGD_phi2_q90': phi2_q90,
            'DGD_spectral_decay': spectral_decay
        }
    
    def _build_laplacian(self, data: np.ndarray) -> np.ndarray:
        """
        Build normalized graph Laplacian.
        
        Args:
            data: Point cloud
            
        Returns:
            Normalized Laplacian matrix
        """
        graph_type = self.params.get('graph_type', 'knn')
        
        # Build adjacency matrix
        if graph_type == 'knn':
            k = self.params.get('k_neighbors', 5)
            adj_matrix = build_knn_graph(data, k=k, weighted=True)
        elif graph_type == 'epsilon':
            epsilon = self.params.get('epsilon')
            if epsilon is None:
                # Auto-select epsilon as median distance
                from scipy.spatial.distance import pdist
                distances = pdist(data)
                epsilon = np.median(distances)
            adj_matrix = build_epsilon_graph(data, epsilon=epsilon, weighted=True)
        else:
            raise ValueError(f"Unknown graph type: {graph_type}")
        
        # Compute degree matrix
        degrees = np.sum(adj_matrix, axis=1)
        degrees[degrees == 0] = 1  # Avoid division by zero
        
        # Normalized Laplacian: L = I - D^{-1/2} A D^{-1/2}
        D_inv_sqrt = np.diag(1.0 / np.sqrt(degrees))
        L = np.eye(len(data)) - D_inv_sqrt @ adj_matrix @ D_inv_sqrt
        
        return L
    
    def _compute_heat_trace_efficient(self, laplacian: np.ndarray,
                                     times: Union[str, np.ndarray] = 'logspace') -> tuple:
        """
        Compute heat trace θ(t) = Tr(exp(-tL)) efficiently using:
        - Eigendecomposition for small matrices
        - Lanczos method for medium matrices
        - Stochastic trace estimator for large matrices

        Args:
            laplacian: Graph Laplacian
            times: 'logspace' or array of time points

        Returns:
            (times, heat_trace) arrays
        """
        n = laplacian.shape[0]

        # Generate time grid
        if isinstance(times, str) and times == 'logspace':
            n_samples = self.params.get('n_time_samples', 20)
            time_range = self.params.get('time_range', (0.01, 10.0))
            time_grid = np.logspace(
                np.log10(time_range[0]),
                np.log10(time_range[1]),
                n_samples
            )
        else:
            time_grid = np.asarray(times)

        # Choose method based on matrix size
        if n <= 100:
            # Small: exact eigendecomposition
            heat_trace = self._heat_trace_exact(laplacian, time_grid)
        elif n <= 500:
            # Medium: Lanczos method
            heat_trace = self._heat_trace_lanczos(laplacian, time_grid)
        else:
            # Large: stochastic trace estimator
            heat_trace = self._heat_trace_stochastic(laplacian, time_grid)

        return time_grid, heat_trace

    def _heat_trace_exact(self, laplacian: np.ndarray, times: np.ndarray) -> np.ndarray:
        """Exact heat trace via full eigendecomposition."""
        eigenvalues = np.linalg.eigvalsh(laplacian)
        heat_trace = np.array([
            np.sum(np.exp(-eigenvalues * t))
            for t in times
        ])
        return heat_trace

    def _heat_trace_lanczos(self, laplacian: np.ndarray, times: np.ndarray) -> np.ndarray:
        """Heat trace via Lanczos eigendecomposition."""
        n = laplacian.shape[0]
        k = min(n - 2, 100)  # Number of eigenvalues

        try:
            # Convert to sparse if needed
            if not issparse(laplacian):
                L_sparse = csr_matrix(laplacian)
            else:
                L_sparse = laplacian

            eigenvalues = eigsh(L_sparse, k=k, return_eigenvectors=False, which='SM')

            # Approximate trace (assumes remaining eigenvalues are large)
            heat_trace = np.array([
                np.sum(np.exp(-eigenvalues * t))
                for t in times
            ])
        except:
            # Fallback to exact
            heat_trace = self._heat_trace_exact(laplacian, times)

        return heat_trace

    def _heat_trace_stochastic(self, laplacian: np.ndarray, times: np.ndarray,
                               n_samples: int = 20) -> np.ndarray:
        """
        Stochastic trace estimator: Tr(f(L)) ≈ (1/m) Σ v_i^T f(L) v_i
        where v_i are random Rademacher vectors.
        """
        n = laplacian.shape[0]
        heat_trace = np.zeros(len(times))

        # Generate random probe vectors
        np.random.seed(42)  # For reproducibility

        for _ in range(n_samples):
            # Rademacher vector (±1 with equal probability)
            v = np.random.choice([-1, 1], size=n).astype(float)

            for i, t in enumerate(times):
                # Compute exp(-tL) v using matrix exponential
                # For efficiency, use Krylov subspace methods
                Lv = laplacian @ v

                # Padé approximation for exp(-tL)v
                exp_Lv = self._expm_multiply(-t * laplacian, v)

                # Trace contribution
                heat_trace[i] += np.dot(v, exp_Lv)

        heat_trace /= n_samples
        return heat_trace

    def _expm_multiply(self, A: np.ndarray, v: np.ndarray) -> np.ndarray:
        """
        Compute exp(A) @ v efficiently using scaling and squaring.
        """
        try:
            from scipy.sparse.linalg import expm_multiply
            if issparse(A):
                return expm_multiply(A, v)
            else:
                return expm_multiply(csr_matrix(A), v)
        except:
            # Fallback: direct computation
            return expm(A) @ v
    
    def _compute_phi1(self, times: np.ndarray, heat_trace: np.ndarray,
                     epsilon: float = 1e-10) -> np.ndarray:
        """
        Compute φ1(t) = t * θ''(t) / (θ'(t) + ε)
        
        This is a dimensionless curvature-like ratio.
        
        Args:
            times: Time points
            heat_trace: Heat trace values
            epsilon: Regularization parameter
            
        Returns:
            φ1 values at each time point
        """
        # Compute derivatives using finite differences
        dt = np.diff(times)
        
        # First derivative: θ'(t)
        theta_prime = np.gradient(heat_trace, times)
        
        # Second derivative: θ''(t)
        theta_double_prime = np.gradient(theta_prime, times)
        
        # Compute ratio: t * θ''(t) / (θ'(t) + ε)
        phi1 = times * theta_double_prime / (np.abs(theta_prime) + epsilon)
        
        # Clip extreme values for stability
        phi1 = np.clip(phi1, -10, 10)
        
        return phi1
    
    def _compute_phi2(self, times: np.ndarray, heat_trace: np.ndarray) -> np.ndarray:
        """
        Compute φ2(t) = θ(t) / θ(t0)
        
        Ratio of heat trace at different times (dimensionless).
        
        Args:
            times: Time points
            heat_trace: Heat trace values
            
        Returns:
            φ2 values (ratios relative to first time point)
        """
        t0_trace = heat_trace[0]
        if abs(t0_trace) < 1e-10:
            return np.ones_like(heat_trace)
        
        return heat_trace / t0_trace
    
    def _compute_spectral_decay(self, laplacian: np.ndarray) -> float:
        """
        Compute spectral decay rate (dimensionless).
        
        Measures how quickly eigenvalues decay, indicating
        geometric complexity.
        
        Args:
            laplacian: Graph Laplacian
            
        Returns:
            Spectral decay rate
        """
        n = laplacian.shape[0]
        use_sparse = self.params.get('use_sparse', True)
        
        if use_sparse and n > 100:
            try:
                k = min(n - 2, 20)
                eigenvalues = eigsh(laplacian, k=k, return_eigenvectors=False)
                eigenvalues = np.sort(eigenvalues)
            except:
                eigenvalues = np.linalg.eigvalsh(laplacian)
        else:
            eigenvalues = np.linalg.eigvalsh(laplacian)
        
        # Remove near-zero eigenvalues
        eigenvalues = eigenvalues[eigenvalues > 1e-10]
        
        if len(eigenvalues) < 2:
            return 0.0
        
        # Fit power law: λ_k ~ k^(-α)
        # Take log: log(λ_k) ~ -α log(k)
        k_values = np.arange(1, len(eigenvalues) + 1)
        
        # Linear regression in log-log space
        log_k = np.log(k_values)
        log_lambda = np.log(eigenvalues)
        
        # Slope gives decay rate
        coeffs = np.polyfit(log_k, log_lambda, 1)
        decay_rate = -coeffs[0]  # Negative of slope
        
        return max(0.0, decay_rate)  # Ensure non-negative

