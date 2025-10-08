"""
Kernel Mean Embedding Divergence (KME-Δ)

Represents distributions in RKHS and compares to a reference state.
Uses multi-scale kernels to capture distributional drift in a dimensionless way.

Key idea: For kernel k_σ, mean embedding μ = E[k_σ(x, ·)]
Compare current state to reference using relative RKHS norms.

Input: samples or embeddings (with optional attention weights), baseline reference
Steps: multi-scale kernels → MMD-like squared norms → ratio vs baseline
Output keys: {'KME_delta_F', 'KME_sigma_0.5', 'KME_sigma_1.0', ...}
"""

import numpy as np
from typing import Dict, Any, Optional, List, Union
from .base import Descriptor


class KernelMeanEmbeddingDelta(Descriptor):
    """
    Kernel Mean Embedding Divergence (KME-Δ)
    
    Computes dimensionless distributional divergence using:
    - Multi-scale RBF kernels
    - RKHS mean embeddings
    - MMD-style contrasts with reference distribution
    
    All features are scale-free and dimensionless.
    """
    
    name = "kme_delta"
    
    def __init__(self,
                 kernel_type: str = 'rbf',
                 sigma_scales: Optional[List[float]] = None,
                 reference_type: str = 'uniform',
                 reference_data: Optional[np.ndarray] = None,
                 scale_weights: Optional[List[float]] = None,
                 use_attention_weights: bool = False):
        """
        Initialize KME-Δ descriptor.

        Args:
            kernel_type: Kernel type ('rbf', 'laplacian')
            sigma_scales: List of kernel bandwidth scales
            reference_type: Reference distribution ('uniform', 'gaussian', 'data')
            reference_data: Reference data if reference_type='data'
            scale_weights: Weights for each scale (default: equal)
            use_attention_weights: If True, use attention weights for embeddings
        """
        super().__init__(
            kernel_type=kernel_type,
            sigma_scales=sigma_scales,
            reference_type=reference_type,
            reference_data=reference_data,
            scale_weights=scale_weights,
            use_attention_weights=use_attention_weights
        )

        # Default sigma scales (multiscale)
        if sigma_scales is None:
            self.sigma_scales = [0.1, 0.5, 1.0, 2.0, 5.0]
        else:
            self.sigma_scales = sigma_scales

        # Default weights (equal)
        if scale_weights is None:
            self.scale_weights = [1.0] * len(self.sigma_scales)
        else:
            self.scale_weights = scale_weights
    
    def compute(self, data: Union[np.ndarray, Dict], **kwargs) -> Dict[str, float]:
        """
        Compute KME-Δ features from samples or embeddings.

        Args:
            data: Point cloud (n_points, n_features) OR dict with:
                  - 'embeddings': embedding matrix
                  - 'attention_weights': optional attention weights (n_points,)
            **kwargs: Additional parameters:
                - reference_data: baseline reference
                - attention_weights: alternative way to pass weights

        Returns:
            Dictionary with dimensionless features:
            - KME_delta_F: Combined descriptor value (weighted combination)
            - KME_sigma_{σ}: Divergence at each scale σ
            - KME_mean: Mean divergence across scales
            - KME_max: Maximum divergence
        """
        # Parse input
        if isinstance(data, dict):
            embeddings = data.get('embeddings')
            attention_weights = data.get('attention_weights', kwargs.get('attention_weights'))
        else:
            embeddings = data
            attention_weights = kwargs.get('attention_weights')

        # Validate
        if isinstance(embeddings, np.ndarray):
            self.validate_data(embeddings, min_points=2)
        else:
            raise ValueError("Data must be numpy array or dict with 'embeddings' key")

        # Normalize attention weights if provided
        if attention_weights is not None:
            attention_weights = np.asarray(attention_weights)
            attention_weights = attention_weights / attention_weights.sum()

        # Get or generate reference data
        reference = kwargs.get('reference_data', self.params.get('reference_data'))
        if reference is None:
            reference = self._generate_reference(embeddings)

        # Compute divergence at each scale
        divergences = {}

        for sigma in self.sigma_scales:
            # Compute MMD with optional attention weights
            div = self._compute_mmd_weighted(
                embeddings, reference, sigma,
                weights_X=attention_weights
            )

            # Store with sigma in key name
            key = f'KME_sigma_{sigma}'
            divergences[key] = div

        # Weighted combination for main descriptor
        div_values = np.array(list(divergences.values()))
        weights = np.array(self.scale_weights[:len(div_values)])
        weights = weights / weights.sum()  # Normalize

        kme_delta_f = np.sqrt(np.sum(weights * div_values**2))

        # Build results
        results = {
            'KME_delta_F': kme_delta_f,
            'KME_mean': np.mean(div_values),
            'KME_max': np.max(div_values),
            'KME_min': np.min(div_values)
        }

        # Add per-scale divergences
        results.update(divergences)

        return results
    
    def _generate_reference(self, data: np.ndarray) -> np.ndarray:
        """
        Generate reference distribution.
        
        Args:
            data: Input data for determining reference
            
        Returns:
            Reference point cloud
        """
        reference_type = self.params.get('reference_type', 'uniform')
        n_points = len(data)
        n_features = data.shape[1] if data.ndim > 1 else 1
        
        if reference_type == 'uniform':
            # Uniform distribution in data bounding box
            min_vals = data.min(axis=0)
            max_vals = data.max(axis=0)
            reference = np.random.uniform(
                min_vals, max_vals, size=(n_points, n_features)
            )
        
        elif reference_type == 'gaussian':
            # Gaussian with same mean and covariance
            mean = data.mean(axis=0)
            cov = np.cov(data.T)
            reference = np.random.multivariate_normal(
                mean, cov, size=n_points
            )
        
        elif reference_type == 'subsample':
            # Random subsample of data (for self-comparison)
            indices = np.random.choice(len(data), size=n_points, replace=True)
            reference = data[indices]
        
        else:
            raise ValueError(f"Unknown reference type: {reference_type}")
        
        return reference
    
    def _compute_kernel_matrix(self, X: np.ndarray, Y: np.ndarray,
                               sigma: float) -> np.ndarray:
        """
        Compute kernel matrix K[i,j] = k(X[i], Y[j]).
        
        Args:
            X: First point set (n, d)
            Y: Second point set (m, d)
            sigma: Kernel bandwidth
            
        Returns:
            Kernel matrix (n, m)
        """
        kernel_type = self.params.get('kernel_type', 'rbf')
        
        # Compute pairwise squared distances
        X_sq = np.sum(X**2, axis=1, keepdims=True)
        Y_sq = np.sum(Y**2, axis=1, keepdims=True)
        sq_dists = X_sq + Y_sq.T - 2 * X @ Y.T
        sq_dists = np.maximum(sq_dists, 0)  # Numerical stability
        
        if kernel_type == 'rbf':
            # RBF kernel: k(x,y) = exp(-||x-y||^2 / (2σ^2))
            K = np.exp(-sq_dists / (2 * sigma**2))
        
        elif kernel_type == 'laplacian':
            # Laplacian kernel: k(x,y) = exp(-||x-y|| / σ)
            dists = np.sqrt(sq_dists)
            K = np.exp(-dists / sigma)
        
        else:
            raise ValueError(f"Unknown kernel type: {kernel_type}")
        
        return K
    
    def _compute_mmd(self, X: np.ndarray, Y: np.ndarray, sigma: float,
                    epsilon: float = 1e-10) -> float:
        """
        Compute Maximum Mean Discrepancy (MMD) between X and Y.

        MMD^2 = ||μ_X - μ_Y||^2_H
              = E[k(x,x')] - 2E[k(x,y)] + E[k(y,y')]

        Returns normalized (dimensionless) version.

        Args:
            X: First point set
            Y: Second point set
            sigma: Kernel bandwidth
            epsilon: Regularization

        Returns:
            Normalized MMD (dimensionless)
        """
        return self._compute_mmd_weighted(X, Y, sigma, epsilon=epsilon)

    def _compute_mmd_weighted(self, X: np.ndarray, Y: np.ndarray, sigma: float,
                             weights_X: Optional[np.ndarray] = None,
                             weights_Y: Optional[np.ndarray] = None,
                             epsilon: float = 1e-10) -> float:
        """
        Compute weighted MMD with optional attention weights.

        Weighted MMD^2 = ||μ_X - μ_Y||^2_H where
        μ_X = Σ_i w_i k(x_i, ·) with Σ w_i = 1

        Args:
            X: First point set (n, d)
            Y: Second point set (m, d)
            sigma: Kernel bandwidth
            weights_X: Optional weights for X (n,)
            weights_Y: Optional weights for Y (m,)
            epsilon: Regularization

        Returns:
            Normalized weighted MMD (dimensionless)
        """
        n = len(X)
        m = len(Y)

        # Default to uniform weights
        if weights_X is None:
            weights_X = np.ones(n) / n
        else:
            weights_X = weights_X / weights_X.sum()

        if weights_Y is None:
            weights_Y = np.ones(m) / m
        else:
            weights_Y = weights_Y / weights_Y.sum()

        # Compute kernel matrices
        K_XX = self._compute_kernel_matrix(X, X, sigma)
        K_YY = self._compute_kernel_matrix(Y, Y, sigma)
        K_XY = self._compute_kernel_matrix(X, Y, sigma)

        # Weighted MMD^2 = w_X^T K_XX w_X - 2 w_X^T K_XY w_Y + w_Y^T K_YY w_Y
        term1 = weights_X @ K_XX @ weights_X
        term2 = weights_Y @ K_YY @ weights_Y
        term3 = weights_X @ K_XY @ weights_Y

        mmd_squared = term1 + term2 - 2 * term3
        mmd_squared = max(0, mmd_squared)  # Ensure non-negative

        # Normalize by reference norm for dimensionless output
        ref_norm_sq = term2 + epsilon

        return np.sqrt(mmd_squared / ref_norm_sq)
    
    def compute_witness_function(self, data: np.ndarray, 
                                 grid_points: np.ndarray,
                                 sigma: float = 1.0) -> np.ndarray:
        """
        Compute witness function for visualization.
        
        The witness function w(x) = μ_data(x) - μ_ref(x) shows
        where distributions differ.
        
        Args:
            data: Data point cloud
            grid_points: Points to evaluate witness function
            sigma: Kernel bandwidth
            
        Returns:
            Witness function values at grid points
        """
        reference = self._generate_reference(data)
        
        # Compute mean embeddings at grid points
        K_data = self._compute_kernel_matrix(grid_points, data, sigma)
        K_ref = self._compute_kernel_matrix(grid_points, reference, sigma)
        
        # Mean embeddings
        mu_data = K_data.mean(axis=1)
        mu_ref = K_ref.mean(axis=1)
        
        # Witness function
        witness = mu_data - mu_ref
        
        return witness

