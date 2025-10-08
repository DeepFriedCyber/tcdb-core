"""
KME-Δ (Kernel Mean Embedding Divergence) - Production Version

Fully working implementation with attention weights support.
Based on clean production skeleton with enhancements.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple

import numpy as np

from .base_v2 import Descriptor, pairwise_sq_dists, rbf_kernel, normalize_weights, validate_data


@dataclass
class KME_Delta(Descriptor):
    """
    Kernel Mean Embedding divergence (multi-scale, dimensionless).
    
    Returns a scalar 'KME_delta_F' plus per-scale contributions.
    
    F = sqrt( sum_j w_j * ||mu_j - mu*_j||^2 / (||mu*_j||^2 + eps) )
    
    Where mu_j is the empirical RKHS mean embedding under an RBF kernel of width sigma_j.
    
    Attributes:
        sigmas: Kernel bandwidth scales
        weights: Optional weights for each scale (default: uniform)
        eps: Regularization epsilon
        name: Descriptor name
    """
    
    sigmas: Tuple[float, ...] = (0.5, 1.0, 2.0)
    weights: Optional[Tuple[float, ...]] = None
    eps: float = 1e-12
    name: str = "kme_delta"

    def compute(
        self,
        X: np.ndarray | Dict,
        X_ref: Optional[np.ndarray] = None,
        sample_weights: Optional[np.ndarray] = None,
        ref_weights: Optional[np.ndarray] = None,
        **kwargs,
    ) -> Dict[str, float]:
        """
        Compute KME-Δ features.
        
        Args:
            X: Point cloud (n, d) OR dict with 'embeddings' and optional 'attention_weights'
            X_ref: Reference point cloud (m, d). If None, uses shuffled copy
            sample_weights: Optional weights for X samples
            ref_weights: Optional weights for reference samples
            **kwargs: Additional parameters
            
        Returns:
            Dictionary with:
                - KME_delta_F: Combined descriptor value
                - KME_sigma_{σ}: Divergence at each scale σ
                - KME_mean: Mean divergence across scales
                - KME_max: Maximum divergence
        """
        # Parse input
        if isinstance(X, dict):
            embeddings = X.get('embeddings')
            if embeddings is None:
                raise ValueError("Dict input must contain 'embeddings' key")
            X_data = embeddings
            sample_weights = X.get('attention_weights', sample_weights)
        else:
            X_data = X
        
        # Validate
        validate_data(X_data, min_points=2)
        
        n, d = X_data.shape
        
        # Reference data
        if X_ref is None:
            # Default: compare against a shuffled copy (proxy baseline)
            X_ref = X_data[::-1].copy()
        
        validate_data(X_ref, min_points=2)
        
        if X_ref.shape[1] != d:
            raise ValueError(f"X_ref dimension mismatch: {X_ref.shape[1]} != {d}")
        
        m = X_ref.shape[0]
        
        # Scale weights
        if self.weights is None:
            w = np.ones(len(self.sigmas), dtype=float) / len(self.sigmas)
        else:
            w = np.array(self.weights, dtype=float)
            w = w / w.sum()
        
        # Normalize sample weights (dimensionless)
        sample_weights = normalize_weights(sample_weights, n)
        ref_weights = normalize_weights(ref_weights, m)
        
        # Compute per-scale divergences
        per_scale = []
        features: Dict[str, float] = {}
        
        for j, (sigma, wj) in enumerate(zip(self.sigmas, w)):
            # Kernel matrices
            Kxx = rbf_kernel(X_data, X_data, sigma)
            Kyy = rbf_kernel(X_ref, X_ref, sigma)
            Kxy = rbf_kernel(X_data, X_ref, sigma)
            
            # Weighted MMD^2 components
            sw = sample_weights[:, None] * sample_weights[None, :]
            rw = ref_weights[:, None] * ref_weights[None, :]
            srw = sample_weights[:, None] * ref_weights[None, :]
            
            mmd2 = (sw * Kxx).sum() + (rw * Kyy).sum() - 2.0 * (srw * Kxy).sum()
            
            # Reference norm (||mu*||^2) = E_{y,y'} k(y,y') with ref weights
            ref_norm2 = (rw * Kyy).sum()
            
            # Dimensionless ratio
            ratio = mmd2 / (ref_norm2 + self.eps)
            per_scale.append(wj * ratio)
            features[f"KME_sigma_{sigma:g}"] = float(ratio)
        
        # Combined descriptor
        F = math.sqrt(float(np.clip(np.sum(per_scale), 0.0, np.inf)))
        features["KME_delta_F"] = F
        
        # Additional statistics
        divergences = [features[f"KME_sigma_{sigma:g}"] for sigma in self.sigmas]
        features["KME_mean"] = float(np.mean(divergences))
        features["KME_max"] = float(np.max(divergences))
        features["KME_min"] = float(np.min(divergences))
        
        return features


# Alias for compatibility
KernelMeanEmbeddingDelta = KME_Delta

