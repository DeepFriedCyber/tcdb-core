"""
Enhanced base descriptor interface with cleaner design.

This module provides the core abstractions for dimensionless, multiscale descriptors
following production-ready patterns.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Any, Dict, Mapping, Optional
import numpy as np


class Descriptor(ABC):
    """
    Base interface for all dimensionless, multiscale descriptors.
    
    Each descriptor returns a dict[str, float] so it's trivially loggable/serializable.
    All implementations MUST be dimensionless (ratios, probabilities, normalized stats).
    """

    name: str = "descriptor"

    @abstractmethod
    def compute(self, data: Any, **kwargs) -> Dict[str, float]:
        """
        Compute descriptor features from `data` and return a flat dict of floats.
        
        Args:
            data: Input data (point cloud, graph, embeddings, etc.)
            **kwargs: Additional parameters
            
        Returns:
            Dictionary of dimensionless scalar features
        """
        ...

    def __call__(self, data: Any, **kwargs) -> Dict[str, float]:
        """Convenience method to call compute directly."""
        return self.compute(data, **kwargs)


def merge_features(*feature_dicts: Mapping[str, float]) -> Dict[str, float]:
    """
    Merge multiple feature dictionaries into one.
    
    Args:
        *feature_dicts: Variable number of feature dictionaries
        
    Returns:
        Merged dictionary
    """
    out: Dict[str, float] = {}
    for d in feature_dicts:
        out.update(d)
    return out


def validate_data(
    data: np.ndarray,
    min_points: int = 2,
    min_features: int = 1,
    allow_nan: bool = False
) -> None:
    """
    Validate input data array.
    
    Args:
        data: Input array to validate
        min_points: Minimum number of points required
        min_features: Minimum number of features required
        allow_nan: Whether to allow NaN values
        
    Raises:
        ValueError: If validation fails
    """
    if not isinstance(data, np.ndarray):
        raise ValueError(f"Data must be numpy array, got {type(data)}")
    
    if data.ndim != 2:
        raise ValueError(f"Data must be 2D array, got shape {data.shape}")
    
    n_points, n_features = data.shape
    
    if n_points < min_points:
        raise ValueError(f"Need at least {min_points} points, got {n_points}")
    
    if n_features < min_features:
        raise ValueError(f"Need at least {min_features} features, got {n_features}")
    
    if not allow_nan and np.any(np.isnan(data)):
        raise ValueError("Data contains NaN values")
    
    if not allow_nan and np.any(np.isinf(data)):
        raise ValueError("Data contains infinite values")


# Utility functions for common operations

def pairwise_sq_dists(X: np.ndarray, Y: np.ndarray) -> np.ndarray:
    """
    Efficient computation of pairwise squared Euclidean distances.
    
    Args:
        X: First point set (n, d)
        Y: Second point set (m, d)
        
    Returns:
        Distance matrix (n, m)
    """
    X2 = (X * X).sum(axis=1)[:, None]
    Y2 = (Y * Y).sum(axis=1)[None, :]
    return X2 + Y2 - 2.0 * X @ Y.T


def rbf_kernel(X: np.ndarray, Y: np.ndarray, sigma: float) -> np.ndarray:
    """
    RBF (Gaussian) kernel matrix.
    
    Args:
        X: First point set (n, d)
        Y: Second point set (m, d)
        sigma: Kernel bandwidth
        
    Returns:
        Kernel matrix (n, m)
    """
    D2 = pairwise_sq_dists(X, Y)
    return np.exp(-D2 / (2.0 * sigma * sigma))


def safe_divide(
    numerator: float | np.ndarray,
    denominator: float | np.ndarray,
    epsilon: float = 1e-12,
    default: float = 0.0
) -> float | np.ndarray:
    """
    Safe division with epsilon regularization.
    
    Args:
        numerator: Numerator value(s)
        denominator: Denominator value(s)
        epsilon: Small value to add to denominator
        default: Default value if denominator is zero
        
    Returns:
        Result of division
    """
    denom = denominator + epsilon
    if isinstance(denom, np.ndarray):
        result = numerator / denom
        result[np.abs(denominator) < epsilon] = default
        return result
    else:
        return numerator / denom if abs(denominator) >= epsilon else default


def normalize_weights(weights: Optional[np.ndarray], n: int) -> np.ndarray:
    """
    Normalize weights to sum to 1, or create uniform weights.
    
    Args:
        weights: Optional weight array
        n: Number of points (for uniform weights)
        
    Returns:
        Normalized weight array
    """
    if weights is None:
        return np.ones(n) / n
    else:
        weights = np.asarray(weights)
        return weights / weights.sum()


class DescriptorRegistry:
    """
    Registry for managing descriptor instances.
    
    Allows dynamic registration and retrieval of descriptors.
    """
    
    def __init__(self):
        self._descriptors: Dict[str, type[Descriptor]] = {}
    
    def register(self, name: str, descriptor_class: type[Descriptor]) -> None:
        """
        Register a descriptor class.
        
        Args:
            name: Unique name for the descriptor
            descriptor_class: Descriptor class to register
        """
        self._descriptors[name] = descriptor_class
    
    def get(self, name: str, **kwargs) -> Descriptor:
        """
        Get a descriptor instance by name.
        
        Args:
            name: Descriptor name
            **kwargs: Parameters to pass to descriptor constructor
            
        Returns:
            Descriptor instance
            
        Raises:
            KeyError: If descriptor not found
        """
        if name not in self._descriptors:
            raise KeyError(f"Descriptor '{name}' not found. Available: {list(self._descriptors.keys())}")
        
        return self._descriptors[name](**kwargs)
    
    def list(self) -> list[str]:
        """List all registered descriptor names."""
        return list(self._descriptors.keys())
    
    def __contains__(self, name: str) -> bool:
        """Check if descriptor is registered."""
        return name in self._descriptors


# Global registry instance
_global_registry = DescriptorRegistry()


def get_registry() -> DescriptorRegistry:
    """Get the global descriptor registry."""
    return _global_registry

