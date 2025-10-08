"""
Base descriptor interface and utilities

Provides the abstract base class for all descriptors and common utilities.
"""

from abc import ABC, abstractmethod
from typing import Any, Dict, Optional, Type
import numpy as np


class Descriptor(ABC):
    """
    Abstract base class for all descriptors.
    
    All descriptors must implement the compute() method which takes data
    (point cloud, weighted graph, or embedding matrix) and returns a
    dictionary of dimensionless scalar features.
    """
    
    name: str = "base_descriptor"
    
    def __init__(self, **kwargs):
        """
        Initialize descriptor with optional parameters.
        
        Args:
            **kwargs: Descriptor-specific parameters
        """
        self.params = kwargs
    
    @abstractmethod
    def compute(self, data: Any, **kwargs) -> Dict[str, float]:
        """
        Compute descriptor features from data.
        
        Args:
            data: Input data (point cloud, graph, or embedding matrix)
            **kwargs: Additional computation parameters
            
        Returns:
            Dictionary of dimensionless scalar features
            Example: {'F': 0.73, 'H0': 1.2, 'TV0': 0.45}
        """
        pass
    
    def __call__(self, data: Any, **kwargs) -> Dict[str, float]:
        """
        Convenience method to call compute().
        
        Args:
            data: Input data
            **kwargs: Additional parameters
            
        Returns:
            Dictionary of features
        """
        return self.compute(data, **kwargs)
    
    def validate_data(self, data: np.ndarray, min_points: int = 2) -> None:
        """
        Validate input data format.
        
        Args:
            data: Input data array
            min_points: Minimum number of points required
            
        Raises:
            ValueError: If data is invalid
        """
        if not isinstance(data, np.ndarray):
            raise ValueError(f"Data must be numpy array, got {type(data)}")
        
        if data.ndim not in [1, 2]:
            raise ValueError(f"Data must be 1D or 2D array, got {data.ndim}D")
        
        if len(data) < min_points:
            raise ValueError(f"Need at least {min_points} points, got {len(data)}")
    
    def safe_divide(self, numerator: float, denominator: float, 
                   epsilon: float = 1e-10, default: float = 0.0) -> float:
        """
        Safe division with epsilon protection.
        
        Args:
            numerator: Numerator value
            denominator: Denominator value
            epsilon: Small value to prevent division by zero
            default: Default value if denominator is too small
            
        Returns:
            Division result or default value
        """
        if abs(denominator) < epsilon:
            return default
        return numerator / denominator


class DescriptorRegistry:
    """
    Registry for managing available descriptors.
    
    Allows dynamic registration and retrieval of descriptor classes.
    """
    
    def __init__(self):
        self._descriptors: Dict[str, Type[Descriptor]] = {}
    
    def register(self, name: str, descriptor_class: Type[Descriptor]) -> None:
        """
        Register a descriptor class.
        
        Args:
            name: Unique identifier for the descriptor
            descriptor_class: Descriptor class to register
        """
        if not issubclass(descriptor_class, Descriptor):
            raise ValueError(f"{descriptor_class} must inherit from Descriptor")
        self._descriptors[name] = descriptor_class
    
    def get(self, name: str, **kwargs) -> Descriptor:
        """
        Get an instance of a registered descriptor.
        
        Args:
            name: Descriptor identifier
            **kwargs: Parameters to pass to descriptor constructor
            
        Returns:
            Descriptor instance
            
        Raises:
            KeyError: If descriptor not found
        """
        if name not in self._descriptors:
            raise KeyError(f"Descriptor '{name}' not found. Available: {self.list()}")
        return self._descriptors[name](**kwargs)
    
    def list(self) -> list:
        """
        List all registered descriptor names.
        
        Returns:
            List of descriptor names
        """
        return list(self._descriptors.keys())
    
    def __contains__(self, name: str) -> bool:
        """Check if descriptor is registered."""
        return name in self._descriptors


# Utility functions for common operations

def compute_distance_matrix(points: np.ndarray, metric: str = 'euclidean') -> np.ndarray:
    """
    Compute pairwise distance matrix.
    
    Args:
        points: Point cloud (n_points, n_features)
        metric: Distance metric ('euclidean', 'manhattan', etc.)
        
    Returns:
        Distance matrix (n_points, n_points)
    """
    from scipy.spatial.distance import pdist, squareform
    return squareform(pdist(points, metric=metric))


def normalize_array(arr: np.ndarray, method: str = 'minmax') -> np.ndarray:
    """
    Normalize array values.
    
    Args:
        arr: Input array
        method: Normalization method ('minmax', 'zscore', 'sum')
        
    Returns:
        Normalized array
    """
    if method == 'minmax':
        min_val, max_val = arr.min(), arr.max()
        if max_val - min_val < 1e-10:
            return np.zeros_like(arr)
        return (arr - min_val) / (max_val - min_val)
    
    elif method == 'zscore':
        mean, std = arr.mean(), arr.std()
        if std < 1e-10:
            return np.zeros_like(arr)
        return (arr - mean) / std
    
    elif method == 'sum':
        total = arr.sum()
        if abs(total) < 1e-10:
            return np.zeros_like(arr)
        return arr / total
    
    else:
        raise ValueError(f"Unknown normalization method: {method}")


def compute_entropy(probabilities: np.ndarray, base: float = 2.0) -> float:
    """
    Compute Shannon entropy from probability distribution.
    
    Args:
        probabilities: Probability distribution (must sum to 1)
        base: Logarithm base (2 for bits, e for nats)
        
    Returns:
        Entropy value
    """
    # Filter out zero probabilities
    p = probabilities[probabilities > 0]
    if len(p) == 0:
        return 0.0
    return -np.sum(p * np.log(p) / np.log(base))


def build_knn_graph(points: np.ndarray, k: int = 5, 
                   weighted: bool = True) -> np.ndarray:
    """
    Build k-nearest neighbors graph.
    
    Args:
        points: Point cloud (n_points, n_features)
        k: Number of nearest neighbors
        weighted: If True, use distances as weights
        
    Returns:
        Adjacency matrix (n_points, n_points)
    """
    from sklearn.neighbors import kneighbors_graph
    
    # Build kNN graph
    graph = kneighbors_graph(
        points, k, mode='distance' if weighted else 'connectivity',
        include_self=False
    )
    
    # Make symmetric
    graph = (graph + graph.T) / 2
    
    return graph.toarray()


def build_epsilon_graph(points: np.ndarray, epsilon: float,
                       weighted: bool = True) -> np.ndarray:
    """
    Build epsilon-neighborhood graph.
    
    Args:
        points: Point cloud (n_points, n_features)
        epsilon: Distance threshold
        weighted: If True, use distances as weights
        
    Returns:
        Adjacency matrix (n_points, n_points)
    """
    dist_matrix = compute_distance_matrix(points)
    
    if weighted:
        # Use distances as weights, zero out beyond epsilon
        adj_matrix = np.where(dist_matrix <= epsilon, dist_matrix, 0.0)
    else:
        # Binary adjacency
        adj_matrix = (dist_matrix <= epsilon).astype(float)
    
    # Zero out diagonal
    np.fill_diagonal(adj_matrix, 0.0)
    
    return adj_matrix

