"""
Embedding extraction utilities

Provides functions for extracting embeddings from various sources:
- Layer embeddings from neural networks
- Attention weights
- Batch processing
"""

import numpy as np
from typing import List, Dict, Optional, Callable, Any


def extract_layer_embeddings(model: Any,
                            data: np.ndarray,
                            layer_names: Optional[List[str]] = None) -> Dict[str, np.ndarray]:
    """
    Extract embeddings from specific layers of a model.
    
    Args:
        model: Neural network model (PyTorch, TensorFlow, etc.)
        data: Input data
        layer_names: Names of layers to extract (all if None)
        
    Returns:
        Dictionary mapping layer names to embeddings
    """
    embeddings = {}
    
    # This is a placeholder - actual implementation depends on framework
    # For PyTorch:
    # - Use forward hooks
    # For TensorFlow:
    # - Use intermediate layer models
    
    # Example structure:
    # embeddings['layer1'] = np.array(...)
    # embeddings['layer2'] = np.array(...)
    
    return embeddings


def extract_attention_weights(model: Any,
                             data: np.ndarray,
                             layer_idx: Optional[int] = None,
                             head_idx: Optional[int] = None) -> np.ndarray:
    """
    Extract attention weights from transformer model.
    
    Args:
        model: Transformer model
        data: Input data
        layer_idx: Layer index (all if None)
        head_idx: Attention head index (all if None)
        
    Returns:
        Attention weight matrix
    """
    # Placeholder - actual implementation depends on model
    # Returns attention matrix (n_tokens, n_tokens)
    
    return np.eye(10)  # Placeholder


def batch_process_embeddings(data_loader: Any,
                            extractor_fn: Callable,
                            batch_size: int = 32,
                            max_batches: Optional[int] = None) -> List[np.ndarray]:
    """
    Process embeddings in batches.
    
    Args:
        data_loader: Data loader iterator
        extractor_fn: Function to extract embeddings from batch
        batch_size: Batch size
        max_batches: Maximum number of batches (all if None)
        
    Returns:
        List of embedding arrays
    """
    embeddings = []
    
    for i, batch in enumerate(data_loader):
        if max_batches is not None and i >= max_batches:
            break
        
        batch_embeddings = extractor_fn(batch)
        embeddings.append(batch_embeddings)
    
    return embeddings


def aggregate_embeddings(embeddings: List[np.ndarray],
                        method: str = 'mean') -> np.ndarray:
    """
    Aggregate multiple embeddings into single representation.
    
    Args:
        embeddings: List of embedding arrays
        method: Aggregation method ('mean', 'max', 'concat')
        
    Returns:
        Aggregated embedding
    """
    if len(embeddings) == 0:
        raise ValueError("No embeddings to aggregate")
    
    if method == 'mean':
        return np.mean(embeddings, axis=0)
    
    elif method == 'max':
        return np.max(embeddings, axis=0)
    
    elif method == 'concat':
        return np.concatenate(embeddings, axis=-1)
    
    elif method == 'median':
        return np.median(embeddings, axis=0)
    
    else:
        raise ValueError(f"Unknown aggregation method: {method}")


def normalize_embeddings(embeddings: np.ndarray,
                        method: str = 'l2') -> np.ndarray:
    """
    Normalize embeddings.
    
    Args:
        embeddings: Embedding array (n_samples, n_features)
        method: Normalization method ('l2', 'l1', 'minmax', 'zscore')
        
    Returns:
        Normalized embeddings
    """
    if method == 'l2':
        # L2 normalization (unit norm)
        norms = np.linalg.norm(embeddings, axis=1, keepdims=True)
        norms[norms == 0] = 1
        return embeddings / norms
    
    elif method == 'l1':
        # L1 normalization
        norms = np.sum(np.abs(embeddings), axis=1, keepdims=True)
        norms[norms == 0] = 1
        return embeddings / norms
    
    elif method == 'minmax':
        # Min-max normalization to [0, 1]
        min_vals = embeddings.min(axis=0, keepdims=True)
        max_vals = embeddings.max(axis=0, keepdims=True)
        range_vals = max_vals - min_vals
        range_vals[range_vals == 0] = 1
        return (embeddings - min_vals) / range_vals
    
    elif method == 'zscore':
        # Z-score normalization
        mean = embeddings.mean(axis=0, keepdims=True)
        std = embeddings.std(axis=0, keepdims=True)
        std[std == 0] = 1
        return (embeddings - mean) / std
    
    else:
        raise ValueError(f"Unknown normalization method: {method}")


def reduce_dimensionality(embeddings: np.ndarray,
                         n_components: int = 2,
                         method: str = 'pca') -> np.ndarray:
    """
    Reduce dimensionality of embeddings.
    
    Args:
        embeddings: High-dimensional embeddings
        n_components: Target dimensionality
        method: Reduction method ('pca', 'tsne', 'umap')
        
    Returns:
        Low-dimensional embeddings
    """
    if method == 'pca':
        from sklearn.decomposition import PCA
        reducer = PCA(n_components=n_components)
        return reducer.fit_transform(embeddings)
    
    elif method == 'tsne':
        from sklearn.manifold import TSNE
        reducer = TSNE(n_components=n_components)
        return reducer.fit_transform(embeddings)
    
    elif method == 'umap':
        try:
            import umap
            reducer = umap.UMAP(n_components=n_components)
            return reducer.fit_transform(embeddings)
        except ImportError:
            raise ImportError("UMAP not installed. Use: pip install umap-learn")
    
    else:
        raise ValueError(f"Unknown reduction method: {method}")


def compute_embedding_statistics(embeddings: np.ndarray) -> Dict[str, float]:
    """
    Compute statistics of embeddings.
    
    Args:
        embeddings: Embedding array (n_samples, n_features)
        
    Returns:
        Dictionary of statistics
    """
    return {
        'n_samples': embeddings.shape[0],
        'n_features': embeddings.shape[1] if embeddings.ndim > 1 else 1,
        'mean_norm': float(np.linalg.norm(embeddings, axis=1).mean()),
        'std_norm': float(np.linalg.norm(embeddings, axis=1).std()),
        'mean_value': float(embeddings.mean()),
        'std_value': float(embeddings.std()),
        'min_value': float(embeddings.min()),
        'max_value': float(embeddings.max()),
    }


def create_point_cloud_from_embeddings(embeddings: np.ndarray,
                                      sample_size: Optional[int] = None,
                                      random_seed: Optional[int] = None) -> np.ndarray:
    """
    Create point cloud from embeddings for TDA.
    
    Args:
        embeddings: Embedding array
        sample_size: Number of points to sample (all if None)
        random_seed: Random seed for reproducibility
        
    Returns:
        Point cloud array
    """
    if random_seed is not None:
        np.random.seed(random_seed)
    
    if sample_size is not None and sample_size < len(embeddings):
        # Random sampling
        indices = np.random.choice(len(embeddings), size=sample_size, replace=False)
        return embeddings[indices]
    
    return embeddings


def compute_embedding_distances(embeddings: np.ndarray,
                               metric: str = 'euclidean') -> np.ndarray:
    """
    Compute pairwise distances between embeddings.
    
    Args:
        embeddings: Embedding array
        metric: Distance metric
        
    Returns:
        Distance matrix
    """
    from scipy.spatial.distance import pdist, squareform
    return squareform(pdist(embeddings, metric=metric))

