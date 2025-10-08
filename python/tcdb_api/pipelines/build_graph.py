"""
Graph construction utilities

Provides functions for building various types of graphs from point clouds:
- k-nearest neighbors (kNN)
- Epsilon-neighborhood
- Vietoris-Rips
- Graph Laplacians
"""

import numpy as np
from typing import Optional, Tuple
from scipy.spatial.distance import pdist, squareform
from sklearn.neighbors import kneighbors_graph


def build_knn_graph(points: np.ndarray, 
                   k: int = 5,
                   weighted: bool = True,
                   symmetric: bool = True) -> np.ndarray:
    """
    Build k-nearest neighbors graph.
    
    Args:
        points: Point cloud (n_points, n_features)
        k: Number of nearest neighbors
        weighted: If True, use distances as weights
        symmetric: If True, symmetrize the graph
        
    Returns:
        Adjacency matrix (n_points, n_points)
    """
    if len(points) < k:
        k = len(points) - 1
    
    # Build kNN graph
    mode = 'distance' if weighted else 'connectivity'
    graph = kneighbors_graph(
        points, k, mode=mode, include_self=False
    )
    
    # Convert to dense array
    adj_matrix = graph.toarray()
    
    # Symmetrize if requested
    if symmetric:
        adj_matrix = (adj_matrix + adj_matrix.T) / 2
    
    return adj_matrix


def build_epsilon_graph(points: np.ndarray,
                       epsilon: Optional[float] = None,
                       weighted: bool = True,
                       auto_epsilon_percentile: float = 50.0) -> np.ndarray:
    """
    Build epsilon-neighborhood graph.
    
    Args:
        points: Point cloud (n_points, n_features)
        epsilon: Distance threshold (auto-computed if None)
        weighted: If True, use distances as weights
        auto_epsilon_percentile: Percentile for auto epsilon selection
        
    Returns:
        Adjacency matrix (n_points, n_points)
    """
    # Compute distance matrix
    dist_matrix = squareform(pdist(points))
    
    # Auto-select epsilon if not provided
    if epsilon is None:
        # Use percentile of pairwise distances
        epsilon = np.percentile(dist_matrix[dist_matrix > 0], auto_epsilon_percentile)
    
    if weighted:
        # Use distances as weights, zero out beyond epsilon
        adj_matrix = np.where(dist_matrix <= epsilon, dist_matrix, 0.0)
    else:
        # Binary adjacency
        adj_matrix = (dist_matrix <= epsilon).astype(float)
    
    # Zero out diagonal
    np.fill_diagonal(adj_matrix, 0.0)
    
    return adj_matrix


def build_rips_graph(points: np.ndarray,
                    max_edge_length: Optional[float] = None,
                    percentile: float = 75.0) -> Tuple[np.ndarray, float]:
    """
    Build Vietoris-Rips graph for TDA.
    
    Args:
        points: Point cloud (n_points, n_features)
        max_edge_length: Maximum edge length (auto if None)
        percentile: Percentile for auto max_edge_length
        
    Returns:
        (adjacency_matrix, max_edge_length)
    """
    # Compute distance matrix
    dist_matrix = squareform(pdist(points))
    
    # Auto-select max edge length
    if max_edge_length is None:
        max_edge_length = np.percentile(
            dist_matrix[dist_matrix > 0], 
            percentile
        )
    
    # Build adjacency matrix (weighted by distance)
    adj_matrix = np.where(
        dist_matrix <= max_edge_length,
        dist_matrix,
        0.0
    )
    
    # Zero out diagonal
    np.fill_diagonal(adj_matrix, 0.0)
    
    return adj_matrix, max_edge_length


def compute_graph_laplacian(adj_matrix: np.ndarray,
                           normalized: bool = True,
                           regularization: float = 1e-10) -> np.ndarray:
    """
    Compute graph Laplacian from adjacency matrix.
    
    Args:
        adj_matrix: Adjacency matrix (n, n)
        normalized: If True, compute normalized Laplacian
        regularization: Small value added to degrees for stability
        
    Returns:
        Laplacian matrix (n, n)
    """
    # Compute degree matrix
    degrees = np.sum(adj_matrix, axis=1) + regularization
    
    if normalized:
        # Normalized Laplacian: L = I - D^{-1/2} A D^{-1/2}
        D_inv_sqrt = np.diag(1.0 / np.sqrt(degrees))
        L = np.eye(len(adj_matrix)) - D_inv_sqrt @ adj_matrix @ D_inv_sqrt
    else:
        # Unnormalized Laplacian: L = D - A
        D = np.diag(degrees)
        L = D - adj_matrix
    
    return L


def compute_distance_matrix(points: np.ndarray,
                           metric: str = 'euclidean') -> np.ndarray:
    """
    Compute pairwise distance matrix.
    
    Args:
        points: Point cloud (n_points, n_features)
        metric: Distance metric ('euclidean', 'manhattan', 'cosine', etc.)
        
    Returns:
        Distance matrix (n_points, n_points)
    """
    return squareform(pdist(points, metric=metric))


def compute_adjacency_statistics(adj_matrix: np.ndarray) -> dict:
    """
    Compute statistics of adjacency matrix.
    
    Args:
        adj_matrix: Adjacency matrix
        
    Returns:
        Dictionary of statistics
    """
    n = len(adj_matrix)
    
    # Degree statistics
    degrees = np.sum(adj_matrix > 0, axis=1)
    
    # Edge statistics
    n_edges = np.sum(adj_matrix > 0) / 2  # Undirected
    
    # Weight statistics (if weighted)
    weights = adj_matrix[adj_matrix > 0]
    
    return {
        'n_nodes': n,
        'n_edges': int(n_edges),
        'density': n_edges / (n * (n - 1) / 2) if n > 1 else 0,
        'mean_degree': float(degrees.mean()),
        'max_degree': int(degrees.max()),
        'min_degree': int(degrees.min()),
        'mean_weight': float(weights.mean()) if len(weights) > 0 else 0,
        'max_weight': float(weights.max()) if len(weights) > 0 else 0,
    }


def prune_isolated_nodes(adj_matrix: np.ndarray,
                        min_degree: int = 1) -> Tuple[np.ndarray, np.ndarray]:
    """
    Remove isolated nodes from graph.
    
    Args:
        adj_matrix: Adjacency matrix
        min_degree: Minimum degree to keep node
        
    Returns:
        (pruned_adjacency, kept_indices)
    """
    degrees = np.sum(adj_matrix > 0, axis=1)
    keep_mask = degrees >= min_degree
    keep_indices = np.where(keep_mask)[0]
    
    # Extract submatrix
    pruned = adj_matrix[np.ix_(keep_indices, keep_indices)]
    
    return pruned, keep_indices


def add_self_loops(adj_matrix: np.ndarray, weight: float = 1.0) -> np.ndarray:
    """
    Add self-loops to graph.
    
    Args:
        adj_matrix: Adjacency matrix
        weight: Weight for self-loops
        
    Returns:
        Adjacency matrix with self-loops
    """
    adj_with_loops = adj_matrix.copy()
    np.fill_diagonal(adj_with_loops, weight)
    return adj_with_loops


def compute_graph_spectrum(laplacian: np.ndarray,
                          k: Optional[int] = None) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute eigenvalues and eigenvectors of graph Laplacian.
    
    Args:
        laplacian: Graph Laplacian
        k: Number of eigenvalues to compute (all if None)
        
    Returns:
        (eigenvalues, eigenvectors)
    """
    if k is None or k >= len(laplacian) - 1:
        # Compute all eigenvalues
        eigenvalues, eigenvectors = np.linalg.eigh(laplacian)
    else:
        # Compute k smallest eigenvalues
        from scipy.sparse.linalg import eigsh
        eigenvalues, eigenvectors = eigsh(laplacian, k=k, which='SM')
    
    # Sort by eigenvalue
    idx = np.argsort(eigenvalues)
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]
    
    return eigenvalues, eigenvectors

