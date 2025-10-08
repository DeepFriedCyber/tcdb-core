"""
Filtration construction utilities

Provides functions for building various types of filtrations:
- Vietoris-Rips
- Alpha complex
- Weighted filtrations
"""

import numpy as np
from typing import List, Tuple, Optional, Dict
from scipy.spatial.distance import pdist, squareform


def build_vr_filtration(points: np.ndarray,
                       max_dimension: int = 2,
                       max_edge_length: Optional[float] = None) -> Dict:
    """
    Build Vietoris-Rips filtration.
    
    Args:
        points: Point cloud (n_points, n_features)
        max_dimension: Maximum simplex dimension
        max_edge_length: Maximum edge length (auto if None)
        
    Returns:
        Dictionary with filtration data
    """
    # Compute distance matrix
    dist_matrix = squareform(pdist(points))
    
    # Auto-select max edge length
    if max_edge_length is None:
        max_edge_length = np.percentile(dist_matrix[dist_matrix > 0], 75)
    
    # Build simplices with filtration values
    simplices = []
    
    # 0-simplices (vertices) - appear at time 0
    for i in range(len(points)):
        simplices.append({
            'vertices': [i],
            'dimension': 0,
            'filtration_value': 0.0
        })
    
    # 1-simplices (edges) - appear at distance between points
    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            dist = dist_matrix[i, j]
            if dist <= max_edge_length:
                simplices.append({
                    'vertices': [i, j],
                    'dimension': 1,
                    'filtration_value': dist
                })
    
    # Higher-dimensional simplices (if requested)
    if max_dimension >= 2:
        # For simplicity, only add 2-simplices (triangles)
        # Full implementation would use incremental algorithm
        for i in range(len(points)):
            for j in range(i + 1, len(points)):
                for k in range(j + 1, len(points)):
                    # Triangle appears when longest edge appears
                    d_ij = dist_matrix[i, j]
                    d_jk = dist_matrix[j, k]
                    d_ik = dist_matrix[i, k]
                    
                    max_dist = max(d_ij, d_jk, d_ik)
                    
                    if max_dist <= max_edge_length:
                        simplices.append({
                            'vertices': [i, j, k],
                            'dimension': 2,
                            'filtration_value': max_dist
                        })
    
    # Sort by filtration value
    simplices.sort(key=lambda s: s['filtration_value'])
    
    return {
        'simplices': simplices,
        'max_dimension': max_dimension,
        'max_edge_length': max_edge_length,
        'n_points': len(points)
    }


def build_alpha_filtration(points: np.ndarray,
                          max_dimension: int = 2) -> Dict:
    """
    Build Alpha complex filtration.
    
    Note: This is a simplified version. Full alpha complex
    requires Delaunay triangulation.
    
    Args:
        points: Point cloud (n_points, n_features)
        max_dimension: Maximum simplex dimension
        
    Returns:
        Dictionary with filtration data
    """
    # For 2D points, we can use Delaunay
    if points.shape[1] == 2:
        try:
            from scipy.spatial import Delaunay
            
            tri = Delaunay(points)
            simplices = []
            
            # Add vertices
            for i in range(len(points)):
                simplices.append({
                    'vertices': [i],
                    'dimension': 0,
                    'filtration_value': 0.0
                })
            
            # Add triangles from Delaunay
            for simplex in tri.simplices:
                # Compute circumradius
                pts = points[simplex]
                circumradius = _compute_circumradius_2d(pts)
                
                # Add edges
                for i in range(3):
                    for j in range(i + 1, 3):
                        edge = sorted([simplex[i], simplex[j]])
                        simplices.append({
                            'vertices': edge,
                            'dimension': 1,
                            'filtration_value': circumradius
                        })
                
                # Add triangle
                simplices.append({
                    'vertices': sorted(simplex.tolist()),
                    'dimension': 2,
                    'filtration_value': circumradius
                })
            
            # Remove duplicates and sort
            unique_simplices = _remove_duplicate_simplices(simplices)
            unique_simplices.sort(key=lambda s: s['filtration_value'])
            
            return {
                'simplices': unique_simplices,
                'max_dimension': max_dimension,
                'n_points': len(points)
            }
        except:
            pass
    
    # Fallback to Rips for higher dimensions or if Delaunay fails
    return build_vr_filtration(points, max_dimension)


def build_weighted_filtration(points: np.ndarray,
                             weights: np.ndarray,
                             max_dimension: int = 2) -> Dict:
    """
    Build weighted filtration using vertex weights.
    
    Args:
        points: Point cloud (n_points, n_features)
        weights: Vertex weights (n_points,)
        max_dimension: Maximum simplex dimension
        
    Returns:
        Dictionary with filtration data
    """
    # Normalize weights to [0, 1]
    weights = (weights - weights.min()) / (weights.max() - weights.min() + 1e-10)
    
    # Compute distance matrix
    dist_matrix = squareform(pdist(points))
    
    simplices = []
    
    # 0-simplices appear at their weight value
    for i in range(len(points)):
        simplices.append({
            'vertices': [i],
            'dimension': 0,
            'filtration_value': weights[i]
        })
    
    # 1-simplices appear at max of endpoint weights and distance
    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            filt_val = max(weights[i], weights[j], dist_matrix[i, j])
            simplices.append({
                'vertices': [i, j],
                'dimension': 1,
                'filtration_value': filt_val
            })
    
    # 2-simplices
    if max_dimension >= 2:
        for i in range(len(points)):
            for j in range(i + 1, len(points)):
                for k in range(j + 1, len(points)):
                    filt_val = max(
                        weights[i], weights[j], weights[k],
                        dist_matrix[i, j], dist_matrix[j, k], dist_matrix[i, k]
                    )
                    simplices.append({
                        'vertices': [i, j, k],
                        'dimension': 2,
                        'filtration_value': filt_val
                    })
    
    simplices.sort(key=lambda s: s['filtration_value'])
    
    return {
        'simplices': simplices,
        'max_dimension': max_dimension,
        'n_points': len(points)
    }


def extract_persistence_pairs(filtration: Dict) -> List[Tuple[float, float, int]]:
    """
    Extract persistence pairs from filtration.
    
    Note: This is a placeholder. Full implementation requires
    persistence algorithm.
    
    Args:
        filtration: Filtration dictionary
        
    Returns:
        List of (birth, death, dimension) tuples
    """
    # Placeholder - would need full persistence computation
    pairs = []
    
    # Add one persistent component (connected component)
    pairs.append((0.0, float('inf'), 0))
    
    return pairs


def compute_betti_curve(filtration: Dict,
                       dimension: int = 0,
                       n_samples: int = 100) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute Betti curve for a given dimension.
    
    Args:
        filtration: Filtration dictionary
        dimension: Homology dimension
        n_samples: Number of sample points
        
    Returns:
        (filtration_values, betti_numbers)
    """
    simplices = filtration['simplices']
    
    # Get filtration value range
    filt_values = [s['filtration_value'] for s in simplices]
    min_val = min(filt_values)
    max_val = max(filt_values)
    
    # Sample filtration values
    sample_values = np.linspace(min_val, max_val, n_samples)
    
    # Placeholder Betti numbers (would need persistence computation)
    betti_numbers = np.zeros(n_samples)
    
    if dimension == 0:
        # Connected components decrease as edges are added
        n_points = filtration['n_points']
        betti_numbers[0] = n_points
        # Simplified: assume becomes connected
        betti_numbers[-1] = 1
        # Linear interpolation
        betti_numbers = np.linspace(n_points, 1, n_samples)
    
    return sample_values, betti_numbers


# Helper functions

def _compute_circumradius_2d(points: np.ndarray) -> float:
    """
    Compute circumradius of triangle in 2D.
    
    Args:
        points: Triangle vertices (3, 2)
        
    Returns:
        Circumradius
    """
    a, b, c = points
    
    # Side lengths
    ab = np.linalg.norm(b - a)
    bc = np.linalg.norm(c - b)
    ca = np.linalg.norm(a - c)
    
    # Area using cross product
    area = 0.5 * abs((b[0] - a[0]) * (c[1] - a[1]) - (c[0] - a[0]) * (b[1] - a[1]))
    
    if area < 1e-10:
        return max(ab, bc, ca)
    
    # Circumradius formula
    R = (ab * bc * ca) / (4 * area)
    
    return R


def _remove_duplicate_simplices(simplices: List[Dict]) -> List[Dict]:
    """
    Remove duplicate simplices, keeping minimum filtration value.
    
    Args:
        simplices: List of simplex dictionaries
        
    Returns:
        List of unique simplices
    """
    unique = {}
    
    for s in simplices:
        key = tuple(sorted(s['vertices']))
        if key not in unique or s['filtration_value'] < unique[key]['filtration_value']:
            unique[key] = s
    
    return list(unique.values())

