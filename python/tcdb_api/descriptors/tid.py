"""
Topological-Information Descriptor (TID)

Turns topology into unit-free statistics using:
1. Persistence entropy from persistence diagrams
2. Betti curve total variation
3. Persistence landscape shape spread

All outputs are dimensionless ratios or probabilities.
"""

import numpy as np
from typing import Dict, Any, Optional, List, Tuple
from .base import Descriptor, compute_entropy


class TopologicalInformationDescriptor(Descriptor):
    """
    Topological-Information Descriptor (TID)
    
    Computes dimensionless topological features using:
    - Persistence entropy (information-theoretic)
    - Betti curve total variation (topological stability)
    - Persistence landscape ratios (shape spread)
    
    All features are scale-free and dimensionless.
    """
    
    name = "tid"
    
    def __init__(self, 
                 max_dimension: int = 2,
                 max_edge_length: Optional[float] = None,
                 n_bins: int = 100,
                 alpha_weights: Optional[Dict[int, float]] = None,
                 beta_weights: Optional[Dict[int, float]] = None,
                 gamma_weights: Optional[Dict[int, float]] = None):
        """
        Initialize TID descriptor.
        
        Args:
            max_dimension: Maximum homology dimension to compute
            max_edge_length: Maximum edge length for Rips complex (auto if None)
            n_bins: Number of bins for Betti curve discretization
            alpha_weights: Weights for persistence entropy per dimension
            beta_weights: Weights for total variation per dimension
            gamma_weights: Weights for landscape ratio per dimension
        """
        super().__init__(
            max_dimension=max_dimension,
            max_edge_length=max_edge_length,
            n_bins=n_bins
        )
        
        # Default weights (equal across dimensions)
        self.alpha_weights = alpha_weights or {k: 1.0 for k in range(max_dimension + 1)}
        self.beta_weights = beta_weights or {k: 1.0 for k in range(max_dimension + 1)}
        self.gamma_weights = gamma_weights or {k: 1.0 for k in range(max_dimension + 1)}
    
    def compute(self, data: np.ndarray, **kwargs) -> Dict[str, float]:
        """
        Compute TID features from point cloud.
        
        Args:
            data: Point cloud (n_points, n_features)
            **kwargs: Additional parameters
            
        Returns:
            Dictionary with dimensionless features:
            - F_TID: Combined descriptor value
            - H{k}: Persistence entropy for dimension k
            - TV{k}: Total variation for dimension k
            - L{k}: Landscape ratio for dimension k
        """
        self.validate_data(data, min_points=3)
        
        # Compute persistence diagrams
        diagrams = self._compute_persistence_diagrams(data)
        
        results = {}
        f_tid = 0.0
        
        # Process each dimension
        for dim, diagram in diagrams.items():
            if len(diagram) == 0:
                continue
            
            # 1. Persistence entropy
            H_k = self._persistence_entropy(diagram)
            results[f'H{dim}'] = H_k
            f_tid += self.alpha_weights.get(dim, 1.0) * H_k
            
            # 2. Betti curve total variation
            TV_k = self._betti_curve_total_variation(diagram)
            results[f'TV{dim}'] = TV_k
            f_tid += self.beta_weights.get(dim, 1.0) * TV_k
            
            # 3. Landscape ratio
            L_k = self._landscape_ratio(diagram)
            results[f'L{dim}'] = L_k
            f_tid += self.gamma_weights.get(dim, 1.0) * L_k
        
        results['F_TID'] = f_tid
        
        return results
    
    def _compute_persistence_diagrams(self, data: np.ndarray) -> Dict[int, np.ndarray]:
        """
        Compute persistence diagrams using Ripser.
        
        Args:
            data: Point cloud
            
        Returns:
            Dictionary mapping dimension to persistence diagram
        """
        try:
            from ripser import ripser
        except ImportError:
            raise ImportError("ripser is required for TID. Install with: pip install ripser")
        
        # Determine max edge length if not specified
        max_edge = self.params.get('max_edge_length')
        if max_edge is None:
            from scipy.spatial.distance import pdist
            distances = pdist(data)
            max_edge = np.percentile(distances, 90)  # Use 90th percentile
        
        # Compute persistence
        result = ripser(
            data,
            maxdim=self.params['max_dimension'],
            thresh=max_edge
        )
        
        # Extract diagrams per dimension
        diagrams = {}
        for dim in range(self.params['max_dimension'] + 1):
            dgm = result['dgms'][dim]
            # Filter out infinite points and ensure valid intervals
            dgm = dgm[np.isfinite(dgm).all(axis=1)]
            dgm = dgm[dgm[:, 1] > dgm[:, 0]]  # death > birth
            diagrams[dim] = dgm
        
        return diagrams
    
    def _persistence_entropy(self, diagram: np.ndarray) -> float:
        """
        Compute persistence entropy.
        
        Args:
            diagram: Persistence diagram (n_points, 2) with (birth, death)
            
        Returns:
            Normalized persistence entropy (dimensionless)
        """
        if len(diagram) == 0:
            return 0.0
        
        # Compute lifetimes
        lifetimes = diagram[:, 1] - diagram[:, 0]
        
        # Normalize to probabilities
        total_persistence = lifetimes.sum()
        if total_persistence < 1e-10:
            return 0.0
        
        probabilities = lifetimes / total_persistence
        
        # Compute entropy
        entropy = compute_entropy(probabilities, base=2.0)
        
        # Normalize by maximum possible entropy (log2(n))
        max_entropy = np.log2(len(diagram)) if len(diagram) > 1 else 1.0
        
        return self.safe_divide(entropy, max_entropy, default=0.0)
    
    def _betti_curve_total_variation(self, diagram: np.ndarray) -> float:
        """
        Compute total variation of Betti curve.
        
        Args:
            diagram: Persistence diagram
            
        Returns:
            Normalized total variation (dimensionless)
        """
        if len(diagram) == 0:
            return 0.0
        
        # Get birth and death times
        births = diagram[:, 0]
        deaths = diagram[:, 1]
        
        # Create normalized time axis [0, 1]
        min_time = births.min()
        max_time = deaths.max()
        time_range = max_time - min_time
        
        if time_range < 1e-10:
            return 0.0
        
        # Normalize times to [0, 1]
        births_norm = (births - min_time) / time_range
        deaths_norm = (deaths - min_time) / time_range
        
        # Compute Betti curve on normalized axis
        n_bins = self.params.get('n_bins', 100)
        tau = np.linspace(0, 1, n_bins)
        betti = np.zeros(n_bins)
        
        for i in range(len(diagram)):
            # Count features alive at each time
            mask = (tau >= births_norm[i]) & (tau <= deaths_norm[i])
            betti[mask] += 1
        
        # Compute total variation (sum of absolute differences)
        tv = np.sum(np.abs(np.diff(betti)))
        
        # Normalize by number of features (dimensionless)
        return self.safe_divide(tv, len(diagram), default=0.0)
    
    def _landscape_ratio(self, diagram: np.ndarray) -> float:
        """
        Compute persistence landscape ratio (L1 / L∞).
        
        Args:
            diagram: Persistence diagram
            
        Returns:
            Landscape ratio (dimensionless)
        """
        if len(diagram) == 0:
            return 0.0
        
        # Compute lifetimes (landscape amplitudes)
        lifetimes = diagram[:, 1] - diagram[:, 0]
        
        # L1 norm (sum of lifetimes)
        l1_norm = np.sum(lifetimes)
        
        # L∞ norm (max lifetime)
        linf_norm = np.max(lifetimes)
        
        # Ratio is dimensionless
        return self.safe_divide(l1_norm, linf_norm * len(diagram), default=0.0)
    
    def compute_betti_numbers(self, data: np.ndarray) -> Dict[int, int]:
        """
        Compute Betti numbers at maximum filtration value.
        
        Args:
            data: Point cloud
            
        Returns:
            Dictionary mapping dimension to Betti number
        """
        diagrams = self._compute_persistence_diagrams(data)
        
        betti_numbers = {}
        for dim, diagram in diagrams.items():
            # Count features that persist to the end
            # (infinite death time or very long persistence)
            if len(diagram) > 0:
                lifetimes = diagram[:, 1] - diagram[:, 0]
                # Features with persistence > 50% of max are considered significant
                threshold = 0.5 * lifetimes.max() if len(lifetimes) > 0 else 0
                betti_numbers[dim] = np.sum(lifetimes > threshold)
            else:
                betti_numbers[dim] = 0
        
        return betti_numbers

