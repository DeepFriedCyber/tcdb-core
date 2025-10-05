import numpy as np
import gudhi
from core.interfaces import TDAModule
from typing import Dict, Any, List, Tuple

class RipsTDA(TDAModule):
    def __init__(self, max_edge_length: float = 0.5, max_dimension: int = 3):
        self.name = "RipsTDA"
        self.max_edge_length = max_edge_length
        self.max_dimension = max_dimension
    
    def compute_persistence(self, embeddings: np.ndarray) -> List[Tuple]:
        rips = gudhi.RipsComplex(points=embeddings, max_edge_length=self.max_edge_length)
        st = rips.create_simplex_tree(max_dimension=self.max_dimension)
        return st.persistence()
    
    def extract_features(self, persistence: List[Tuple]) -> Dict[str, float]:
        features = {}
        for dim in range(self.max_dimension + 1):
            h_features = [pt for pt in persistence if pt[0] == dim]
            lifetimes = [pt[1][1] - pt[1][0] for pt in h_features if pt[1][1] < float('inf')]
            features[f'num_h{dim}'] = len(h_features)
            features[f'max_h{dim}_lifetime'] = max(lifetimes) if lifetimes else 0.0
            features[f'mean_h{dim}_lifetime'] = np.mean(lifetimes) if lifetimes else 0.0
        return features
    
    def get_metadata(self) -> Dict[str, Any]:
        return {
            'name': self.name,
            'type': 'rips_complex',
            'max_edge_length': self.max_edge_length,
            'max_dimension': self.max_dimension
        }