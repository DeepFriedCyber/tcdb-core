import numpy as np
from core.interfaces import EmbeddingModule
from typing import Dict, Any

class StandardEmbedding(EmbeddingModule):
    def __init__(self):
        self.name = "StandardEmbedding"
    
    def fit_transform(self, X: np.ndarray) -> np.ndarray:
        return X.copy()
    
    def get_metadata(self) -> Dict[str, Any]:
        return {'name': self.name, 'type': 'baseline'}