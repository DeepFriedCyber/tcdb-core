import numpy as np
from typing import Dict, Any

class StandardEmbedding:
    def __init__(self):
        self.name = "StandardEmbedding"

    def fit_transform(self, X: np.ndarray) -> np.ndarray:
        return X.copy()

    def get_metadata(self) -> Dict[str, Any]:
        return {'name': self.name, 'type': 'baseline'}
