from abc import ABC, abstractmethod
import numpy as np
from typing import Dict, Any, List, Tuple

class EmbeddingModule(ABC):
    @abstractmethod
    def fit_transform(self, X: np.ndarray) -> np.ndarray:
        pass
    
    @abstractmethod
    def get_metadata(self) -> Dict[str, Any]:
        pass

class TDAModule(ABC):
    @abstractmethod
    def compute_persistence(self, embeddings: np.ndarray) -> List[Tuple]:
        pass
    
    @abstractmethod
    def extract_features(self, persistence: List[Tuple]) -> Dict[str, float]:
        pass
    
    @abstractmethod
    def get_metadata(self) -> Dict[str, Any]:
        pass

class DownstreamModule(ABC):
    @abstractmethod
    def train(self, X: np.ndarray, y: np.ndarray) -> None:
        pass
    
    @abstractmethod
    def evaluate(self, X: np.ndarray, y: np.ndarray) -> Dict[str, float]:
        pass
    
    @abstractmethod
    def get_metadata(self) -> Dict[str, Any]:
        pass