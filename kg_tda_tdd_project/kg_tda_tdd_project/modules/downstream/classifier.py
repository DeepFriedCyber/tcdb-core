import numpy as np
from sklearn.ensemble import RandomForestClassifier
from sklearn.model_selection import cross_val_score
from core.interfaces import DownstreamModule
from typing import Dict, Any

class ClassificationModule(DownstreamModule):
    def __init__(self, n_estimators: int = 100, cv: int = 3):
        self.name = "ClassificationModule"
        self.n_estimators = n_estimators
        self.cv = cv
        self.model = RandomForestClassifier(n_estimators=n_estimators, random_state=42)
    
    def train(self, X: np.ndarray, y: np.ndarray) -> None:
        self.model.fit(X, y)
    
    def evaluate(self, X: np.ndarray, y: np.ndarray) -> Dict[str, float]:
        scores = cross_val_score(self.model, X, y, cv=self.cv)
        return {
            'mean_accuracy': float(scores.mean()),
            'std_accuracy': float(scores.std()),
            'min_accuracy': float(scores.min()),
            'max_accuracy': float(scores.max())
        }
    
    def get_metadata(self) -> Dict[str, Any]:
        return {
            'name': self.name,
            'type': 'classification',
            'n_estimators': self.n_estimators,
            'cv': self.cv
        }