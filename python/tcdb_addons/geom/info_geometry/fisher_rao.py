
import numpy as np

class FisherRaoMetric:
    def __init__(self, dist: str="gaussian"):
        self.dist = dist

    def gram(self, X: np.ndarray) -> np.ndarray:
        X = np.asarray(X, float)
        Xc = X - X.mean(0, keepdims=True)
        G = Xc @ Xc.T
        denom = np.linalg.norm(G) or 1.0
        return G / denom
