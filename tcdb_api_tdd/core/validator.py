import numpy as np
from typing import List, Dict

class CoreValidator:
    def __init__(self, strict_mode: bool = True):
        self.strict_mode = strict_mode
        self.violations = []

    def validate_embeddings(self, embeddings: np.ndarray) -> bool:
        if not isinstance(embeddings, np.ndarray):
            self._log_violation("Embeddings must be numpy array")
            return False
        if len(embeddings.shape) != 2:
            self._log_violation("Embeddings must be 2D array")
            return False
        if np.any(np.isnan(embeddings)) or np.any(np.isinf(embeddings)):
            self._log_violation("Embeddings contain NaN or Inf")
            return False
        return True

    def validate_persistence(self, persistence: List) -> bool:
        if not isinstance(persistence, list):
            self._log_violation("Persistence must be a list")
            return False
        for pt in persistence:
            if not isinstance(pt, tuple) or len(pt) != 2:
                self._log_violation("Invalid persistence format")
                return False
        return True

    def validate_features(self, features: Dict[str, float]) -> bool:
        if not isinstance(features, dict):
            self._log_violation("Features must be a dictionary")
            return False
        for key, value in features.items():
            if not isinstance(value, (int, float, np.integer, np.floating)):
                self._log_violation(f"Feature {key} has invalid type")
                return False
            if np.isnan(value) or np.isinf(value):
                self._log_violation(f"Feature {key} is NaN or Inf")
                return False
        return True

    def _log_violation(self, message: str):
        self.violations.append(message)
        if self.strict_mode:
            raise ValueError(f"Core invariant violated: {message}")

    def get_violations(self) -> List[str]:
        return self.violations.copy()

    def clear_violations(self):
        self.violations.clear()
