import pytest
import numpy as np
from core.validator import CoreValidator

class TestCoreValidator:
    def test_valid_embeddings(self):
        validator = CoreValidator(strict_mode=False)
        valid = np.random.rand(10, 4)
        assert validator.validate_embeddings(valid) is True
    
    def test_reject_nan_embeddings(self):
        validator = CoreValidator(strict_mode=False)
        invalid = np.array([[1.0, np.nan]])
        assert validator.validate_embeddings(invalid) is False
    
    def test_valid_persistence(self):
        validator = CoreValidator(strict_mode=False)
        valid = [(0, (0.0, 0.5)), (1, (0.1, 0.8))]
        assert validator.validate_persistence(valid) is True
    
    def test_valid_features(self):
        validator = CoreValidator(strict_mode=False)
        valid = {'num_h1': 5, 'max_lifetime': 0.8}
        assert validator.validate_features(valid) is True