import pytest
import numpy as np
from modules.tda.rips import RipsTDA

class TestRipsTDA:
    def test_compute_persistence(self):
        module = RipsTDA()
        embeddings = np.random.rand(20, 3)
        persistence = module.compute_persistence(embeddings)
        assert isinstance(persistence, list)
    
    def test_extract_features(self):
        module = RipsTDA()
        embeddings = np.random.rand(20, 3)
        persistence = module.compute_persistence(embeddings)
        features = module.extract_features(persistence)
        assert isinstance(features, dict)
        assert 'num_h0' in features