import pytest
import numpy as np
from modules.embeddings.standard import StandardEmbedding

class TestStandardEmbedding:
    def test_fit_transform_preserves_shape(self):
        module = StandardEmbedding()
        X = np.random.rand(10, 4)
        result = module.fit_transform(X)
        assert result.shape == X.shape
    
    def test_get_metadata(self):
        module = StandardEmbedding()
        metadata = module.get_metadata()
        assert 'name' in metadata