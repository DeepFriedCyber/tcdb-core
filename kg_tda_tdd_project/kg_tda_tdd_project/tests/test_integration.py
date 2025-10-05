import pytest
import numpy as np
from modules.embeddings.standard import StandardEmbedding
from modules.tda.rips import RipsTDA
from modular_harness import ModularHarness

class TestIntegration:
    def test_harness_runs(self):
        X = np.random.rand(50, 4)
        embedding_modules = {'Standard': StandardEmbedding()}
        tda_modules = {'Rips': RipsTDA()}
        
        harness = ModularHarness(embedding_modules, tda_modules, n_jobs=1)
        harness.run(X)
        
        assert len(harness.results) > 0
    
    def test_harness_summary(self):
        X = np.random.rand(50, 4)
        embedding_modules = {'Standard': StandardEmbedding()}
        tda_modules = {'Rips': RipsTDA()}
        
        harness = ModularHarness(embedding_modules, tda_modules, n_jobs=1)
        harness.run(X)
        df = harness.summary()
        
        assert 'embedding' in df.columns
        assert 'tda' in df.columns