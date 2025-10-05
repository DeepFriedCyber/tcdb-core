import numpy as np
import pandas as pd
import time
from joblib import Parallel, delayed
from typing import Dict, List, Any, Optional
from core.interfaces import EmbeddingModule, TDAModule, DownstreamModule
from core.validator import CoreValidator

class ModularHarness:
    def __init__(self, 
                 embedding_modules: Dict[str, EmbeddingModule],
                 tda_modules: Dict[str, TDAModule],
                 downstream_modules: Optional[Dict[str, DownstreamModule]] = None,
                 n_jobs: int = 1,
                 strict_validation: bool = True):
        self.embedding_modules = embedding_modules
        self.tda_modules = tda_modules
        self.downstream_modules = downstream_modules or {}
        self.n_jobs = n_jobs
        self.validator = CoreValidator(strict_mode=strict_validation)
        self.results = []
    
    def run(self, X: np.ndarray, y: Optional[np.ndarray] = None):
        tasks = []
        for emb_name, emb_mod in self.embedding_modules.items():
            for tda_name, tda_mod in self.tda_modules.items():
                tasks.append((emb_name, emb_mod, tda_name, tda_mod))
        
        results = Parallel(n_jobs=self.n_jobs)(
            delayed(self._run_single)(X, y, emb_name, emb_mod, tda_name, tda_mod)
            for emb_name, emb_mod, tda_name, tda_mod in tasks
        )
        
        self.results = [r for r in results if r is not None]
    
    def _run_single(self, X, y, emb_name, emb_mod, tda_name, tda_mod):
        try:
            self.validator.clear_violations()
            
            t0 = time.time()
            embeddings = emb_mod.fit_transform(X)
            t1 = time.time()
            
            if not self.validator.validate_embeddings(embeddings):
                return None
            
            persistence = tda_mod.compute_persistence(embeddings)
            t2 = time.time()
            
            if not self.validator.validate_persistence(persistence):
                return None
            
            features = tda_mod.extract_features(persistence)
            
            if not self.validator.validate_features(features):
                return None
            
            downstream_scores = {}
            if y is not None and self.downstream_modules:
                X_feat = self._features_to_array(features, len(y))
                for ds_name, ds_mod in self.downstream_modules.items():
                    try:
                        scores = ds_mod.evaluate(X_feat, y)
                        downstream_scores[ds_name] = scores
                    except Exception as e:
                        print(f"Downstream {ds_name} failed: {e}")
            
            return {
                'embedding': emb_name,
                'tda': tda_name,
                'embedding_time': t1 - t0,
                'tda_time': t2 - t1,
                'features': features,
                'downstream_scores': downstream_scores,
                'validation_passed': True
            }
        except Exception as e:
            print(f"Error in {emb_name} + {tda_name}: {e}")
            return None
    
    def _features_to_array(self, features: Dict[str, float], n_samples: int) -> np.ndarray:
        feat_vec = np.array([features[k] for k in sorted(features)])
        return np.repeat(feat_vec.reshape(1, -1), n_samples, axis=0)
    
    def summary(self) -> pd.DataFrame:
        if not self.results:
            return pd.DataFrame()
        
        summary_data = []
        for r in self.results:
            row = {
                'embedding': r['embedding'],
                'tda': r['tda'],
                'embedding_time': r['embedding_time'],
                'tda_time': r['tda_time'],
                'validation_passed': r['validation_passed']
            }
            row.update({k: v for k, v in r['features'].items()})
            for ds_name, scores in r['downstream_scores'].items():
                for metric, value in scores.items():
                    row[f'{ds_name}_{metric}'] = value
            summary_data.append(row)
        
        return pd.DataFrame(summary_data)
    
    def get_best_module_combination(self, metric: str) -> Dict[str, Any]:
        df = self.summary()
        if metric not in df.columns:
            return {}
        best_idx = df[metric].idxmax()
        return self.results[best_idx]