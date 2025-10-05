#!/usr/bin/env python3
import numpy as np
from modules.embeddings.standard import StandardEmbedding
from modules.tda.rips import RipsTDA
from modules.downstream.classifier import ClassificationModule
from modular_harness import ModularHarness

def main():
    print("TDD Modular KG with TDA - Basic Example")
    print("=" * 60)
    
    # Generate data
    np.random.seed(42)
    X = np.random.rand(100, 4)
    y = np.random.randint(0, 2, 100)
    
    # Setup modules
    embedding_modules = {'Standard': StandardEmbedding()}
    tda_modules = {'Rips': RipsTDA(max_edge_length=0.5, max_dimension=2)}
    downstream_modules = {'Classifier': ClassificationModule(n_estimators=50, cv=3)}
    
    # Run harness
    harness = ModularHarness(
        embedding_modules=embedding_modules,
        tda_modules=tda_modules,
        downstream_modules=downstream_modules,
        n_jobs=1
    )
    
    print("Running...")
    harness.run(X, y)
    
    print("\nResults:")
    df = harness.summary()
    print(df)
    
    best = harness.get_best_module_combination('Classifier_mean_accuracy')
    if best:
        print(f"\nBest: {best['embedding']} + {best['tda']}")
        print(f"Accuracy: {best['downstream_scores']['Classifier']['mean_accuracy']:.4f}")

if __name__ == '__main__':
    main()