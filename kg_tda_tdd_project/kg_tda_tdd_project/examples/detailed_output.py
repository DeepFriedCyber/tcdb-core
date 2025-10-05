#!/usr/bin/env python3
import numpy as np
import pandas as pd
from modules.embeddings.standard import StandardEmbedding
from modules.tda.rips import RipsTDA
from modules.downstream.classifier import ClassificationModule
from modular_harness import ModularHarness

def main():
    pd.set_option('display.max_columns', None)
    pd.set_option('display.width', None)
    pd.set_option('display.max_colwidth', None)

    print('TDD Modular KG with TDA - Detailed Output')
    print('=' * 80)

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

    print('Running pipeline...')
    harness.run(X, y)

    print('\nFull Results:')
    df = harness.summary()
    print(df.to_string())

    print('\n' + '=' * 80)
    print('Feature Breakdown:')
    for result in harness.results:
        print(f'\nEmbedding: {result["embedding"]} + TDA: {result["tda"]}')
        print(f'  Embedding Time: {result["embedding_time"]:.4f}s')
        print(f'  TDA Time: {result["tda_time"]:.4f}s')
        print(f'  Features extracted:')
        for k, v in result['features'].items():
            print(f'    {k}: {v:.4f}')
        print(f'  Downstream Scores:')
        for ds_name, scores in result['downstream_scores'].items():
            for metric, value in scores.items():
                print(f'    {ds_name}_{metric}: {value:.4f}')

if __name__ == '__main__':
    main()

