"""
Pipeline utilities for descriptor computation

Provides utilities for:
- Graph construction (kNN, epsilon-graphs)
- Filtration building
- Embedding extraction
- Laplacian computation
"""

from .build_graph import (
    build_knn_graph,
    build_epsilon_graph,
    build_rips_graph,
    compute_graph_laplacian
)

from .filtrations import (
    build_vr_filtration,
    build_alpha_filtration,
    build_weighted_filtration
)

from .embeddings import (
    extract_layer_embeddings,
    extract_attention_weights,
    batch_process_embeddings
)

__all__ = [
    # Graph construction
    'build_knn_graph',
    'build_epsilon_graph',
    'build_rips_graph',
    'compute_graph_laplacian',
    
    # Filtrations
    'build_vr_filtration',
    'build_alpha_filtration',
    'build_weighted_filtration',
    
    # Embeddings
    'extract_layer_embeddings',
    'extract_attention_weights',
    'batch_process_embeddings',
]

