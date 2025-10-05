"""
TCDB API - Python interface to Rust-powered topological data analysis

This package provides a high-level Python API for topological computations,
backed by verified Rust implementations.
"""

__version__ = "1.0.0"

# Import Rust bindings
try:
    from tcdb_core import Simplex, SimplicialComplex, PersistenceDiagram
    RUST_AVAILABLE = True
except ImportError:
    RUST_AVAILABLE = False
    import warnings
    warnings.warn(
        "Rust bindings not available. Install with: maturin develop",
        ImportWarning
    )

# Import Python API
from .app import create_app
from .endpoints.pipeline import run_pipeline
from .endpoints.tda import compute_persistence

__all__ = [
    'create_app',
    'run_pipeline',
    'compute_persistence',
    'Simplex',
    'SimplicialComplex',
    'PersistenceDiagram',
    'RUST_AVAILABLE',
]

