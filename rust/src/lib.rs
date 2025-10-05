//! TCDB Core - Topological Data Analysis in Rust
//! 
//! High-performance topological computations with Python bindings.

pub mod simplicial_complex;
pub mod filtration;
pub mod persistent_homology;
pub mod bindings;

pub use simplicial_complex::{SimplicialComplex, Simplex};
pub use filtration::{Filtration, FiltrationValue};
pub use persistent_homology::{PersistentHomology, Barcode, PersistenceDiagram};

use thiserror::Error;

#[derive(Error, Debug)]
pub enum TcdbError {
    #[error("Invalid simplex dimension: {0}")]
    InvalidDimension(usize),
    
    #[error("Simplex not found in complex")]
    SimplexNotFound,
    
    #[error("Invalid filtration value")]
    InvalidFiltration,
    
    #[error("Computation error: {0}")]
    ComputationError(String),
}

pub type Result<T> = std::result::Result<T, TcdbError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_library_loads() {
        // Smoke test - library compiles and loads
        assert!(true);
    }
}

