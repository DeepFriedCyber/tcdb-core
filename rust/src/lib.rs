//! TCDB Core - Topological Data Analysis in Rust
//! 
//! High-performance topological computations with Python bindings.

pub mod simplicial_complex;
pub mod filtration;
pub mod persistent_homology;
pub mod topology;
pub mod provenance;
pub mod data_proof;
pub mod cross_domain;
pub mod entropy;
pub mod reasoner;
pub mod embed;
pub mod streaming;
pub mod bayes;
pub mod euler;
pub mod bindings;

pub use simplicial_complex::{SimplicialComplex, Simplex};
pub use filtration::{Filtration, FiltrationValue};
pub use persistent_homology::{PersistentHomology, Barcode, PersistenceDiagram};
pub use topology::{EmbeddingCapture, TopologicalSignature, VietorisRips};
pub use provenance::{ProvenanceTracker, ReasoningStep, OperationType, ProvenanceGraph, Certificate, hash_persistence_diagram};
pub use data_proof::{DataFingerprint, DataProver, ModelAuditor, Dataset};
pub use cross_domain::{DomainMapper, PrincipleTransferEngine, DomainStructure};
pub use entropy::{shannon_entropy, persistence_entropy, normalized_entropy, self_information};
pub use reasoner::{Constraint, BettiCurve, PD, Violation, check};
pub use embed::{landscape_features, landscape_features_auto, landscape_distance, landscape_similarity};
pub use streaming::Streamer;
pub use bayes::{Evidence, Posterior, posterior, sequential_update};
pub use euler::FVector;

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

