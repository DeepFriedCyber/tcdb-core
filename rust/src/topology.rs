//! Topological Signature Generation
//! 
//! Implements topological signature computation for embeddings using persistent homology.

use crate::{Result, PersistenceDiagram};
use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Captures an embedding with its source information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingCapture {
    pub embedding: Vec<f64>,
    pub source: String,
}

impl EmbeddingCapture {
    /// Create a new embedding capture
    pub fn new(embedding: Vec<f64>, source: &str) -> Self {
        Self {
            embedding,
            source: source.to_string(),
        }
    }

    /// Compute topological signature for this embedding
    pub fn compute_signature(&self) -> TopologicalSignature {
        // Convert flat embedding to point cloud (assume 3D for now)
        let points = self.embedding_to_points();
        
        // Compute Vietoris-Rips complex and persistent homology
        let persistence_diagram = self.compute_persistence_diagram(&points);
        let betti_numbers = self.compute_betti_numbers(&persistence_diagram);
        
        // Generate hash
        let hash = self.compute_hash(&persistence_diagram, &betti_numbers);
        
        TopologicalSignature {
            persistence_diagram,
            betti_numbers,
            hash,
        }
    }

    fn embedding_to_points(&self) -> Vec<Vec<f64>> {
        if self.embedding.is_empty() {
            return vec![];
        }

        // For simplicity, assume 3D points
        let dim = 3;
        let mut points = Vec::new();
        
        for chunk in self.embedding.chunks(dim) {
            if chunk.len() == dim {
                points.push(chunk.to_vec());
            }
        }
        
        points
    }

    fn compute_persistence_diagram(&self, points: &[Vec<f64>]) -> PersistenceDiagram {
        if points.is_empty() {
            return PersistenceDiagram::new(0);
        }

        // Simple implementation - in practice would use proper Vietoris-Rips
        let mut diagram = PersistenceDiagram::new(0);
        
        // Add connected components (0-dimensional features)
        for _point in points.iter() {
            diagram.add_point(0.0, f64::INFINITY); // Each point is a connected component
        }
        
        diagram
    }

    fn compute_betti_numbers(&self, diagram: &PersistenceDiagram) -> Vec<usize> {
        // Simple computation of Betti numbers from persistence diagram
        let mut betti = vec![0; 3]; // B0, B1, B2
        
        for point in &diagram.points {
            if point.dimension < betti.len() {
                if point.is_infinite() {
                    betti[point.dimension] += 1;
                }
            }
        }
        
        betti
    }

    fn compute_hash(&self, diagram: &PersistenceDiagram, betti: &[usize]) -> String {
        let mut hasher = DefaultHasher::new();

        // Hash the original embedding data for uniqueness
        for &value in &self.embedding {
            value.to_bits().hash(&mut hasher);
        }

        // Hash the persistence diagram
        for point in &diagram.points {
            point.birth.to_bits().hash(&mut hasher);
            if !point.death.is_infinite() {
                point.death.to_bits().hash(&mut hasher);
            }
            point.dimension.hash(&mut hasher);
        }

        // Hash the Betti numbers
        betti.hash(&mut hasher);

        format!("{:x}", hasher.finish())
    }
}

/// Topological signature containing persistence information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TopologicalSignature {
    pub persistence_diagram: PersistenceDiagram,
    pub betti_numbers: Vec<usize>,
    pub hash: String,
}

impl TopologicalSignature {
    /// Check if this signature is valid
    pub fn is_valid(&self) -> bool {
        // Basic validation
        !self.hash.is_empty() &&
        !self.betti_numbers.is_empty()
    }
}

/// Vietoris-Rips complex computation (simplified)
pub struct VietorisRips {
    pub epsilon: f64,
}

impl VietorisRips {
    pub fn new(epsilon: f64) -> Self {
        Self { epsilon }
    }

    pub fn compute_complex(&self, points: &[Vec<f64>]) -> Result<Vec<Vec<usize>>> {
        if points.is_empty() {
            return Ok(vec![]);
        }

        let mut simplices = Vec::new();
        
        // Add vertices (0-simplices)
        for i in 0..points.len() {
            simplices.push(vec![i]);
        }
        
        // Add edges (1-simplices) for points within epsilon distance
        for i in 0..points.len() {
            for j in (i + 1)..points.len() {
                if self.distance(&points[i], &points[j]) <= self.epsilon {
                    simplices.push(vec![i, j]);
                }
            }
        }
        
        Ok(simplices)
    }

    fn distance(&self, p1: &[f64], p2: &[f64]) -> f64 {
        if p1.len() != p2.len() {
            return f64::INFINITY;
        }
        
        p1.iter()
            .zip(p2.iter())
            .map(|(a, b)| (a - b).powi(2))
            .sum::<f64>()
            .sqrt()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_embedding_capture_creation() {
        let embedding = vec![1.0, 2.0, 3.0];
        let capture = EmbeddingCapture::new(embedding.clone(), "test_source");
        
        assert_eq!(capture.embedding, embedding);
        assert_eq!(capture.source, "test_source");
    }

    #[test]
    fn test_signature_validation() {
        let mut diagram = PersistenceDiagram::new(0);
        diagram.add_point(0.0, 1.0);
        
        let signature = TopologicalSignature {
            persistence_diagram: diagram,
            betti_numbers: vec![1, 0, 0],
            hash: "test_hash".to_string(),
        };
        
        assert!(signature.is_valid());
    }

    #[test]
    fn test_vietoris_rips_empty() {
        let vr = VietorisRips::new(1.0);
        let result = vr.compute_complex(&[]).unwrap();
        assert!(result.is_empty());
    }
}
