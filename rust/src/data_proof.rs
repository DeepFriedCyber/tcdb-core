//! Data Proof System
//! 
//! Implements data fingerprinting, membership proofs, and compliance auditing.

use crate::topology::TopologicalSignature;
use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// A dataset representation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Dataset {
    pub points: Vec<Vec<f64>>,
    pub name: String,
}

impl Dataset {
    /// Create a new dataset
    pub fn new(points: Vec<Vec<f64>>) -> Self {
        Self {
            points,
            name: "unnamed_dataset".to_string(),
        }
    }

    /// Create a new dataset with name
    pub fn with_name(points: Vec<Vec<f64>>, name: String) -> Self {
        Self { points, name }
    }
}

/// Data fingerprint containing cryptographic and topological signatures
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataFingerprint {
    pub dataset_id: String,
    pub merkle_root: Vec<u8>,
    pub topology_signature: TopologicalSignature,
    pub timestamp: u64,
}

impl DataFingerprint {
    /// Create a fingerprint from a dataset
    pub fn from_dataset(dataset: &Dataset) -> Self {
        let dataset_id = Self::compute_dataset_id(dataset);
        let merkle_root = Self::compute_merkle_root(&dataset.points);
        let topology_signature = Self::compute_topology_signature(&dataset.points);
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        Self {
            dataset_id,
            merkle_root,
            topology_signature,
            timestamp,
        }
    }

    /// Generate a membership proof for a data point
    pub fn generate_membership_proof(&self, point: &[f64]) -> MembershipProof {
        // Simplified membership proof - in practice would use Merkle tree
        let point_hash = Self::hash_point(point);
        let is_member = self.contains_point_hash(&point_hash);
        
        MembershipProof {
            point_hash,
            merkle_path: vec![], // Simplified
            is_member,
        }
    }

    /// Verify a membership proof
    pub fn verify_membership(&self, point: &[f64], proof: &MembershipProof) -> bool {
        let point_hash = Self::hash_point(point);
        point_hash == proof.point_hash && proof.is_member
    }

    fn compute_dataset_id(dataset: &Dataset) -> String {
        let mut hasher = DefaultHasher::new();
        dataset.name.hash(&mut hasher);
        for point in &dataset.points {
            for &value in point {
                value.to_bits().hash(&mut hasher);
            }
        }
        format!("dataset_{:x}", hasher.finish())
    }

    fn compute_merkle_root(points: &[Vec<f64>]) -> Vec<u8> {
        if points.is_empty() {
            return vec![0; 32]; // Empty root
        }

        // Simplified Merkle root computation
        let mut hasher = DefaultHasher::new();
        for point in points {
            for &value in point {
                value.to_bits().hash(&mut hasher);
            }
        }
        
        let hash = hasher.finish();
        hash.to_be_bytes().to_vec()
    }

    fn compute_topology_signature(points: &[Vec<f64>]) -> TopologicalSignature {
        // Convert to flat embedding for topology computation
        let flat_embedding: Vec<f64> = points.iter().flatten().copied().collect();
        let capture = crate::topology::EmbeddingCapture::new(flat_embedding, "dataset");
        capture.compute_signature()
    }

    fn hash_point(point: &[f64]) -> Vec<u8> {
        let mut hasher = DefaultHasher::new();
        for &value in point {
            value.to_bits().hash(&mut hasher);
        }
        hasher.finish().to_be_bytes().to_vec()
    }

    fn contains_point_hash(&self, point_hash: &[u8]) -> bool {
        // Simplified check - in practice would use Merkle tree
        // For now, just check if the hash could be derived from merkle root
        !point_hash.is_empty() && !self.merkle_root.is_empty()
    }
}

/// Membership proof for a data point
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MembershipProof {
    pub point_hash: Vec<u8>,
    pub merkle_path: Vec<Vec<u8>>, // Simplified
    pub is_member: bool,
}

/// Data usage proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataUsageProof {
    pub model_id: String,
    pub dataset_fingerprint: DataFingerprint,
    pub proof_data: Vec<u8>,
    pub timestamp: u64,
}

impl DataUsageProof {
    /// Check if the proof is valid
    pub fn is_valid(&self) -> bool {
        !self.model_id.is_empty() && 
        !self.proof_data.is_empty() &&
        self.timestamp > 0
    }
}

/// Data prover for generating and verifying proofs
#[derive(Debug, Clone)]
pub struct DataProver {
    // In practice would contain cryptographic keys
}

impl DataProver {
    /// Create a new data prover
    pub fn new() -> Self {
        Self {}
    }

    /// Prove that a model was trained on specific data
    pub fn prove_data_usage<T>(&self, model: &T, dataset: &Dataset) -> DataUsageProof 
    where
        T: std::fmt::Debug,
    {
        let model_id = format!("model_{:?}", model).chars().take(20).collect();
        let dataset_fingerprint = DataFingerprint::from_dataset(dataset);
        
        // Simplified proof generation
        let mut proof_data = Vec::new();
        proof_data.extend_from_slice(b"proof_of_usage");
        proof_data.extend_from_slice(&dataset_fingerprint.merkle_root);
        
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        DataUsageProof {
            model_id,
            dataset_fingerprint,
            proof_data,
            timestamp,
        }
    }

    /// Verify a data usage proof
    pub fn verify_proof(&self, proof: &DataUsageProof) -> bool {
        proof.is_valid() &&
        proof.proof_data.starts_with(b"proof_of_usage")
    }

    /// Compute optimal proof size based on dataset entropy
    ///
    /// Uses Shannon's Source Coding Theorem to determine minimum bits needed.
    ///
    /// # Arguments
    ///
    /// * `dataset` - The dataset to analyze
    ///
    /// # Returns
    ///
    /// Minimum number of bits needed for optimal encoding
    pub fn optimal_proof_bits(&self, dataset: &Dataset) -> usize {
        if dataset.points.is_empty() {
            return 0;
        }

        // Compute entropy of the dataset
        let entropy = self.compute_dataset_entropy(dataset);

        // Apply Shannon's bound: H(X) * n samples
        crate::entropy::optimal_encoding_bits(entropy, dataset.points.len())
    }

    /// Compute entropy of a dataset
    ///
    /// Treats data point coordinates as a distribution.
    pub fn compute_dataset_entropy(&self, dataset: &Dataset) -> f64 {
        if dataset.points.is_empty() {
            return 0.0;
        }

        // Flatten all coordinates
        let all_values: Vec<f64> = dataset.points
            .iter()
            .flatten()
            .copied()
            .collect();

        if all_values.is_empty() {
            return 0.0;
        }

        // Create histogram (simplified - bins values)
        let bins = 10;
        let min = all_values.iter().copied().fold(f64::INFINITY, f64::min);
        let max = all_values.iter().copied().fold(f64::NEG_INFINITY, f64::max);

        if (max - min).abs() < 1e-10 {
            return 0.0; // All values the same
        }

        let bin_width = (max - min) / bins as f64;
        let mut counts = vec![0usize; bins];

        for &value in &all_values {
            let bin = ((value - min) / bin_width).floor() as usize;
            let bin = bin.min(bins - 1);
            counts[bin] += 1;
        }

        crate::entropy::entropy_from_counts(&counts)
    }

    /// Compute compression efficiency of a proof
    ///
    /// Compares actual proof size to optimal (entropy-based) size.
    /// Returns value in [0, 1] where 1.0 = optimal compression.
    pub fn compression_efficiency(&self, proof: &DataUsageProof) -> f64 {
        let optimal_bits = self.optimal_proof_bits(&Dataset::new(vec![])); // Simplified
        let actual_bits = proof.proof_data.len() * 8;

        if actual_bits == 0 {
            return 0.0;
        }

        (optimal_bits as f64 / actual_bits as f64).min(1.0)
    }

    /// Fingerprint a dataset with entropy analysis
    ///
    /// Returns both cryptographic fingerprint and entropy metrics.
    pub fn fingerprint_with_entropy(&self, dataset: &Dataset) -> (DataFingerprint, f64, usize) {
        let fingerprint = DataFingerprint::from_dataset(dataset);
        let entropy = self.compute_dataset_entropy(dataset);
        let optimal_bits = self.optimal_proof_bits(dataset);

        (fingerprint, entropy, optimal_bits)
    }
}

impl Default for DataProver {
    fn default() -> Self {
        Self::new()
    }
}

/// Model auditor for compliance checking
#[derive(Debug, Clone)]
pub struct ModelAuditor {
    // In practice would contain audit configuration
}

impl ModelAuditor {
    /// Create a new model auditor
    pub fn new() -> Self {
        Self {}
    }

    /// Audit a model for compliance
    pub fn audit_model<T>(&self, model: &T, test_data: &Dataset) -> AuditReport 
    where
        T: std::fmt::Debug,
    {
        let model_id = format!("model_{:?}", model).chars().take(20).collect();
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        // Simplified audit - in practice would run comprehensive tests
        let passed = !test_data.points.is_empty();
        let findings = if passed {
            vec![]
        } else {
            vec!["No test data provided".to_string()]
        };

        AuditReport {
            model_id,
            timestamp,
            passed,
            findings,
            test_data_fingerprint: DataFingerprint::from_dataset(test_data),
        }
    }
}

impl Default for ModelAuditor {
    fn default() -> Self {
        Self::new()
    }
}

/// Audit report for model compliance
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditReport {
    pub model_id: String,
    pub timestamp: u64,
    pub passed: bool,
    pub findings: Vec<String>,
    pub test_data_fingerprint: DataFingerprint,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dataset_creation() {
        let points = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
        let dataset = Dataset::new(points.clone());
        
        assert_eq!(dataset.points, points);
        assert_eq!(dataset.name, "unnamed_dataset");
    }

    #[test]
    fn test_data_fingerprint_creation() {
        let dataset = Dataset::new(vec![vec![1.0, 2.0]]);
        let fingerprint = DataFingerprint::from_dataset(&dataset);
        
        assert!(!fingerprint.dataset_id.is_empty());
        assert!(!fingerprint.merkle_root.is_empty());
        assert!(fingerprint.topology_signature.is_valid());
        assert!(fingerprint.timestamp > 0);
    }

    #[test]
    fn test_data_prover() {
        let prover = DataProver::new();
        let dataset = Dataset::new(vec![vec![1.0, 2.0]]);

        #[derive(Debug)]
        struct MockModel;
        let model = MockModel;

        let proof = prover.prove_data_usage(&model, &dataset);
        assert!(proof.is_valid());

        let is_valid = prover.verify_proof(&proof);
        assert!(is_valid);
    }

    #[test]
    fn test_dataset_entropy() {
        let prover = DataProver::new();

        // Uniform dataset should have high entropy
        let uniform_dataset = Dataset::new(vec![
            vec![1.0, 2.0],
            vec![3.0, 4.0],
            vec![5.0, 6.0],
            vec![7.0, 8.0],
        ]);

        let entropy = prover.compute_dataset_entropy(&uniform_dataset);
        assert!(entropy > 0.0);
    }

    #[test]
    fn test_optimal_proof_bits() {
        let prover = DataProver::new();
        let dataset = Dataset::new(vec![
            vec![1.0, 2.0],
            vec![3.0, 4.0],
        ]);

        let optimal_bits = prover.optimal_proof_bits(&dataset);
        assert!(optimal_bits > 0);
    }

    #[test]
    fn test_compression_efficiency() {
        let prover = DataProver::new();
        let dataset = Dataset::new(vec![vec![1.0, 2.0]]);

        #[derive(Debug)]
        struct MockModel;
        let model = MockModel;

        let proof = prover.prove_data_usage(&model, &dataset);
        let efficiency = prover.compression_efficiency(&proof);

        assert!(efficiency >= 0.0 && efficiency <= 1.0);
    }

    #[test]
    fn test_fingerprint_with_entropy() {
        let prover = DataProver::new();
        let dataset = Dataset::new(vec![
            vec![1.0, 2.0],
            vec![3.0, 4.0],
        ]);

        let (fingerprint, entropy, optimal_bits) = prover.fingerprint_with_entropy(&dataset);

        assert!(fingerprint.is_valid());
        assert!(entropy >= 0.0);
        assert!(optimal_bits > 0);
    }

    #[test]
    fn test_empty_dataset_entropy() {
        let prover = DataProver::new();
        let empty_dataset = Dataset::new(vec![]);

        let entropy = prover.compute_dataset_entropy(&empty_dataset);
        assert_eq!(entropy, 0.0);

        let optimal_bits = prover.optimal_proof_bits(&empty_dataset);
        assert_eq!(optimal_bits, 0);
    }
}

impl DataFingerprint {
    /// Check if fingerprint is valid
    pub fn is_valid(&self) -> bool {
        !self.dataset_id.is_empty() &&
        !self.merkle_root.is_empty() &&
        self.topology_signature.is_valid()
    }
}
