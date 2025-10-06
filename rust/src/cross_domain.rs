//! Cross-Domain Reasoning System
//! 
//! Implements domain mapping, principle transfer, and hidden connection discovery.

use crate::topology::TopologicalSignature;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// A domain structure containing axioms and topological information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DomainStructure {
    pub name: String,
    pub axioms: Vec<String>,
    pub topology_signature: Option<TopologicalSignature>,
    pub metadata: HashMap<String, String>,
}

impl DomainStructure {
    /// Create a new domain structure
    pub fn new(name: String, axioms: Vec<String>) -> Self {
        Self {
            name,
            axioms,
            topology_signature: None,
            metadata: HashMap::new(),
        }
    }

    /// Create a domain structure with topology
    pub fn with_topology(name: String, axioms: Vec<String>, topology: TopologicalSignature) -> Self {
        Self {
            name,
            axioms,
            topology_signature: Some(topology),
            metadata: HashMap::new(),
        }
    }

    /// Check if this domain structure is valid
    pub fn is_valid(&self) -> bool {
        !self.name.is_empty()
    }

    /// Add metadata to the domain
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }
}

/// Domain mapper for managing and comparing domains
#[derive(Debug, Clone)]
pub struct DomainMapper {
    domains: HashMap<String, DomainStructure>,
}

impl DomainMapper {
    /// Create a new domain mapper
    pub fn new() -> Self {
        Self {
            domains: HashMap::new(),
        }
    }

    /// Register a new domain
    pub fn register_domain(&mut self, domain: DomainStructure) {
        self.domains.insert(domain.name.clone(), domain);
    }

    /// Get all known domains
    pub fn get_known_domains(&self) -> &HashMap<String, DomainStructure> {
        &self.domains
    }

    /// Find domains that are topologically equivalent
    pub fn find_equivalent_domains(&self, domain_name: &str) -> Vec<String> {
        let mut equivalents = Vec::new();
        
        if let Some(target_domain) = self.domains.get(domain_name) {
            if let Some(target_topology) = &target_domain.topology_signature {
                for (name, domain) in &self.domains {
                    if name != domain_name {
                        if let Some(domain_topology) = &domain.topology_signature {
                            if self.are_topologically_similar(target_topology, domain_topology) {
                                equivalents.push(name.clone());
                            }
                        }
                    }
                }
            }
        }
        
        equivalents
    }

    /// Get information about a specific domain
    pub fn get_domain_info(&self, domain_name: &str) -> Option<&DomainStructure> {
        self.domains.get(domain_name)
    }

    fn are_topologically_similar(&self, sig1: &TopologicalSignature, sig2: &TopologicalSignature) -> bool {
        // Simple similarity check based on Betti numbers
        if sig1.betti_numbers.len() != sig2.betti_numbers.len() {
            return false;
        }
        
        // Check if Betti numbers are similar (allowing for small differences)
        for (b1, b2) in sig1.betti_numbers.iter().zip(sig2.betti_numbers.iter()) {
            let diff = if b1 > b2 { b1 - b2 } else { b2 - b1 };
            if diff > 2 { // Allow difference of up to 2
                return false;
            }
        }
        
        true
    }
}

impl Default for DomainMapper {
    fn default() -> Self {
        Self::new()
    }
}

/// A principle that can be transferred between domains
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Principle {
    pub name: String,
    pub description: String,
    pub domain: String,
    pub is_topological: bool,
    pub confidence: f64,
}

impl Principle {
    /// Create a new principle
    pub fn new(name: String, description: String, domain: String) -> Self {
        Self {
            name,
            description,
            domain,
            is_topological: false,
            confidence: 1.0,
        }
    }

    /// Create a topological principle
    pub fn topological(name: String, description: String, domain: String, confidence: f64) -> Self {
        Self {
            name,
            description,
            domain,
            is_topological: true,
            confidence,
        }
    }
}

/// Result of principle transfer
#[derive(Debug, Clone)]
pub struct TransferResult {
    pub success: bool,
    pub transferred_principle: Option<Principle>,
    pub confidence: f64,
    pub explanation: String,
}

impl TransferResult {
    pub fn success(principle: Principle, confidence: f64, explanation: String) -> Self {
        Self {
            success: true,
            transferred_principle: Some(principle),
            confidence,
            explanation,
        }
    }

    pub fn failure(explanation: String) -> Self {
        Self {
            success: false,
            transferred_principle: None,
            confidence: 0.0,
            explanation,
        }
    }
}

/// Hidden connection between domains
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HiddenConnection {
    pub domain1: String,
    pub domain2: String,
    pub connection_type: String,
    pub strength: f64,
    pub evidence: Vec<String>,
}

/// Engine for transferring principles between domains
#[derive(Debug, Clone)]
pub struct PrincipleTransferEngine {
    domain_mapper: DomainMapper,
    principles: Vec<Principle>,
}

impl PrincipleTransferEngine {
    /// Create a new principle transfer engine
    pub fn new(domain_mapper: DomainMapper) -> Self {
        Self {
            domain_mapper,
            principles: Vec::new(),
        }
    }

    /// Add a principle to the engine
    pub fn add_principle(&mut self, principle: Principle) {
        self.principles.push(principle);
    }

    /// Transfer a principle from one domain to another
    pub fn transfer_principle(
        &self,
        principle: &Principle,
        source_domain: &str,
        target_domain: &str,
    ) -> Result<TransferResult, String> {
        // Check if domains exist
        let source = self.domain_mapper.get_domain_info(source_domain)
            .ok_or_else(|| format!("Source domain '{}' not found", source_domain))?;
        let target = self.domain_mapper.get_domain_info(target_domain)
            .ok_or_else(|| format!("Target domain '{}' not found", target_domain))?;

        // Check topological compatibility
        let compatibility = self.check_topological_compatibility(source, target);
        
        if compatibility > 0.5 {
            let mut transferred = principle.clone();
            transferred.domain = target_domain.to_string();
            transferred.confidence *= compatibility;
            
            Ok(TransferResult::success(
                transferred,
                compatibility,
                format!("Successfully transferred principle from {} to {}", source_domain, target_domain)
            ))
        } else {
            Ok(TransferResult::failure(
                format!("Insufficient topological compatibility ({:.2}) between {} and {}", 
                       compatibility, source_domain, target_domain)
            ))
        }
    }

    /// Discover hidden connections between domains
    pub fn discover_hidden_connections(&self) -> Vec<HiddenConnection> {
        let mut connections = Vec::new();
        let domains: Vec<_> = self.domain_mapper.get_known_domains().keys().collect();
        
        // Compare all pairs of domains
        for i in 0..domains.len() {
            for j in (i + 1)..domains.len() {
                let domain1 = domains[i];
                let domain2 = domains[j];
                
                if let (Some(d1), Some(d2)) = (
                    self.domain_mapper.get_domain_info(domain1),
                    self.domain_mapper.get_domain_info(domain2)
                ) {
                    let compatibility = self.check_topological_compatibility(d1, d2);
                    
                    if compatibility > 0.3 { // Threshold for hidden connections
                        let connection = HiddenConnection {
                            domain1: domain1.clone(),
                            domain2: domain2.clone(),
                            connection_type: "topological_similarity".to_string(),
                            strength: compatibility,
                            evidence: vec![
                                format!("Topological compatibility: {:.2}", compatibility)
                            ],
                        };
                        connections.push(connection);
                    }
                }
            }
        }
        
        connections
    }

    fn check_topological_compatibility(&self, domain1: &DomainStructure, domain2: &DomainStructure) -> f64 {
        match (&domain1.topology_signature, &domain2.topology_signature) {
            (Some(sig1), Some(sig2)) => {
                // Simple compatibility based on Betti number similarity
                if sig1.betti_numbers.len() != sig2.betti_numbers.len() {
                    return 0.0;
                }
                
                let mut total_diff = 0.0;
                let mut max_possible_diff = 0.0;
                
                for (b1, b2) in sig1.betti_numbers.iter().zip(sig2.betti_numbers.iter()) {
                    let diff = if b1 > b2 { b1 - b2 } else { b2 - b1 } as f64;
                    let max_val = (*b1.max(b2)) as f64;
                    total_diff += diff;
                    max_possible_diff += max_val;
                }
                
                if max_possible_diff == 0.0 {
                    1.0 // Both have all zero Betti numbers
                } else {
                    1.0 - (total_diff / max_possible_diff).min(1.0)
                }
            }
            (None, None) => 0.5, // No topology info, assume moderate compatibility
            _ => 0.1, // One has topology, one doesn't - low compatibility
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_domain_structure_creation() {
        let domain = DomainStructure::new("test_domain".to_string(), vec![]);
        assert_eq!(domain.name, "test_domain");
        assert!(domain.is_valid());
    }

    #[test]
    fn test_domain_mapper_creation() {
        let mapper = DomainMapper::new();
        assert_eq!(mapper.get_known_domains().len(), 0);
    }

    #[test]
    fn test_principle_creation() {
        let principle = Principle::new(
            "test_principle".to_string(),
            "A test principle".to_string(),
            "test_domain".to_string(),
        );
        assert_eq!(principle.name, "test_principle");
        assert!(!principle.is_topological);
    }

    #[test]
    fn test_principle_transfer_engine_creation() {
        let mapper = DomainMapper::new();
        let engine = PrincipleTransferEngine::new(mapper);
        assert_eq!(engine.principles.len(), 0);
    }
}
