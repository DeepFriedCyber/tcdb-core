//! Provenance System
//! 
//! Implements provenance tracking for AI reasoning steps and operations.

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use uuid::Uuid;

/// Types of operations that can be tracked
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum OperationType {
    Generation { 
        prompt: String, 
        model: String 
    },
    Retrieval { 
        query: String, 
        sources: Vec<String> 
    },
    Transformation { 
        method: String, 
        parameters: HashMap<String, String> 
    },
}

/// A single reasoning step in the provenance chain
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReasoningStep {
    pub step_id: Uuid,
    pub operation: OperationType,
    pub input_signatures: Vec<String>,
    pub output: String,
    pub timestamp: u64,
}

impl ReasoningStep {
    /// Create a new reasoning step
    pub fn new(
        step_id: Uuid,
        operation: OperationType,
        input_signatures: Vec<String>,
        output: String,
    ) -> Self {
        Self {
            step_id,
            operation,
            input_signatures,
            output,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
        }
    }

    /// Compute a signature for this reasoning step
    pub fn compute_signature(&self) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        self.step_id.hash(&mut hasher);
        self.output.hash(&mut hasher);
        self.timestamp.hash(&mut hasher);
        
        format!("{:x}", hasher.finish())
    }
}

/// A node in the provenance graph
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenanceNode {
    pub step_id: Uuid,
    pub operation: OperationType,
    pub output: String,
    pub timestamp: u64,
}

/// An edge in the provenance graph representing dependencies
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenanceEdge {
    pub from: Uuid,
    pub to: Uuid,
    pub dependency_type: String,
}

/// The complete provenance graph
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProvenanceGraph {
    pub nodes: HashMap<Uuid, ProvenanceNode>,
    pub edges: Vec<ProvenanceEdge>,
}

impl ProvenanceGraph {
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            edges: Vec::new(),
        }
    }
}

/// Verification result for provenance
#[derive(Debug, Clone)]
pub struct ProvenanceVerification {
    pub is_valid: bool,
    pub errors: Vec<String>,
}

impl ProvenanceVerification {
    pub fn new() -> Self {
        Self {
            is_valid: true,
            errors: Vec::new(),
        }
    }

    pub fn is_valid(&self) -> bool {
        self.is_valid && self.errors.is_empty()
    }

    pub fn add_error(&mut self, error: String) {
        self.is_valid = false;
        self.errors.push(error);
    }
}

/// Main provenance tracker
#[derive(Debug, Clone)]
pub struct ProvenanceTracker {
    graph: ProvenanceGraph,
    step_signatures: HashMap<Uuid, String>,
}

impl ProvenanceTracker {
    /// Create a new provenance tracker
    pub fn new() -> Self {
        Self {
            graph: ProvenanceGraph::new(),
            step_signatures: HashMap::new(),
        }
    }

    /// Add a reasoning step to the provenance
    pub fn add_step(&mut self, step: ReasoningStep) {
        let signature = step.compute_signature();
        
        // Create node
        let node = ProvenanceNode {
            step_id: step.step_id,
            operation: step.operation.clone(),
            output: step.output.clone(),
            timestamp: step.timestamp,
        };
        
        self.graph.nodes.insert(step.step_id, node);
        self.step_signatures.insert(step.step_id, signature);
        
        // Create edges for dependencies
        for input_sig in &step.input_signatures {
            if let Some(parent_id) = self.find_step_by_signature(input_sig) {
                let edge = ProvenanceEdge {
                    from: parent_id,
                    to: step.step_id,
                    dependency_type: "input_dependency".to_string(),
                };
                self.graph.edges.push(edge);
            }
        }
    }

    /// Get the provenance graph
    pub fn get_provenance_graph(&self) -> &ProvenanceGraph {
        &self.graph
    }

    /// Verify the provenance integrity
    pub fn verify_provenance(&self) -> ProvenanceVerification {
        let mut verification = ProvenanceVerification::new();
        
        // Check that all edges reference valid nodes
        for edge in &self.graph.edges {
            if !self.graph.nodes.contains_key(&edge.from) {
                verification.add_error(format!("Edge references non-existent source node: {}", edge.from));
            }
            if !self.graph.nodes.contains_key(&edge.to) {
                verification.add_error(format!("Edge references non-existent target node: {}", edge.to));
            }
        }
        
        // Check for cycles (simplified check)
        if self.has_cycles() {
            verification.add_error("Provenance graph contains cycles".to_string());
        }
        
        verification
    }

    /// Export provenance as JSON string
    pub fn export_provenance(&self) -> String {
        serde_json::to_string(&self.graph).unwrap_or_default()
    }

    /// Import provenance from JSON string
    pub fn import_provenance(json: &str) -> Self {
        let graph: ProvenanceGraph = serde_json::from_str(json).unwrap_or_else(|_| ProvenanceGraph::new());
        
        let mut tracker = Self {
            graph,
            step_signatures: HashMap::new(),
        };
        
        // Rebuild signatures
        for (id, node) in &tracker.graph.nodes {
            let step = ReasoningStep {
                step_id: *id,
                operation: node.operation.clone(),
                input_signatures: Vec::new(), // Simplified
                output: node.output.clone(),
                timestamp: node.timestamp,
            };
            let signature = step.compute_signature();
            tracker.step_signatures.insert(*id, signature);
        }
        
        tracker
    }

    fn find_step_by_signature(&self, signature: &str) -> Option<Uuid> {
        for (id, sig) in &self.step_signatures {
            if sig == signature {
                return Some(*id);
            }
        }
        None
    }

    fn has_cycles(&self) -> bool {
        // Simple cycle detection using DFS
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();
        
        for node_id in self.graph.nodes.keys() {
            if !visited.contains(node_id) {
                if self.has_cycle_util(*node_id, &mut visited, &mut rec_stack) {
                    return true;
                }
            }
        }
        
        false
    }

    fn has_cycle_util(&self, node: Uuid, visited: &mut HashSet<Uuid>, rec_stack: &mut HashSet<Uuid>) -> bool {
        visited.insert(node);
        rec_stack.insert(node);
        
        // Check all adjacent nodes
        for edge in &self.graph.edges {
            if edge.from == node {
                let adjacent = edge.to;
                if !visited.contains(&adjacent) {
                    if self.has_cycle_util(adjacent, visited, rec_stack) {
                        return true;
                    }
                } else if rec_stack.contains(&adjacent) {
                    return true;
                }
            }
        }
        
        rec_stack.remove(&node);
        false
    }
}

impl Default for ProvenanceTracker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reasoning_step_creation() {
        let step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation { 
                prompt: "test".to_string(), 
                model: "test-model".to_string() 
            },
            vec![],
            "output".to_string(),
        );
        
        assert!(!step.compute_signature().is_empty());
        assert_eq!(step.output, "output");
    }

    #[test]
    fn test_provenance_tracker_creation() {
        let tracker = ProvenanceTracker::new();
        assert_eq!(tracker.graph.nodes.len(), 0);
        assert_eq!(tracker.graph.edges.len(), 0);
    }
}
