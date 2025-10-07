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

    /// Compute entropy of operation types distribution
    ///
    /// Measures how diverse the reasoning operations are.
    /// High entropy = many different operation types used.
    /// Low entropy = dominated by one operation type.
    pub fn operation_entropy(&self) -> f64 {
        let mut operation_counts: HashMap<String, usize> = HashMap::new();

        for node in self.graph.nodes.values() {
            let op_type = match &node.operation {
                OperationType::Generation { .. } => "generation",
                OperationType::Retrieval { .. } => "retrieval",
                OperationType::Transformation { .. } => "transformation",
            };
            *operation_counts.entry(op_type.to_string()).or_insert(0) += 1;
        }

        let counts: Vec<usize> = operation_counts.values().copied().collect();
        crate::entropy::entropy_from_counts(&counts)
    }

    /// Compute path entropy for a specific reasoning path
    ///
    /// Measures the "surprise" or complexity of a reasoning path.
    /// Assumes uniform probability for simplicity (can be extended with learned probabilities).
    pub fn path_entropy(&self, step_id: &Uuid) -> f64 {
        let path_length = self.get_path_length(step_id);
        if path_length == 0 {
            return 0.0;
        }

        // Simplified: assume uniform probability for each step
        // In practice, could use learned probabilities from historical data
        let prob_per_step = 1.0 / path_length as f64;
        crate::entropy::self_information(prob_per_step)
    }

    /// Get the length of the reasoning path to a step
    fn get_path_length(&self, step_id: &Uuid) -> usize {
        let mut length = 0;
        let mut current = *step_id;
        let mut visited = HashSet::new();

        while let Some(node) = self.graph.nodes.get(&current) {
            if visited.contains(&current) {
                break; // Cycle detected
            }
            visited.insert(current);
            length += 1;

            // Find parent
            let parent = self.graph.edges.iter()
                .find(|e| e.to == current)
                .map(|e| e.from);

            match parent {
                Some(p) => current = p,
                None => break,
            }
        }

        length
    }

    /// Compute branching entropy
    ///
    /// Measures how much the reasoning branches out.
    /// High entropy = many different branches.
    /// Low entropy = linear reasoning path.
    pub fn branching_entropy(&self) -> f64 {
        let mut out_degrees: Vec<usize> = Vec::new();

        for node_id in self.graph.nodes.keys() {
            let out_degree = self.graph.edges.iter()
                .filter(|e| e.from == *node_id)
                .count();
            if out_degree > 0 {
                out_degrees.push(out_degree);
            }
        }

        if out_degrees.is_empty() {
            return 0.0;
        }

        crate::entropy::entropy_from_counts(&out_degrees)
    }

    /// Compute complexity score of the provenance graph
    ///
    /// Combines operation entropy and branching entropy.
    /// Returns value in [0, 1] where higher = more complex reasoning.
    pub fn complexity_score(&self) -> f64 {
        if self.graph.nodes.is_empty() {
            return 0.0;
        }

        let op_entropy = self.operation_entropy();
        let branch_entropy = self.branching_entropy();

        // Normalize by maximum possible entropy
        let max_op_entropy = (3.0_f64).log2(); // 3 operation types
        let max_branch_entropy = (self.graph.nodes.len() as f64).log2();

        let norm_op = if max_op_entropy > 0.0 {
            op_entropy / max_op_entropy
        } else {
            0.0
        };

        let norm_branch = if max_branch_entropy > 0.0 {
            branch_entropy / max_branch_entropy
        } else {
            0.0
        };

        (norm_op + norm_branch) / 2.0
    }

    /// Find the most surprising (informative) reasoning steps
    ///
    /// Returns steps sorted by their information content.
    pub fn most_surprising_steps(&self) -> Vec<(Uuid, f64)> {
        let mut steps: Vec<(Uuid, f64)> = self.graph.nodes.keys()
            .map(|id| {
                let info = self.path_entropy(id);
                (*id, info)
            })
            .collect();

        steps.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        steps
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

    #[test]
    fn test_operation_entropy() {
        let mut tracker = ProvenanceTracker::new();

        // Add diverse operations
        tracker.add_step(ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation {
                prompt: "test".to_string(),
                model: "model1".to_string()
            },
            vec![],
            "output1".to_string(),
        ));

        tracker.add_step(ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Retrieval {
                query: "test".to_string(),
                sources: vec![]
            },
            vec![],
            "output2".to_string(),
        ));

        tracker.add_step(ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Transformation {
                method: "test".to_string(),
                parameters: HashMap::new()
            },
            vec![],
            "output3".to_string(),
        ));

        let entropy = tracker.operation_entropy();
        // Three different operations should have log2(3) ≈ 1.58 bits
        assert!(entropy > 1.0 && entropy < 2.0);
    }

    #[test]
    fn test_path_entropy() {
        let mut tracker = ProvenanceTracker::new();
        let step_id = Uuid::new_v4();

        tracker.add_step(ReasoningStep::new(
            step_id,
            OperationType::Generation {
                prompt: "test".to_string(),
                model: "model1".to_string()
            },
            vec![],
            "output".to_string(),
        ));

        let entropy = tracker.path_entropy(&step_id);
        assert!(entropy >= 0.0);
    }

    #[test]
    fn test_branching_entropy() {
        let mut tracker = ProvenanceTracker::new();
        let parent_id = Uuid::new_v4();
        let parent_sig = "parent_sig".to_string();

        // Add parent
        let parent_step = ReasoningStep::new(
            parent_id,
            OperationType::Generation {
                prompt: "parent".to_string(),
                model: "model1".to_string()
            },
            vec![],
            "parent_output".to_string(),
        );
        tracker.step_signatures.insert(parent_id, parent_sig.clone());
        tracker.add_step(parent_step);

        // Add two children
        tracker.add_step(ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Transformation {
                method: "child1".to_string(),
                parameters: HashMap::new()
            },
            vec![parent_sig.clone()],
            "child1_output".to_string(),
        ));

        tracker.add_step(ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Transformation {
                method: "child2".to_string(),
                parameters: HashMap::new()
            },
            vec![parent_sig],
            "child2_output".to_string(),
        ));

        let entropy = tracker.branching_entropy();
        assert!(entropy >= 0.0);
    }

    #[test]
    fn test_complexity_score() {
        let mut tracker = ProvenanceTracker::new();

        tracker.add_step(ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation {
                prompt: "test".to_string(),
                model: "model1".to_string()
            },
            vec![],
            "output".to_string(),
        ));

        let complexity = tracker.complexity_score();
        assert!(complexity >= 0.0 && complexity <= 1.0);
    }

    #[test]
    fn test_most_surprising_steps() {
        let mut tracker = ProvenanceTracker::new();

        let id1 = Uuid::new_v4();
        let id2 = Uuid::new_v4();

        tracker.add_step(ReasoningStep::new(
            id1,
            OperationType::Generation {
                prompt: "test1".to_string(),
                model: "model1".to_string()
            },
            vec![],
            "output1".to_string(),
        ));

        tracker.add_step(ReasoningStep::new(
            id2,
            OperationType::Retrieval {
                query: "test2".to_string(),
                sources: vec![]
            },
            vec![],
            "output2".to_string(),
        ));

        let surprising = tracker.most_surprising_steps();
        assert_eq!(surprising.len(), 2);
    }
}
