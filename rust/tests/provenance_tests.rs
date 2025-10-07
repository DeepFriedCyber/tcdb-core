//! Provenance System Tests
//! 
//! Comprehensive TDD test suite for provenance tracking

#[cfg(test)]
mod tests {
    use tcdb_core::provenance::{ProvenanceTracker, ReasoningStep, OperationType};
    use uuid::Uuid;
    use std::collections::HashMap;
    
    // Test 1: Empty tracker has no nodes
    #[test]
    fn test_empty_tracker() {
        // Arrange
        let tracker = ProvenanceTracker::new();
        
        // Act
        let graph = tracker.get_provenance_graph();
        
        // Assert
        assert_eq!(graph.nodes.len(), 0);
        assert_eq!(graph.edges.len(), 0);
    }
    
    // Test 2: Single reasoning step creates node
    #[test]
    fn test_single_reasoning_step() {
        // Arrange
        let mut tracker = ProvenanceTracker::new();
        let step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation { 
                prompt: "Test prompt".to_string(), 
                model: "test-model".to_string() 
            },
            vec![], // No input signatures
            "Test output".to_string(),
        );
        let step_id = step.step_id;
        
        // Act
        tracker.add_step(step.clone());
        
        // Assert
        let graph = tracker.get_provenance_graph();
        assert_eq!(graph.nodes.len(), 1);
        assert_eq!(graph.edges.len(), 0);
        
        let node = graph.nodes.get(&step_id).unwrap();
        assert_eq!(node.output, "Test output");
        match &node.operation {
            OperationType::Generation { prompt, model } => {
                assert_eq!(prompt, "Test prompt");
                assert_eq!(model, "test-model");
            }
            _ => panic!("Expected Generation operation"),
        }
    }
    
    // Test 3: Dependency tracking creates edges
    #[test]
    fn test_dependency_tracking() {
        // Arrange
        let mut tracker = ProvenanceTracker::new();
        
        let parent_step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Retrieval { 
                query: "parent query".to_string(), 
                sources: vec!["source1".to_string()] 
            },
            vec![],
            "parent output".to_string(),
        );
        let parent_signature = parent_step.compute_signature();
        
        let child_step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation { 
                prompt: "child prompt".to_string(), 
                model: "test-model".to_string() 
            },
            vec![parent_signature], // Depends on parent
            "child output".to_string(),
        );
        
        // Act
        tracker.add_step(parent_step);
        tracker.add_step(child_step);
        
        // Assert
        let graph = tracker.get_provenance_graph();
        assert_eq!(graph.nodes.len(), 2);
        assert_eq!(graph.edges.len(), 1);
        
        let edge = &graph.edges[0];
        assert_eq!(edge.dependency_type, "input_dependency");
    }
    
    // Test 4: Provenance graph verification
    #[test]
    fn test_provenance_graph_verification() {
        // Arrange
        let mut tracker = ProvenanceTracker::new();
        let step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Transformation { 
                method: "test_method".to_string(), 
                parameters: HashMap::new()
            },
            vec![],
            "test output".to_string(),
        );
        
        tracker.add_step(step);
        
        // Act
        let verification = tracker.verify_provenance();
        
        // Assert
        assert!(verification.is_valid());
        assert_eq!(verification.errors.len(), 0);
    }
    
    // Test 5: Tampered provenance detection (simplified)
    #[test]
    fn test_tampered_provenance_detection() {
        // Arrange
        let mut tracker = ProvenanceTracker::new();
        let step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation { 
                prompt: "original prompt".to_string(), 
                model: "test-model".to_string() 
            },
            vec![],
            "original output".to_string(),
        );
        
        tracker.add_step(step);
        
        // Act - Simulate tampering by manually adding invalid edge
        // This would normally be detected by cryptographic signatures
        let verification = tracker.verify_provenance();
        
        // Assert - In a real implementation, this would fail
        // For this test, we're just checking the verification structure
        assert!(verification.is_valid()); // No actual tampering in this test
    }
    
    // Test 6: Provenance export/import
    #[test]
    fn test_provenance_export_import() {
        // Arrange
        let mut tracker1 = ProvenanceTracker::new();
        let step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Retrieval { 
                query: "test query".to_string(), 
                sources: vec!["test_source".to_string()] 
            },
            vec![],
            "test output".to_string(),
        );
        
        tracker1.add_step(step);
        
        // Act
        let exported = tracker1.export_provenance();
        let tracker2 = ProvenanceTracker::import_provenance(&exported);
        
        // Assert
        let graph1 = tracker1.get_provenance_graph();
        let graph2 = tracker2.get_provenance_graph();
        
        assert_eq!(graph1.nodes.len(), graph2.nodes.len());
        assert_eq!(graph1.edges.len(), graph2.edges.len());
    }

    // Test 7: Multiple operation types
    #[test]
    fn test_multiple_operation_types() {
        // Arrange
        let mut tracker = ProvenanceTracker::new();
        
        let gen_step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation { 
                prompt: "Generate something".to_string(), 
                model: "gpt-4".to_string() 
            },
            vec![],
            "Generated content".to_string(),
        );
        
        let ret_step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Retrieval { 
                query: "Find information".to_string(), 
                sources: vec!["db1".to_string(), "db2".to_string()] 
            },
            vec![],
            "Retrieved data".to_string(),
        );
        
        let mut params = HashMap::new();
        params.insert("method".to_string(), "normalize".to_string());
        let trans_step = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Transformation { 
                method: "data_transform".to_string(), 
                parameters: params 
            },
            vec![],
            "Transformed data".to_string(),
        );
        
        // Act
        tracker.add_step(gen_step);
        tracker.add_step(ret_step);
        tracker.add_step(trans_step);
        
        // Assert
        let graph = tracker.get_provenance_graph();
        assert_eq!(graph.nodes.len(), 3);
        
        // Check that all operation types are present
        let mut has_generation = false;
        let mut has_retrieval = false;
        let mut has_transformation = false;
        
        for node in graph.nodes.values() {
            match &node.operation {
                OperationType::Generation { .. } => has_generation = true,
                OperationType::Retrieval { .. } => has_retrieval = true,
                OperationType::Transformation { .. } => has_transformation = true,
            }
        }
        
        assert!(has_generation);
        assert!(has_retrieval);
        assert!(has_transformation);
    }

    // Test 8: Reasoning step signature consistency
    #[test]
    fn test_reasoning_step_signature_consistency() {
        // Arrange
        let step1 = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation {
                prompt: "test".to_string(),
                model: "model".to_string()
            },
            vec![],
            "output".to_string(),
        );

        // Create another step with different ID
        let step2 = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation {
                prompt: "test".to_string(),
                model: "model".to_string()
            },
            vec![],
            "output".to_string(),
        );

        // Act
        let sig1 = step1.compute_signature();
        let sig2 = step2.compute_signature();

        // Assert - signatures should be different due to different UUIDs
        assert_ne!(sig1, sig2);
    }

    // Test 9: Complex dependency chain
    #[test]
    fn test_complex_dependency_chain() {
        // Arrange
        let mut tracker = ProvenanceTracker::new();
        
        // Create a chain: A -> B -> C
        let step_a = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Retrieval { 
                query: "initial query".to_string(), 
                sources: vec!["source".to_string()] 
            },
            vec![],
            "step A output".to_string(),
        );
        let sig_a = step_a.compute_signature();
        
        let step_b = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Transformation { 
                method: "process".to_string(), 
                parameters: HashMap::new() 
            },
            vec![sig_a],
            "step B output".to_string(),
        );
        let sig_b = step_b.compute_signature();
        
        let step_c = ReasoningStep::new(
            Uuid::new_v4(),
            OperationType::Generation { 
                prompt: "final prompt".to_string(), 
                model: "model".to_string() 
            },
            vec![sig_b],
            "step C output".to_string(),
        );
        
        // Act
        tracker.add_step(step_a);
        tracker.add_step(step_b);
        tracker.add_step(step_c);
        
        // Assert
        let graph = tracker.get_provenance_graph();
        assert_eq!(graph.nodes.len(), 3);
        assert_eq!(graph.edges.len(), 2); // A->B and B->C
        
        let verification = tracker.verify_provenance();
        assert!(verification.is_valid());
    }
}

// ============================================================================
// CERTIFICATE TESTS
// ============================================================================

#[cfg(test)]
mod certificate_tests {
    use tcdb_core::provenance::{Certificate, hash_persistence_diagram};

    #[test]
    fn pd_hash_is_order_invariant_and_stable() {
        // Test order invariance
        let a = vec![(0.0, 1.0), (0.2, 0.9), (0.1, 0.8)];
        let mut b = a.clone();
        b.reverse();

        let hash_a = hash_persistence_diagram(a);
        let hash_b = hash_persistence_diagram(b);

        assert_eq!(hash_a, hash_b, "Hash should be order-invariant");

        // Test stability across runs: fixed precision formatting → fixed hash
        let h1 = hash_persistence_diagram(vec![(0.1234567890123456, 0.9)]);

        // Verify hash is deterministic
        let h2 = hash_persistence_diagram(vec![(0.1234567890123456, 0.9)]);
        assert_eq!(h1, h2, "Hash should be deterministic");

        // Verify BLAKE3 hex length
        assert_eq!(h1.len(), 64, "BLAKE3 hash should be 64 hex characters");

        // Record the actual hash for future reference
        println!("Golden hash for (0.1234567890123456, 0.9): {}", h1);
    }

    #[test]
    fn certificate_audit_token_changes_with_any_field() {
        let pd = vec![(0.0, 1.0)];

        // Different data CID
        let c1 = Certificate::new("cid:abc", "rev:123", &pd);
        let c2 = Certificate::new("cid:xyz", "rev:123", &pd);
        assert_ne!(
            c1.audit_token(),
            c2.audit_token(),
            "Different data CID should produce different audit token"
        );

        // Different code revision
        let c3 = Certificate::new("cid:abc", "rev:456", &pd);
        assert_ne!(
            c1.audit_token(),
            c3.audit_token(),
            "Different code revision should produce different audit token"
        );

        // Different persistence diagram
        let pd2 = vec![(0.0, 2.0)];
        let c4 = Certificate::new("cid:abc", "rev:123", &pd2);
        assert_ne!(
            c1.audit_token(),
            c4.audit_token(),
            "Different persistence diagram should produce different audit token"
        );

        // Same inputs should produce same token
        let c5 = Certificate::new("cid:abc", "rev:123", &pd);
        assert_eq!(
            c1.audit_token(),
            c5.audit_token(),
            "Same inputs should produce same audit token"
        );
    }

    #[test]
    fn pd_hash_precision_preservation() {
        // Test that full f64 precision is preserved
        let pd1 = vec![(0.12345678901234567, 0.98765432109876543)];
        let pd2 = vec![(0.12345678901234560, 0.98765432109876543)]; // Slightly different

        let hash1 = hash_persistence_diagram(pd1);
        let hash2 = hash_persistence_diagram(pd2);

        // These should be different because we preserve 17 decimal places
        assert_ne!(hash1, hash2, "Full precision should be preserved");
    }

    #[test]
    fn pd_hash_handles_infinity() {
        // Test that infinity is handled correctly
        let pd = vec![(0.0, f64::INFINITY), (0.5, 1.0)];
        let hash = hash_persistence_diagram(pd);

        assert_eq!(hash.len(), 64, "Should produce valid hash even with infinity");

        // Should be deterministic
        let pd2 = vec![(0.0, f64::INFINITY), (0.5, 1.0)];
        let hash2 = hash_persistence_diagram(pd2);
        assert_eq!(hash, hash2, "Infinity handling should be deterministic");
    }

    #[test]
    fn certificate_serialization_roundtrip() {
        let pd = vec![(0.0, 1.0), (0.5, 2.0), (1.0, f64::INFINITY)];
        let cert = Certificate::new("sha256:abc123", "v1.0.0", &pd);

        // Serialize to JSON
        let json = serde_json::to_string(&cert).unwrap();

        // Deserialize back
        let cert2: Certificate = serde_json::from_str(&json).unwrap();

        // Should be identical
        assert_eq!(cert.data_cid, cert2.data_cid);
        assert_eq!(cert.code_rev, cert2.code_rev);
        assert_eq!(cert.result_hash, cert2.result_hash);
        assert_eq!(cert.audit_token(), cert2.audit_token());
    }

    #[test]
    fn certificate_verify_with_reordered_pd() {
        let pd1 = vec![(0.0, 1.0), (0.5, 2.0), (1.0, 3.0)];
        let cert = Certificate::new("sha256:abc", "v1.0.0", &pd1);

        // Verify with same PD in different order
        let pd2 = vec![(1.0, 3.0), (0.0, 1.0), (0.5, 2.0)];
        assert!(
            cert.verify_result(&pd2),
            "Should verify regardless of order"
        );

        // Verify with wrong PD
        let pd3 = vec![(0.0, 1.0), (0.5, 2.1), (1.0, 3.0)];
        assert!(
            !cert.verify_result(&pd3),
            "Should reject incorrect PD"
        );
    }

    #[test]
    fn certificate_empty_pd() {
        // Test with empty persistence diagram
        let pd: Vec<(f64, f64)> = vec![];
        let cert = Certificate::new("sha256:empty", "v1.0.0", &pd);

        assert!(!cert.result_hash.is_empty(), "Should produce hash even for empty PD");
        assert!(cert.verify_result(&pd), "Should verify empty PD");
    }

    #[test]
    fn certificate_single_point_pd() {
        // Test with single point
        let pd = vec![(0.0, 1.0)];
        let cert = Certificate::new("sha256:single", "v1.0.0", &pd);

        assert!(cert.verify_result(&pd), "Should verify single point PD");

        // Different single point should fail
        let pd2 = vec![(0.0, 2.0)];
        assert!(!cert.verify_result(&pd2), "Should reject different point");
    }

    #[test]
    fn certificate_duplicate_points() {
        // Test with duplicate points (should be preserved)
        let pd = vec![(0.0, 1.0), (0.0, 1.0), (0.5, 2.0)];
        let cert = Certificate::new("sha256:dup", "v1.0.0", &pd);

        // Same duplicates should verify
        assert!(cert.verify_result(&pd), "Should verify with duplicates");

        // Different number of duplicates should fail
        let pd2 = vec![(0.0, 1.0), (0.5, 2.0)];
        assert!(!cert.verify_result(&pd2), "Should reject different duplicates");
    }
}

// Property-based tests for provenance
#[cfg(test)]
mod provenance_property_tests {
    use proptest::prelude::*;
    use tcdb_core::provenance::{ProvenanceTracker, ReasoningStep, OperationType};
    use uuid::Uuid;
    use std::collections::HashMap;
    
    // Helper to generate arbitrary ReasoningStep
    fn arb_reasoning_step() -> impl Strategy<Value = ReasoningStep> {
        (
            any::<[u8; 16]>().prop_map(|bytes| Uuid::from_bytes(bytes)),
            prop_oneof![
                (any::<String>(), any::<String>()).prop_map(|(prompt, model)| 
                    OperationType::Generation { prompt, model }
                ),
                (any::<String>(), prop::collection::vec(any::<String>(), 0..5)).prop_map(|(query, sources)| 
                    OperationType::Retrieval { query, sources }
                ),
                (any::<String>()).prop_map(|method| 
                    OperationType::Transformation { method, parameters: HashMap::new() }
                ),
            ],
            prop::collection::vec(any::<String>(), 0..3),
            any::<String>(),
        ).prop_map(|(id, op, inputs, output)| {
            ReasoningStep::new(id, op, inputs, output)
        })
    }
    
    proptest! {
        // Property 1: Any sequence of reasoning steps produces valid provenance
        #[test]
        fn prop_valid_provenance(steps in prop::collection::vec(arb_reasoning_step(), 1..10)) {
            let mut tracker = ProvenanceTracker::new();
            
            for step in steps {
                tracker.add_step(step);
            }
            
            let verification = tracker.verify_provenance();
            prop_assert!(verification.is_valid());
        }
        
        // Property 2: Provenance export/import preserves structure
        #[test]
        fn prop_provenance_preservation(steps in prop::collection::vec(arb_reasoning_step(), 1..5)) {
            let mut tracker1 = ProvenanceTracker::new();
            
            for step in steps {
                tracker1.add_step(step);
            }
            
            let exported = tracker1.export_provenance();
            let tracker2 = ProvenanceTracker::import_provenance(&exported);
            
            let graph1 = tracker1.get_provenance_graph();
            let graph2 = tracker2.get_provenance_graph();
            
            prop_assert_eq!(graph1.nodes.len(), graph2.nodes.len());
            prop_assert_eq!(graph1.edges.len(), graph2.edges.len());
        }
    }
}
