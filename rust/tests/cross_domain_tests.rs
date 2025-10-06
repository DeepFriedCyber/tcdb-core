//! Cross-Domain Reasoning Tests
//! 
//! Comprehensive TDD test suite for cross-domain reasoning system

#[cfg(test)]
mod tests {
    use tcdb_core::cross_domain::{DomainMapper, PrincipleTransferEngine, DomainStructure};
    use tcdb_core::topology::{TopologicalSignature, EmbeddingCapture};
    use tcdb_core::PersistenceDiagram;
    
    // Test 1: Domain mapper initialization
    #[test]
    fn test_domain_mapper_initialization() {
        // Arrange
        let mapper = DomainMapper::new();
        
        // Act
        let known_domains = mapper.get_known_domains();
        
        // Assert
        assert_eq!(known_domains.len(), 0); // Starts empty
    }
    
    // Test 2: Register domain structure
    #[test]
    fn test_register_domain_structure() {
        // Arrange
        let mut mapper = DomainMapper::new();
        let domain_struct = DomainStructure::new(
            "test_domain".to_string(),
            vec![], // No axioms for test
        );
        
        // Act
        mapper.register_domain(domain_struct.clone());
        
        // Assert
        let known_domains = mapper.get_known_domains();
        assert!(known_domains.contains_key("test_domain"));
        assert_eq!(known_domains.get("test_domain").unwrap().name, "test_domain");
    }
    
    // Test 3: Find equivalent domains (no matches)
    #[test]
    fn test_find_equivalent_domains_no_matches() {
        // Arrange
        let mapper = DomainMapper::new();
        
        // Act
        let equivalences = mapper.find_equivalent_domains("nonexistent_domain");
        
        // Assert
        assert_eq!(equivalences.len(), 0);
    }
    
    // Test 4: Principle transfer engine initialization
    #[test]
    fn test_principle_transfer_engine_initialization() {
        // Arrange
        let mapper = DomainMapper::new();
        
        // Act
        let engine = PrincipleTransferEngine::new(mapper);
        
        // Assert
        // Should not panic and should be created successfully
        assert_eq!(engine.discover_hidden_connections().len(), 0); // No domains yet
    }
    
    // Test 5: Transfer principle between domains
    #[test]
    fn test_principle_transfer() {
        // Arrange
        let mut mapper = DomainMapper::new();
        
        // Create two domains with similar topology
        let embedding1 = vec![1.0, 2.0, 3.0];
        let capture1 = EmbeddingCapture::new(embedding1, "domain1");
        let topology1 = capture1.compute_signature();
        
        let embedding2 = vec![1.1, 2.1, 3.1]; // Similar embedding
        let capture2 = EmbeddingCapture::new(embedding2, "domain2");
        let topology2 = capture2.compute_signature();
        
        let domain1 = DomainStructure::with_topology(
            "source_domain".to_string(),
            vec!["axiom1".to_string()],
            topology1,
        );
        let domain2 = DomainStructure::with_topology(
            "target_domain".to_string(),
            vec!["axiom2".to_string()],
            topology2,
        );
        
        mapper.register_domain(domain1);
        mapper.register_domain(domain2);
        
        let engine = PrincipleTransferEngine::new(mapper);
        
        // Mock principle
        let principle = tcdb_core::cross_domain::Principle::new(
            "test_principle".to_string(),
            "A test principle".to_string(),
            "source_domain".to_string(),
        );
        
        // Act
        let result = engine.transfer_principle(&principle, "source_domain", "target_domain");
        
        // Assert
        assert!(result.is_ok());
        let transfer_result = result.unwrap();
        assert!(transfer_result.success); // Should succeed with similar topology
    }
    
    // Test 6: Discover hidden connections
    #[test]
    fn test_discover_hidden_connections() {
        // Arrange
        let mut mapper = DomainMapper::new();
        
        // Create domains with similar topology
        let embedding1 = vec![0.0, 0.0, 1.0, 0.0, 1.0, 1.0]; // Two points
        let capture1 = EmbeddingCapture::new(embedding1, "domain1");
        let topology1 = capture1.compute_signature();
        
        let embedding2 = vec![0.0, 0.0, 1.0, 0.0, 1.0, 1.0]; // Same topology
        let capture2 = EmbeddingCapture::new(embedding2, "domain2");
        let topology2 = capture2.compute_signature();
        
        let domain1 = DomainStructure::with_topology(
            "neural_networks".to_string(),
            vec![],
            topology1,
        );
        let domain2 = DomainStructure::with_topology(
            "power_grids".to_string(),
            vec![],
            topology2,
        );
        
        mapper.register_domain(domain1);
        mapper.register_domain(domain2);
        
        let engine = PrincipleTransferEngine::new(mapper);
        
        // Act
        let connections = engine.discover_hidden_connections();
        
        // Assert
        assert!(connections.len() > 0); // Should find connection between similar domains
        let connection = &connections[0];
        assert!(connection.strength > 0.3); // Should have reasonable strength
    }
    
    // Test 7: Domain structure validation
    #[test]
    fn test_domain_structure_validation() {
        // Arrange
        let valid_struct = DomainStructure::new(
            "valid_domain".to_string(),
            vec![], // Axioms would be added in real implementation
        );
        
        let invalid_struct = DomainStructure::new(
            "".to_string(), // Empty name should be invalid
            vec![],
        );
        
        // Act & Assert
        assert!(valid_struct.is_valid());
        assert!(!invalid_struct.is_valid());
    }

    // Test 8: Domain with metadata
    #[test]
    fn test_domain_with_metadata() {
        // Arrange
        let mut domain = DomainStructure::new(
            "test_domain".to_string(),
            vec!["axiom1".to_string()],
        );
        
        // Act
        domain.add_metadata("type".to_string(), "mathematical".to_string());
        domain.add_metadata("complexity".to_string(), "high".to_string());
        
        // Assert
        assert_eq!(domain.metadata.get("type"), Some(&"mathematical".to_string()));
        assert_eq!(domain.metadata.get("complexity"), Some(&"high".to_string()));
    }

    // Test 9: Find equivalent domains with topology
    #[test]
    fn test_find_equivalent_domains_with_topology() {
        // Arrange
        let mut mapper = DomainMapper::new();
        
        // Create domains with similar topology
        let embedding = vec![1.0, 2.0, 3.0];
        let capture = EmbeddingCapture::new(embedding, "test");
        let topology = capture.compute_signature();
        
        let domain1 = DomainStructure::with_topology(
            "domain1".to_string(),
            vec![],
            topology.clone(),
        );
        let domain2 = DomainStructure::with_topology(
            "domain2".to_string(),
            vec![],
            topology,
        );
        
        mapper.register_domain(domain1);
        mapper.register_domain(domain2);
        
        // Act
        let equivalents = mapper.find_equivalent_domains("domain1");
        
        // Assert
        assert!(equivalents.contains(&"domain2".to_string()));
    }

    // Test 10: Principle transfer with incompatible domains
    #[test]
    fn test_principle_transfer_incompatible_domains() {
        // Arrange
        let mut mapper = DomainMapper::new();
        
        // Create domains with very different topology
        let embedding1 = vec![]; // Empty
        let capture1 = EmbeddingCapture::new(embedding1, "domain1");
        let topology1 = capture1.compute_signature();
        
        let embedding2 = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0]; // Two points
        let capture2 = EmbeddingCapture::new(embedding2, "domain2");
        let topology2 = capture2.compute_signature();
        
        let domain1 = DomainStructure::with_topology(
            "empty_domain".to_string(),
            vec![],
            topology1,
        );
        let domain2 = DomainStructure::with_topology(
            "populated_domain".to_string(),
            vec![],
            topology2,
        );
        
        mapper.register_domain(domain1);
        mapper.register_domain(domain2);
        
        let engine = PrincipleTransferEngine::new(mapper);
        
        let principle = tcdb_core::cross_domain::Principle::new(
            "test_principle".to_string(),
            "A test principle".to_string(),
            "empty_domain".to_string(),
        );
        
        // Act
        let result = engine.transfer_principle(&principle, "empty_domain", "populated_domain");
        
        // Assert
        assert!(result.is_ok());
        let transfer_result = result.unwrap();
        // May succeed or fail depending on compatibility threshold
        // Just check that it doesn't panic
    }

    // Test 11: Transfer to nonexistent domain
    #[test]
    fn test_transfer_to_nonexistent_domain() {
        // Arrange
        let mapper = DomainMapper::new();
        let engine = PrincipleTransferEngine::new(mapper);
        
        let principle = tcdb_core::cross_domain::Principle::new(
            "test_principle".to_string(),
            "A test principle".to_string(),
            "source_domain".to_string(),
        );
        
        // Act
        let result = engine.transfer_principle(&principle, "nonexistent_source", "nonexistent_target");
        
        // Assert
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("not found"));
    }

    // Test 12: Domain mapper default
    #[test]
    fn test_domain_mapper_default() {
        // Arrange & Act
        let mapper = DomainMapper::default();
        
        // Assert
        assert_eq!(mapper.get_known_domains().len(), 0);
    }
}

// Property-based tests for cross-domain reasoning
#[cfg(test)]
mod property_tests {
    use proptest::prelude::*;
    use tcdb_core::cross_domain::{DomainMapper, DomainStructure};
    
    proptest! {
        // Property 1: Any domain name can be registered
        #[test]
        fn prop_domain_registration(domain_name in "[a-zA-Z0-9_]+") {
            let mut mapper = DomainMapper::new();
            let domain_struct = DomainStructure::new(domain_name.clone(), vec![]);
            
            mapper.register_domain(domain_struct);
            
            let known_domains = mapper.get_known_domains();
            prop_assert!(known_domains.contains_key(&domain_name));
        }
        
        // Property 2: Domain mapper preserves registered domains
        #[test]
        fn prop_domain_preservation(domains in prop::collection::vec("[a-zA-Z0-9_]+", 1..10)) {
            let mut mapper = DomainMapper::new();
            
            for domain_name in &domains {
                let domain_struct = DomainStructure::new(domain_name.clone(), vec![]);
                mapper.register_domain(domain_struct);
            }
            
            let known_domains = mapper.get_known_domains();
            for domain_name in &domains {
                prop_assert!(known_domains.contains_key(domain_name));
            }
        }

        // Property 3: Valid domain names create valid domain structures
        #[test]
        fn prop_valid_domain_structures(domain_name in "[a-zA-Z0-9_]+", 
                                       axioms in prop::collection::vec(any::<String>(), 0..5)) {
            let domain = DomainStructure::new(domain_name, axioms);
            prop_assert!(domain.is_valid());
        }
    }
}
