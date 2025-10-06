//! Data Proof System Tests
//! 
//! Comprehensive TDD test suite for data proof system

#[cfg(test)]
mod tests {
    use tcdb_core::data_proof::{DataFingerprint, DataProver, ModelAuditor, Dataset};
    
    // Test 1: Empty dataset fingerprint
    #[test]
    fn test_empty_dataset_fingerprint() {
        // Arrange
        let empty_dataset = Dataset::new(vec![]);
        
        // Act
        let fingerprint = DataFingerprint::from_dataset(&empty_dataset);
        
        // Assert
        assert!(!fingerprint.dataset_id.is_empty());
        assert_eq!(fingerprint.topology_signature.betti_numbers.len(), 3); // B0, B1, B2
        assert_eq!(fingerprint.topology_signature.betti_numbers[0], 0); // No connected components
    }
    
    // Test 2: Single data point fingerprint
    #[test]
    fn test_single_point_fingerprint() {
        // Arrange
        let single_point = vec![vec![1.0, 2.0, 3.0]];
        let dataset = Dataset::new(single_point);
        
        // Act
        let fingerprint = DataFingerprint::from_dataset(&dataset);
        
        // Assert
        assert!(fingerprint.merkle_root.len() > 0);
        assert_eq!(fingerprint.topology_signature.betti_numbers[0], 1); // One connected component
    }
    
    // Test 3: Fingerprint uniqueness
    #[test]
    fn test_fingerprint_uniqueness() {
        // Arrange
        let data1 = Dataset::new(vec![vec![1.0, 2.0], vec![3.0, 4.0]]);
        let data2 = Dataset::new(vec![vec![10.0, 20.0], vec![30.0, 40.0]]);
        
        // Act
        let fingerprint1 = DataFingerprint::from_dataset(&data1);
        let fingerprint2 = DataFingerprint::from_dataset(&data2);
        
        // Assert
        assert_ne!(fingerprint1.merkle_root, fingerprint2.merkle_root);
        assert_ne!(fingerprint1.topology_signature.hash, fingerprint2.topology_signature.hash);
    }
    
    // Test 4: Membership proof verification
    #[test]
    fn test_membership_proof_verification() {
        // Arrange
        let data_points = vec![
            vec![1.0, 2.0],
            vec![3.0, 4.0],
            vec![5.0, 6.0]
        ];
        let dataset = Dataset::new(data_points.clone());
        let fingerprint = DataFingerprint::from_dataset(&dataset);
        
        // Act
        let proof = fingerprint.generate_membership_proof(&data_points[0]);
        let is_member = fingerprint.verify_membership(&data_points[0], &proof);
        
        // Assert
        assert!(is_member);
    }
    
    // Test 5: Non-member proof rejection
    #[test]
    fn test_non_member_proof_rejection() {
        // Arrange
        let dataset_data = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
        let dataset = Dataset::new(dataset_data.clone());
        let fingerprint = DataFingerprint::from_dataset(&dataset);
        let non_member = vec![100.0, 200.0]; // Not in dataset
        
        // Act
        let proof = fingerprint.generate_membership_proof(&dataset_data[0]);
        let is_member = fingerprint.verify_membership(&non_member, &proof);
        
        // Assert
        assert!(!is_member); // Should fail because point hash doesn't match
    }
    
    // Test 6: Data usage proof generation
    #[test]
    fn test_data_usage_proof_generation() {
        // Arrange
        let prover = DataProver::new();
        let dataset = Dataset::new(vec![vec![1.0, 2.0], vec![3.0, 4.0]]);
        
        #[derive(Debug)]
        struct MockModel {
            id: String,
        }
        
        let model = MockModel { id: "test_model".to_string() };
        
        // Act
        let proof = prover.prove_data_usage(&model, &dataset);
        
        // Assert
        assert!(proof.is_valid());
        assert!(!proof.proof_data.is_empty());
    }
    
    // Test 7: Data usage proof verification
    #[test]
    fn test_data_usage_proof_verification() {
        // Arrange
        let prover = DataProver::new();
        let verifier = DataProver::new();
        let dataset = Dataset::new(vec![vec![1.0, 2.0], vec![3.0, 4.0]]);
        
        #[derive(Debug)]
        struct MockModel;
        let model = MockModel;
        
        // Act
        let proof = prover.prove_data_usage(&model, &dataset);
        let is_valid = verifier.verify_proof(&proof);
        
        // Assert
        assert!(is_valid);
    }
    
    // Test 8: Compliance audit
    #[test]
    fn test_compliance_audit() {
        // Arrange
        let auditor = ModelAuditor::new();
        
        #[derive(Debug)]
        struct MockModel;
        let model = MockModel;
        let test_data = Dataset::new(vec![vec![1.0, 2.0], vec![3.0, 4.0]]);
        
        // Act
        let audit_report = auditor.audit_model(&model, &test_data);
        
        // Assert
        assert!(audit_report.timestamp > 0);
        assert!(!audit_report.model_id.is_empty());
        assert!(audit_report.passed); // Should pass with valid test data
        assert!(audit_report.findings.is_empty()); // No findings for valid data
    }

    // Test 9: Failed compliance audit
    #[test]
    fn test_failed_compliance_audit() {
        // Arrange
        let auditor = ModelAuditor::new();
        
        #[derive(Debug)]
        struct MockModel;
        let model = MockModel;
        let empty_test_data = Dataset::new(vec![]); // Empty test data should fail
        
        // Act
        let audit_report = auditor.audit_model(&model, &empty_test_data);
        
        // Assert
        assert!(!audit_report.passed); // Should fail with empty test data
        assert!(!audit_report.findings.is_empty()); // Should have findings
    }

    // Test 10: Dataset with name
    #[test]
    fn test_dataset_with_name() {
        // Arrange
        let points = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
        let name = "test_dataset".to_string();
        
        // Act
        let dataset = Dataset::with_name(points.clone(), name.clone());
        
        // Assert
        assert_eq!(dataset.points, points);
        assert_eq!(dataset.name, name);
    }

    // Test 11: Fingerprint determinism
    #[test]
    fn test_fingerprint_determinism() {
        // Arrange
        let points = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
        let dataset1 = Dataset::new(points.clone());
        let dataset2 = Dataset::new(points);
        
        // Act
        let fingerprint1 = DataFingerprint::from_dataset(&dataset1);
        let fingerprint2 = DataFingerprint::from_dataset(&dataset2);
        
        // Assert
        assert_eq!(fingerprint1.merkle_root, fingerprint2.merkle_root);
        assert_eq!(fingerprint1.topology_signature.hash, fingerprint2.topology_signature.hash);
        // Note: timestamps may differ, so we don't compare them
    }

    // Test 12: Large dataset handling
    #[test]
    fn test_large_dataset_handling() {
        // Arrange
        let large_dataset: Vec<Vec<f64>> = (0..100)
            .map(|i| vec![i as f64, (i * 2) as f64])
            .collect();
        let dataset = Dataset::new(large_dataset);
        
        // Act
        let fingerprint = DataFingerprint::from_dataset(&dataset);
        
        // Assert
        assert!(!fingerprint.dataset_id.is_empty());
        assert!(!fingerprint.merkle_root.is_empty());
        assert!(fingerprint.topology_signature.is_valid());
    }

    // Test 13: Prover default construction
    #[test]
    fn test_prover_default() {
        // Arrange & Act
        let prover = DataProver::default();
        let dataset = Dataset::new(vec![vec![1.0, 2.0]]);
        
        #[derive(Debug)]
        struct MockModel;
        let model = MockModel;
        
        // Act
        let proof = prover.prove_data_usage(&model, &dataset);
        
        // Assert
        assert!(proof.is_valid());
    }

    // Test 14: Auditor default construction
    #[test]
    fn test_auditor_default() {
        // Arrange & Act
        let auditor = ModelAuditor::default();
        
        #[derive(Debug)]
        struct MockModel;
        let model = MockModel;
        let test_data = Dataset::new(vec![vec![1.0, 2.0]]);
        
        // Act
        let report = auditor.audit_model(&model, &test_data);
        
        // Assert
        assert!(report.timestamp > 0);
        assert!(!report.model_id.is_empty());
    }
}

// Property-based tests using proptest
#[cfg(test)]
mod property_tests {
    use proptest::prelude::*;
    use tcdb_core::data_proof::{DataFingerprint, DataProver, Dataset};
    
    proptest! {
        // Property 1: Any dataset produces a valid fingerprint
        #[test]
        fn prop_valid_fingerprint(data in prop::collection::vec(
            prop::collection::vec(prop::num::f64::ANY, 1..10), 
            1..100
        )) {
            let dataset = Dataset::new(data);
            let fingerprint = DataFingerprint::from_dataset(&dataset);
            
            prop_assert!(!fingerprint.dataset_id.is_empty());
            prop_assert!(fingerprint.merkle_root.len() > 0);
        }
        
        // Property 2: Fingerprint is deterministic
        #[test]
        fn prop_fingerprint_deterministic(data in prop::collection::vec(
            prop::collection::vec(prop::num::f64::ANY, 1..10), 
            1..50
        )) {
            let dataset = Dataset::new(data.clone());
            let fingerprint1 = DataFingerprint::from_dataset(&dataset);
            let fingerprint2 = DataFingerprint::from_dataset(&dataset);
            
            prop_assert_eq!(fingerprint1.merkle_root, fingerprint2.merkle_root);
            prop_assert_eq!(fingerprint1.topology_signature.hash, fingerprint2.topology_signature.hash);
        }

        // Property 3: Data usage proofs are always valid when properly generated
        #[test]
        fn prop_data_usage_proof_validity(data in prop::collection::vec(
            prop::collection::vec(prop::num::f64::ANY, 1..5), 
            1..20
        )) {
            let prover = DataProver::new();
            let dataset = Dataset::new(data);
            
            #[derive(Debug)]
            struct MockModel;
            let model = MockModel;
            
            let proof = prover.prove_data_usage(&model, &dataset);
            
            prop_assert!(proof.is_valid());
            prop_assert!(prover.verify_proof(&proof));
        }
    }
}
