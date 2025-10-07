//! Provenance Certificate Example
//!
//! Demonstrates how to create verifiable computational proofs using
//! provenance certificates with persistent homology.

use tcdb_core::{
    Certificate, Filtration, PersistentHomology, Simplex,
    hash_persistence_diagram,
};

fn main() {
    println!("=== Provenance Certificate Example ===\n");

    // ========================================================================
    // STEP 1: Input Data
    // ========================================================================
    
    println!("STEP 1: Input Data");
    println!("------------------");
    
    // In practice, this would be actual data (point cloud, time series, etc.)
    let input_data = b"circle_dataset_100_points";
    
    // Compute content ID (in practice, use SHA256 or IPFS CID)
    let data_cid = format!("sha256:{}", blake3::hash(input_data).to_hex());
    println!("Data CID: {}", data_cid);
    println!();

    // ========================================================================
    // STEP 2: Code Version
    // ========================================================================
    
    println!("STEP 2: Code Version");
    println!("--------------------");
    
    // In practice, use git commit hash or semver
    let code_rev = "v1.0.0";
    println!("Code version: {}", code_rev);
    println!();

    // ========================================================================
    // STEP 3: Computation (Persistent Homology)
    // ========================================================================
    
    println!("STEP 3: Computation");
    println!("-------------------");
    
    // Build filtration (simplified circle example)
    let mut filtration = Filtration::new();
    
    // Add 4 vertices
    filtration.add_simplex(0.0, Simplex::new(vec![0])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![1])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![2])).unwrap();
    filtration.add_simplex(0.0, Simplex::new(vec![3])).unwrap();
    
    // Add 4 edges forming a cycle
    filtration.add_simplex(1.0, Simplex::new(vec![0, 1])).unwrap();
    filtration.add_simplex(1.0, Simplex::new(vec![1, 2])).unwrap();
    filtration.add_simplex(1.0, Simplex::new(vec![2, 3])).unwrap();
    filtration.add_simplex(1.0, Simplex::new(vec![3, 0])).unwrap();
    
    println!("Filtration built: 4 vertices, 4 edges (cycle)");
    
    // Compute persistent homology
    let ph = PersistentHomology::new(filtration);
    let diagrams = ph.compute().unwrap();
    
    println!("Persistent homology computed");
    
    // Extract persistence diagram as (birth, death) pairs
    let mut pd_points = Vec::new();
    for diagram in &diagrams {
        for point in &diagram.points {
            pd_points.push((point.birth, point.death));
        }
    }
    
    println!("Persistence diagram: {} points", pd_points.len());
    for (i, (b, d)) in pd_points.iter().enumerate() {
        if d.is_infinite() {
            println!("  Point {}: birth={:.2}, death=inf", i, b);
        } else {
            println!("  Point {}: birth={:.2}, death={:.2}", i, b, d);
        }
    }
    println!();

    // ========================================================================
    // STEP 4: Create Certificate
    // ========================================================================
    
    println!("STEP 4: Create Certificate");
    println!("--------------------------");
    
    let cert = Certificate::new(&data_cid, code_rev, &pd_points);
    
    println!("Certificate created:");
    println!("  Data CID: {}", cert.data_cid);
    println!("  Code Rev: {}", cert.code_rev);
    println!("  Result Hash: {}", cert.result_hash);
    println!();

    // ========================================================================
    // STEP 5: Generate Audit Token
    // ========================================================================
    
    println!("STEP 5: Generate Audit Token");
    println!("-----------------------------");
    
    let audit_token = cert.audit_token();
    println!("Audit Token: {}", audit_token);
    println!("(This is a single hash representing the entire certificate)");
    println!();

    // ========================================================================
    // STEP 6: Serialize Certificate
    // ========================================================================
    
    println!("STEP 6: Serialize Certificate");
    println!("------------------------------");
    
    let json = serde_json::to_string_pretty(&cert).unwrap();
    println!("Certificate JSON:");
    println!("{}", json);
    println!();

    // ========================================================================
    // STEP 7: Verification
    // ========================================================================
    
    println!("STEP 7: Verification");
    println!("--------------------");
    
    // Simulate loading certificate from storage
    let cert_loaded: Certificate = serde_json::from_str(&json).unwrap();
    
    // Verify audit token matches
    assert_eq!(cert_loaded.audit_token(), audit_token);
    println!("✓ Audit token verified");
    
    // Verify result matches
    assert!(cert_loaded.verify_result(&pd_points));
    println!("✓ Result verified");
    
    // Try with wrong result
    let wrong_pd = vec![(0.0, 1.0), (0.5, 2.1)]; // Different
    assert!(!cert_loaded.verify_result(&wrong_pd));
    println!("✓ Wrong result correctly rejected");
    println!();

    // ========================================================================
    // STEP 8: Reproducibility Test
    // ========================================================================
    
    println!("STEP 8: Reproducibility Test");
    println!("-----------------------------");
    
    // Create another certificate with same inputs
    let cert2 = Certificate::new(&data_cid, code_rev, &pd_points);
    
    // Should be identical
    assert_eq!(cert.data_cid, cert2.data_cid);
    assert_eq!(cert.code_rev, cert2.code_rev);
    assert_eq!(cert.result_hash, cert2.result_hash);
    assert_eq!(cert.audit_token(), cert2.audit_token());
    
    println!("✓ Certificates are deterministic");
    println!("✓ Same inputs → same certificate");
    println!();

    // ========================================================================
    // STEP 9: Order Independence
    // ========================================================================
    
    println!("STEP 9: Order Independence");
    println!("--------------------------");
    
    // Create certificate with points in different order
    let mut pd_shuffled = pd_points.clone();
    pd_shuffled.reverse();
    
    let cert3 = Certificate::new(&data_cid, code_rev, &pd_shuffled);
    
    // Result hash should be same (canonical ordering)
    assert_eq!(cert.result_hash, cert3.result_hash);
    
    println!("✓ Order-independent hashing");
    println!("✓ Canonical sorting ensures consistency");
    println!();

    // ========================================================================
    // STEP 10: Use Cases
    // ========================================================================
    
    println!("STEP 10: Use Cases");
    println!("------------------");
    
    println!("This certificate can be used for:");
    println!();
    
    println!("1. Scientific Reproducibility");
    println!("   - Publish certificate with paper");
    println!("   - Anyone can verify computation");
    println!();
    
    println!("2. AI Model Auditing");
    println!("   - Prove what data trained model");
    println!("   - Verify code version used");
    println!();
    
    println!("3. Regulatory Compliance");
    println!("   - Prove approved data/code used");
    println!("   - Immutable audit trail");
    println!();
    
    println!("4. Blockchain Integration");
    println!("   - Store audit token on-chain");
    println!("   - Timestamped proof of computation");
    println!();

    // ========================================================================
    // Summary
    // ========================================================================
    
    println!("=== Summary ===");
    println!();
    println!("✓ Certificate created and verified");
    println!("✓ Deterministic computation proven");
    println!("✓ Order-independent hashing confirmed");
    println!("✓ Serialization/deserialization working");
    println!();
    println!("Certificate binds:");
    println!("  • Data: {}", cert.data_cid);
    println!("  • Code: {}", cert.code_rev);
    println!("  • Result: {} points", pd_points.len());
    println!();
    println!("Audit Token: {}", audit_token);
    println!();
    println!("Anyone can verify this computation by:");
    println!("  1. Loading data from CID");
    println!("  2. Running code version {}", code_rev);
    println!("  3. Comparing result hash");
    println!();
    println!("🎯 Verifiable computational proof complete!");
}

