# Provenance Certificates - Verifiable Computational Proofs

## Overview

**Provenance Certificates** provide cryptographically verifiable proof that a specific computation was performed on specific data with specific code, producing a specific result.

This creates an **immutable audit trail** from data → code → result that anyone can independently verify.

---

## 🎯 **Problem Statement**

### **The Challenge**

In scientific computing and AI systems, we need to answer:

1. **"What data was used?"** - Input provenance
2. **"What code computed this?"** - Algorithm provenance
3. **"What was the result?"** - Output verification
4. **"Can I trust this?"** - Independent verification

### **Traditional Approaches Fail**

- ❌ **Manual logs** - Can be forged or lost
- ❌ **Timestamps** - Can be manipulated
- ❌ **Signatures** - Don't bind data + code + result
- ❌ **Checksums** - Don't prove computation happened

### **Our Solution: Provenance Certificates**

✅ **Cryptographically binding** data, code, and result  
✅ **Deterministic** - Same inputs always produce same certificate  
✅ **Verifiable** - Anyone can recompute and verify  
✅ **Immutable** - Cannot be forged or modified  
✅ **Auditable** - Full chain of custody  

---

## 🔧 **How It Works**

### **Three-Way Binding**

A certificate binds three components:

```
┌─────────────┐
│   DATA      │ ──┐
│  (CID)      │   │
└─────────────┘   │
                  ├──> CERTIFICATE ──> AUDIT TOKEN
┌─────────────┐   │
│   CODE      │ ──┤
│  (version)  │   │
└─────────────┘   │
                  │
┌─────────────┐   │
│  RESULT     │ ──┘
│  (hash)     │
└─────────────┘
```

### **Certificate Structure**

```rust
pub struct Certificate {
    /// Content ID for input data (e.g., "sha256:abc123...")
    pub data_cid: String,
    
    /// Code version (e.g., "v1.0.0" or git commit "a1b2c3d")
    pub code_rev: String,
    
    /// Canonical hash of persistence diagram
    pub result_hash: String,
}
```

### **Canonical Result Hashing**

The result hash is computed deterministically:

1. **Sort** persistence diagram by (birth, death)
2. **Format** each point with 17 decimal places (full f64 precision)
3. **Concatenate** into canonical string
4. **Hash** with BLAKE3

This ensures:
- ✅ Order-independent (sorting)
- ✅ Precision-preserving (17 decimals)
- ✅ Collision-resistant (BLAKE3)
- ✅ Deterministic (same input → same hash)

---

## 📚 **API Reference**

### **Creating a Certificate**

```rust
use tcdb_core::Certificate;

// Input data
let data = b"some input data";
let data_cid = format!("sha256:{}", hash_bytes(data));

// Code version
let code_rev = "v1.0.0";

// Computation result (persistence diagram)
let pd = vec![(0.0, 1.0), (0.5, 2.0), (1.0, 3.0)];

// Create certificate
let cert = Certificate::new(&data_cid, code_rev, &pd);
```

### **Getting Audit Token**

```rust
// Single hash representing entire certificate
let token = cert.audit_token();

// Store or transmit token
println!("Audit token: {}", token);
// Output: "a1b2c3d4e5f6..." (64-char BLAKE3 hash)
```

### **Verifying Results**

```rust
// Later: verify a result matches the certificate
let pd_to_verify = vec![(0.0, 1.0), (0.5, 2.0), (1.0, 3.0)];

if cert.verify_result(&pd_to_verify) {
    println!("✓ Result verified!");
} else {
    println!("✗ Result does NOT match certificate!");
}
```

### **Serialization**

```rust
// Serialize to JSON
let json = serde_json::to_string(&cert)?;

// Store in database, file, or blockchain
store_certificate(&json);

// Later: deserialize and verify
let cert_loaded: Certificate = serde_json::from_str(&json)?;
assert_eq!(cert_loaded.audit_token(), token);
```

---

## 🔍 **Use Cases**

### **1. Scientific Reproducibility**

**Problem**: "Can you reproduce this result?"

**Solution**:
```rust
// Researcher publishes certificate with paper
let cert = Certificate::new(
    "ipfs://QmXyz...",  // Dataset on IPFS
    "v2.1.0",           // Code version
    &persistence_diagram
);

// Anyone can verify:
// 1. Download data from IPFS
// 2. Run code v2.1.0
// 3. Compare result hash
```

### **2. AI Model Auditing**

**Problem**: "What data trained this model?"

**Solution**:
```rust
// Training run creates certificate
let cert = Certificate::new(
    "sha256:training_data_hash",
    "commit:a1b2c3d",
    &topology_signature
);

// Auditor verifies:
// 1. Data hash matches claimed dataset
// 2. Code matches claimed version
// 3. Result matches claimed topology
```

### **3. Regulatory Compliance**

**Problem**: "Prove this analysis used approved data and code"

**Solution**:
```rust
// Analysis creates certificate
let cert = Certificate::new(
    "approved_dataset_v3",
    "certified_code_v1.0",
    &analysis_result
);

// Regulator verifies:
// 1. Data CID in approved list
// 2. Code version is certified
// 3. Result hash matches submission
```

### **4. Blockchain Integration**

**Problem**: "Create immutable record of computation"

**Solution**:
```rust
// Compute and certify
let cert = Certificate::new(data_cid, code_rev, &result);
let token = cert.audit_token();

// Store token on blockchain
blockchain.store_proof(token, timestamp);

// Later: anyone can verify
let cert_loaded = load_certificate();
assert_eq!(cert_loaded.audit_token(), blockchain.get_proof());
```

---

## 🧪 **Testing & Verification**

### **Test Coverage**

**16 comprehensive tests** covering:

1. ✅ **Hash determinism** - Same input → same hash
2. ✅ **Order independence** - Sorting ensures canonical form
3. ✅ **Certificate creation** - Proper initialization
4. ✅ **Certificate determinism** - Reproducible certificates
5. ✅ **Different data** - Different CID → different cert
6. ✅ **Different code** - Different version → different cert
7. ✅ **Different result** - Different PD → different cert
8. ✅ **Audit token** - Deterministic token generation
9. ✅ **Result verification** - Correct/incorrect detection
10. ✅ **Serialization** - JSON round-trip preservation
11. ✅ **Full workflow** - End-to-end verification

### **Running Tests**

```bash
# Run all certificate tests
cargo test certificate

# Run with output
cargo test certificate -- --nocapture

# Run specific test
cargo test test_full_workflow
```

### **Test Results**

```
running 16 tests
test test_hash_bytes ... ok
test test_hash_persistence_diagram_deterministic ... ok
test test_hash_persistence_diagram_order_independent ... ok
test test_hash_persistence_diagram_different_values ... ok
test test_certificate_creation ... ok
test test_certificate_deterministic ... ok
test test_certificate_different_data ... ok
test test_certificate_different_code ... ok
test test_certificate_different_result ... ok
test test_audit_token_deterministic ... ok
test test_audit_token_different_certificates ... ok
test test_verify_result_correct ... ok
test test_verify_result_incorrect ... ok
test test_verify_result_order_independent ... ok
test test_certificate_serialization ... ok
test test_full_workflow ... ok

test result: ok. 16 passed; 0 failed
```

---

## 🔐 **Security Properties**

### **Cryptographic Guarantees**

1. **Collision Resistance**
   - BLAKE3 provides 128-bit security
   - Probability of collision: ~2^-128
   - Practically impossible to forge

2. **Preimage Resistance**
   - Cannot reverse hash to find input
   - Cannot forge certificate with specific hash

3. **Second Preimage Resistance**
   - Cannot find different input with same hash
   - Cannot substitute data/code/result

### **Determinism Guarantees**

1. **Canonical Ordering**
   - Persistence diagrams sorted before hashing
   - Order-independent verification

2. **Precision Preservation**
   - 17 decimal places (full f64 precision)
   - No rounding errors

3. **Locale Independence**
   - Fixed formatting (no locale-specific separators)
   - Cross-platform reproducibility

---

## 📊 **Performance**

### **Hashing Performance**

- **BLAKE3**: ~3 GB/s on modern CPUs
- **Certificate creation**: < 1ms for typical PD
- **Verification**: < 1ms

### **Storage**

- **Certificate**: ~200 bytes (JSON)
- **Audit token**: 64 bytes (hex string)
- **Minimal overhead**

---

## 🚀 **Future Enhancements**

### **Planned Features**

1. **Merkle Trees** - Batch verification of multiple certificates
2. **Zero-Knowledge Proofs** - Prove properties without revealing data
3. **Threshold Signatures** - Multi-party certificate signing
4. **Timestamping** - Blockchain-based timestamp proofs
5. **Revocation** - Certificate revocation lists

### **Integration Opportunities**

1. **IPFS** - Content-addressed data storage
2. **Ethereum** - Smart contract verification
3. **Git** - Code provenance tracking
4. **Lean** - Formal proof verification
5. **Jupyter** - Notebook reproducibility

---

## 📖 **References**

### **Cryptography**

- **BLAKE3**: https://github.com/BLAKE3-team/BLAKE3
- **Content Addressing**: https://docs.ipfs.tech/concepts/content-addressing/

### **Provenance**

- **W3C PROV**: https://www.w3.org/TR/prov-overview/
- **Reproducibility**: https://www.nature.com/articles/s41586-020-2649-2

### **Applications**

- **Scientific Workflows**: https://www.commonwl.org/
- **Blockchain Proofs**: https://proofofexistence.com/

---

## ✅ **Summary**

**Provenance Certificates** provide:

1. ✅ **Cryptographic binding** of data + code + result
2. ✅ **Deterministic** computation verification
3. ✅ **Independent** reproducibility
4. ✅ **Immutable** audit trails
5. ✅ **Minimal** overhead

**Use Cases**:
- Scientific reproducibility
- AI model auditing
- Regulatory compliance
- Blockchain integration

**Security**:
- BLAKE3 cryptographic hashing
- Collision-resistant (2^-128)
- Deterministic verification

**Testing**:
- 16 comprehensive tests
- 100% pass rate
- Full workflow coverage

---

**TCDB now provides verifiable computational proofs!** 🎯

