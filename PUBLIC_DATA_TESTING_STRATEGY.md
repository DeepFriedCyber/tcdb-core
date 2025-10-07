# Public Data Testing Strategy for TCDB

## Overview

This document outlines a comprehensive strategy for testing TCDB functionality using **publicly available, verifiable datasets**. This ensures independent verification of correctness.

---

## 🎯 **Testing Goals**

1. **Reproducibility** - Anyone can run the same tests
2. **Verifiability** - Results can be checked against known ground truth
3. **Comprehensiveness** - Cover all TCDB modules
4. **Benchmarking** - Compare against established tools
5. **Documentation** - Clear examples for users

---

## 📊 **Public Datasets by Module**

### **1. Topological Data Analysis (TDA)**

#### **A. Classic Point Clouds**

**Dataset**: **Circle** (100 points sampled from unit circle)
- **Source**: Generate programmatically
- **Ground Truth**: 
  - β₀ = 1 (one component)
  - β₁ = 1 (one loop)
  - β₂ = 0 (no voids)
- **Verification**: Well-known result in TDA literature

**Dataset**: **Sphere** (S²)
- **Source**: Generate using spherical coordinates
- **Ground Truth**:
  - β₀ = 1
  - β₁ = 0
  - β₂ = 1
- **Verification**: Euler characteristic χ = 2

**Dataset**: **Torus** (T²)
- **Source**: Generate using torus parametrization
- **Ground Truth**:
  - β₀ = 1
  - β₁ = 2 (two independent loops)
  - β₂ = 1
- **Verification**: Euler characteristic χ = 0

#### **B. Real-World TDA Datasets**

**Dataset**: **MNIST Digits** (subset)
- **Source**: http://yann.lecun.com/exdb/mnist/
- **License**: Public domain
- **Size**: 60,000 training images (28×28 pixels)
- **Test**: Topological signatures of digit classes
- **Verification**: Compare with published TDA papers on MNIST

**Dataset**: **Iris Dataset**
- **Source**: UCI Machine Learning Repository
- **License**: Public domain
- **Size**: 150 samples, 4 features
- **Test**: Persistence diagrams for species clusters
- **Verification**: Well-studied in ML literature

**Dataset**: **Protein Structures** (PDB)
- **Source**: RCSB Protein Data Bank (https://www.rcsb.org/)
- **License**: Open access
- **Example**: 1CRN (Crambin, 46 residues)
- **Test**: Alpha shape persistence
- **Verification**: Published protein topology papers

#### **C. Benchmark TDA Datasets**

**Dataset**: **Ripser Benchmark Suite**
- **Source**: https://github.com/Ripser/ripser
- **Datasets**: 
  - `random16.lower_distance_matrix`
  - `sphere_3_192.distance_matrix`
  - `dragon2000.distance_matrix`
- **Verification**: Compare results with Ripser output

---

### **2. Persistent Homology**

#### **A. Synthetic Examples with Known Results**

**Example 1**: **Two Points**
```rust
// Points: [0], [1]
// Edge: [0,1] at t=1.0
// Expected: 
//   - 2 components born at t=0
//   - 1 component dies at t=1
//   - β₀(t) = 2 for t<1, β₀(t) = 1 for t≥1
```

**Example 2**: **Triangle**
```rust
// Vertices: [0], [1], [2] at t=0
// Edges: [0,1], [1,2], [0,2] at t=1
// Triangle: [0,1,2] at t=2
// Expected:
//   - Loop born at t=1, dies at t=2
//   - Persistence = 1.0
```

**Example 3**: **Noisy Circle**
```rust
// 100 points sampled from circle + Gaussian noise
// Expected: One prominent loop in H₁
// Verification: Persistence should be >> noise level
```

#### **B. Published Benchmark Results**

**Dataset**: **Edelsbrunner & Harer Examples**
- **Source**: "Computational Topology: An Introduction" (2010)
- **Examples**: Figures 7.3, 7.4, 7.5 (persistence diagrams)
- **Verification**: Reproduce exact diagrams from book

**Dataset**: **Carlsson et al. (2008) - Natural Images**
- **Source**: "On the Local Behavior of Spaces of Natural Images"
- **Data**: 3×3 image patches from natural images
- **Expected**: Klein bottle topology
- **Verification**: Reproduce published persistence diagrams

---

### **3. Cross-Domain Reasoning**

#### **A. Multi-Modal Datasets**

**Dataset**: **COCO (Common Objects in Context)**
- **Source**: https://cocodataset.org/
- **License**: CC BY 4.0
- **Modalities**: Images + captions + segmentations
- **Test**: Transfer topological features across modalities
- **Verification**: Compare with published multi-modal learning results

**Dataset**: **AudioSet**
- **Source**: https://research.google.com/audioset/
- **License**: CC BY 4.0
- **Modalities**: Audio + video + labels
- **Test**: Cross-domain topological signatures
- **Verification**: Audio-visual correspondence metrics

#### **B. Domain Adaptation Benchmarks**

**Dataset**: **Office-31**
- **Source**: https://faculty.cc.gatech.edu/~judy/domainadapt/
- **Domains**: Amazon, DSLR, Webcam (product images)
- **Test**: Topological domain alignment
- **Verification**: Classification accuracy after transfer

---

### **4. Data Provenance**

#### **A. Synthetic Reasoning Chains**

**Example**: **Mathematical Proof**
```
Generation: "Define prime number"
  ↓
Retrieval: "Fetch definition from knowledge base"
  ↓
Transformation: "Apply to specific number"
  ↓
Output: "17 is prime"
```
**Verification**: Trace back to axioms

#### **B. Real Reasoning Datasets**

**Dataset**: **ProofWiki**
- **Source**: https://proofwiki.org/
- **License**: CC BY-SA
- **Content**: Mathematical proofs with dependencies
- **Test**: Build provenance DAG
- **Verification**: Check proof validity

**Dataset**: **Lean Mathlib**
- **Source**: https://github.com/leanprover-community/mathlib
- **License**: Apache 2.0
- **Content**: Formal proofs in Lean
- **Test**: Extract reasoning steps
- **Verification**: Lean type-checker

---

### **5. Data Proofs (Merkle Trees)**

#### **A. Blockchain Data**

**Dataset**: **Bitcoin Blocks**
- **Source**: https://blockchain.info/
- **License**: Public blockchain data
- **Test**: Verify Merkle tree construction
- **Verification**: Compare with actual block hashes

**Dataset**: **Ethereum State**
- **Source**: https://etherscan.io/
- **License**: Public blockchain data
- **Test**: Merkle Patricia tree verification
- **Verification**: Compare with Ethereum nodes

#### **B. Git Repositories**

**Dataset**: **Linux Kernel**
- **Source**: https://github.com/torvalds/linux
- **License**: GPL-2.0
- **Test**: Commit hash verification
- **Verification**: Git's own hash verification

---

## 🧪 **Testing Implementation**

### **Directory Structure**

```
tcdb-core/
├── tests/
│   ├── public_data/
│   │   ├── tda/
│   │   │   ├── circle_test.rs
│   │   │   ├── sphere_test.rs
│   │   │   ├── torus_test.rs
│   │   │   ├── mnist_test.rs
│   │   │   └── iris_test.rs
│   │   ├── persistence/
│   │   │   ├── two_points_test.rs
│   │   │   ├── triangle_test.rs
│   │   │   └── benchmark_test.rs
│   │   ├── cross_domain/
│   │   │   ├── coco_test.rs
│   │   │   └── office31_test.rs
│   │   ├── provenance/
│   │   │   ├── proofwiki_test.rs
│   │   │   └── mathlib_test.rs
│   │   └── data_proof/
│   │       ├── bitcoin_test.rs
│   │       └── git_test.rs
│   └── data/
│       ├── download.sh          # Script to fetch datasets
│       ├── README.md            # Data sources and licenses
│       └── checksums.txt        # Verify data integrity
```

---

## 📝 **Example Test: Circle Dataset**

### **Test Implementation**

```rust
// tests/public_data/tda/circle_test.rs

use tcdb_core::{Dataset, TopologicalSignature, PersistentHomology, Filtration};
use std::f64::consts::PI;

#[test]
fn test_circle_topology() {
    // Generate 100 points on unit circle
    let n = 100;
    let points: Vec<Vec<f64>> = (0..n)
        .map(|i| {
            let theta = 2.0 * PI * (i as f64) / (n as f64);
            vec![theta.cos(), theta.sin()]
        })
        .collect();
    
    let dataset = Dataset::new(points);
    
    // Compute topological signature
    let signature = TopologicalSignature::from_point_cloud(&dataset, 0.5).unwrap();
    
    // Verify Betti numbers
    assert_eq!(signature.betti_numbers[0], 1, "Should have 1 connected component");
    assert_eq!(signature.betti_numbers[1], 1, "Should have 1 loop");
    assert_eq!(signature.betti_numbers[2], 0, "Should have 0 voids");
    
    // Verify Euler characteristic
    let euler = signature.euler_characteristic();
    assert_eq!(euler, 0, "Circle has Euler characteristic 0");
    
    // Compute persistence diagram
    let filtration = signature.build_vietoris_rips(2.0, 2);
    let ph = PersistentHomology::new(filtration);
    let diagrams = ph.compute().unwrap();
    
    // Verify H₁ has one prominent feature
    let h1 = diagrams.iter().find(|d| d.dimension == 1).unwrap();
    let significant = h1.significant_points(0.1);
    assert_eq!(significant.len(), 1, "Should have 1 significant loop");
    
    // Verify persistence is large (loop is real, not noise)
    let loop_persistence = significant[0].persistence();
    assert!(loop_persistence > 0.5, "Loop should have high persistence");
}

#[test]
fn test_circle_vs_ripser() {
    // Load pre-computed Ripser results
    let ripser_output = include_str!("../../data/circle_ripser_output.txt");
    let expected_diagram = parse_ripser_output(ripser_output);
    
    // Compute with TCDB
    let dataset = generate_circle(100);
    let signature = TopologicalSignature::from_point_cloud(&dataset, 0.5).unwrap();
    let filtration = signature.build_vietoris_rips(2.0, 2);
    let ph = PersistentHomology::new(filtration);
    let diagrams = ph.compute().unwrap();
    
    // Compare results
    let h1 = diagrams.iter().find(|d| d.dimension == 1).unwrap();
    assert_diagrams_equal(h1, &expected_diagram, 1e-6);
}

fn generate_circle(n: usize) -> Dataset {
    let points: Vec<Vec<f64>> = (0..n)
        .map(|i| {
            let theta = 2.0 * PI * (i as f64) / (n as f64);
            vec![theta.cos(), theta.sin()]
        })
        .collect();
    Dataset::new(points)
}

fn parse_ripser_output(output: &str) -> PersistenceDiagram {
    // Parse Ripser format
    // ...
}

fn assert_diagrams_equal(actual: &PersistenceDiagram, expected: &PersistenceDiagram, tolerance: f64) {
    assert_eq!(actual.points.len(), expected.points.len());
    for (a, e) in actual.points.iter().zip(expected.points.iter()) {
        assert!((a.birth - e.birth).abs() < tolerance);
        assert!((a.death - e.death).abs() < tolerance);
    }
}
```

---

## 📊 **Verification Methods**

### **1. Ground Truth Comparison**

```rust
#[test]
fn verify_against_ground_truth() {
    let result = tcdb_compute(...);
    let ground_truth = load_ground_truth("data/expected_result.json");
    assert_eq!(result, ground_truth);
}
```

### **2. Cross-Tool Validation**

Compare TCDB results with established tools:
- **Ripser** - Persistent homology
- **GUDHI** - TDA library
- **Dionysus** - Persistence computation
- **scikit-tda** - Python TDA tools

### **3. Mathematical Invariants**

```rust
#[test]
fn verify_euler_characteristic() {
    let signature = compute_topology(...);
    let euler = signature.euler_characteristic();
    let expected_euler = 2; // For sphere
    assert_eq!(euler, expected_euler);
}
```

### **4. Reproducibility Tests**

```rust
#[test]
fn test_reproducibility() {
    let result1 = tcdb_compute(data.clone());
    let result2 = tcdb_compute(data.clone());
    assert_eq!(result1, result2, "Results should be deterministic");
}
```

---

## 🚀 **Implementation Plan**

### **Phase 1: Basic Synthetic Tests** (Week 1)
- ✅ Circle, sphere, torus
- ✅ Two points, triangle
- ✅ Known Betti numbers

### **Phase 2: Benchmark Datasets** (Week 2)
- ⬜ Ripser benchmark suite
- ⬜ Edelsbrunner & Harer examples
- ⬜ Cross-tool validation

### **Phase 3: Real-World Data** (Week 3)
- ⬜ MNIST subset
- ⬜ Iris dataset
- ⬜ Protein structures

### **Phase 4: Multi-Modal** (Week 4)
- ⬜ COCO dataset
- ⬜ Office-31
- ⬜ Cross-domain tests

### **Phase 5: Provenance & Proofs** (Week 5)
- ⬜ ProofWiki
- ⬜ Bitcoin blocks
- ⬜ Git repositories

---

## 📚 **Documentation**

### **For Each Test**:
1. **Dataset description** - What it is, where it's from
2. **Expected results** - Ground truth values
3. **Verification method** - How to check correctness
4. **References** - Papers, tools, documentation
5. **License** - Data usage rights

### **Example Documentation**:

```markdown
## Circle Test

**Dataset**: 100 points sampled uniformly from unit circle

**Source**: Generated programmatically using `θ ∈ [0, 2π)`

**Expected Results**:
- β₀ = 1 (one connected component)
- β₁ = 1 (one loop)
- Euler characteristic χ = 0

**Verification**:
- Compare with Ripser output (included in `data/circle_ripser_output.txt`)
- Check mathematical invariants (Euler characteristic)
- Visual inspection of persistence diagram

**References**:
- Edelsbrunner & Harer, "Computational Topology", Example 7.1
- Ripser documentation: https://ripser.scikit-tda.org/

**License**: Generated data, no restrictions
```

---

## 🎯 **Success Criteria**

### **Correctness**:
- ✅ All tests pass
- ✅ Results match ground truth within tolerance
- ✅ Cross-tool validation succeeds

### **Reproducibility**:
- ✅ Anyone can download data and run tests
- ✅ Results are deterministic
- ✅ Clear documentation

### **Coverage**:
- ✅ All TCDB modules tested
- ✅ Multiple datasets per module
- ✅ Edge cases covered

---

## 📦 **Deliverables**

1. **Test Suite** - Comprehensive public data tests
2. **Data Download Script** - Automated dataset fetching
3. **Documentation** - Clear instructions and references
4. **CI Integration** - Automated testing on GitHub Actions
5. **Benchmark Report** - Performance comparison with other tools

---

## 🔗 **Resources**

### **TDA Tools for Comparison**:
- **Ripser**: https://github.com/Ripser/ripser
- **GUDHI**: https://gudhi.inria.fr/
- **Dionysus**: https://www.mrzv.org/software/dionysus2/
- **giotto-tda**: https://github.com/giotto-ai/giotto-tda

### **Dataset Repositories**:
- **UCI ML Repository**: https://archive.ics.uci.edu/ml/
- **Kaggle Datasets**: https://www.kaggle.com/datasets
- **OpenML**: https://www.openml.org/
- **TDA Datasets**: https://github.com/scikit-tda/datasets

### **Papers with Reproducible Results**:
- Carlsson et al. (2008) - Natural image topology
- Ghrist (2008) - Elementary Applied Topology
- Edelsbrunner & Harer (2010) - Computational Topology

---

## 🎉 **Summary**

This strategy provides:
- ✅ **Verifiable correctness** - Compare with known results
- ✅ **Independent validation** - Anyone can reproduce
- ✅ **Comprehensive coverage** - All modules tested
- ✅ **Benchmarking** - Compare with established tools
- ✅ **Documentation** - Clear examples for users

**Next Steps**: Implement Phase 1 (basic synthetic tests) to establish the testing framework!

