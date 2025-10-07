# TCDB Core Architecture

## Design Philosophy

**Correctness + Performance + Usability**

1. **Rust Core**: Performance-critical computations
2. **Lean Verification**: Mathematical correctness proofs
3. **Python API**: Easy-to-use interface

## Layer Architecture

```
┌─────────────────────────────────────────┐
│         Python API Layer                │
│  (Flask REST API + Python bindings)     │
├─────────────────────────────────────────┤
│         PyO3 Bindings Layer             │
│  (Rust ↔ Python interface)              │
├─────────────────────────────────────────┤
│         Rust Core Layer                 │
│  (High-performance computations)        │
├─────────────────────────────────────────┤
│         Lean Verification Layer         │
│  (Mathematical proofs)                  │
└─────────────────────────────────────────┘
```

## Component Details

### 1. Rust Core (`rust/src/`)

#### `lib.rs`
- Main library entry point
- Error types and result handling
- Module exports

#### `simplicial_complex.rs`
- `Simplex`: Ordered set of vertices
- `SimplicialComplex`: Collection of simplices
- Operations:
  - `add_simplex()`: Add with automatic face closure
  - `euler_characteristic()`: Compute χ
  - `verify_closure()`: Check mathematical invariant

**Key Properties**:
- Closure property enforced automatically
- Efficient HashSet-based storage
- O(1) simplex lookup

#### `filtration.rs`
- `Filtration`: Assigns real values to simplices
- `FiltrationValue`: Type alias for f64
- Operations:
  - `set_value()`: Set with monotonicity check
  - `simplices_at_value()`: Get sublevel set
  - `verify_monotonicity()`: Check invariant

**Key Properties**:
- Monotonicity: f(σ) ≤ f(τ) for σ ⊆ τ
- Sublevel sets form simplicial complexes

#### `persistent_homology.rs`
- `PersistencePoint`: (birth, death, dimension)
- `PersistenceDiagram`: Collection of points
- `Barcode`: Alternative representation
- `PersistentHomology`: Computation engine

**Algorithm** (TODO: Full implementation):
1. Build boundary matrix
2. Reduce matrix (column algorithm)
3. Extract birth-death pairs
4. Construct persistence diagram

#### `bindings.rs`
- PyO3 wrappers for Python
- Type conversions
- Error handling
- Module definition

### 2. Lean Verification (`lean/Tcdb/`)

#### `Topology/SimplicialComplex.lean`
- Formal definition of simplices
- Closure property proof
- Euler characteristic correctness
- Face relation properties

**Key Theorems**:
```lean
theorem faces_count_correct : 
  k-simplex has exactly k+1 faces

theorem closure_property : 
  ∀ σ ∈ K, ∀ τ face of σ → τ ∈ K

theorem euler_characteristic_correct :
  χ = Σ(-1)^k * n_k
```

#### `Topology/Filtration.lean`
- Filtration definition
- Monotonicity property
- Sublevel set theorems

**Key Theorems**:
```lean
theorem monotone_property :
  σ ⊆ τ → f(σ) ≤ f(τ)

theorem sublevel_is_complex :
  K_t = {σ | f(σ) ≤ t} is a simplicial complex
```

#### `PersistentHomology/Basic.lean`
- Persistence module definition
- Diagram construction
- Stability theorem

**Key Theorems**:
```lean
theorem structure_theorem :
  Persistence modules decompose into intervals

theorem persistence_stability :
  |f - g|_∞ ≤ ε → d_bottleneck(D_f, D_g) ≤ ε
```

#### `PersistentHomology/BettiNumbers.lean`
- Betti number definition
- Relationship to homology
- Euler characteristic formula

**Key Theorems**:
```lean
theorem betti_number_is_rank :
  β_k = rank(H_k)

theorem euler_from_betti :
  χ = Σ(-1)^k * β_k
```

### 3. Python API (`python/tcdb_api/`)

#### `app.py`
- Flask application factory
- CORS configuration
- Rate limiting
- Error handlers

#### `endpoints/health.py`
- Health checks
- Component status
- Rust binding verification

#### `endpoints/tda.py`
- Simplex creation
- Complex construction
- Rips complex computation
- Persistence computation

#### `endpoints/pipeline.py`
- Full TDA pipeline
- Job management
- Async processing (future)

## Data Flow

### Example: Computing Persistent Homology

```
1. User Request (Python/REST)
   ↓
2. Python API validates input
   ↓
3. PyO3 converts to Rust types
   ↓
4. Rust builds simplicial complex
   ↓
5. Rust constructs filtration
   ↓
6. Rust computes persistence
   ↓
7. PyO3 converts results to Python
   ↓
8. Python API returns JSON
```

### Type Conversions

**Python → Rust**:
```python
vertices: List[int] → Vec<usize>
points: np.ndarray → Vec<Vec<f64>>
```

**Rust → Python**:
```rust
Simplex → PySimplex
SimplicialComplex → PySimplicialComplex
PersistenceDiagram → PyPersistenceDiagram
```

## Testing Strategy

### 1. Unit Tests (Rust)
- Each module has `#[cfg(test)]` section
- Test mathematical properties
- Test edge cases

### 2. Integration Tests (Rust)
- `rust/tests/integration_test.rs`
- Test component interactions
- Test realistic workflows

### 3. Binding Tests (Python)
- `python/tests/test_rust_bindings.py`
- Test Python ↔ Rust interface
- Test type conversions

### 4. API Tests (Python)
- `python/tests/test_api.py`
- Test REST endpoints
- Test error handling

### 5. Property Tests (Rust)
- Use `proptest` crate
- Test invariants hold for random inputs
- Fuzzing for edge cases

## Performance Considerations

### Rust Optimizations
- `HashSet` for O(1) simplex lookup
- `rayon` for parallel computation (future)
- Zero-copy where possible
- Efficient memory layout

### Python Optimizations
- Minimize Python ↔ Rust crossings
- Batch operations
- NumPy integration for arrays

### Future Optimizations
- GPU acceleration for matrix operations
- Sparse matrix representations
- Incremental computation
- Caching of intermediate results

## Error Handling

### Rust Errors
```rust
pub enum TcdbError {
    InvalidDimension(usize),
    SimplexNotFound,
    InvalidFiltration,
    ComputationError(String),
}
```

### Python Errors
- `PyValueError` for invalid inputs
- `PyRuntimeError` for computation errors
- HTTP status codes for API errors

## Build System

### Cargo (Rust)
- Workspace with single member
- Release optimizations
- Feature flags for optional components

### Maturin (Python Bindings)
- Builds Rust → Python extension
- Handles PyO3 integration
- Creates wheels for distribution

### Makefile
- Unified build interface
- Test runners
- Development helpers

## Deployment

### Development
```bash
maturin develop  # Build and install locally
```

### Production
```bash
maturin build --release  # Build wheel
pip install target/wheels/*.whl
```

### Docker (Future)
```dockerfile
FROM rust:1.70 as builder
# Build Rust library
FROM python:3.11
# Install Python package
```

## Verification & Certificates

### LLM Hallucination Prevention

TCDB provides a **verification layer** to prevent LLM hallucinations about topological properties.

#### Architecture

```
┌─────────────────────────────────────────┐
│         LLM Output (Unverified)         │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│      TCDB Verification Gates            │
│                                         │
│  1. Topology Constraints                │
│     - Euler characteristic              │
│     - Betti numbers ≥ 0                 │
│     - Death ≥ Birth in PD               │
│                                         │
│  2. Bayesian Confidence                 │
│     - Posterior computation             │
│     - Evidence validation               │
│                                         │
│  3. Provenance Verification             │
│     - BLAKE3 hashing                    │
│     - Cryptographic binding             │
│                                         │
│  4. Reasoner Constraints                │
│     - Similarity ∈ [0,1]                │
│     - Statistics consistency            │
└──────────────┬──────────────────────────┘
               │
               ▼
┌─────────────────────────────────────────┐
│    Verified Output or Violation Report  │
└─────────────────────────────────────────┘
```

#### Components

**1. Provenance Certificates** (`rust/src/provenance.rs`)
- BLAKE3 hashing of persistence diagrams
- Cryptographic binding of data, code, and results
- Audit tokens for tamper detection

**2. Reasoner Constraints** (`rust/src/reasoner.rs`)
- Lightweight validation gates
- Constraint checking (BettiNonNegative, DeathGeBirth, etc.)
- Violation reporting with severity levels

**3. Bayesian Inference** (`rust/src/bayes.rs`)
- Posterior probability computation
- Sequential evidence updates
- Confidence validation

**4. Evaluation Harness** (`examples/eval/hallucination_eval.py`)
- A/B testing framework
- Hallucination detection metrics
- Precision, recall, F1 scoring

#### Usage Example

```python
from python.examples.llm_verification_layer import LLMVerificationLayer

# Create verifier
verifier = LLMVerificationLayer(strict_mode=True)

# Verify LLM output
llm_output = {
    "euler_characteristic": 5,  # LLM claim
    "confidence": 0.99
}

ground_truth = {
    "fvector": [6, 12, 8],  # Actual data (sphere)
    "bayesian": {"prior": 0.01, "evidence": {...}}
}

# Check all gates
verified = verifier.verify_topology_claim(llm_output, ground_truth)

if not verified:
    print(verifier.get_violations_report())
    # Output: "❌ HALLUCINATION: Sphere has χ = 2, not 5"
```

#### CI Integration

The verification layer is integrated into CI/CD:

```yaml
# .github/workflows/ci.yml
- name: Run hallucination evaluation
  run: |
    python examples/eval/hallucination_eval.py
```

**Detection Rate**: 100% on test suite (14/14 tests passing)

**See**: `LLM_HALLUCINATION_PREVENTION.md` for full details.

---

## Future Architecture

### Planned Components

1. **Streaming Engine** ✅ (Implemented)
   - Incremental updates
   - Sliding window persistence
   - Real-time computation

2. **Visualization**
   - Persistence diagram plots
   - Barcode visualization
   - Interactive 3D complex viewer

3. **GPU Acceleration**
   - CUDA kernels for matrix reduction
   - Parallel filtration construction

4. **Distributed Computing**
   - Partition large complexes
   - Parallel persistence computation
   - Result aggregation

5. **LLM Safety API**
   - Real-time verification endpoints
   - Hallucination detection service
   - Confidence calibration

## References

- **Rust API Guidelines**: https://rust-lang.github.io/api-guidelines/
- **PyO3 Guide**: https://pyo3.rs/
- **Lean 4 Manual**: https://leanprover.github.io/lean4/doc/
- **Flask Best Practices**: https://flask.palletsprojects.com/

