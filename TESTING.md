# 🧪 TCDB-Core Testing Guide

## Overview

TCDB-Core has comprehensive test coverage across all components. This guide shows you how to run all available tests.

---

## ✅ Current Test Status

```
✅ Rust: 25/25 tests passing (100%)
✅ Lean: Builds successfully
⏳ Python: Integration tests ready (requires maturin build)
```

---

## 🚀 Quick Test Commands

### Run All Tests (Automated)

**Windows (PowerShell)**:
```powershell
.\test_all.ps1
```

**Linux/macOS (Bash)**:
```bash
chmod +x test_all.sh
./test_all.sh
```

**Python Integration Tests**:
```bash
python test_python.py
```

---

## 📋 Individual Test Suites

### 1. Rust Unit Tests (25 tests)

```bash
cd rust

# Run all tests
cargo test

# Run with output
cargo test -- --nocapture

# Run specific module
cargo test simplicial_complex
cargo test filtration
cargo test persistent_homology
cargo test bindings

# Run specific test
cargo test test_euler_characteristic_triangle
```

**Test Breakdown**:
- `simplicial_complex`: 9 tests
- `filtration`: 6 tests
- `persistent_homology`: 5 tests
- `bindings`: 3 tests
- `lib`: 2 tests

**Expected Output**:
```
running 25 tests
test bindings::tests::test_py_complex_creation ... ok
test bindings::tests::test_py_simplex_creation ... ok
test bindings::tests::test_py_complex_euler ... ok
test filtration::tests::test_filtration_add_simplex ... ok
test filtration::tests::test_filtration_complex_at ... ok
test filtration::tests::test_filtration_creation ... ok
test filtration::tests::test_filtration_invalid_value ... ok
test filtration::tests::test_filtration_monotonicity ... ok
test filtration::tests::test_filtration_values_sorted ... ok
test persistent_homology::tests::test_barcode_conversion ... ok
test persistent_homology::tests::test_diagram_betti_number ... ok
test persistent_homology::tests::test_diagram_creation ... ok
test persistent_homology::tests::test_diagram_significant_points ... ok
test persistent_homology::tests::test_persistence_point_creation ... ok
test persistent_homology::tests::test_persistence_point_infinite ... ok
test simplicial_complex::tests::test_complex_add_simplex ... ok
test simplicial_complex::tests::test_complex_closure_property ... ok
test simplicial_complex::tests::test_complex_creation ... ok
test simplicial_complex::tests::test_euler_characteristic_triangle ... ok
test simplicial_complex::tests::test_euler_characteristic_sphere ... ok
test simplicial_complex::tests::test_simplex_creation ... ok
test simplicial_complex::tests::test_simplex_deduplication ... ok
test simplicial_complex::tests::test_simplex_faces ... ok
test simplicial_complex::tests::test_simplex_is_face_of ... ok
test tests::test_library_loads ... ok

test result: ok. 25 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
```

---

### 2. Lean Verification

```bash
cd lean

# Update dependencies (first time only)
lake update

# Build and verify proofs
lake build
```

**Expected Output**:
```
Building Tcdb.Topology.SimplicialComplex
Building Tcdb.Topology.Filtration
Building Tcdb.PersistentHomology.PersistentHomology
Building Tcdb.PersistentHomology.Basic
Building Tcdb.PersistentHomology.BettiNumbers
```

**Note**: Some proofs use `sorry` placeholders - this is expected for now.

---

### 3. Python Integration Tests

**Prerequisites**: Build Python bindings first
```bash
maturin develop --release
```

**Run Tests**:
```bash
# Automated test suite
python test_python.py

# Manual tests
python -c "import tcdb_core; print('✓ Import works')"

# Test each component
python << 'EOF'
import tcdb_core

# Test Simplex
s = tcdb_core.Simplex([0, 1, 2])
print(f"✓ Simplex dimension: {s.dimension()}")

# Test SimplicialComplex
c = tcdb_core.SimplicialComplex()
c.add_simplex([0, 1, 2])
print(f"✓ Complex dimension: {c.dimension()}")
print(f"✓ Euler characteristic: {c.euler_characteristic()}")

# Test Filtration
f = tcdb_core.Filtration()
f.add_simplex(0.0, [0])
f.add_simplex(0.5, [0, 1])
print(f"✓ Filtration values: {f.values()}")

# Test PersistencePoint
p = tcdb_core.PersistencePoint(0.0, 1.0, 1)
print(f"✓ Persistence: {p.persistence()}")

print("\n✅ All Python tests passed!")
EOF
```

---

### 4. Examples

```bash
# Basic usage
python examples/basic_usage.py

# Rips complex
python examples/rips_complex.py
```

---

### 5. REST API Tests

**Start Server**:
```bash
python -m flask --app python.tcdb_api.app run --port 8000
```

**Test Endpoints** (in another terminal):

```bash
# Health check
curl http://localhost:8000/api/v1/health

# Expected: {"status": "healthy", "version": "1.0.0", ...}

# Create simplex
curl -X POST http://localhost:8000/api/v1/tda/simplex \
  -H "Content-Type: application/json" \
  -d '{"vertices": [0, 1, 2]}'

# Expected: {"dimension": 2, "vertices": [0, 1, 2]}

# Create complex
curl -X POST http://localhost:8000/api/v1/tda/complex \
  -H "Content-Type: application/json" \
  -d '{"simplices": [[0,1,2], [1,2,3]]}'

# Expected: {"dimension": 2, "euler_characteristic": 0, "closure_valid": true}
```

---

## 📊 Test Coverage

### Rust Tests Cover:

#### Simplicial Complex (9 tests)
- ✅ Simplex creation and properties
- ✅ Face computation
- ✅ Dimension calculation
- ✅ Complex creation
- ✅ Adding simplices
- ✅ Closure property verification
- ✅ Euler characteristic (triangle, sphere)
- ✅ Deduplication
- ✅ Face relations

#### Filtration (6 tests)
- ✅ Filtration creation
- ✅ Adding simplices at values
- ✅ Invalid value rejection (NaN, Inf)
- ✅ Complex at specific time
- ✅ Monotonicity verification
- ✅ Sorted filtration values

#### Persistent Homology (5 tests)
- ✅ Persistence point creation
- ✅ Infinite features
- ✅ Diagram creation
- ✅ Betti number computation
- ✅ Barcode conversion
- ✅ Significant points filtering

#### Python Bindings (3 tests)
- ✅ Simplex wrapper
- ✅ Complex wrapper
- ✅ Euler characteristic through Python

---

## 🐛 Troubleshooting Tests

### Rust Tests Fail

**Issue**: Compilation errors
```bash
cd rust
cargo clean
cargo build --release
cargo test
```

**Issue**: Specific test fails
```bash
# Run with output to see details
cargo test test_name -- --nocapture
```

### Lean Build Fails

**Issue**: Missing dependencies
```bash
cd lean
lake update
lake build
```

**Issue**: Proof errors
- Check that you're using Lean 4.3.0: `lean --version`
- Some `sorry` placeholders are expected

### Python Tests Fail

**Issue**: Import error
```bash
# Rebuild bindings
pip uninstall tcdb-core
maturin develop --release

# Verify
python -c "import tcdb_core; print(tcdb_core.__file__)"
```

**Issue**: Assertion errors
- Check that you built with `--release` flag
- Verify Rust tests pass first

---

## 🔍 Detailed Test Information

### Test Files Location

```
tcdb-core/
├── rust/
│   └── src/
│       ├── lib.rs                    # 2 tests
│       ├── simplicial_complex.rs     # 9 tests
│       ├── filtration.rs             # 6 tests
│       ├── persistent_homology.rs    # 5 tests
│       └── bindings.rs               # 3 tests
├── test_python.py                    # Python integration tests
├── test_all.sh                       # Bash test runner
└── test_all.ps1                      # PowerShell test runner
```

### Adding New Tests

**Rust**:
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_feature() {
        // Your test code
        assert_eq!(1 + 1, 2);
    }
}
```

**Python**:
```python
def test_my_feature():
    """Test description"""
    import tcdb_core
    # Your test code
    assert True
```

---

## 📈 Performance Tests

### Benchmarks

```bash
cd rust

# Run benchmarks
cargo bench

# Run specific benchmark
cargo bench persistent_homology
```

### Profile Performance

```bash
# Install flamegraph
cargo install flamegraph

# Generate flamegraph
cargo flamegraph --bench persistent_homology
```

---

## ✅ Continuous Integration

### GitHub Actions (Future)

```yaml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Install Rust
        uses: actions-rs/toolchain@v1
      - name: Run tests
        run: cargo test --all
```

---

## 📝 Test Checklist

Before committing:
- [ ] All Rust tests pass: `cargo test`
- [ ] Rust builds in release mode: `cargo build --release`
- [ ] Lean proofs build: `cd lean && lake build`
- [ ] Python bindings build: `maturin develop --release`
- [ ] Python tests pass: `python test_python.py`
- [ ] Examples run: `python examples/basic_usage.py`
- [ ] No compiler warnings: `cargo clippy`
- [ ] Code formatted: `cargo fmt`

---

## 🎯 Summary

**Available Test Scripts**:
1. `test_all.ps1` - PowerShell comprehensive test suite
2. `test_all.sh` - Bash comprehensive test suite
3. `test_python.py` - Python integration tests

**Quick Commands**:
```bash
# Rust
cargo test

# Python
python test_python.py

# All (Windows)
.\test_all.ps1

# All (Linux/macOS)
./test_all.sh
```

**Current Status**: ✅ **25/25 Rust tests passing (100%)**

---

**Happy Testing!** 🧪✅

