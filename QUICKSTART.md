# 🚀 Quick Start Guide

Get up and running with TCDB Core in 5 minutes!

## Prerequisites

```bash
# Check versions
rustc --version  # Need 1.70+
python --version # Need 3.8+
```

If you don't have Rust:
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

## Installation

### Option 1: Quick Install (Recommended)

```bash
# Clone repository
git clone https://github.com/DeepFriedCyber/tcdb-core.git
cd tcdb-core

# Install everything
make dev
```

### Option 2: Step-by-Step

```bash
# 1. Build Rust library
cd rust
cargo build --release
cargo test
cd ..

# 2. Install Python dependencies
pip install maturin numpy flask flask-cors

# 3. Build Python bindings
maturin develop --release

# 4. Install Python package
pip install -e ".[dev]"
```

## Verify Installation

```bash
# Run all tests
make test
```

Expected output:
```
🧪 Running Rust tests...
test tests::test_library_loads ... ok
test simplicial_complex::tests::test_simplex_creation ... ok
...
✅ All tests passed!
```

## First Example: Python

Create `example.py`:

```python
import tcdb_core

# Create a triangle
complex = tcdb_core.SimplicialComplex()
complex.add_simplex([0, 1, 2])

print(f"Dimension: {complex.dimension()}")
print(f"Euler characteristic: {complex.euler_characteristic()}")
print(f"Closure verified: {complex.verify_closure()}")
```

Run it:
```bash
python example.py
```

Output:
```
Dimension: 2
Euler characteristic: 1
Closure verified: True
```

## Second Example: REST API

### Start the server:

```bash
cd python
python -m flask --app tcdb_api.app run
```

### Test endpoints:

```bash
# Health check
curl http://localhost:5000/api/v1/health

# Create a simplex
curl -X POST http://localhost:5000/api/v1/tda/simplex \
  -H "Content-Type: application/json" \
  -d '{"vertices": [0, 1, 2]}'

# Response:
# {"dimension": 2, "vertices": [0, 1, 2]}
```

## Third Example: Rips Complex

Create `rips_example.py`:

```python
import tcdb_core
import numpy as np

# Create point cloud
points = np.array([
    [0.0, 0.0],
    [1.0, 0.0],
    [0.0, 1.0],
    [1.0, 1.0]
])

# Build Rips complex
complex = tcdb_core.SimplicialComplex()

# Add vertices
for i in range(len(points)):
    complex.add_simplex([i])

# Add edges within distance threshold
max_dist = 1.5
for i in range(len(points)):
    for j in range(i + 1, len(points)):
        dist = np.linalg.norm(points[i] - points[j])
        if dist <= max_dist:
            complex.add_simplex([i, j])

print(f"Built Rips complex:")
print(f"  Dimension: {complex.dimension()}")
print(f"  Euler characteristic: {complex.euler_characteristic()}")
```

Run it:
```bash
python rips_example.py
```

## Fourth Example: REST API Pipeline

```bash
curl -X POST http://localhost:5000/api/v1/pipeline/run \
  -H "Content-Type: application/json" \
  -d '{
    "data": [
      [0.0, 0.0],
      [1.0, 0.0],
      [0.0, 1.0],
      [1.0, 1.0]
    ],
    "max_dimension": 2,
    "max_edge_length": 1.5
  }'
```

Response:
```json
{
  "job_id": "550e8400-e29b-41d4-a716-446655440000",
  "status": "completed",
  "results": {
    "euler_characteristic": 1,
    "dimension": 1,
    "num_vertices": 4,
    "max_edge_length": 1.5
  },
  "metadata": {
    "backend": "rust",
    "verified": true
  }
}
```

## Common Operations

### Create Simplices

```python
import tcdb_core

# Vertex (0-simplex)
vertex = tcdb_core.Simplex([0])
print(vertex.dimension())  # 0

# Edge (1-simplex)
edge = tcdb_core.Simplex([0, 1])
print(edge.dimension())  # 1

# Triangle (2-simplex)
triangle = tcdb_core.Simplex([0, 1, 2])
print(triangle.dimension())  # 2
```

### Build Complexes

```python
# Empty complex
complex = tcdb_core.SimplicialComplex()

# Add simplices (faces added automatically)
complex.add_simplex([0, 1, 2])  # Adds triangle + edges + vertices

# Query
print(complex.dimension())              # 2
print(complex.euler_characteristic())   # 1
print(complex.verify_closure())         # True
```

### Compute Topological Properties

```python
# Triangle: χ = 3 - 3 + 1 = 1
complex1 = tcdb_core.SimplicialComplex()
complex1.add_simplex([0, 1, 2])
print(complex1.euler_characteristic())  # 1

# Tetrahedron (2-sphere): χ = 2
complex2 = tcdb_core.SimplicialComplex()
complex2.add_simplex([0, 1, 2])
complex2.add_simplex([0, 1, 3])
complex2.add_simplex([0, 2, 3])
complex2.add_simplex([1, 2, 3])
print(complex2.euler_characteristic())  # 2
```

## Troubleshooting

### "Rust bindings not available"

```bash
# Rebuild bindings
maturin develop --release
```

### "cargo: command not found"

```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env
```

### Tests failing

```bash
# Clean and rebuild
make clean
make build
make test
```

### Import errors

```bash
# Check installation
python -c "import tcdb_core; print('OK')"

# Reinstall if needed
pip uninstall tcdb-core
maturin develop --release
```

## Next Steps

1. **Read the docs**: See `ARCHITECTURE.md` for design details
2. **Explore examples**: Check `python/tests/` for more examples
3. **Run benchmarks**: `make bench` to see performance
4. **Verify proofs**: `make lean-check` to verify Lean proofs
5. **Contribute**: See `CONTRIBUTING.md` (coming soon)

## Learning Resources

### Topological Data Analysis
- Edelsbrunner & Harer: "Computational Topology"
- Ghrist: "Elementary Applied Topology"
- Carlsson: "Topology and Data" (2009)

### Rust
- The Rust Book: https://doc.rust-lang.org/book/
- Rust by Example: https://doc.rust-lang.org/rust-by-example/

### Lean
- Theorem Proving in Lean: https://leanprover.github.io/theorem_proving_in_lean4/
- Mathematics in Lean: https://leanprover-community.github.io/mathematics_in_lean/

## Support

- **Issues**: https://github.com/DeepFriedCyber/tcdb-core/issues
- **Discussions**: https://github.com/DeepFriedCyber/tcdb-core/discussions

## What's Next?

Try building a complete TDA pipeline:

```python
import tcdb_core
import numpy as np

# 1. Generate data
points = np.random.randn(100, 3)

# 2. Build Rips complex
complex = tcdb_core.SimplicialComplex()
for i in range(len(points)):
    complex.add_simplex([i])

max_dist = 0.5
for i in range(len(points)):
    for j in range(i + 1, len(points)):
        if np.linalg.norm(points[i] - points[j]) <= max_dist:
            complex.add_simplex([i, j])

# 3. Compute properties
print(f"Euler characteristic: {complex.euler_characteristic()}")
print(f"Dimension: {complex.dimension()}")

# 4. TODO: Compute persistent homology (coming soon!)
```

Happy computing! 🦀🔬

