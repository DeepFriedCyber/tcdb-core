# TCDB Python Bindings

Python bindings for TCDB (Topological Constraint Database), providing high-performance topological data analysis with formal verification.

## Installation

### From Source

```bash
# Install maturin
pip install maturin

# Build and install
cd rust
maturin develop --release
```

### From PyPI (when published)

```bash
pip install tcdb-core
```

## Features

### 1. **Euler Characteristic** 🎯

Compute topological invariants:

```python
import tcdb_core

# Standard complexes
triangle = tcdb_core.FVector.triangle()
print(f"χ(triangle) = {triangle.euler_characteristic()}")  # 1

# Classical surfaces
sphere = tcdb_core.FVector([6, 12, 8])
print(f"χ(sphere) = {sphere.euler_characteristic()}")  # 2

torus = tcdb_core.FVector([9, 27, 18])
print(f"χ(torus) = {torus.euler_characteristic()}")  # 0

# Disjoint union (additive)
union = triangle.disjoint_union(triangle)
print(f"χ(T ⊔ T) = {union.euler_characteristic()}")  # 2
```

---

### 2. **Bayesian Inference** 📊

Probabilistic reasoning over topological evidence:

```python
import tcdb_core

# Create evidence
evidence = tcdb_core.Evidence(0.9, 0.1)  # P(E|H), P(E|¬H)

# Compute posterior
prior = 0.5
posterior = tcdb_core.py_posterior(prior, evidence)

print(f"Prior: {prior}")
print(f"Posterior: {posterior.posterior}")
print(f"Belief change: {posterior.belief_change()}")

# Sequential updating
evidence_list = [
    tcdb_core.Evidence(0.8, 0.2),
    tcdb_core.Evidence(0.9, 0.1),
]
final = tcdb_core.py_sequential_update(prior, evidence_list)
```

---

### 3. **Streaming Filtrations** 🌊

Real-time topological analysis:

```python
import tcdb_core
import math

# Create streamer with window size 50
streamer = tcdb_core.Streamer(50)

# Stream data
for i in range(100):
    t = i * 0.1
    value = math.sin(t)
    streamer.push((t, value))
    
    # Get current persistence diagram
    pd = streamer.pd()
    print(f"t={t:.1f}: {len(pd)} features")

# Window statistics
stats = streamer.statistics()
if stats:
    min_val, max_val, mean, std_dev = stats
    print(f"Mean: {mean:.2f}, Std: {std_dev:.2f}")
```

---

### 4. **Landscape Embeddings** 🗺️

ML-ready feature vectors from persistence diagrams:

```python
import tcdb_core

# Persistence diagram
pd = [(0.0, 1.0), (0.5, 1.5), (1.0, 2.0)]

# Compute landscape features
features = tcdb_core.py_landscape_features_auto(pd, levels=2, samples=10)
print(f"Feature vector: {len(features)} dimensions")

# Compare persistence diagrams
pd1 = [(0.0, 1.0), (0.5, 1.5)]
pd2 = [(0.0, 1.1), (0.5, 1.6)]

f1 = tcdb_core.py_landscape_features_auto(pd1, 2, 10)
f2 = tcdb_core.py_landscape_features_auto(pd2, 2, 10)

distance = tcdb_core.py_landscape_distance(f1, f2)
similarity = tcdb_core.py_landscape_similarity(f1, f2)

print(f"Distance: {distance:.4f}")
print(f"Similarity: {similarity:.4f}")
```

---

## API Reference

### Euler Characteristic

#### `FVector`

```python
class FVector:
    def __init__(self, faces: list[int])
    
    @staticmethod
    def empty() -> FVector
    
    @staticmethod
    def point() -> FVector
    
    @staticmethod
    def interval() -> FVector
    
    @staticmethod
    def triangle() -> FVector
    
    @staticmethod
    def tetrahedron() -> FVector
    
    def euler_characteristic(self) -> int
    
    def disjoint_union(self, other: FVector) -> FVector
    
    def get_face_count(self, k: int) -> int
    
    def max_dimension(self) -> int
```

---

### Bayesian Inference

#### `Evidence`

```python
class Evidence:
    def __init__(self, like_h: float, like_not_h: float)
    
    @property
    def like_h(self) -> float
    
    @property
    def like_not_h(self) -> float
    
    def likelihood_ratio(self) -> float
    
    def supports_h(self) -> bool
    
    def is_neutral(self, epsilon: float) -> bool
```

#### `Posterior`

```python
class Posterior:
    @property
    def prior(self) -> float
    
    @property
    def posterior(self) -> float
    
    @property
    def evidence(self) -> Evidence
    
    def belief_change(self) -> float
    
    def posterior_odds(self) -> float
    
    def bayes_factor(self) -> float
```

#### Functions

```python
def py_posterior(prior: float, evidence: Evidence) -> Posterior

def py_sequential_update(prior: float, evidence: list[Evidence]) -> Posterior
```

---

### Streaming Filtrations

#### `Streamer`

```python
class Streamer:
    def __init__(self, max_len: int)
    
    def push(self, sample: tuple[float, float])
    
    def pd(self) -> list[tuple[float, float]]
    
    def statistics(self) -> tuple[float, float, float, float] | None
    
    def len(self) -> int
    
    def is_empty(self) -> bool
    
    def clear(self)
```

---

### Landscape Embeddings

#### Functions

```python
def py_landscape_features(
    pd: list[tuple[float, float]],
    levels: int,
    samples: int,
    tmin: float,
    tmax: float
) -> list[float]

def py_landscape_features_auto(
    pd: list[tuple[float, float]],
    levels: int,
    samples: int
) -> list[float]

def py_landscape_distance(f1: list[float], f2: list[float]) -> float

def py_landscape_similarity(f1: list[float], f2: list[float]) -> float
```

---

## Examples

See the `examples/` directory for complete examples:

- `euler_characteristic_example.py` - Topological invariants
- `bayesian_inference_example.py` - Probabilistic reasoning
- `streaming_example.py` - Real-time analysis
- `landscape_embeddings_example.py` - ML features

Run an example:

```bash
cd python/examples
python euler_characteristic_example.py
```

---

## Testing

Run the test suite:

```bash
cd python
pytest tests/ -v
```

---

## Performance

TCDB is built in Rust for maximum performance:

- **Euler characteristic**: ~1 μs
- **Bayesian update**: ~100 ns
- **Streaming push**: ~1 μs (amortized)
- **Landscape features**: ~10 μs per PD point

---

## Documentation

Full documentation available at:
- [Rust docs](https://docs.rs/tcdb-core)
- [GitHub](https://github.com/DeepFriedCyber/tcdb-core)

---

## License

MIT License - see LICENSE file for details.

---

## Citation

If you use TCDB in your research, please cite:

```bibtex
@software{tcdb2024,
  title = {TCDB: Topological Constraint Database with Formal Verification},
  author = {Your Name},
  year = {2024},
  url = {https://github.com/DeepFriedCyber/tcdb-core}
}
```

---

## Contributing

Contributions welcome! Please see CONTRIBUTING.md for guidelines.

---

## Support

- Issues: https://github.com/DeepFriedCyber/tcdb-core/issues
- Discussions: https://github.com/DeepFriedCyber/tcdb-core/discussions

