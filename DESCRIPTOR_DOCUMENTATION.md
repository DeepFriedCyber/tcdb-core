# Topological Descriptors Documentation

## Overview

This module provides four patent-clean descriptor families for summarizing micro→macro structure in a **dimensionless** way. All descriptors are:

- **Dimensionless**: Built from probabilities or ratios
- **Micro→macro capable**: Explicit multiscale parameters
- **Implementation-ready**: Standard libraries, no dependencies on proprietary methods
- **Mathematically independent**: Non-overlapping approaches

## The Four Descriptors

### 1. TID (Topological-Information Descriptor)

**Idea**: Turn topology into unit-free statistics using information theory.

**Components**:
- **Persistence Entropy** (H_k): Shannon entropy of normalized persistence lifetimes
- **Betti Curve Total Variation** (TV_k): Stability measure from Betti curve changes
- **Persistence Landscape Ratio** (L_k): Shape spread using L1/L∞ norms

**Formula**:
```
F_TID = Σ_k (α_k·H_k + β_k·TV_k + γ_k·L_k)
```

**Use Cases**:
- Detecting topological features (holes, voids, connected components)
- Comparing shapes and structures
- Monitoring topological stability

**Example**:
```python
from tcdb_api.descriptors import TopologicalInformationDescriptor

tid = TopologicalInformationDescriptor(max_dimension=2)
result = tid.compute(point_cloud)

print(f"Combined TID: {result['F_TID']}")
print(f"H0 (persistence entropy, dim 0): {result['H0']}")
print(f"TV1 (total variation, dim 1): {result['TV1']}")
```

---

### 2. DGD (Diffusion-Geometry Descriptor)

**Idea**: Use heat diffusion on data graphs to extract scale-free geometric features.

**Components**:
- **φ1(t)**: Curvature-like ratio `t·θ''(t) / θ'(t)`
- **φ2(t)**: Heat trace ratio `θ(t) / θ(t₀)`
- **Spectral Decay**: Eigenvalue decay rate

**Formula**:
```
F_DGD = ∫ w(t) (a·φ1(t) + b·φ2(t)) dt
```

where θ(t) = Tr(exp(-tL)) is the heat trace.

**Use Cases**:
- Geometric complexity analysis
- Multiscale structure detection
- Spectral graph analysis

**Example**:
```python
from tcdb_api.descriptors import DiffusionGeometryDescriptor

dgd = DiffusionGeometryDescriptor(
    graph_type='knn',
    k_neighbors=5,
    n_time_samples=20
)
result = dgd.compute(point_cloud)

print(f"Combined DGD: {result['F_DGD']}")
print(f"Curvature ratio: {result['phi1_mean']}")
print(f"Spectral decay: {result['spectral_decay']}")
```

---

### 3. KME-Δ (Kernel Mean Embedding Divergence)

**Idea**: Represent distributions in RKHS and compare to a reference state using multi-scale kernels.

**Components**:
- Multi-scale RBF kernels with bandwidths σ_j
- Mean embeddings μ_j in RKHS
- MMD-style divergence from reference

**Formula**:
```
F_KME-Δ = √(Σ_j ω_j · ||μ_j - μ*_j||²_H / ||μ*_j||²_H)
```

**Use Cases**:
- Distributional drift detection
- Anomaly detection
- Layer-wise neural network analysis

**Example**:
```python
from tcdb_api.descriptors import KernelMeanEmbeddingDelta

kme = KernelMeanEmbeddingDelta(
    kernel_type='rbf',
    sigma_scales=[0.1, 0.5, 1.0, 2.0, 5.0],
    reference_type='uniform'
)
result = kme.compute(point_cloud)

print(f"Combined KME-Δ: {result['F_KME_DELTA']}")
print(f"Mean divergence: {result['mean_divergence']}")
```

---

### 4. GSER (Graph-Scattering Energy Ratio)

**Idea**: Pass signals through graph wavelet filters and compute energy ratios across scales.

**Components**:
- First-order scattering: S1_j = ||x ⋆ ψ_j||₁
- Second-order scattering: S2_{j1,j2} = ||(|x ⋆ ψ_{j1}|) ⋆ ψ_{j2}||₁
- Energy ratios normalized by total energy

**Formula**:
```
F_GSER = Σ_{j1≤j2} η_{j1,j2} · S_{j1,j2} / E
```

**Use Cases**:
- Signal processing on graphs
- Multiscale feature extraction
- Stable geometric descriptors

**Example**:
```python
from tcdb_api.descriptors import GraphScatteringEnergyRatio

gser = GraphScatteringEnergyRatio(
    n_scales=4,
    graph_type='knn',
    signal_type='coordinates'
)
result = gser.compute(point_cloud)

print(f"Combined GSER: {result['F_GSER']}")
print(f"Energy concentration: {result['energy_concentration']}")
```

---

## API Usage

### REST API Endpoints

#### List Available Descriptors
```bash
GET /api/v1/descriptors/list
```

**Response**:
```json
{
  "descriptors": [
    {
      "name": "tid",
      "full_name": "Topological-Information Descriptor",
      "description": "...",
      "features": "..."
    },
    ...
  ]
}
```

#### Compute Single Descriptor
```bash
POST /api/v1/descriptors/compute
```

**Request**:
```json
{
  "data": [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0], [1.0, 1.0]],
  "descriptor_type": "tid",
  "parameters": {
    "max_dimension": 2
  }
}
```

**Response**:
```json
{
  "descriptor_type": "tid",
  "features": {
    "F_TID": 0.73,
    "H0": 0.45,
    "H1": 0.28,
    "TV0": 0.12,
    "TV1": 0.08,
    "L0": 0.15,
    "L1": 0.10
  },
  "metadata": {
    "n_points": 4,
    "n_features": 2,
    "descriptor_name": "tid"
  }
}
```

#### Compute Multiple Descriptors (Batch)
```bash
POST /api/v1/descriptors/compute/batch
```

**Request**:
```json
{
  "data": [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]],
  "descriptor_types": ["tid", "dgd", "kme_delta"],
  "parameters": {
    "tid": {"max_dimension": 2},
    "dgd": {"n_time_samples": 10}
  }
}
```

**Response**:
```json
{
  "results": {
    "tid": {"F_TID": 0.73, ...},
    "dgd": {"F_DGD": 0.45, ...},
    "kme_delta": {"F_KME_DELTA": 0.62, ...}
  },
  "metadata": {
    "n_points": 3,
    "descriptor_types": ["tid", "dgd", "kme_delta"]
  }
}
```

#### Get Descriptor Configuration
```bash
GET /api/v1/descriptors/config/{descriptor_type}
```

---

## Python API Usage

### Basic Usage

```python
import numpy as np
from tcdb_api.descriptors import TopologicalInformationDescriptor

# Create point cloud
points = np.random.randn(50, 3)

# Create descriptor
tid = TopologicalInformationDescriptor(max_dimension=2)

# Compute features
result = tid.compute(points)

print(result)
# {'F_TID': 0.73, 'H0': 0.45, 'H1': 0.28, ...}
```

### Using the Registry

```python
from tcdb_api.descriptors import DescriptorRegistry

# Create registry
registry = DescriptorRegistry()

# Get descriptor by name
descriptor = registry.get('tid', max_dimension=2)

# Compute
result = descriptor.compute(points)
```

### Batch Processing

```python
from tcdb_api.descriptors import (
    TopologicalInformationDescriptor,
    DiffusionGeometryDescriptor,
    KernelMeanEmbeddingDelta,
    GraphScatteringEnergyRatio
)

# Create all descriptors
descriptors = {
    'TID': TopologicalInformationDescriptor(),
    'DGD': DiffusionGeometryDescriptor(),
    'KME-Δ': KernelMeanEmbeddingDelta(),
    'GSER': GraphScatteringEnergyRatio()
}

# Compute all
results = {}
for name, descriptor in descriptors.items():
    results[name] = descriptor.compute(points)
```

---

## Configuration

Default configurations are in `python/tcdb_api/config/descriptor_defaults.yaml`.

### TID Configuration
```yaml
tid:
  max_dimension: 2
  max_edge_length: null  # Auto-computed
  n_bins: 100
  alpha_weights: {0: 1.0, 1: 1.0, 2: 1.0}
  beta_weights: {0: 1.0, 1: 1.0, 2: 1.0}
  gamma_weights: {0: 1.0, 1: 1.0, 2: 1.0}
```

### DGD Configuration
```yaml
dgd:
  graph_type: 'knn'
  k_neighbors: 5
  n_time_samples: 20
  time_range: [0.01, 10.0]
  weight_a: 1.0
  weight_b: 1.0
```

### KME-Δ Configuration
```yaml
kme_delta:
  kernel_type: 'rbf'
  sigma_scales: [0.1, 0.5, 1.0, 2.0, 5.0]
  reference_type: 'uniform'
```

### GSER Configuration
```yaml
gser:
  n_scales: 4
  graph_type: 'knn'
  k_neighbors: 5
  signal_type: 'coordinates'
```

---

## Mathematical Properties

### Dimensionless Guarantee

All descriptors return values that are:
1. **Ratios**: Normalized by appropriate denominators
2. **Probabilities**: Sum to 1 or bounded in [0,1]
3. **Scale-free**: Invariant (or nearly so) to uniform scaling

### Stability

- **TID**: Stable to small perturbations via persistence stability theorem
- **DGD**: Stable via spectral stability of Laplacian
- **KME-Δ**: Stable via kernel smoothness
- **GSER**: Stable via wavelet frame properties

### Computational Complexity

- **TID**: O(n³) for persistence computation
- **DGD**: O(n³) for eigendecomposition (O(nk²) sparse)
- **KME-Δ**: O(n²) for kernel matrix
- **GSER**: O(n³) for wavelet computation

---

## Examples

See `examples/descriptor_usage.py` for comprehensive examples including:
- Basic usage of each descriptor
- Batch comparison
- Scale invariance tests
- Registry usage

---

## Testing

Run tests with:
```bash
pytest python/tests/test_descriptors.py
pytest python/tests/test_descriptor_api.py
```

---

## References

- **TDA**: Carlsson, G. (2009). "Topology and data"
- **Diffusion Geometry**: Coifman & Lafon (2006). "Diffusion maps"
- **Kernel Methods**: Gretton et al. (2012). "A kernel two-sample test"
- **Graph Wavelets**: Hammond et al. (2011). "Wavelets on graphs"

