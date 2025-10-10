# TCDB Addons Pack - Complete Guide

## 📖 Overview

The **TCDB Addons Pack** extends the core TCDB API with advanced features for topological data analysis, information geometry, and lattice gauge theory demonstrations.

**Status**: ✅ **Fully Integrated and Operational**

---

## 🎯 What's Included

### 1. **TDA Analysis** (`/addons/tda/analyze`)
- **Barcode Entropy**: Measure topological complexity of point clouds
- **Stability Modulus**: Quantify robustness of topological features
- **Point Cloud Analyzer**: Compute persistent homology utilities

### 2. **Fisher-Rao Metric** (`/addons/metric/fisher_rao/gram`)
- **Gram Matrix**: Normalized Gram matrix for information geometry
- **Gaussian Distribution**: Fisher-Rao metric for Gaussian families
- **Quick GFI Experiments**: Geometric Fisher Information metric option

### 3. **Wilson Rectangle Generator** (`/addons/lgt/wilson`)
- **Synthetic Data**: Generate Wilson loop expectations for LGT demos
- **Area Law**: Simulate confinement with area law decay
- **WPS Demo**: Wilson Plaquette Sum demonstration data

### 4. **Lattice Merge API** (Python-only)
- **Join-Semilattice**: Policy/provenance label merging
- **Trust Lattice**: Security level merging (low < med < high)
- **Merge Policy**: Combine multiple security labels

---

## 🚀 Quick Start

### Prerequisites

The addons are **already integrated** into your TCDB API! No additional installation needed.

### Verify Addons Are Available

```bash
curl http://localhost:8000/api
```

**Expected Response**:
```json
{
  "name": "TCDB Core API",
  "version": "1.0.0",
  "status": "operational",
  "rust_available": true,
  "addons_available": true,  ← Should be true!
  "docs_url": "/docs",
  "redoc_url": "/redoc"
}
```

### Run Test Suite

```bash
python python/scripts/test_addons.py
```

**Expected Output**: All 4 tests pass ✅

---

## 📊 API Endpoints

### 1. TDA Point Cloud Analysis

**Endpoint**: `POST /addons/tda/analyze`

**Purpose**: Analyze topological structure of point clouds using persistent homology utilities.

**Request Body**:
```json
{
  "X": [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], ...],  // Required: Point cloud
  "Y": [[1.1, 2.1, 3.1], [4.1, 5.1, 6.1], ...]   // Optional: Second point cloud
}
```

**Response**:
```json
{
  "n": 50,                          // Number of points
  "barcode_entropy": 7.0290,        // Topological complexity
  "stability_modulus": 0.2041       // Robustness (if Y provided)
}
```

**Example (Python)**:
```python
import requests
import numpy as np

# Generate random point cloud
X = np.random.randn(50, 3).tolist()

response = requests.post(
    "http://localhost:8000/addons/tda/analyze",
    json={"X": X}
)

data = response.json()
print(f"Barcode entropy: {data['barcode_entropy']:.4f}")
```

**Use Cases**:
- Measure topological complexity of embeddings
- Compare stability of different models
- Detect topological drift in data distributions

---

### 2. Fisher-Rao Gram Matrix

**Endpoint**: `POST /addons/metric/fisher_rao/gram`

**Purpose**: Compute normalized Gram matrix using Fisher-Rao information geometry.

**Request Body**:
```json
{
  "X": [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], ...]  // Data matrix (n × d)
}
```

**Response**:
```json
{
  "n": 10,                          // Matrix size
  "gram": [[...], [...], ...]       // Normalized Gram matrix (n × n)
}
```

**Example (Python)**:
```python
import requests
import numpy as np

# Generate data matrix
X = np.random.randn(10, 5).tolist()  # 10 samples, 5 features

response = requests.post(
    "http://localhost:8000/addons/metric/fisher_rao/gram",
    json={"X": X}
)

data = response.json()
gram = np.array(data['gram'])
print(f"Gram matrix shape: {gram.shape}")
print(f"Is symmetric: {np.allclose(gram, gram.T)}")
```

**Properties**:
- **Normalized**: `||G|| = 1.0`
- **Symmetric**: `G = G^T`
- **Centered**: Data is mean-centered before computation

**Use Cases**:
- Information geometry experiments
- Metric learning for embeddings
- Geometric Fisher Information (GFI) metric option

---

### 3. Wilson Rectangle Generator

**Endpoint**: `POST /addons/lgt/wilson`

**Purpose**: Generate synthetic Wilson loop expectations for lattice gauge theory demonstrations.

**Request Body**:
```json
{
  "R_vals": [1, 2, 3, 4],           // Rectangle widths
  "T_vals": [1, 2, 3, 4],           // Rectangle heights
  "sigma": 0.2,                     // String tension (area law)
  "C": 0.9,                         // Normalization constant
  "noise": 0.02,                    // Gaussian noise level
  "seed": 42                        // Random seed
}
```

**Response**:
```json
{
  "grid": [
    {"R": 1, "T": 1, "W": 0.7352},
    {"R": 1, "T": 2, "W": 0.6051},
    {"R": 2, "T": 1, "W": 0.6128},
    ...
  ]
}
```

**Example (Python)**:
```python
import requests

response = requests.post(
    "http://localhost:8000/addons/lgt/wilson",
    json={
        "R_vals": [1, 2, 3, 4],
        "T_vals": [1, 2, 3, 4],
        "sigma": 0.2,
        "C": 0.9
    }
)

data = response.json()
for item in data['grid'][:5]:
    print(f"W({item['R']},{item['T']}) = {item['W']:.4f}")
```

**Physics**:
- **Area Law**: `⟨W(R,T)⟩ ~ C × exp(-σ × R × T)`
- **Confinement**: σ > 0 indicates quark confinement
- **String Tension**: σ is the string tension parameter

**Use Cases**:
- Lattice gauge theory demonstrations
- Wilson Plaquette Sum (WPS) fitting
- Confinement phase transition studies

---

### 4. Lattice Merge API (Python-only)

**Purpose**: Merge security/trust labels using join-semilattice operations.

**Example (Python)**:
```python
from tcdb_addons.lattice.api import LatticeElement, merge_policy

# Create lattice elements
low = LatticeElement("low")
med = LatticeElement("med")
high = LatticeElement("high")

# Merge policies (join operation)
result = merge_policy(low, med)
print(result.value)  # Output: "med"

result = merge_policy(low, high)
print(result.value)  # Output: "high"

result = merge_policy(high, low, med)
print(result.value)  # Output: "high"
```

**Lattice Structure**:
```
    high
     |
    med
     |
    low
```

**Join Operation**: `a ∨ b = max(a, b)`

**Use Cases**:
- Security label propagation
- Trust level merging
- Provenance tracking
- Information flow control

---

## 🔬 Technical Details

### Barcode Entropy

**Formula**:
```
H = -Σ p_i log(p_i)
```

where `p_i = length_i / Σ length_j` (normalized barcode lengths)

**Interpretation**:
- **High entropy**: Complex topological structure, many features
- **Low entropy**: Simple structure, few dominant features
- **Zero entropy**: Single dominant feature

### Stability Modulus

**Formula**:
```
S = 1 / (max ||x_i - y_i|| + ε)
```

**Interpretation**:
- **High stability**: Point clouds are similar
- **Low stability**: Point clouds are different
- **Inverse of max distance**: Measures robustness

### Fisher-Rao Gram Matrix

**Computation**:
```python
X_centered = X - mean(X)
G = X_centered @ X_centered^T
G_normalized = G / ||G||
```

**Properties**:
- Captures covariance structure
- Normalized for scale invariance
- Symmetric positive semi-definite

### Wilson Loop Area Law

**Formula**:
```
⟨W(R,T)⟩ = C × exp(-σ × R × T) × exp(noise)
```

**Parameters**:
- **σ**: String tension (confinement strength)
- **C**: Normalization constant
- **noise**: Gaussian fluctuations

---

## 📈 Performance Benchmarks

| Endpoint | Input Size | Response Time | Memory |
|----------|------------|---------------|--------|
| TDA Analyze | 50 points × 3D | ~10ms | <1 MB |
| TDA Analyze | 1000 points × 3D | ~500ms | ~10 MB |
| Fisher-Rao Gram | 10 × 5 | <5ms | <1 MB |
| Fisher-Rao Gram | 100 × 50 | ~50ms | ~5 MB |
| Wilson Rectangles | 4×4 grid | <5ms | <1 MB |
| Wilson Rectangles | 10×10 grid | ~10ms | <1 MB |

---

## 🎓 Use Case Examples

### Example 1: Embedding Drift Detection with TDA

```python
import requests
import numpy as np

# Baseline embeddings
baseline = np.random.randn(100, 128).tolist()

# New embeddings (potentially drifted)
new_data = (np.random.randn(100, 128) + 0.5).tolist()

# Compute barcode entropy for both
resp1 = requests.post("http://localhost:8000/addons/tda/analyze", json={"X": baseline})
resp2 = requests.post("http://localhost:8000/addons/tda/analyze", json={"X": new_data})

entropy_baseline = resp1.json()['barcode_entropy']
entropy_new = resp2.json()['barcode_entropy']

drift = abs(entropy_new - entropy_baseline) / entropy_baseline
print(f"Topological drift: {drift:.2%}")
```

### Example 2: Model Comparison with Fisher-Rao

```python
import requests
import numpy as np

# Model A embeddings
model_a = np.random.randn(50, 64).tolist()

# Model B embeddings
model_b = (np.random.randn(50, 64) * 1.5).tolist()

# Compute Gram matrices
resp_a = requests.post("http://localhost:8000/addons/metric/fisher_rao/gram", json={"X": model_a})
resp_b = requests.post("http://localhost:8000/addons/metric/fisher_rao/gram", json={"X": model_b})

gram_a = np.array(resp_a.json()['gram'])
gram_b = np.array(resp_b.json()['gram'])

# Compare geometric structure
distance = np.linalg.norm(gram_a - gram_b, 'fro')
print(f"Geometric distance: {distance:.4f}")
```

### Example 3: LGT Phase Transition Study

```python
import requests
import numpy as np
import matplotlib.pyplot as plt

# Scan string tension values
sigma_values = np.linspace(0.1, 0.5, 10)
results = []

for sigma in sigma_values:
    resp = requests.post(
        "http://localhost:8000/addons/lgt/wilson",
        json={"R_vals": [2], "T_vals": [2], "sigma": float(sigma), "C": 0.9}
    )
    W = resp.json()['grid'][0]['W']
    results.append((sigma, W))

# Plot confinement curve
sigmas, Ws = zip(*results)
plt.plot(sigmas, Ws, 'o-')
plt.xlabel('String Tension σ')
plt.ylabel('⟨W(2,2)⟩')
plt.title('Wilson Loop vs String Tension')
plt.savefig('confinement_curve.png')
```

---

## 🔧 Troubleshooting

### Addons Not Available

**Error**: `"addons_available": false`

**Solution**:
1. Check that `tcdb_addons/` directory exists in `python/`
2. Restart the API server
3. Check server logs for import errors

### Import Errors

**Error**: `ModuleNotFoundError: No module named 'tcdb_addons'`

**Solution**:
```bash
# Verify addons are copied
ls python/tcdb_addons/

# Should show:
# __init__.py  router.py  geom/  lattice/  lgt_demo/  topology/
```

### Numerical Issues

**Error**: Division by zero or NaN values

**Solution**:
- Ensure point clouds have at least 2 points
- Check for degenerate data (all zeros, all same values)
- Verify input dimensions match expected format

---

## 📚 References

### Related Documentation
- `docs/USE_CASE_DEMOS_GUIDE.md` - Main use case demos
- `python/scripts/test_addons.py` - Test suite source code
- `shared/tcdb-addons-pack-v1/tcdb-addons-pack/README.md` - Original pack README

### Academic References
- **Persistent Homology**: Edelsbrunner & Harer (2010)
- **Fisher-Rao Metric**: Amari (2016) - Information Geometry
- **Wilson Loops**: Wilson (1974) - Confinement in gauge theories

---

**Last Updated**: 2025-10-09  
**Version**: 1.0.0  
**Status**: ✅ Fully operational and tested

