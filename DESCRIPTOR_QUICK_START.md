# Descriptor Quick Start Guide

## Installation

```bash
# Install dependencies
pip install scikit-learn ripser persim pyyaml

# Or install tcdb-core with all dependencies
pip install -e .
```

## 30-Second Example

```python
import numpy as np
from tcdb_api.descriptors import TopologicalInformationDescriptor

# Create data
points = np.random.randn(50, 3)

# Compute descriptor
tid = TopologicalInformationDescriptor()
result = tid.compute(points)

print(f"TID: {result['F_TID']:.4f}")
```

## API Quick Start

```bash
# Start server
python run_api.py

# Compute descriptor
curl -X POST http://localhost:8000/api/v1/descriptors/compute \
  -H "Content-Type: application/json" \
  -d '{
    "data": [[0,0], [1,0], [0,1], [1,1]],
    "descriptor_type": "tid"
  }'
```

## The Four Descriptors

### TID - Topology + Information Theory
```python
from tcdb_api.descriptors import TopologicalInformationDescriptor

tid = TopologicalInformationDescriptor(max_dimension=2)
result = tid.compute(points)
# Output: F_TID, H0, H1, H2, TV0, TV1, TV2, L0, L1, L2
```

**Use for**: Detecting holes, voids, connected components

### DGD - Heat Diffusion on Graphs
```python
from tcdb_api.descriptors import DiffusionGeometryDescriptor

dgd = DiffusionGeometryDescriptor(k_neighbors=5)
result = dgd.compute(points, times='logspace')
# Output: DGD_F, DGD_phi1_mean, DGD_phi2_q90, DGD_spectral_decay

# Or with pre-computed Laplacian
result = dgd.compute({'laplacian': laplacian_matrix})
```

**Use for**: Geometric complexity, spectral analysis
**Efficient methods**: Auto-selects Lanczos/stochastic for large graphs

### KME-Δ - Distributional Divergence
```python
from tcdb_api.descriptors import KernelMeanEmbeddingDelta

kme = KernelMeanEmbeddingDelta(sigma_scales=[0.5, 1.0, 2.0])
result = kme.compute(points)
# Output: KME_delta_F, KME_mean, KME_sigma_0.5, KME_sigma_1.0, ...

# With attention weights (e.g., from transformer)
result = kme.compute({
    'embeddings': embeddings,
    'attention_weights': attention_weights
})
```

**Use for**: Anomaly detection, drift monitoring, embedding comparison
**Supports**: Attention-weighted MMD for transformer embeddings

### GSER - Graph Wavelet Scattering
```python
from tcdb_api.descriptors import GraphScatteringEnergyRatio

gser = GraphScatteringEnergyRatio(n_scales=4)
result = gser.compute(points)
# Output: F_GSER, energy_concentration, S1_*, S2_*_*
```

**Use for**: Signal processing, multiscale features

## Batch Processing

```python
from tcdb_api.descriptors import DescriptorRegistry

registry = DescriptorRegistry()

# Compute all descriptors
for name in ['tid', 'dgd', 'kme_delta', 'gser']:
    descriptor = registry.get(name)
    result = descriptor.compute(points)
    print(f"{name}: {result[f'F_{name.upper()}']:.4f}")
```

## Common Patterns

### Pattern 1: Anomaly Detection
```python
kme = KernelMeanEmbeddingDelta(reference_type='gaussian')

# Baseline
baseline_result = kme.compute(normal_data)
baseline_value = baseline_result['F_KME_DELTA']

# New data
new_result = kme.compute(new_data)
new_value = new_result['F_KME_DELTA']

# Check for anomaly
if new_value > 2 * baseline_value:
    print("Anomaly detected!")
```

### Pattern 2: Topological Feature Detection
```python
tid = TopologicalInformationDescriptor(max_dimension=2)

result = tid.compute(point_cloud)
betti = tid.compute_betti_numbers(point_cloud)

print(f"Connected components: {betti[0]}")
print(f"Holes: {betti[1]}")
print(f"Voids: {betti[2]}")
```

### Pattern 3: Time Series Monitoring
```python
dgd = DiffusionGeometryDescriptor()

history = []
for data_snapshot in time_series:
    result = dgd.compute(data_snapshot)
    history.append(result['F_DGD'])

# Detect changes
import numpy as np
if np.std(history[-10:]) > threshold:
    print("Significant change detected!")
```

## Configuration

### Quick Config Override
```python
tid = TopologicalInformationDescriptor(
    max_dimension=1,        # Faster
    max_edge_length=2.0,    # Explicit threshold
    n_bins=50               # Fewer bins
)
```

### Load from YAML
```python
from tcdb_api.config import get_default_config

config = get_default_config()
tid_params = config.get('tid')

tid = TopologicalInformationDescriptor(**tid_params)
```

## Performance Tips

### For Large Datasets (>1000 points)
```python
# Use sparse methods
dgd = DiffusionGeometryDescriptor(use_sparse=True)

# Reduce dimensions
tid = TopologicalInformationDescriptor(max_dimension=1)

# Fewer samples
dgd = DiffusionGeometryDescriptor(n_time_samples=10)
```

### For Real-Time Applications
```python
# Minimal configuration
tid = TopologicalInformationDescriptor(
    max_dimension=1,
    n_bins=50
)

dgd = DiffusionGeometryDescriptor(
    k_neighbors=3,
    n_time_samples=5
)

kme = KernelMeanEmbeddingDelta(
    sigma_scales=[1.0]
)

gser = GraphScatteringEnergyRatio(
    n_scales=2
)
```

## Troubleshooting

### "ImportError: ripser not found"
```bash
pip install ripser persim
```

### "Memory error"
```python
# Sample your data
points = points[::10]  # Every 10th point

# Or use sparse methods
dgd = DiffusionGeometryDescriptor(use_sparse=True)
```

### "Computation too slow"
```python
# Reduce parameters
tid = TopologicalInformationDescriptor(max_dimension=1)
dgd = DiffusionGeometryDescriptor(n_time_samples=5)
kme = KernelMeanEmbeddingDelta(sigma_scales=[1.0])
gser = GraphScatteringEnergyRatio(n_scales=2)
```

## API Endpoints

### List Descriptors
```bash
curl http://localhost:8000/api/v1/descriptors/list
```

### Compute Single
```bash
curl -X POST http://localhost:8000/api/v1/descriptors/compute \
  -H "Content-Type: application/json" \
  -d '{
    "data": [[0,0], [1,0], [0,1]],
    "descriptor_type": "tid"
  }'
```

### Compute Batch
```bash
curl -X POST http://localhost:8000/api/v1/descriptors/compute/batch \
  -H "Content-Type: application/json" \
  -d '{
    "data": [[0,0], [1,0], [0,1]],
    "descriptor_types": ["tid", "dgd"]
  }'
```

### Get Config
```bash
curl http://localhost:8000/api/v1/descriptors/config/tid
```

## Testing

```bash
# Run all tests
pytest python/tests/test_descriptors.py -v

# Run specific test
pytest python/tests/test_descriptors.py::TestTopologicalInformationDescriptor -v

# With coverage
pytest python/tests/test_descriptors.py --cov=tcdb_api.descriptors
```

## Examples

```bash
# Run comprehensive examples
python examples/descriptor_usage.py
```

## Documentation

- **Full Documentation**: `DESCRIPTOR_DOCUMENTATION.md`
- **Implementation Summary**: `DESCRIPTOR_IMPLEMENTATION_SUMMARY.md`
- **Module README**: `python/tcdb_api/descriptors/README.md`

## Next Steps

1. **Try the examples**: `python examples/descriptor_usage.py`
2. **Read the docs**: `DESCRIPTOR_DOCUMENTATION.md`
3. **Run the tests**: `pytest python/tests/test_descriptors.py`
4. **Start the API**: `python run_api.py`
5. **Explore the API docs**: http://localhost:8000/docs

## Support

- Check `DESCRIPTOR_DOCUMENTATION.md` for detailed API reference
- See `examples/descriptor_usage.py` for more examples
- Run tests to verify installation: `pytest python/tests/test_descriptors.py`

---

**Ready to use!** All four descriptors are production-ready with full documentation and tests.

