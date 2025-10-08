# TCDB Descriptors Module

## Quick Start

```python
import numpy as np
from tcdb_api.descriptors import TopologicalInformationDescriptor

# Create point cloud
points = np.random.randn(50, 3)

# Compute TID descriptor
tid = TopologicalInformationDescriptor(max_dimension=2)
result = tid.compute(points)

print(f"TID value: {result['F_TID']:.4f}")
```

## Available Descriptors

### 1. TID - Topological-Information Descriptor
Combines persistence entropy, Betti curve total variation, and landscape ratios.

```python
from tcdb_api.descriptors import TopologicalInformationDescriptor

tid = TopologicalInformationDescriptor(
    max_dimension=2,
    max_edge_length=None,  # Auto
    n_bins=100
)
result = tid.compute(points)
```

**Output**: `F_TID`, `H0`, `H1`, `H2`, `TV0`, `TV1`, `TV2`, `L0`, `L1`, `L2`

### 2. DGD - Diffusion-Geometry Descriptor
Heat diffusion on graphs with multiscale analysis.

```python
from tcdb_api.descriptors import DiffusionGeometryDescriptor

dgd = DiffusionGeometryDescriptor(
    graph_type='knn',
    k_neighbors=5,
    n_time_samples=20
)
result = dgd.compute(points)
```

**Output**: `F_DGD`, `phi1_mean`, `phi2_mean`, `spectral_decay`

### 3. KME-Δ - Kernel Mean Embedding Divergence
RKHS-based distributional comparison.

```python
from tcdb_api.descriptors import KernelMeanEmbeddingDelta

kme = KernelMeanEmbeddingDelta(
    kernel_type='rbf',
    sigma_scales=[0.1, 0.5, 1.0, 2.0, 5.0],
    reference_type='uniform'
)
result = kme.compute(points)
```

**Output**: `F_KME_DELTA`, `mean_divergence`, `divergence_scale_0`, ...

### 4. GSER - Graph-Scattering Energy Ratio
Graph wavelet scattering transform.

```python
from tcdb_api.descriptors import GraphScatteringEnergyRatio

gser = GraphScatteringEnergyRatio(
    n_scales=4,
    graph_type='knn',
    signal_type='coordinates'
)
result = gser.compute(points)
```

**Output**: `F_GSER`, `energy_concentration`, `S1_0`, `S1_1`, `S2_0_0`, ...

## Using the Registry

```python
from tcdb_api.descriptors import DescriptorRegistry

registry = DescriptorRegistry()

# List available
print(registry.list())  # ['tid', 'dgd', 'kme_delta', 'gser']

# Get descriptor
descriptor = registry.get('tid', max_dimension=2)
result = descriptor.compute(points)
```

## REST API

### Compute Single Descriptor
```bash
curl -X POST http://localhost:8000/api/v1/descriptors/compute \
  -H "Content-Type: application/json" \
  -d '{
    "data": [[0,0], [1,0], [0,1], [1,1]],
    "descriptor_type": "tid",
    "parameters": {"max_dimension": 2}
  }'
```

### Compute Multiple Descriptors
```bash
curl -X POST http://localhost:8000/api/v1/descriptors/compute/batch \
  -H "Content-Type: application/json" \
  -d '{
    "data": [[0,0], [1,0], [0,1]],
    "descriptor_types": ["tid", "dgd", "kme_delta"],
    "parameters": {
      "tid": {"max_dimension": 1},
      "dgd": {"n_time_samples": 10}
    }
  }'
```

## Key Features

✅ **Dimensionless**: All outputs are ratios or probabilities  
✅ **Multiscale**: Explicit scale parameters  
✅ **Patent-clean**: Independent mathematical formulations  
✅ **Fast**: Optimized implementations with sparse methods  
✅ **Tested**: Comprehensive unit and integration tests  

## Architecture

```
descriptors/
├── __init__.py          # Main exports
├── base.py              # Abstract interface
├── tid.py               # Topological-Information
├── dgd.py               # Diffusion-Geometry
├── kme_delta.py         # Kernel Mean Embedding
└── gser.py              # Graph-Scattering
```

## Dependencies

- `numpy>=1.21.0`
- `scipy>=1.7.0`
- `scikit-learn>=1.0.0`
- `ripser>=0.6.0` (for TID)
- `persim>=0.3.0` (for TID)

## Examples

See `examples/descriptor_usage.py` for comprehensive examples.

## Documentation

See `DESCRIPTOR_DOCUMENTATION.md` for full mathematical details and API reference.

## Testing

```bash
# Unit tests
pytest python/tests/test_descriptors.py

# API tests
pytest python/tests/test_descriptor_api.py
```

## Configuration

Default configurations in `python/tcdb_api/config/descriptor_defaults.yaml`.

Override per-descriptor:
```python
from tcdb_api.config import get_default_config

config = get_default_config()
tid_config = config.get('tid')
tid_config['max_dimension'] = 3

tid = TopologicalInformationDescriptor(**tid_config)
```

## Performance Tips

1. **Use sparse methods** for large graphs (>100 nodes):
   ```python
   dgd = DiffusionGeometryDescriptor(use_sparse=True)
   ```

2. **Reduce time samples** for faster DGD:
   ```python
   dgd = DiffusionGeometryDescriptor(n_time_samples=10)
   ```

3. **Limit scales** for faster KME-Δ:
   ```python
   kme = KernelMeanEmbeddingDelta(sigma_scales=[0.5, 1.0])
   ```

4. **Lower max_dimension** for faster TID:
   ```python
   tid = TopologicalInformationDescriptor(max_dimension=1)
   ```

## Common Use Cases

### Anomaly Detection
```python
# Compute KME-Δ to detect distributional drift
kme = KernelMeanEmbeddingDelta(reference_type='gaussian')
result = kme.compute(new_data)

if result['F_KME_DELTA'] > threshold:
    print("Anomaly detected!")
```

### Topological Feature Detection
```python
# Use TID to detect holes and voids
tid = TopologicalInformationDescriptor(max_dimension=2)
result = tid.compute(point_cloud)

betti = tid.compute_betti_numbers(point_cloud)
print(f"Holes (H1): {betti[1]}")
```

### Geometric Complexity
```python
# Use DGD to measure geometric complexity
dgd = DiffusionGeometryDescriptor()
result = dgd.compute(point_cloud)

print(f"Spectral decay: {result['spectral_decay']}")
```

### Signal Analysis on Graphs
```python
# Use GSER for multiscale signal features
gser = GraphScatteringEnergyRatio(n_scales=4)
result = gser.compute(point_cloud)

print(f"Energy concentration: {result['energy_concentration']}")
```

## Troubleshooting

**ImportError: ripser not found**
```bash
pip install ripser persim
```

**Memory error on large datasets**
- Use sparse methods: `use_sparse=True`
- Reduce dimensions: `max_dimension=1`
- Sample data: `points = points[::10]`

**Slow computation**
- Reduce time samples: `n_time_samples=10`
- Reduce scales: `n_scales=2`
- Use kNN instead of epsilon graphs

## Contributing

See `CONTRIBUTING.md` for guidelines.

## License

MIT License - see `LICENSE` file.

