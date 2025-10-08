# TCDB Domain Adapters

Lightweight, domain-specific adapters for the TCDB descriptor API. These adapters provide high-level interfaces for common use cases in LLM analysis, cybersecurity, and bioinformatics.

## Overview

Each adapter:
- **Minimal dependencies**: Only requires `requests`, `numpy`, and `scipy`
- **Domain-specific**: Tailored to common data formats in each domain
- **Standalone**: Can be used independently of the full tcdb_api package
- **Well-tested**: Includes comprehensive tests and examples

## Available Adapters

### 1. LLM Adapter (`llm_adapter.py`)

Analyzes transformer internals (embeddings, attention) to detect semantic drift and attention patterns.

**Use Cases:**
- Detect semantic drift in fine-tuned models
- Analyze attention graph structure
- Monitor embedding space topology
- Track model behavior changes

**Example:**
```python
from tcdb_api.adapters import LLMAdapter, DescriptorClient

# Initialize
client = DescriptorClient("http://localhost:8000")
adapter = LLMAdapter(client)

# Get model outputs
embeddings = model.get_hidden_states(tokens)  # (seq_len, hidden_dim)
attention = model.get_attention_weights(tokens)  # (n_heads, seq_len, seq_len)

# Compute descriptors
results = adapter.compute_descriptors(
    embeddings,
    attention=attention,
    baseline_embeddings=baseline_embeddings
)

# Check for drift
drift_result = adapter.detect_drift(
    current_embeddings=embeddings,
    baseline_embeddings=baseline_embeddings,
    threshold=0.5
)

if drift_result["drift_detected"]:
    print(f"⚠️  Drift detected! Score: {drift_result['drift_score']:.3f}")
```

**Descriptors Computed:**
- **KME-Δ**: Semantic drift vs baseline
- **TID**: Topology of embedding cloud
- **DGD**: Diffusion geometry on attention graph
- **GSER**: Multi-scale attention patterns

### 2. Cyber Adapter (`cyber_adapter.py`)

Analyzes network flows and logs to detect anomalies and topology changes.

**Use Cases:**
- Network intrusion detection
- Anomalous traffic pattern detection
- Network topology monitoring
- Behavioral analysis of network entities

**Example:**
```python
from tcdb_api.adapters import CyberAdapter, DescriptorClient

# Initialize
client = DescriptorClient("http://localhost:8000")
adapter = CyberAdapter(client, n_nodes=100)

# Network flows in time window
edges = [
    (src_id, dst_id, weight),
    ...
]

# Per-node signals (e.g., failed logins)
signal = np.array([...])  # Length = n_nodes

# Detect anomalies
anomaly_result = adapter.detect_anomaly(
    edges,
    node_signal=signal,
    gser_threshold=0.8,
    dgd_threshold=2.0
)

if anomaly_result["anomaly_detected"]:
    print(f"⚠️  Anomaly detected!")
    print(f"  GSER score: {anomaly_result['gser_score']:.3f}")
    print(f"  DGD score: {anomaly_result['dgd_score']:.3f}")
```

**Descriptors Computed:**
- **DGD**: Network topology health
- **GSER**: Multi-scale burst detection
- **KME-Δ**: Behavioral drift (optional, with feature embeddings)

### 3. Bio Adapter (`bio_adapter.py`)

Analyzes protein structures and ensembles to detect conformational changes.

**Use Cases:**
- MD trajectory analysis
- Protein ensemble comparison
- Conformational change detection
- Contact network analysis

**Example:**
```python
from tcdb_api.adapters import BioAdapter, DescriptorClient

# Initialize
client = DescriptorClient("http://localhost:8000")
adapter = BioAdapter(client)

# MD trajectory frames
coords_list = [frame1, frame2, ...]  # Each frame: (N_atoms, 3)

# Reference ensemble (e.g., wild-type)
ref_coords_list = [ref1, ref2, ...]

# Analyze conformational change
change_result = adapter.analyze_conformational_change(
    coords_list,
    ref_coords_list,
    threshold=0.5
)

if change_result["significant_change"]:
    print(f"⚠️  Significant conformational change detected!")
    print(f"  Drift score: {change_result['drift_score']:.3f}")
```

**Descriptors Computed:**
- **KME-Δ**: Conformational drift
- **TID**: Topological diversity of conformations
- **DGD**: Contact network geometry
- **GSER**: Residue flexibility patterns

## Installation

### Minimal (adapters only)
```bash
pip install requests numpy scipy
```

### Full (with optional dependencies)
```bash
pip install requests numpy scipy scikit-learn
```

Note: `scikit-learn` is only required for the bio adapter's PCA functionality.

## Quick Start

### 1. Start the API
```bash
python run_api.py
```

### 2. Test the adapters
```bash
# Test LLM adapter
python -m tcdb_api.adapters.llm_adapter

# Test Cyber adapter
python -m tcdb_api.adapters.cyber_adapter

# Test Bio adapter
python -m tcdb_api.adapters.bio_adapter
```

### 3. Use in your code
```python
from tcdb_api.adapters import DescriptorClient, LLMAdapter

client = DescriptorClient("http://localhost:8000")
adapter = LLMAdapter(client)

# Your analysis code here...
```

## API Reference

### DescriptorClient

**Methods:**
- `compute(name, params=None, **payload)` - Compute a descriptor
- `list_descriptors()` - List available descriptors
- `health_check()` - Check API health
- `csr_to_coo_payload(A)` - Convert sparse matrix to API payload
- `validate_point_cloud(X)` - Validate point cloud data
- `validate_graph(A)` - Validate graph data

### LLMAdapter

**Methods:**
- `compute_descriptors(token_embeddings, attention=None, baseline_embeddings=None, tau=0.0)` - Compute all descriptors
- `detect_drift(current_embeddings, baseline_embeddings, threshold=0.5)` - Detect semantic drift
- `analyze_attention_structure(attention, tau=0.1)` - Analyze attention graph

### CyberAdapter

**Methods:**
- `compute_descriptors(edges, node_signal=None, baseline_embeddings=None, window_embeddings=None)` - Compute all descriptors
- `detect_anomaly(edges, node_signal=None, gser_threshold=0.8, dgd_threshold=2.0)` - Detect anomalies
- `analyze_time_window(edges, node_signal=None, window_id=None)` - Analyze time window

### BioAdapter

**Methods:**
- `compute_descriptors(coords_list, contact_graph=None, ref_coords_list=None, contact_cutoff=8.0)` - Compute all descriptors
- `analyze_conformational_change(coords_list, ref_coords_list, threshold=0.5)` - Analyze conformational changes

## Advanced Usage

### Custom Parameters

All adapters support custom descriptor parameters:

```python
results = adapter.compute_descriptors(
    data,
    kme_params={"sigmas": [0.1, 0.5, 1.0, 2.0]},
    tid_params={"max_dimension": 2},
    dgd_params={"n_time_samples": 32},
    gser_params={"n_scales": 4, "k_neighbors": 10}
)
```

### Batch Processing

Process multiple time windows or samples:

```python
results_list = []
for window in time_windows:
    results = adapter.compute_descriptors(window.data)
    results_list.append(results)

# Analyze trends
drift_scores = [r["kme_delta"]["KME_delta_F"] for r in results_list]
```

### Custom Client Configuration

```python
client = DescriptorClient(
    base_url="http://api.example.com:8080",
    timeout=120  # Longer timeout for large datasets
)
```

## Testing

Run adapter tests:

```bash
pytest python/tests/test_adapters.py -v
```

## Examples

See the `examples/` directory for complete examples:
- `examples/llm_drift_detection.py` - LLM drift monitoring
- `examples/cyber_anomaly_detection.py` - Network anomaly detection
- `examples/bio_ensemble_analysis.py` - Protein ensemble analysis

## Troubleshooting

### API Connection Issues

```python
client = DescriptorClient("http://localhost:8000")

if not client.health_check():
    print("❌ API is not running")
    print("Start it with: python run_api.py")
else:
    print("✅ API is healthy")
```

### Data Validation

All adapters validate inputs before sending to the API:

```python
try:
    results = adapter.compute_descriptors(data)
except ValueError as e:
    print(f"❌ Invalid data: {e}")
```

## Performance Tips

1. **Batch similar requests** - Reuse the same client instance
2. **Adjust timeout** - Increase for large datasets
3. **Use sparse matrices** - For large graphs, use scipy.sparse
4. **Cache baselines** - Store baseline embeddings for repeated comparisons

## Contributing

To add a new domain adapter:

1. Create `python/tcdb_api/adapters/your_adapter.py`
2. Inherit from or use `DescriptorClient`
3. Add domain-specific data processing
4. Include a `__main__` demo block
5. Add tests to `python/tests/test_adapters.py`
6. Update this README

## License

Same as tcdb-core (see main LICENSE file).

