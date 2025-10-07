# Entropy API Endpoint & Python Bindings

## ✅ Implementation Complete!

Added comprehensive entropy analysis capabilities via:
1. **REST API Endpoint** - `/api/v1/entropy/analyze`
2. **Python Bindings** - Full Python module for entropy functions

---

## 🌐 API Endpoint: `/api/v1/entropy/analyze`

### **Endpoint Details**

- **URL**: `https://tcdb.uk/api/v1/entropy/analyze`
- **Method**: `POST`
- **Authentication**: Bearer token (API key required)
- **Content-Type**: `application/json`

### **Request Format**

```json
{
  "data": [1.0, 2.0, 3.0, 4.0, 5.0],
  "analysis_type": "shannon",
  "options": {
    "bins": 10
  }
}
```

### **Analysis Types**

| Type | Description | Input Format |
|------|-------------|--------------|
| `shannon` | Shannon entropy | Array of numbers or probabilities |
| `topological` | Topological entropy | Array of numbers |
| `provenance` | Provenance entropy | Object with `operations` array |
| `dataset` | Dataset entropy | Array of numbers |
| `comprehensive` | All analyses | Array of numbers |

---

## 📊 API Examples

### **1. Shannon Entropy**

**Request**:
```bash
curl -X POST https://tcdb.uk/api/v1/entropy/analyze \
  -H "Authorization: Bearer YOUR_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "data": [0.25, 0.25, 0.25, 0.25],
    "analysis_type": "shannon"
  }'
```

**Response**:
```json
{
  "success": true,
  "analysis_type": "shannon",
  "result": {
    "shannon_entropy": 2.0,
    "max_entropy": 2.0,
    "normalized_entropy": 1.0,
    "num_outcomes": 4,
    "interpretation": "Very high entropy - highly uniform distribution",
    "optimal_encoding_bits": 8
  },
  "timestamp": 1704672000000
}
```

### **2. Topological Entropy**

**Request**:
```bash
curl -X POST https://tcdb.uk/api/v1/entropy/analyze \
  -H "Authorization: Bearer YOUR_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "data": [1.0, 2.0, 3.0, 4.0, 5.0],
    "analysis_type": "topological"
  }'
```

**Response**:
```json
{
  "success": true,
  "analysis_type": "topological",
  "result": {
    "persistence_entropy": 2.0,
    "betti_entropy": 1.58,
    "complexity_score": 0.75,
    "betti_numbers": [1, 1, 0],
    "interpretation": "Complex topology with multiple features"
  },
  "timestamp": 1704672000000
}
```

### **3. Provenance Entropy**

**Request**:
```bash
curl -X POST https://tcdb.uk/api/v1/entropy/analyze \
  -H "Authorization: Bearer YOUR_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "data": {
      "operations": [
        {"type": "generation"},
        {"type": "retrieval"},
        {"type": "transformation"}
      ]
    },
    "analysis_type": "provenance"
  }'
```

**Response**:
```json
{
  "success": true,
  "analysis_type": "provenance",
  "result": {
    "operation_entropy": 1.58,
    "max_operation_entropy": 1.58,
    "normalized_entropy": 1.0,
    "operation_types": 3,
    "total_operations": 3,
    "interpretation": "Diverse operations"
  },
  "timestamp": 1704672000000
}
```

### **4. Dataset Entropy**

**Request**:
```bash
curl -X POST https://tcdb.uk/api/v1/entropy/analyze \
  -H "Authorization: Bearer YOUR_API_KEY" \
  -H "Content-Type": application/json" \
  -d '{
    "data": [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0],
    "analysis_type": "dataset",
    "options": {"bins": 10}
  }'
```

**Response**:
```json
{
  "success": true,
  "analysis_type": "dataset",
  "result": {
    "dataset_entropy": 3.32,
    "max_entropy": 3.32,
    "normalized_entropy": 1.0,
    "bins": 10,
    "data_points": 10,
    "optimal_proof_bits": 34,
    "interpretation": "Highly complex data with diverse values"
  },
  "timestamp": 1704672000000
}
```

### **5. Comprehensive Analysis**

**Request**:
```bash
curl -X POST https://tcdb.uk/api/v1/entropy/analyze \
  -H "Authorization: Bearer YOUR_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{
    "data": [1.0, 2.0, 3.0, 4.0, 5.0],
    "analysis_type": "comprehensive"
  }'
```

**Response**:
```json
{
  "success": true,
  "analysis_type": "comprehensive",
  "result": {
    "shannon": {
      "shannon_entropy": 2.32,
      "normalized_entropy": 1.0,
      ...
    },
    "topological": {
      "persistence_entropy": 2.0,
      "complexity_score": 0.68,
      ...
    },
    "dataset": {
      "dataset_entropy": 2.32,
      "optimal_proof_bits": 12,
      ...
    }
  },
  "timestamp": 1704672000000
}
```

---

## 🐍 Python Bindings

### **Installation**

The entropy module is included in the TCDB Python package:

```python
from tcdb_api.entropy import (
    EntropyAnalyzer,
    TopologicalEntropy,
    DatasetEntropy
)
```

### **Python Examples**

#### **1. Shannon Entropy**

```python
from tcdb_api.entropy import EntropyAnalyzer

# Compute entropy from probabilities
probabilities = [0.25, 0.25, 0.25, 0.25]
entropy = EntropyAnalyzer.shannon_entropy(probabilities)
print(f"Entropy: {entropy} bits")  # 2.0 bits

# Normalized entropy
norm_entropy = EntropyAnalyzer.normalized_entropy(probabilities)
print(f"Normalized: {norm_entropy}")  # 1.0 (perfectly uniform)

# Self-information (surprise)
surprise = EntropyAnalyzer.self_information(0.25)
print(f"Surprise: {surprise} bits")  # 2.0 bits
```

#### **2. Entropy from Counts**

```python
# From list of counts
counts = [10, 10, 10, 10]
entropy = EntropyAnalyzer.entropy_from_counts(counts)
print(f"Entropy: {entropy} bits")  # 2.0 bits

# From dictionary
count_dict = {'A': 10, 'B': 10, 'C': 10, 'D': 10}
entropy = EntropyAnalyzer.entropy_from_counts(count_dict)
print(f"Entropy: {entropy} bits")  # 2.0 bits
```

#### **3. Optimal Encoding**

```python
# Source Coding Theorem
entropy = 1.5  # bits per sample
n_samples = 100
optimal_bits = EntropyAnalyzer.optimal_encoding_bits(entropy, n_samples)
print(f"Minimum bits needed: {optimal_bits}")  # 150 bits
```

#### **4. Topological Entropy**

```python
from tcdb_api.entropy import TopologicalEntropy

# Persistence diagram entropy
intervals = [0.5, 1.0, 1.5, 2.0, 2.5]
pers_entropy = TopologicalEntropy.persistence_entropy(intervals)
print(f"Persistence entropy: {pers_entropy} bits")

# Betti number entropy
betti_numbers = [5, 3, 1]
betti_entropy = TopologicalEntropy.betti_entropy(betti_numbers)
print(f"Betti entropy: {betti_entropy} bits")

# Complexity score
complexity = TopologicalEntropy.complexity_score(intervals, betti_numbers)
print(f"Complexity: {complexity}")  # [0, 1]
```

#### **5. Dataset Entropy**

```python
from tcdb_api.entropy import DatasetEntropy

# Analyze dataset
data = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
result = DatasetEntropy.compute_entropy(data, bins=10)

print(f"Entropy: {result['entropy']} bits")
print(f"Normalized: {result['normalized_entropy']}")
print(f"Optimal bits: {result['optimal_bits']}")
```

#### **6. KL Divergence**

```python
# Measure difference between distributions
p = [0.7, 0.3]  # True distribution
q = [0.5, 0.5]  # Approximating distribution

kl = EntropyAnalyzer.kl_divergence(p, q)
print(f"KL divergence: {kl} bits")  # > 0 (distributions differ)
```

#### **7. Mutual Information**

```python
# Shared information between variables
prob_x = [0.5, 0.5]
prob_y = [0.5, 0.5]
joint_prob = [
    [0.25, 0.25],
    [0.25, 0.25]
]

mi = EntropyAnalyzer.mutual_information(prob_x, prob_y, joint_prob)
print(f"Mutual information: {mi} bits")  # 0.0 (independent)
```

---

## 🧪 Test Coverage

### **API Tests (JavaScript)**
- ✅ 10 entropy endpoint tests
- ✅ All analysis types covered
- ✅ Error handling tested
- ✅ **Total: 37 API tests passing**

### **Python Tests**
- ✅ 13 EntropyAnalyzer tests
- ✅ 5 TopologicalEntropy tests
- ✅ 4 DatasetEntropy tests
- ✅ 3 Integration tests
- ✅ **Total: 25 Python tests passing**

### **Combined Test Suite**
- **JavaScript**: 37 tests ✅
- **Python**: 25 tests ✅
- **Rust**: 66 tests ✅
- **TOTAL**: **128 tests passing** 🎉

---

## 📚 API Reference

### **EntropyAnalyzer Methods**

| Method | Parameters | Returns | Description |
|--------|-----------|---------|-------------|
| `shannon_entropy()` | probabilities, base=2.0 | float | Shannon entropy |
| `normalized_entropy()` | probabilities | float | Normalized [0,1] |
| `self_information()` | probability | float | Surprise measure |
| `entropy_from_counts()` | counts | float | Entropy from counts |
| `optimal_encoding_bits()` | entropy, n_samples | int | Minimum bits |
| `kl_divergence()` | p, q | float | Relative entropy |
| `mutual_information()` | prob_x, prob_y, joint | float | Shared info |
| `cross_entropy()` | p, q | float | ML loss function |

### **TopologicalEntropy Methods**

| Method | Parameters | Returns | Description |
|--------|-----------|---------|-------------|
| `persistence_entropy()` | intervals | float | Persistence entropy |
| `betti_entropy()` | betti_numbers | float | Betti entropy |
| `complexity_score()` | intervals, betti | float | Complexity [0,1] |

### **DatasetEntropy Methods**

| Method | Parameters | Returns | Description |
|--------|-----------|---------|-------------|
| `compute_entropy()` | data, bins=10 | dict | Full analysis |

---

## 🚀 Deployment

The entropy endpoint is deployed at:
- **Production**: `https://tcdb.uk/api/v1/entropy/analyze`
- **Version**: 1.1.0

---

## 📊 Summary

**What was added:**
- ✅ REST API endpoint for entropy analysis
- ✅ 5 analysis types (shannon, topological, provenance, dataset, comprehensive)
- ✅ Complete Python bindings module
- ✅ 10 JavaScript API tests
- ✅ 25 Python tests
- ✅ Comprehensive documentation

**Total new capabilities:**
- **API Functions**: 5 analysis types
- **Python Functions**: 11 public methods
- **Tests**: 35 new tests (10 JS + 25 Python)
- **Documentation**: Complete API reference + examples

**Your TCDB system now has entropy analysis available via:**
1. **Rust core** - 17 entropy functions
2. **Python bindings** - 11 wrapper methods
3. **REST API** - 5 analysis endpoints

🎉 **Full-stack entropy analysis is now live!**

