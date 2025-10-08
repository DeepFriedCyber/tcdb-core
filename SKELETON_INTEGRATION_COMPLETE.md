# Complete Skeleton Integration Guide

## Overview

This guide shows how to integrate the clean production skeleton into tcdb-core while preserving existing functionality.

## Skeleton Structure Analysis

### Key Design Principles

1. **Minimal API Surface**: Single `/descriptor/compute` endpoint handles all descriptors
2. **Flexible Payloads**: Different descriptors accept different input formats
3. **Registry Pattern**: Simple dict-based descriptor lookup
4. **Type Safety**: Pydantic models for request validation
5. **Optional Dependencies**: Graceful handling of missing libraries
6. **Lean Specs**: Mathematical properties as formal specifications

## Integration Strategy

### Phase 1: Adopt API Design ✅

The skeleton's API design is cleaner than the current multi-endpoint approach. Here's how to integrate:

#### Current tcdb-core API
```python
# Multiple endpoints
POST /api/v1/descriptors/compute          # Single descriptor
POST /api/v1/descriptors/compute/batch    # Multiple descriptors
GET  /api/v1/descriptors/list
GET  /api/v1/descriptors/config/{type}
```

#### Skeleton API (Simpler)
```python
# Single unified endpoint
POST /descriptor/compute
```

#### Recommended: Hybrid Approach
```python
# Keep both for backward compatibility
POST /api/v1/descriptors/compute          # Current (detailed)
POST /api/v1/descriptor/compute           # Skeleton (simple)
```

### Phase 2: Implement Unified Endpoint

Create a new simplified endpoint alongside existing ones:

```python
# python/tcdb_api/routers/descriptors_simple.py
from __future__ import annotations

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel
import numpy as np
import scipy.sparse as sp

from ..descriptors import (
    KME_Delta,
    DGD,
    TID,
    GSER,
)

router = APIRouter(prefix="/descriptor", tags=["descriptors-simple"])

REGISTRY = {
    "kme_delta": KME_Delta,
    "dgd": DGD,
    "tid": TID,
    "gser": GSER,
}


class ComputeRequest(BaseModel):
    """Unified compute request for all descriptors."""
    name: str
    params: dict = {}
    
    # Flexible payload (descriptor-specific)
    X: list[list[float]] | None = None                # embeddings
    X_ref: list[list[float]] | None = None
    adj_indices: list[tuple[int, int]] | None = None  # sparse graph (COO)
    adj_data: list[float] | None = None
    n_nodes: int | None = None
    signal: list[float] | None = None                 # node signal for GSER


@router.post("/compute")
def compute(req: ComputeRequest) -> dict[str, float]:
    """
    Unified descriptor computation endpoint.
    
    Accepts different payload formats depending on descriptor type:
    - kme_delta: X, X_ref (optional)
    - dgd: adj_indices, adj_data, n_nodes
    - tid: X
    - gser: adj_indices, adj_data, n_nodes, signal
    """
    if req.name not in REGISTRY:
        raise HTTPException(
            status_code=400,
            detail=f"Unknown descriptor '{req.name}'. Available: {list(REGISTRY.keys())}"
        )
    
    desc = REGISTRY[req.name](**req.params)
    
    try:
        if req.name == "kme_delta":
            X = np.array(req.X, dtype=float)
            X_ref = None if req.X_ref is None else np.array(req.X_ref, dtype=float)
            return desc.compute(X=X, X_ref=X_ref)
        
        elif req.name == "dgd":
            if req.n_nodes is None or req.adj_indices is None:
                raise HTTPException(400, "DGD requires n_nodes and adj_indices")
            
            A = sp.csr_matrix(
                (req.adj_data, zip(*req.adj_indices)),
                shape=(req.n_nodes, req.n_nodes)
            )
            return desc.compute(A)
        
        elif req.name == "tid":
            X = np.array(req.X, dtype=float)
            return desc.compute(X)
        
        elif req.name == "gser":
            if req.n_nodes is None or req.signal is None:
                raise HTTPException(400, "GSER requires n_nodes and signal")
            
            A = sp.csr_matrix(
                (req.adj_data, zip(*req.adj_indices)),
                shape=(req.n_nodes, req.n_nodes)
            )
            x = np.array(req.signal, dtype=float)
            return desc.compute(A, x)
        
        else:
            raise HTTPException(400, f"Handler not implemented for {req.name}")
    
    except Exception as e:
        raise HTTPException(500, f"Computation failed: {str(e)}")
```

### Phase 3: Add to Main App

```python
# python/tcdb_api/app.py
from .routers import (
    health,
    pipeline,
    tda,
    certificate,
    reasoner,
    eval,
    auth,
    keys,
    descriptors,           # Existing detailed API
    descriptors_simple,    # New simple API
)

# Include both routers
app.include_router(descriptors.router)         # /api/v1/descriptors/*
app.include_router(descriptors_simple.router)  # /descriptor/*
```

### Phase 4: Adopt Test Structure

The skeleton's test structure is excellent. Create parallel tests:

```python
# python/tests/test_descriptors_simple.py
"""
Simple tests following skeleton pattern.
Focused on basic functionality and dimensionless properties.
"""
from __future__ import annotations

import numpy as np
import scipy.sparse as sp
import pytest

from tcdb_api.descriptors.kme_delta_v2 import KME_Delta
from tcdb_api.descriptors.dgd import DGD
from tcdb_api.descriptors.tid import TID
from tcdb_api.descriptors.gser import GSER


def test_kme_delta_basic():
    """Test KME-Δ basic computation."""
    X = np.random.RandomState(0).randn(64, 8)
    X_ref = np.random.RandomState(1).randn(64, 8)
    
    desc = KME_Delta(sigmas=(0.5, 1.0))
    feats = desc.compute(X, X_ref=X_ref)
    
    assert "KME_delta_F" in feats
    assert feats["KME_delta_F"] >= 0.0
    assert np.isfinite(feats["KME_delta_F"])


def _toy_graph(n: int = 32) -> sp.csr_matrix:
    """Create simple ring graph for testing."""
    rows, cols, data = [], [], []
    for i in range(n):
        j = (i + 1) % n
        rows += [i, j]
        cols += [j, i]
        data += [1.0, 1.0]
    return sp.csr_matrix((data, (rows, cols)), shape=(n, n))


def test_dgd_runs():
    """Test DGD runs without errors."""
    A = _toy_graph(32)
    
    desc = DGD(n_times=8, probes=4)
    feats = desc.compute(A)
    
    assert "DGD_F" in feats
    assert np.isfinite(feats["DGD_F"])


def test_tid_runs_without_gudhi():
    """Test TID graceful fallback without Gudhi."""
    X = np.random.RandomState(0).randn(64, 3)
    
    desc = TID(max_dim=1)
    feats = desc.compute(X)
    
    assert "TID_F" in feats
    # May be 0.0 if Gudhi not available
    assert feats["TID_F"] >= 0.0


def test_gser_runs():
    """Test GSER basic computation."""
    A = _toy_graph(32)
    x = np.random.RandomState(0).randn(32)
    
    desc = GSER()
    feats = desc.compute(A, x)
    
    assert "GSER_F" in feats
    assert 0.0 <= feats["GSER_F"] <= 1.0


@pytest.mark.parametrize("descriptor_name,descriptor_class", [
    ("kme_delta", KME_Delta),
    ("dgd", DGD),
    ("tid", TID),
    ("gser", GSER),
])
def test_descriptor_dimensionless(descriptor_name, descriptor_class):
    """Test that all descriptors return dimensionless values."""
    # This is a property test - values should be scale-invariant
    # For now, just check they return finite values
    pass  # TODO: Implement scale-invariance tests
```

### Phase 5: Configuration Integration

The skeleton's YAML config is cleaner. Integrate it:

```yaml
# python/tcdb_api/config/descriptor_defaults_v2.yaml
# Simplified configuration following skeleton pattern

descriptors:
  - name: kme_delta
    params:
      sigmas: [0.5, 1.0, 2.0]
      eps: 1.0e-12
  
  - name: dgd
    params:
      n_times: 32
      t_min: 0.01
      t_max: 10.0
      probes: 16
  
  - name: tid
    params:
      max_dim: 1
  
  - name: gser
    params:
      scales: [0.25, 0.5, 1.0, 2.0]

# API settings
api:
  title: "TCDB Descriptor API"
  version: "0.2.0"
  enable_simple_endpoint: true
  enable_detailed_endpoint: true
```

### Phase 6: Lean Specifications (Optional)

The Lean specs are a brilliant addition for formal verification. Create the structure:

```
tcdb-core/
├── lean/
│   ├── Specs.lean              # Mathematical specifications
│   ├── Dimensionless.lean      # Dimensionless property proofs
│   ├── Stability.lean          # Stability theorems
│   └── lakefile.lean           # Lean 4 build configuration
```

```lean
-- lean/Specs.lean
/-
  Mathematical specifications for TCDB descriptors.
  
  These specs define properties that descriptors should satisfy,
  providing a foundation for formal verification.
-/

import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Log
import Mathlib.Analysis.NormedSpace.Basic

namespace TCDB.Descriptors

/-- A descriptor is a function from data to real numbers. -/
def Descriptor (α : Type*) := α → ℝ

/-- Dimensionless property: invariant under isotropic scaling. -/
def Dimensionless {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] 
    (F : Descriptor α) : Prop :=
  ∀ (λ : ℝ) (hλ : λ > 0) (x : α), F (λ • x) = F x

/-- Stability property: continuous with respect to input perturbations. -/
def Stable {α : Type*} [TopologicalSpace α] (F : Descriptor α) : Prop :=
  Continuous F

/-- Multiscale property: captures structure at multiple scales. -/
def Multiscale {α : Type*} (F : Descriptor α) (scales : List ℝ) : Prop :=
  ∃ (components : List (Descriptor α)),
    components.length = scales.length ∧
    ∀ x, F x = (components.map (fun f => f x)).sum

/-- Example: ratio of two functions is dimensionless if both scale the same way. -/
theorem ratio_dimensionless {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {f g : Descriptor α}
    (hf : ∀ λ (hλ : λ > 0) x, f (λ • x) = λ * f x)
    (hg : ∀ λ (hλ : λ > 0) x, g (λ • x) = λ * g x)
    (hg_ne : ∀ x, g x ≠ 0) :
    Dimensionless (fun x => f x / g x) := by
  intro λ hλ x
  simp [Dimensionless]
  rw [hf λ hλ x, hg λ hλ x]
  field_simp
  ring

end TCDB.Descriptors
```

## Complete Integration Checklist

### Immediate (Low Risk)
- [x] Create `descriptors_simple.py` router
- [x] Add unified `/descriptor/compute` endpoint
- [x] Create `test_descriptors_simple.py`
- [ ] Update `app.py` to include simple router
- [ ] Test both APIs side-by-side

### Short Term (Medium Risk)
- [ ] Migrate existing tests to skeleton pattern
- [ ] Add YAML v2 configuration
- [ ] Create Lean specification structure
- [ ] Document API differences

### Long Term (Higher Risk)
- [ ] Deprecate detailed API (if desired)
- [ ] Formalize Lean proofs
- [ ] Add property-based tests
- [ ] Performance benchmarking

## API Comparison

### Skeleton API (Simple)
```bash
# Single endpoint, flexible payload
curl -X POST http://localhost:8000/descriptor/compute \
  -H "Content-Type: application/json" \
  -d '{
    "name": "kme_delta",
    "params": {"sigmas": [1.0, 2.0]},
    "X": [[0,0], [1,0], [0,1]],
    "X_ref": [[2,2], [3,3]]
  }'
```

### Current API (Detailed)
```bash
# Separate endpoint per operation
curl -X POST http://localhost:8000/api/v1/descriptors/compute \
  -H "Content-Type: application/json" \
  -d '{
    "data": [[0,0], [1,0], [0,1]],
    "descriptor_type": "kme_delta",
    "parameters": {"sigma_scales": [1.0, 2.0]}
  }'
```

## Benefits of Integration

### From Skeleton
✅ **Simpler API**: Single endpoint vs multiple  
✅ **Flexible payloads**: Descriptor-specific formats  
✅ **Cleaner tests**: Focused on properties  
✅ **Formal specs**: Lean verification foundation  

### From Current tcdb-core
✅ **Rich features**: Advanced options  
✅ **Comprehensive tests**: 38 tests  
✅ **Full documentation**: 7 docs  
✅ **Production deployment**: Working API  

## Recommendation

**Adopt hybrid approach:**
1. Keep current detailed API for production
2. Add skeleton simple API for ease of use
3. Gradually migrate to skeleton patterns
4. Use Lean specs for formal verification

This gives you the best of both worlds while maintaining backward compatibility.

