# Production Skeleton Integration Guide

## Overview

This document compares the production-ready skeleton you provided with the current tcdb-core implementation and provides a migration path.

## Key Design Improvements in Your Skeleton

### 1. **Cleaner Type Hints**
```python
from __future__ import annotations  # ✅ Enables forward references

# Your skeleton
def compute(self, X: np.ndarray, **kwargs) -> Dict[str, float]:
    ...

# Current implementation
def compute(self, data: np.ndarray, **kwargs) -> Dict[str, float]:
    ...
```

### 2. **Dataclass-Based Descriptors**
```python
# Your skeleton - cleaner initialization
@dataclass
class KME_Delta(Descriptor):
    sigmas: Tuple[float, ...] = (0.5, 1.0, 2.0)
    weights: Optional[Tuple[float, ...]] = None
    eps: float = 1e-12
    name: str = "kme_delta"

# Current implementation - manual __init__
class KernelMeanEmbeddingDelta(Descriptor):
    def __init__(self, sigma_scales=None, ...):
        super().__init__(...)
        self.sigma_scales = sigma_scales or [0.5, 1.0, 2.0]
```

### 3. **Graceful Fallbacks**
```python
# Your skeleton - production-ready
try:
    import gudhi
    _HAS_GUDHI = True
except Exception:
    _HAS_GUDHI = False

def compute(self, X, **kwargs):
    if not _HAS_GUDHI:
        return {"TID_F": 0.0, "TID_has_backend": 0.0}
    # ... actual computation
```

### 4. **Simpler Utility Functions**
```python
# Your skeleton - focused and efficient
def _pairwise_sq_dists(X: np.ndarray, Y: np.ndarray) -> np.ndarray:
    X2 = (X * X).sum(axis=1)[:, None]
    Y2 = (Y * Y).sum(axis=1)[None, :]
    return X2 + Y2 - 2.0 * X @ Y.T

def _rbf_kernel(X: np.ndarray, Y: np.ndarray, sigma: float) -> np.ndarray:
    D2 = _pairwise_sq_dists(X, Y)
    return np.exp(-D2 / (2.0 * sigma * sigma))
```

## Comparison Matrix

| Feature | Your Skeleton | Current tcdb-core | Winner |
|---------|---------------|-------------------|--------|
| Type hints | `from __future__ import annotations` | Standard typing | **Skeleton** |
| Descriptor init | `@dataclass` | Manual `__init__` | **Skeleton** |
| Dependency handling | Graceful fallbacks | Hard requirements | **Skeleton** |
| Code simplicity | Minimal, focused | Feature-rich | **Skeleton** |
| Production readiness | ✅ | ✅ | **Tie** |
| Test coverage | Scaffold | Comprehensive | **tcdb-core** |
| Documentation | Minimal | Extensive | **tcdb-core** |
| API integration | Basic | Full FastAPI | **tcdb-core** |
| Advanced features | Scaffold | Implemented | **tcdb-core** |

## Integration Strategy

### Phase 1: Adopt Best Practices (✅ DONE)

Created enhanced versions incorporating your design:
- `base_v2.py` - Cleaner base with utility functions
- `kme_delta_v2.py` - Dataclass-based KME-Δ

### Phase 2: Gradual Migration (RECOMMENDED)

#### Option A: Parallel Implementation
Keep both versions during transition:
```
descriptors/
  base.py          # Current (stable)
  base_v2.py       # Enhanced (new)
  kme_delta.py     # Current
  kme_delta_v2.py  # Enhanced
```

#### Option B: In-Place Upgrade
Replace current with enhanced versions:
```python
# Maintain backward compatibility
from .kme_delta_v2 import KME_Delta as KernelMeanEmbeddingDelta
```

### Phase 3: Full Adoption

Migrate all descriptors to dataclass pattern:

```python
@dataclass
class DGD(Descriptor):
    """Diffusion-Geometry Descriptor"""
    n_times: int = 32
    t_min: float = 1e-2
    t_max: float = 10.0
    probes: int = 16
    name: str = "dgd"
    
    def compute(self, A: sp.spmatrix, **kwargs) -> Dict[str, float]:
        # Implementation
        ...
```

## Specific Improvements to Adopt

### 1. Efficient Distance Computation

**Your skeleton:**
```python
def _pairwise_sq_dists(X: np.ndarray, Y: np.ndarray) -> np.ndarray:
    X2 = (X * X).sum(axis=1)[:, None]
    Y2 = (Y * Y).sum(axis=1)[None, :]
    return X2 + Y2 - 2.0 * X @ Y.T
```

**Current tcdb-core:**
```python
def compute_distance_matrix(X: np.ndarray, Y: Optional[np.ndarray] = None) -> np.ndarray:
    if Y is None:
        Y = X
    from scipy.spatial.distance import cdist
    return cdist(X, Y, metric='euclidean')
```

**Recommendation:** Use your version - it's faster and more memory-efficient.

### 2. Graceful Dependency Handling

**Adopt this pattern everywhere:**
```python
try:
    import gudhi
    _HAS_GUDHI = True
except ImportError:
    _HAS_GUDHI = False

try:
    import ripser
    _HAS_RIPSER = True
except ImportError:
    _HAS_RIPSER = False

def compute(self, X, **kwargs):
    if not _HAS_GUDHI and not _HAS_RIPSER:
        return {
            "TID_F": 0.0,
            "TID_has_backend": 0.0,
            "TID_error": "No TDA backend available"
        }
```

### 3. Dataclass Pattern

**Convert all descriptors:**
```python
from dataclasses import dataclass, field

@dataclass
class TopologicalInformationDescriptor(Descriptor):
    max_dimension: int = 2
    max_edge_length: Optional[float] = None
    n_bins: int = 100
    name: str = "tid"
    
    def compute(self, data: np.ndarray, **kwargs) -> Dict[str, float]:
        ...
```

### 4. Simplified Heat Trace

**Your Hutchinson estimator is excellent:**
```python
def _heat_trace(L: sp.csr_matrix, t: float, n_probe: int = 16, 
                rng: Optional[np.random.Generator] = None) -> float:
    if rng is None:
        rng = np.random.default_rng(0)
    n = L.shape[0]
    tr = 0.0
    for _ in range(n_probe):
        z = rng.choice([-1.0, 1.0], size=n)
        v = spla.expm_multiply(-t * L, z)
        tr += z @ v
    return float(tr / n_probe)
```

**Recommendation:** Replace current stochastic method with this cleaner version.

## Migration Checklist

### Immediate (Low Risk)
- [x] Create `base_v2.py` with enhanced utilities
- [x] Create `kme_delta_v2.py` with dataclass pattern
- [ ] Add graceful fallbacks for optional dependencies
- [ ] Adopt `_pairwise_sq_dists` for efficiency

### Short Term (Medium Risk)
- [ ] Convert DGD to dataclass with your heat trace estimator
- [ ] Convert TID to dataclass with graceful Gudhi fallback
- [ ] Convert GSER to dataclass with diffusion filters
- [ ] Update all tests to handle both versions

### Long Term (Higher Risk)
- [ ] Deprecate old implementations
- [ ] Update all documentation
- [ ] Migrate API endpoints to use v2
- [ ] Remove backward compatibility shims

## Code Examples

### Before (Current)
```python
from tcdb_api.descriptors import KernelMeanEmbeddingDelta

kme = KernelMeanEmbeddingDelta(
    kernel_type='rbf',
    sigma_scales=[0.5, 1.0, 2.0],
    reference_type='uniform'
)
result = kme.compute(data)
```

### After (Enhanced)
```python
from tcdb_api.descriptors import KME_Delta

kme = KME_Delta(
    sigmas=(0.5, 1.0, 2.0),
    weights=None,  # uniform
    eps=1e-12
)
result = kme.compute(data)
```

### Backward Compatible Bridge
```python
# In __init__.py
from .kme_delta_v2 import KME_Delta

# Alias for backward compatibility
class KernelMeanEmbeddingDelta(KME_Delta):
    """Backward compatible wrapper."""
    def __init__(self, kernel_type='rbf', sigma_scales=None, **kwargs):
        sigmas = tuple(sigma_scales) if sigma_scales else (0.5, 1.0, 2.0)
        super().__init__(sigmas=sigmas, **kwargs)
```

## Testing Strategy

### Dual Testing
```python
import pytest
from tcdb_api.descriptors import KernelMeanEmbeddingDelta  # v1
from tcdb_api.descriptors.kme_delta_v2 import KME_Delta    # v2

def test_kme_compatibility():
    """Ensure v1 and v2 produce same results."""
    data = np.random.randn(50, 3)
    
    # v1
    kme_v1 = KernelMeanEmbeddingDelta(sigma_scales=[1.0, 2.0])
    result_v1 = kme_v1.compute(data)
    
    # v2
    kme_v2 = KME_Delta(sigmas=(1.0, 2.0))
    result_v2 = kme_v2.compute(data)
    
    # Compare
    assert abs(result_v1['KME_delta_F'] - result_v2['KME_delta_F']) < 1e-10
```

## Recommendations

### 1. **Adopt Immediately**
- ✅ `from __future__ import annotations`
- ✅ Efficient `_pairwise_sq_dists`
- ✅ Graceful dependency fallbacks
- ✅ Cleaner utility functions

### 2. **Adopt Gradually**
- 🔄 Dataclass pattern for new descriptors
- 🔄 Simplified implementations
- 🔄 Better type hints

### 3. **Keep from Current**
- ✅ Comprehensive tests
- ✅ FastAPI integration
- ✅ Extensive documentation
- ✅ Advanced features (Lanczos, attention weights)

## Conclusion

Your production skeleton provides excellent patterns for:
1. **Code clarity** - Dataclasses, type hints, simple functions
2. **Robustness** - Graceful fallbacks, error handling
3. **Maintainability** - Focused implementations, clear separation

The current tcdb-core implementation excels at:
1. **Feature completeness** - All advanced features implemented
2. **Testing** - Comprehensive test coverage
3. **Integration** - Full API and documentation

**Best path forward:** Merge the strengths of both by:
- Adopting your clean patterns in new code
- Refactoring existing code gradually
- Maintaining backward compatibility during transition
- Keeping comprehensive tests and documentation

The enhanced `base_v2.py` and `kme_delta_v2.py` demonstrate this hybrid approach.

