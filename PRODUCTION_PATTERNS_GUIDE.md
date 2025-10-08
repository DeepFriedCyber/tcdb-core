# Production Patterns Guide

## Overview

This guide demonstrates how to use the production-ready patterns from the skeleton in your own descriptors.

## Pattern 1: Dataclass-Based Descriptors

### Before (Manual __init__)
```python
class MyDescriptor(Descriptor):
    def __init__(self, param1=10, param2=0.5, param3=None):
        super().__init__(param1=param1, param2=param2, param3=param3)
        self.param1 = param1
        self.param2 = param2
        self.param3 = param3 or [1.0, 2.0]
        self.name = "my_descriptor"
```

### After (Dataclass)
```python
from __future__ import annotations
from dataclasses import dataclass
from typing import Tuple, Optional

@dataclass
class MyDescriptor(Descriptor):
    """My descriptor with clean initialization."""
    param1: int = 10
    param2: float = 0.5
    param3: Optional[Tuple[float, ...]] = None
    name: str = "my_descriptor"
    
    def __post_init__(self):
        if self.param3 is None:
            # Use object.__setattr__ for frozen dataclasses
            object.__setattr__(self, 'param3', (1.0, 2.0))
```

**Benefits:**
- ✅ Less boilerplate
- ✅ Automatic type checking
- ✅ Better IDE support
- ✅ Immutable by default (add `frozen=True`)

## Pattern 2: Efficient Distance Computation

### Before (Using scipy.spatial.distance)
```python
from scipy.spatial.distance import cdist

def compute_distances(X, Y):
    return cdist(X, Y, metric='euclidean')
```

### After (Optimized matrix operations)
```python
def pairwise_sq_dists(X: np.ndarray, Y: np.ndarray) -> np.ndarray:
    """Efficient squared Euclidean distances."""
    X2 = (X * X).sum(axis=1)[:, None]
    Y2 = (Y * Y).sum(axis=1)[None, :]
    return X2 + Y2 - 2.0 * X @ Y.T
```

**Benefits:**
- ✅ ~2-3x faster
- ✅ Lower memory usage
- ✅ Returns squared distances (often what you need)

## Pattern 3: Graceful Dependency Handling

### Before (Hard requirement)
```python
import gudhi  # Crashes if not installed

def compute(self, X):
    rips = gudhi.RipsComplex(points=X)
    # ...
```

### After (Graceful fallback)
```python
try:
    import gudhi
    _HAS_GUDHI = True
except ImportError:
    _HAS_GUDHI = False

def compute(self, X, **kwargs) -> Dict[str, float]:
    if not _HAS_GUDHI:
        return {
            "TID_F": 0.0,
            "TID_has_backend": 0.0,
            "TID_error": "Gudhi not installed"
        }
    
    # Actual computation
    rips = gudhi.RipsComplex(points=X)
    # ...
```

**Benefits:**
- ✅ System remains stable
- ✅ Clear error reporting
- ✅ Allows partial functionality
- ✅ Better for CI/CD

## Pattern 4: Type Hints with Future Annotations

### Before (Verbose type hints)
```python
from typing import Dict, List, Optional, Union
import numpy as np

def compute(self, data: Union[np.ndarray, Dict[str, np.ndarray]], 
           weights: Optional[np.ndarray] = None) -> Dict[str, float]:
    pass
```

### After (Clean with future annotations)
```python
from __future__ import annotations
from typing import Optional
import numpy as np

def compute(self, data: np.ndarray | dict[str, np.ndarray],
           weights: Optional[np.ndarray] = None) -> dict[str, float]:
    pass
```

**Benefits:**
- ✅ Cleaner syntax
- ✅ Forward references work
- ✅ Better readability

## Pattern 5: Safe Division

### Before (Manual epsilon handling)
```python
def compute_ratio(numerator, denominator):
    if abs(denominator) < 1e-12:
        return 0.0
    return numerator / denominator
```

### After (Utility function)
```python
def safe_divide(numerator: float | np.ndarray,
               denominator: float | np.ndarray,
               epsilon: float = 1e-12,
               default: float = 0.0) -> float | np.ndarray:
    """Safe division with epsilon regularization."""
    denom = denominator + epsilon
    if isinstance(denom, np.ndarray):
        result = numerator / denom
        result[np.abs(denominator) < epsilon] = default
        return result
    else:
        return numerator / denom if abs(denominator) >= epsilon else default

# Usage
ratio = safe_divide(mmd2, ref_norm2, epsilon=1e-12)
```

**Benefits:**
- ✅ Handles both scalars and arrays
- ✅ Consistent behavior
- ✅ Configurable epsilon and default

## Pattern 6: Stochastic Trace Estimation

### Before (Full eigendecomposition)
```python
def heat_trace(L, t):
    eigenvalues = np.linalg.eigvalsh(L)  # O(n³)
    return np.sum(np.exp(-eigenvalues * t))
```

### After (Hutchinson estimator)
```python
import scipy.sparse.linalg as spla

def heat_trace_stochastic(L: sp.csr_matrix, t: float, 
                         n_probe: int = 16,
                         rng: Optional[np.random.Generator] = None) -> float:
    """
    Hutchinson trace estimator: Tr(f(L)) ≈ (1/m) Σ v_i^T f(L) v_i
    where v_i are random Rademacher vectors.
    """
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

**Benefits:**
- ✅ O(n) instead of O(n³)
- ✅ Works for large matrices
- ✅ Tunable accuracy (n_probe)

## Pattern 7: Normalized Laplacian

### Before (Manual computation)
```python
def normalized_laplacian(A):
    deg = np.array(A.sum(axis=1)).ravel()
    D_inv_sqrt = np.diag(1.0 / np.sqrt(deg))
    L = np.eye(A.shape[0]) - D_inv_sqrt @ A @ D_inv_sqrt
    return L
```

### After (Sparse-aware)
```python
import scipy.sparse as sp

def normalized_laplacian(A: sp.spmatrix) -> sp.csr_matrix:
    """Compute normalized Laplacian: L = I - D^{-1/2} A D^{-1/2}"""
    A = A.tocsr()
    deg = np.array(A.sum(axis=1)).ravel()
    deg[deg == 0.0] = 1.0  # Avoid division by zero
    D_inv_sqrt = sp.diags(1.0 / np.sqrt(deg))
    return sp.eye(A.shape[0], format="csr") - D_inv_sqrt @ A @ D_inv_sqrt
```

**Benefits:**
- ✅ Handles sparse matrices
- ✅ Avoids division by zero
- ✅ Memory efficient

## Pattern 8: Weight Normalization

### Before (Repeated code)
```python
if weights is None:
    weights = np.ones(n) / n
else:
    weights = weights / weights.sum()
```

### After (Utility function)
```python
def normalize_weights(weights: Optional[np.ndarray], n: int) -> np.ndarray:
    """Normalize weights to sum to 1, or create uniform weights."""
    if weights is None:
        return np.ones(n) / n
    else:
        weights = np.asarray(weights)
        return weights / weights.sum()

# Usage
sample_weights = normalize_weights(sample_weights, n)
ref_weights = normalize_weights(ref_weights, m)
```

**Benefits:**
- ✅ DRY (Don't Repeat Yourself)
- ✅ Consistent behavior
- ✅ Easy to test

## Pattern 9: Descriptor Registry

### Before (Manual management)
```python
descriptors = {
    'tid': TopologicalInformationDescriptor,
    'dgd': DiffusionGeometryDescriptor,
}

def get_descriptor(name, **kwargs):
    if name not in descriptors:
        raise ValueError(f"Unknown descriptor: {name}")
    return descriptors[name](**kwargs)
```

### After (Registry pattern)
```python
class DescriptorRegistry:
    def __init__(self):
        self._descriptors: dict[str, type[Descriptor]] = {}
    
    def register(self, name: str, descriptor_class: type[Descriptor]) -> None:
        self._descriptors[name] = descriptor_class
    
    def get(self, name: str, **kwargs) -> Descriptor:
        if name not in self._descriptors:
            raise KeyError(f"Descriptor '{name}' not found")
        return self._descriptors[name](**kwargs)
    
    def list(self) -> list[str]:
        return list(self._descriptors.keys())

# Global registry
registry = DescriptorRegistry()
registry.register('tid', TID)
registry.register('dgd', DGD)

# Usage
descriptor = registry.get('tid', max_dim=2)
```

**Benefits:**
- ✅ Centralized management
- ✅ Easy to extend
- ✅ Better error messages

## Pattern 10: Validation

### Before (Scattered checks)
```python
def compute(self, data):
    if not isinstance(data, np.ndarray):
        raise ValueError("Data must be numpy array")
    if data.ndim != 2:
        raise ValueError("Data must be 2D")
    if data.shape[0] < 2:
        raise ValueError("Need at least 2 points")
    # ... actual computation
```

### After (Centralized validation)
```python
def validate_data(data: np.ndarray,
                 min_points: int = 2,
                 min_features: int = 1,
                 allow_nan: bool = False) -> None:
    """Validate input data array."""
    if not isinstance(data, np.ndarray):
        raise ValueError(f"Data must be numpy array, got {type(data)}")
    
    if data.ndim != 2:
        raise ValueError(f"Data must be 2D array, got shape {data.shape}")
    
    n_points, n_features = data.shape
    
    if n_points < min_points:
        raise ValueError(f"Need at least {min_points} points, got {n_points}")
    
    if n_features < min_features:
        raise ValueError(f"Need at least {min_features} features, got {n_features}")
    
    if not allow_nan and np.any(np.isnan(data)):
        raise ValueError("Data contains NaN values")

# Usage
def compute(self, data, **kwargs):
    validate_data(data, min_points=3)
    # ... actual computation
```

**Benefits:**
- ✅ Consistent validation
- ✅ Better error messages
- ✅ Reusable across descriptors

## Complete Example: New Descriptor

Here's a complete example using all patterns:

```python
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple
import numpy as np
import scipy.sparse as sp

from .base_v2 import (
    Descriptor,
    validate_data,
    safe_divide,
    normalize_weights,
)

try:
    import special_library
    _HAS_SPECIAL = True
except ImportError:
    _HAS_SPECIAL = False


@dataclass
class MyNewDescriptor(Descriptor):
    """
    My new descriptor with production-ready patterns.
    
    Attributes:
        scales: Tuple of scale parameters
        n_samples: Number of samples for estimation
        eps: Regularization epsilon
        name: Descriptor name
    """
    scales: Tuple[float, ...] = (0.5, 1.0, 2.0)
    n_samples: int = 20
    eps: float = 1e-12
    name: str = "my_descriptor"
    
    def compute(self, X: np.ndarray | dict,
               weights: Optional[np.ndarray] = None,
               **kwargs) -> dict[str, float]:
        """
        Compute descriptor features.
        
        Args:
            X: Point cloud (n, d) or dict with 'data' key
            weights: Optional sample weights
            **kwargs: Additional parameters
            
        Returns:
            Dictionary of dimensionless features
        """
        # Handle dict input
        if isinstance(X, dict):
            X_data = X.get('data')
            weights = X.get('weights', weights)
        else:
            X_data = X
        
        # Validate
        validate_data(X_data, min_points=2)
        
        # Check optional dependency
        if not _HAS_SPECIAL:
            return {
                f"{self.name}_F": 0.0,
                f"{self.name}_has_backend": 0.0,
            }
        
        n = X_data.shape[0]
        weights = normalize_weights(weights, n)
        
        # Compute features at each scale
        features = {}
        scale_values = []
        
        for scale in self.scales:
            # Your computation here
            value = self._compute_at_scale(X_data, scale, weights)
            features[f"{self.name}_scale_{scale:g}"] = float(value)
            scale_values.append(value)
        
        # Combined descriptor (dimensionless)
        total = sum(scale_values)
        ref_value = scale_values[0] if scale_values else 1.0
        F = safe_divide(total, ref_value, epsilon=self.eps)
        
        features[f"{self.name}_F"] = float(F)
        features[f"{self.name}_mean"] = float(np.mean(scale_values))
        
        return features
    
    def _compute_at_scale(self, X: np.ndarray, scale: float,
                         weights: np.ndarray) -> float:
        """Compute feature at a specific scale."""
        # Your scale-specific computation
        return 1.0  # Placeholder
```

## Summary

These patterns provide:
- ✅ **Cleaner code** with dataclasses and type hints
- ✅ **Better performance** with optimized algorithms
- ✅ **More robust** with graceful fallbacks
- ✅ **Easier to maintain** with reusable utilities
- ✅ **Production-ready** with proper validation

Adopt them gradually in new code while maintaining backward compatibility with existing implementations.

