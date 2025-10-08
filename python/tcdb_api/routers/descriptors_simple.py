"""
Simple unified descriptor API following production skeleton pattern.

This router provides a single endpoint that handles all descriptor types
with flexible payload formats. Complements the detailed API in descriptors.py.
"""

from __future__ import annotations

from typing import Optional
from fastapi import APIRouter, HTTPException
from pydantic import BaseModel, Field
import numpy as np
import scipy.sparse as sp

from ..descriptors.kme_delta_v2 import KME_Delta
from ..descriptors.dgd import DiffusionGeometryDescriptor as DGD
from ..descriptors.tid import TopologicalInformationDescriptor as TID
from ..descriptors.gser import GraphScatteringEnergyRatio as GSER

router = APIRouter(prefix="/descriptor", tags=["descriptors-simple"])

# Simple registry mapping names to descriptor classes
REGISTRY = {
    "kme_delta": KME_Delta,
    "dgd": DGD,
    "tid": TID,
    "gser": GSER,
}


class ComputeRequest(BaseModel):
    """
    Unified compute request for all descriptors.
    
    Different descriptors use different fields:
    - kme_delta: X, X_ref (optional)
    - dgd: adj_indices, adj_data, n_nodes
    - tid: X
    - gser: adj_indices, adj_data, n_nodes, signal
    """
    
    name: str = Field(..., description="Descriptor name (kme_delta, dgd, tid, gser)")
    params: dict = Field(default_factory=dict, description="Descriptor parameters")
    
    # Point cloud data (for KME-Δ, TID)
    X: Optional[list[list[float]]] = Field(None, description="Point cloud or embeddings (n x d)")
    X_ref: Optional[list[list[float]]] = Field(None, description="Reference point cloud (optional)")
    
    # Sparse graph data (for DGD, GSER)
    adj_indices: Optional[list[tuple[int, int]]] = Field(None, description="Graph edges as (i, j) pairs")
    adj_data: Optional[list[float]] = Field(None, description="Edge weights")
    n_nodes: Optional[int] = Field(None, description="Number of nodes in graph")
    
    # Node signal (for GSER)
    signal: Optional[list[float]] = Field(None, description="Node signal for GSER")
    
    class Config:
        json_schema_extra = {
            "example": {
                "name": "kme_delta",
                "params": {"sigmas": [0.5, 1.0, 2.0]},
                "X": [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]],
                "X_ref": [[2.0, 2.0], [3.0, 3.0]]
            }
        }


@router.get("/list")
def list_descriptors() -> dict[str, list[str]]:
    """
    List available descriptors.
    
    Returns:
        Dictionary with list of descriptor names
    """
    return {
        "descriptors": list(REGISTRY.keys()),
        "count": len(REGISTRY)
    }


@router.post("/compute")
def compute(req: ComputeRequest) -> dict[str, float]:
    """
    Unified descriptor computation endpoint.
    
    Accepts different payload formats depending on descriptor type:
    
    **KME-Δ (kme_delta)**:
    - Requires: X
    - Optional: X_ref
    - Params: sigmas, eps
    
    **DGD (dgd)**:
    - Requires: adj_indices, adj_data, n_nodes
    - Params: n_times, t_min, t_max, probes
    
    **TID (tid)**:
    - Requires: X
    - Params: max_dim
    
    **GSER (gser)**:
    - Requires: adj_indices, adj_data, n_nodes, signal
    - Params: scales
    
    Args:
        req: Compute request with descriptor-specific payload
        
    Returns:
        Dictionary of dimensionless scalar features
        
    Raises:
        HTTPException: If descriptor unknown or computation fails
    """
    # Validate descriptor name
    if req.name not in REGISTRY:
        raise HTTPException(
            status_code=400,
            detail=f"Unknown descriptor '{req.name}'. Available: {list(REGISTRY.keys())}"
        )
    
    # Instantiate descriptor with parameters
    try:
        desc = REGISTRY[req.name](**req.params)
    except Exception as e:
        raise HTTPException(
            status_code=400,
            detail=f"Invalid parameters for {req.name}: {str(e)}"
        )
    
    # Compute based on descriptor type
    try:
        if req.name == "kme_delta":
            return _compute_kme_delta(desc, req)
        elif req.name == "dgd":
            return _compute_dgd(desc, req)
        elif req.name == "tid":
            return _compute_tid(desc, req)
        elif req.name == "gser":
            return _compute_gser(desc, req)
        else:
            raise HTTPException(
                status_code=500,
                detail=f"Handler not implemented for {req.name}"
            )
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(
            status_code=500,
            detail=f"Computation failed: {str(e)}"
        )


def _compute_kme_delta(desc: KME_Delta, req: ComputeRequest) -> dict[str, float]:
    """Compute KME-Δ descriptor."""
    if req.X is None:
        raise HTTPException(400, "KME-Δ requires 'X' (point cloud)")
    
    X = np.array(req.X, dtype=float)
    X_ref = None if req.X_ref is None else np.array(req.X_ref, dtype=float)
    
    return desc.compute(X=X, X_ref=X_ref)


def _compute_dgd(desc: DGD, req: ComputeRequest) -> dict[str, float]:
    """Compute DGD descriptor."""
    if req.n_nodes is None or req.adj_indices is None or req.adj_data is None:
        raise HTTPException(400, "DGD requires 'n_nodes', 'adj_indices', and 'adj_data'")
    
    # Build sparse adjacency matrix from COO format
    A = sp.csr_matrix(
        (req.adj_data, zip(*req.adj_indices)),
        shape=(req.n_nodes, req.n_nodes)
    )
    
    return desc.compute(A)


def _compute_tid(desc: TID, req: ComputeRequest) -> dict[str, float]:
    """Compute TID descriptor."""
    if req.X is None:
        raise HTTPException(400, "TID requires 'X' (point cloud)")
    
    X = np.array(req.X, dtype=float)
    
    return desc.compute(X)


def _compute_gser(desc: GSER, req: ComputeRequest) -> dict[str, float]:
    """Compute GSER descriptor."""
    if req.n_nodes is None or req.adj_indices is None or req.adj_data is None:
        raise HTTPException(400, "GSER requires 'n_nodes', 'adj_indices', and 'adj_data'")
    
    if req.signal is None:
        raise HTTPException(400, "GSER requires 'signal' (node signal)")
    
    # Build sparse adjacency matrix
    A = sp.csr_matrix(
        (req.adj_data, zip(*req.adj_indices)),
        shape=(req.n_nodes, req.n_nodes)
    )
    
    # Convert signal to array
    x = np.array(req.signal, dtype=float)
    
    if len(x) != req.n_nodes:
        raise HTTPException(
            400,
            f"Signal length ({len(x)}) must match n_nodes ({req.n_nodes})"
        )
    
    return desc.compute(A, x)


@router.get("/health")
def health_check() -> dict:
    """Simple health check endpoint."""
    return {
        "status": "healthy",
        "service": "descriptor-api-simple",
        "descriptors_available": len(REGISTRY)
    }

