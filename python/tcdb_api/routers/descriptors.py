"""
Descriptor computation endpoints

Provides REST API for computing topological descriptors:
- TID (Topological-Information Descriptor)
- DGD (Diffusion-Geometry Descriptor)
- KME-Δ (Kernel Mean Embedding Divergence)
- GSER (Graph-Scattering Energy Ratio)
"""

from fastapi import APIRouter, HTTPException, status
from pydantic import BaseModel, Field
from typing import List, Optional, Dict, Any
import numpy as np

from ..descriptors import (
    TopologicalInformationDescriptor,
    DiffusionGeometryDescriptor,
    KernelMeanEmbeddingDelta,
    GraphScatteringEnergyRatio,
    DescriptorRegistry
)
from ..config import get_default_config

router = APIRouter(prefix="/api/v1/descriptors", tags=["descriptors"])

# Initialize registry
registry = DescriptorRegistry()
registry.register('tid', TopologicalInformationDescriptor)
registry.register('dgd', DiffusionGeometryDescriptor)
registry.register('kme_delta', KernelMeanEmbeddingDelta)
registry.register('gser', GraphScatteringEnergyRatio)


# Request/Response Models

class DescriptorRequest(BaseModel):
    """Request model for descriptor computation"""
    data: List[List[float]] = Field(
        ...,
        description="Point cloud data as 2D array",
        example=[[0.0, 0.0], [1.0, 0.0], [0.0, 1.0], [1.0, 1.0]]
    )
    descriptor_type: str = Field(
        ...,
        description="Type of descriptor to compute",
        example="tid"
    )
    parameters: Optional[Dict[str, Any]] = Field(
        None,
        description="Optional descriptor-specific parameters"
    )


class DescriptorResponse(BaseModel):
    """Response model for descriptor computation"""
    descriptor_type: str
    features: Dict[str, float]
    metadata: Dict[str, Any]


class BatchDescriptorRequest(BaseModel):
    """Request model for batch descriptor computation"""
    data: List[List[float]]
    descriptor_types: List[str] = Field(
        ...,
        description="List of descriptor types to compute",
        example=["tid", "dgd"]
    )
    parameters: Optional[Dict[str, Dict[str, Any]]] = Field(
        None,
        description="Parameters per descriptor type"
    )


class BatchDescriptorResponse(BaseModel):
    """Response model for batch descriptor computation"""
    results: Dict[str, Dict[str, float]]
    metadata: Dict[str, Any]


class DescriptorListResponse(BaseModel):
    """Response model for listing available descriptors"""
    descriptors: List[Dict[str, str]]


# Endpoints

@router.get(
    "/list",
    response_model=DescriptorListResponse,
    summary="List available descriptors",
    description="Get a list of all available descriptor types"
)
async def list_descriptors():
    """
    List all available descriptor types.
    
    Returns information about each descriptor including:
    - Name and identifier
    - Description
    - Key features
    """
    descriptors = [
        {
            "name": "tid",
            "full_name": "Topological-Information Descriptor",
            "description": "Combines persistence entropy, Betti curve total variation, and landscape ratios",
            "features": "Dimensionless topological features using information theory"
        },
        {
            "name": "dgd",
            "full_name": "Diffusion-Geometry Descriptor",
            "description": "Heat diffusion on graphs with multiscale analysis",
            "features": "Spectral geometry and diffusion-based features"
        },
        {
            "name": "kme_delta",
            "full_name": "Kernel Mean Embedding Divergence",
            "description": "RKHS-based distributional comparison",
            "features": "Multi-scale kernel divergence from reference distribution"
        },
        {
            "name": "gser",
            "full_name": "Graph-Scattering Energy Ratio",
            "description": "Graph wavelet scattering transform",
            "features": "Multiscale signal processing on graphs"
        }
    ]
    
    return DescriptorListResponse(descriptors=descriptors)


@router.post(
    "/compute",
    response_model=DescriptorResponse,
    summary="Compute descriptor",
    description="Compute a single descriptor from point cloud data"
)
async def compute_descriptor(request: DescriptorRequest):
    """
    Compute a descriptor from point cloud data.
    
    **Supported descriptor types:**
    - `tid`: Topological-Information Descriptor
    - `dgd`: Diffusion-Geometry Descriptor
    - `kme_delta`: Kernel Mean Embedding Divergence
    - `gser`: Graph-Scattering Energy Ratio
    
    **Example:**
    ```json
    {
        "data": [[0.0, 0.0], [1.0, 0.0], [0.0, 1.0], [1.0, 1.0]],
        "descriptor_type": "tid",
        "parameters": {"max_dimension": 2}
    }
    ```
    """
    try:
        # Convert data to numpy array
        data = np.array(request.data)
        
        # Validate data
        if len(data) < 3:
            raise HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail="Need at least 3 points"
            )
        
        # Get configuration
        config = get_default_config()
        descriptor_config = config.get(request.descriptor_type)
        
        # Override with request parameters
        if request.parameters:
            descriptor_config.update(request.parameters)
        
        # Create descriptor
        descriptor = registry.get(request.descriptor_type, **descriptor_config)
        
        # Compute features
        features = descriptor.compute(data)
        
        # Build response
        return DescriptorResponse(
            descriptor_type=request.descriptor_type,
            features=features,
            metadata={
                "n_points": len(data),
                "n_features": data.shape[1] if data.ndim > 1 else 1,
                "descriptor_name": descriptor.name,
                "parameters": descriptor_config
            }
        )
        
    except KeyError as e:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail=f"Unknown descriptor type: {request.descriptor_type}. Use /list to see available types."
        )
    except ValueError as e:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail=str(e)
        )
    except Exception as e:
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail=f"Error computing descriptor: {str(e)}"
        )


@router.post(
    "/compute/batch",
    response_model=BatchDescriptorResponse,
    summary="Compute multiple descriptors",
    description="Compute multiple descriptors from the same point cloud data"
)
async def compute_batch_descriptors(request: BatchDescriptorRequest):
    """
    Compute multiple descriptors from the same data.
    
    This is more efficient than making separate requests when you need
    multiple descriptor types for the same point cloud.
    
    **Example:**
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
    """
    try:
        # Convert data to numpy array
        data = np.array(request.data)
        
        # Validate data
        if len(data) < 3:
            raise HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail="Need at least 3 points"
            )
        
        # Get configuration
        config = get_default_config()
        
        # Compute each descriptor
        results = {}
        
        for desc_type in request.descriptor_types:
            # Get config for this descriptor
            descriptor_config = config.get(desc_type)
            
            # Override with request parameters
            if request.parameters and desc_type in request.parameters:
                descriptor_config.update(request.parameters[desc_type])
            
            # Create and compute
            descriptor = registry.get(desc_type, **descriptor_config)
            features = descriptor.compute(data)
            
            results[desc_type] = features
        
        # Build response
        return BatchDescriptorResponse(
            results=results,
            metadata={
                "n_points": len(data),
                "n_features": data.shape[1] if data.ndim > 1 else 1,
                "descriptor_types": request.descriptor_types
            }
        )
        
    except KeyError as e:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail=f"Unknown descriptor type. Use /list to see available types."
        )
    except ValueError as e:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail=str(e)
        )
    except Exception as e:
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail=f"Error computing descriptors: {str(e)}"
        )


@router.get(
    "/config/{descriptor_type}",
    summary="Get descriptor configuration",
    description="Get default configuration for a descriptor type"
)
async def get_descriptor_config(descriptor_type: str):
    """
    Get the default configuration for a descriptor type.
    
    Useful for understanding what parameters are available.
    """
    try:
        config = get_default_config()
        descriptor_config = config.get(descriptor_type)
        
        return {
            "descriptor_type": descriptor_type,
            "configuration": descriptor_config
        }
    except KeyError:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail=f"Unknown descriptor type: {descriptor_type}"
        )

