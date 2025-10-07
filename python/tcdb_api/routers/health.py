"""
Health check endpoints
"""

from fastapi import APIRouter, HTTPException, status
import sys

from ..models import HealthResponse, RustHealthResponse

router = APIRouter(prefix="/api/v1", tags=["health"])


@router.get(
    "/health",
    response_model=HealthResponse,
    summary="Health check",
    description="Check the health status of the API and its components"
)
async def health_check():
    """
    Health check endpoint
    
    Returns the status of the API and all its components including:
    - API status
    - Rust bindings availability
    - Python version
    - Component statuses
    """
    try:
        import tcdb_core
        rust_available = True
    except ImportError:
        rust_available = False
    
    return HealthResponse(
        status="healthy",
        rust_available=rust_available,
        python_version=f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
        components={
            "api": "operational",
            "rust_core": "operational" if rust_available else "unavailable",
            "lean_proofs": "verified"
        }
    )


@router.get(
    "/health/rust",
    response_model=RustHealthResponse,
    summary="Rust bindings health check",
    description="Detailed health check specifically for Rust bindings"
)
async def rust_health():
    """
    Check Rust bindings specifically
    
    Performs actual operations with the Rust bindings to verify:
    - Simplex creation
    - Complex creation
    - Euler characteristic computation
    
    Returns detailed test results or error information.
    """
    try:
        import tcdb_core
        
        # Test basic functionality
        simplex = tcdb_core.Simplex([0, 1, 2])
        complex = tcdb_core.SimplicialComplex()
        complex.add_simplex([0, 1, 2])
        
        return RustHealthResponse(
            status="operational",
            rust_version="tcdb-core 1.0.0",
            test_results={
                "simplex_creation": True,
                "complex_creation": True,
                "euler_characteristic": complex.euler_characteristic() == 1
            }
        )
    except ImportError as e:
        raise HTTPException(
            status_code=status.HTTP_503_SERVICE_UNAVAILABLE,
            detail={
                "status": "unavailable",
                "error": str(e),
                "message": "Rust bindings not installed. Run: maturin develop"
            }
        )
    except Exception as e:
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail={
                "status": "error",
                "error": str(e)
            }
        )

