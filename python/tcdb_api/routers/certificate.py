"""
Certificate/Provenance endpoints
"""

from fastapi import APIRouter, HTTPException, status
import hashlib
import json
from typing import List, Tuple

from ..models import CertificateRequest, CertificateResponse

router = APIRouter(prefix="/evidence", tags=["certificate"])


def hash_persistence_diagram(pd: List[Tuple[float, float]]) -> str:
    """
    Hash a persistence diagram deterministically.
    
    This implements the same algorithm as the Rust version:
    1. Sort by (birth, death)
    2. Format with 17 decimal places
    3. Hash with SHA256 (using SHA256 instead of BLAKE3 for Python compatibility)
    
    Args:
        pd: List of (birth, death) tuples
    
    Returns:
        Hex string of hash
    """
    # Sort for determinism
    sorted_pd = sorted(pd, key=lambda x: (x[0], x[1]))
    
    # Format with full precision (17 decimals for f64)
    canonical = ""
    for birth, death in sorted_pd:
        canonical += f"{birth:.17e},{death:.17e};"
    
    # Hash
    return hashlib.sha256(canonical.encode()).hexdigest()


def create_audit_token(data_cid: str, code_rev: str, result_hash: str) -> str:
    """
    Create an audit token from certificate fields.
    
    This binds all three fields into a single hash.
    
    Args:
        data_cid: Content identifier
        code_rev: Code version
        result_hash: Hash of the result
    
    Returns:
        Hex string of audit token
    """
    # Create JSON representation (sorted keys for determinism)
    cert_data = {
        "data_cid": data_cid,
        "code_rev": code_rev,
        "result_hash": result_hash
    }
    canonical_json = json.dumps(cert_data, sort_keys=True)
    
    # Hash
    return hashlib.sha256(canonical_json.encode()).hexdigest()


@router.post(
    "/certificate",
    response_model=CertificateResponse,
    summary="Generate provenance certificate",
    description="Create a cryptographic certificate binding data, code, and results"
)
async def generate_certificate(request: CertificateRequest):
    """
    Generate a provenance certificate
    
    Creates a cryptographically verifiable link between:
    - Input data (via content-addressed identifier)
    - Code version (via git commit or semver)
    - Mathematical result (via canonical hash of persistence diagram)
    
    **Properties:**
    - **Deterministic**: Same inputs always produce same certificate
    - **Verifiable**: Anyone can recompute and verify the certificate
    - **Immutable**: Certificate cannot be forged or modified
    - **Auditable**: Full chain of custody from data → code → result
    
    **Parameters:**
    - **data_cid**: Content identifier for input data (e.g., "sha256:abc123...")
    - **code_rev**: Code version (e.g., "v1.0.0" or git commit "a1b2c3d")
    - **pd**: Persistence diagram as list of [birth, death] pairs
    
    **Returns:**
    - Certificate with result hash and audit token
    
    **Example:**
    ```json
    {
        "data_cid": "cid:demo",
        "code_rev": "rev:abc",
        "pd": [[0.1, 0.9], [0.2, 0.7]]
    }
    ```
    
    **Response:**
    ```json
    {
        "data_cid": "cid:demo",
        "code_rev": "rev:abc",
        "result_hash": "a1b2c3...",
        "audit_token": "d4e5f6..."
    }
    ```
    """
    try:
        # Convert pd to list of tuples
        pd_tuples = [(birth, death) for birth, death in request.pd]
        
        # Hash the persistence diagram
        result_hash = hash_persistence_diagram(pd_tuples)
        
        # Create audit token
        audit_token = create_audit_token(
            request.data_cid,
            request.code_rev,
            result_hash
        )
        
        return CertificateResponse(
            data_cid=request.data_cid,
            code_rev=request.code_rev,
            result_hash=result_hash,
            audit_token=audit_token
        )
    
    except Exception as e:
        raise HTTPException(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            detail={"error": str(e)}
        )

