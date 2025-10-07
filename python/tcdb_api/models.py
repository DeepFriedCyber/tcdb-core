"""
Pydantic models for request/response validation
"""

from pydantic import BaseModel, Field, field_validator
from typing import Optional, List, Dict, Any
import math


class SimplexRequest(BaseModel):
    """Request model for creating a simplex"""
    vertices: List[int] = Field(..., description="List of vertex indices", min_length=1)


class SimplexResponse(BaseModel):
    """Response model for simplex creation"""
    vertices: List[int]
    dimension: int


class ComplexRequest(BaseModel):
    """Request model for creating a simplicial complex"""
    simplices: List[List[int]] = Field(..., description="List of simplices (each is a list of vertices)", min_length=1)


class ComplexResponse(BaseModel):
    """Response model for complex creation"""
    dimension: int
    euler_characteristic: int
    closure_verified: bool


class RipsRequest(BaseModel):
    """Request model for Rips complex computation"""
    points: List[List[float]] = Field(..., description="Point cloud data (2D array)", min_length=1)
    max_edge_length: float = Field(1.0, gt=0, description="Maximum edge length for Rips complex")
    max_dimension: int = Field(2, ge=0, le=10, description="Maximum dimension to compute")

    @field_validator('points')
    @classmethod
    def validate_points(cls, v):
        if not v:
            raise ValueError("Points cannot be empty")
        
        # Check all points have same dimension
        dim = len(v[0])
        if not all(len(p) == dim for p in v):
            raise ValueError("All points must have the same dimension")
        
        # Check for NaN or inf
        for point in v:
            for coord in point:
                if math.isnan(coord) or math.isinf(coord):
                    raise ValueError("Points cannot contain NaN or infinity")
        
        return v


class RipsResponse(BaseModel):
    """Response model for Rips complex computation"""
    dimension: int
    euler_characteristic: int
    num_vertices: int
    num_edges: int
    max_edge_length: float
    verified: bool


class PersistenceRequest(BaseModel):
    """Request model for persistence computation"""
    complex: Dict[str, Any] = Field(..., description="Simplicial complex data")
    filtration: Dict[str, Any] = Field(..., description="Filtration values")


class PersistenceDiagram(BaseModel):
    """Persistence diagram for a single dimension"""
    dimension: int
    points: List[Dict[str, float]]


class PersistenceResponse(BaseModel):
    """Response model for persistence computation"""
    diagrams: List[PersistenceDiagram]
    betti_numbers: List[int]
    verified: bool


class PipelineRequest(BaseModel):
    """Request model for running a complete TDA pipeline"""
    data: List[List[float]] = Field(..., description="Point cloud data (2D array)", min_length=1)
    max_dimension: int = Field(2, ge=0, le=10, description="Maximum dimension to compute")
    max_edge_length: float = Field(1.0, gt=0, description="Maximum edge length for Rips complex")

    @field_validator('data')
    @classmethod
    def validate_data(cls, v):
        if not v:
            raise ValueError("Data cannot be empty")
        
        # Check all points have same dimension
        dim = len(v[0])
        if not all(len(p) == dim for p in v):
            raise ValueError("All points must have the same dimension")
        
        # Check for NaN or inf
        for point in v:
            for coord in point:
                if math.isnan(coord) or math.isinf(coord):
                    raise ValueError("Data cannot contain NaN or infinity")
        
        return v


class PipelineResults(BaseModel):
    """Results from pipeline computation"""
    euler_characteristic: int
    dimension: int
    num_vertices: int
    max_edge_length: float


class PipelineMetadata(BaseModel):
    """Metadata about pipeline execution"""
    backend: str = "rust"
    verified: bool = True


class PipelineResponse(BaseModel):
    """Response model for pipeline execution"""
    job_id: str
    status: str
    results: PipelineResults
    metadata: PipelineMetadata


class JobStatus(BaseModel):
    """Job status information"""
    status: str
    created_at: Optional[float] = None
    completed_at: Optional[float] = None
    progress: Optional[int] = None
    result: Optional[PipelineResponse] = None


class JobListResponse(BaseModel):
    """Response model for listing jobs"""
    jobs: List[Dict[str, Any]]


class HealthResponse(BaseModel):
    """Health check response"""
    status: str
    rust_available: bool
    python_version: str
    components: Dict[str, str]


class RustHealthResponse(BaseModel):
    """Rust-specific health check response"""
    status: str
    rust_version: Optional[str] = None
    test_results: Optional[Dict[str, bool]] = None
    error: Optional[str] = None
    message: Optional[str] = None


class ErrorResponse(BaseModel):
    """Error response model"""
    error: str
    message: Optional[str] = None
    detail: Optional[Any] = None


class RootResponse(BaseModel):
    """Root endpoint response"""
    name: str
    version: str
    status: str
    rust_available: bool
    docs_url: str = "/docs"
    redoc_url: str = "/redoc"


# Certificate/Provenance Models

class CertificateRequest(BaseModel):
    """Request model for certificate generation"""
    data_cid: str = Field(..., description="Content identifier for input data")
    code_rev: str = Field(..., description="Code version or git commit")
    pd: List[List[float]] = Field(..., description="Persistence diagram as list of [birth, death] pairs")


class CertificateResponse(BaseModel):
    """Response model for certificate generation"""
    data_cid: str
    code_rev: str
    result_hash: str
    audit_token: str


# Reasoner/Constraint Models

class ReasonerRequest(BaseModel):
    """Request model for constraint checking"""
    constraints: List[str] = Field(..., description="List of constraint names to check")
    pd: List[List[float]] = Field(..., description="Persistence diagram to validate")
    betti: Optional[Dict[str, Any]] = Field(None, description="Betti curve data (optional)")


class ViolationDetail(BaseModel):
    """Details of a constraint violation"""
    constraint: str
    detail: str
    severity: str = "medium"


class ReasonerResponse(BaseModel):
    """Response model for constraint checking"""
    ok: bool
    violations: List[ViolationDetail] = []
    checked_constraints: List[str]


# Evaluation/Hallucination Detection Models

class EvalClaim(BaseModel):
    """A single claim to verify"""
    text: str
    confidence: Optional[float] = None


class EvalItem(BaseModel):
    """A single item to evaluate"""
    id: str
    question: str
    answer_text: str
    claims: List[str] = []
    citations: List[str] = []
    pd: Optional[List[List[float]]] = None
    constraints: Optional[List[str]] = None
    data_cid: Optional[str] = None
    code_rev: Optional[str] = None


class EvalItemResult(BaseModel):
    """Result for a single evaluation item"""
    id: str
    hallucinated: bool
    supported: bool
    violations: List[str] = []
    confidence_score: Optional[float] = None


class EvalSummary(BaseModel):
    """Summary of evaluation results"""
    total_items: int
    hallucinated_count: int
    supported_count: int
    accuracy: float


class EvalRequest(BaseModel):
    """Request model for evaluation"""
    items: List[EvalItem]
    require_tcdb: bool = False


class EvalResponse(BaseModel):
    """Response model for evaluation"""
    items: List[EvalItemResult]
    summary: EvalSummary

