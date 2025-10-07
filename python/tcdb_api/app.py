"""
FastAPI application for TCDB API
"""

from fastapi import FastAPI, Request, status
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse
from fastapi.exceptions import RequestValidationError
from slowapi import Limiter, _rate_limit_exceeded_handler
from slowapi.util import get_remote_address
from slowapi.errors import RateLimitExceeded
import os

from .models import RootResponse, ErrorResponse
from .routers import health, pipeline, tda, certificate, reasoner, eval


def create_app() -> FastAPI:
    """Create and configure the FastAPI application"""

    app = FastAPI(
        title="TCDB Core API",
        description="Topological Computation Database - High-performance topological data analysis",
        version="1.0.0",
        docs_url="/docs",
        redoc_url="/redoc",
        openapi_url="/openapi.json"
    )

    # CORS middleware
    app.add_middleware(
        CORSMiddleware,
        allow_origins=["*"],  # Configure appropriately for production
        allow_credentials=True,
        allow_methods=["*"],
        allow_headers=["*"],
    )

    # Rate limiting
    limiter = Limiter(key_func=get_remote_address)
    app.state.limiter = limiter
    app.add_exception_handler(RateLimitExceeded, _rate_limit_exceeded_handler)

    # Include routers
    app.include_router(health.router)
    app.include_router(pipeline.router)
    app.include_router(tda.router)
    app.include_router(certificate.router)
    app.include_router(reasoner.router)
    app.include_router(eval.router)

    # Root endpoint
    @app.get("/", response_model=RootResponse, tags=["root"])
    async def root():
        """Root endpoint with API information"""
        try:
            import tcdb_core
            rust_available = True
        except ImportError:
            rust_available = False

        return RootResponse(
            name="TCDB Core API",
            version="1.0.0",
            status="operational",
            rust_available=rust_available,
            docs_url="/docs",
            redoc_url="/redoc"
        )

    # Exception handlers
    @app.exception_handler(RequestValidationError)
    async def validation_exception_handler(request: Request, exc: RequestValidationError):
        """Handle validation errors"""
        return JSONResponse(
            status_code=status.HTTP_422_UNPROCESSABLE_ENTITY,
            content={
                "error": "Validation error",
                "detail": exc.errors()
            }
        )

    @app.exception_handler(404)
    async def not_found_handler(request: Request, exc):
        """Handle 404 errors"""
        return JSONResponse(
            status_code=status.HTTP_404_NOT_FOUND,
            content={"error": "Not found"}
        )

    @app.exception_handler(500)
    async def internal_error_handler(request: Request, exc):
        """Handle 500 errors"""
        return JSONResponse(
            status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
            content={"error": "Internal server error"}
        )

    return app


# Create app instance
app = create_app()

