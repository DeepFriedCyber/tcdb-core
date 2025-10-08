"""
FastAPI application for TCDB API
"""

from fastapi import FastAPI, Request, status, Depends
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse, HTMLResponse
from fastapi.exceptions import RequestValidationError
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from slowapi import Limiter, _rate_limit_exceeded_handler
from slowapi.util import get_remote_address
from slowapi.errors import RateLimitExceeded
from sqlalchemy.orm import Session
import os

from .models import RootResponse, ErrorResponse
from .routers import health, pipeline, tda, certificate, reasoner, eval, auth, keys, descriptors, descriptors_simple
from .database import init_db, get_db, User
from .routers.auth import get_current_user_from_cookie


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

    # Initialize database
    init_db()

    # Get base directory
    import pathlib
    base_dir = pathlib.Path(__file__).parent

    # Mount static files
    app.mount("/static", StaticFiles(directory=str(base_dir / "static")), name="static")

    # Templates
    templates = Jinja2Templates(directory=str(base_dir / "templates"))

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
    app.include_router(auth.router)  # Auth routes (login, signup)
    app.include_router(keys.router)  # API key management
    app.include_router(health.router)
    app.include_router(pipeline.router)
    app.include_router(tda.router)
    app.include_router(certificate.router)
    app.include_router(reasoner.router)
    app.include_router(eval.router)
    app.include_router(descriptors.router)  # Descriptor computation (detailed API)
    app.include_router(descriptors_simple.router)  # Descriptor computation (simple unified API)

    # Homepage
    @app.get("/", response_class=HTMLResponse, tags=["pages"])
    async def homepage(request: Request, db: Session = Depends(get_db)):
        """Render homepage"""
        user = get_current_user_from_cookie(request, db)
        return templates.TemplateResponse("index.html", {"request": request, "user": user})

    # Dashboard
    @app.get("/dashboard", response_class=HTMLResponse, tags=["pages"])
    async def dashboard(request: Request, db: Session = Depends(get_db)):
        """Render dashboard (requires login)"""
        user = get_current_user_from_cookie(request, db)
        if not user:
            return templates.TemplateResponse("login.html", {"request": request})
        return templates.TemplateResponse("dashboard.html", {"request": request, "user": user})

    # API root endpoint (JSON)
    @app.get("/api", response_model=RootResponse, tags=["root"])
    async def api_root():
        """API root endpoint with information"""
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

