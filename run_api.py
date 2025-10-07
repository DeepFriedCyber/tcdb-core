#!/usr/bin/env python3
"""
FastAPI server runner for TCDB Core API

Usage:
    python run_api.py              # Development mode with auto-reload
    python run_api.py --prod       # Production mode
    python run_api.py --port 3000  # Custom port
"""

import sys
import os
import argparse


def main():
    parser = argparse.ArgumentParser(description="Run TCDB FastAPI server")
    parser.add_argument(
        "--prod",
        action="store_true",
        help="Run in production mode (no auto-reload, multiple workers)"
    )
    parser.add_argument(
        "--port",
        type=int,
        default=8000,
        help="Port to run the server on (default: 8000)"
    )
    parser.add_argument(
        "--host",
        type=str,
        default="0.0.0.0",
        help="Host to bind to (default: 0.0.0.0)"
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=4,
        help="Number of worker processes in production mode (default: 4)"
    )
    
    args = parser.parse_args()
    
    # Print banner
    print("=" * 70)
    print("🚀 TCDB Core API - FastAPI Server")
    print("=" * 70)
    
    if args.prod:
        print("Mode: Production")
        print(f"Workers: {args.workers}")
    else:
        print("Mode: Development (auto-reload enabled)")
    
    print(f"Host: {args.host}")
    print(f"Port: {args.port}")
    print("-" * 70)
    print(f"📚 API Documentation: http://localhost:{args.port}/docs")
    print(f"📖 ReDoc: http://localhost:{args.port}/redoc")
    print(f"🏥 Health Check: http://localhost:{args.port}/api/v1/health")
    print("=" * 70)
    print()
    
    # Import uvicorn
    try:
        import uvicorn
    except ImportError:
        print("❌ Error: uvicorn not installed")
        print("Install with: pip install uvicorn[standard]")
        sys.exit(1)
    
    # Change to python directory for module imports
    python_dir = os.path.join(os.path.dirname(__file__), "python")
    os.chdir(python_dir)

    # Run server
    if args.prod:
        uvicorn.run(
            "tcdb_api.app:app",
            host=args.host,
            port=args.port,
            workers=args.workers,
            log_level="info"
        )
    else:
        uvicorn.run(
            "tcdb_api.app:app",
            host=args.host,
            port=args.port,
            reload=True,
            reload_dirs=[python_dir],
            log_level="debug"
        )


if __name__ == "__main__":
    main()

