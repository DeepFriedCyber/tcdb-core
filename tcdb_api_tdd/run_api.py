#!/usr/bin/env python3
from api.app import create_app
import os

if __name__ == '__main__':
    app = create_app()
    port = int(os.getenv('API_PORT', 8000))
    print("=" * 60)
    print("TCDB API Server Starting...")
    print("=" * 60)
    print(f"API Documentation: http://localhost:{port}/docs")
    print(f"Health Check: http://localhost:{port}/api/v1/health")
    print("=" * 60)
    app.run(host='0.0.0.0', port=port, debug=True)
