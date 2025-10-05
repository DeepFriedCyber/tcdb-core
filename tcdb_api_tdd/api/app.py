from flask import Flask, jsonify, send_from_directory
from flask_cors import CORS
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from api.routes import pipeline, modules, health, auth
from api.middleware.error_handler import register_error_handlers
from dotenv import load_dotenv
import os

# Load environment variables from .env file
load_dotenv()

def create_app(config=None):
    # Set static folder to serve homepage
    app = Flask(__name__,
                static_folder='../static',
                static_url_path='/static')

    # Configuration from environment variables
    app.config['SECRET_KEY'] = os.getenv('FLASK_SECRET_KEY', 'dev-secret-key-change-in-production')
    app.config['MAX_CONTENT_LENGTH'] = int(os.getenv('MAX_CONTENT_LENGTH', 16 * 1024 * 1024))
    app.config['CLERK_SECRET_KEY'] = os.getenv('CLERK_SECRET_KEY')
    app.config['CLERK_PUBLISHABLE_KEY'] = os.getenv('CLERK_PUBLISHABLE_KEY')

    if config:
        app.config.update(config)

    # Enable CORS
    CORS(app)

    # Rate limiting
    limiter = Limiter(
        app=app,
        key_func=get_remote_address,
        default_limits=["100 per hour"]
    )

    # Register blueprints
    app.register_blueprint(health.bp)
    app.register_blueprint(auth.bp)
    app.register_blueprint(pipeline.bp)
    app.register_blueprint(modules.bp)

    # Register error handlers
    register_error_handlers(app)

    # Homepage route
    @app.route('/')
    def index():
        """Serve the TopoPersist homepage"""
        return send_from_directory(app.static_folder, 'index.html')

    # API documentation endpoint
    @app.route('/docs')
    def docs():
        return jsonify({
            'api_version': 'v1',
            'endpoints': {
                'home': 'GET /',
                'health': 'GET /api/v1/health',
                'auth_config': 'GET /api/v1/auth/config',
                'verify_token': 'POST /api/v1/auth/verify',
                'current_user': 'GET /api/v1/auth/me',
                'run_pipeline': 'POST /api/v1/pipeline/run',
                'get_results': 'GET /api/v1/results/<job_id>',
                'list_modules': 'GET /api/v1/modules'
            },
            'authentication': 'Clerk authentication required',
            'rate_limit': '100 requests per hour'
        })

    return app
