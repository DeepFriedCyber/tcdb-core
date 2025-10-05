"""
Flask application factory for TCDB API
"""

from flask import Flask, jsonify
from flask_cors import CORS
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
import os

def create_app(config=None):
    """Create and configure the Flask application"""
    app = Flask(__name__)
    
    # Configuration
    app.config['SECRET_KEY'] = os.getenv('FLASK_SECRET_KEY', 'dev-secret-key')
    app.config['MAX_CONTENT_LENGTH'] = 16 * 1024 * 1024  # 16MB max
    
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
    from .endpoints import health, pipeline, tda
    app.register_blueprint(health.bp)
    app.register_blueprint(pipeline.bp)
    app.register_blueprint(tda.bp)
    
    # Error handlers
    @app.errorhandler(404)
    def not_found(error):
        return jsonify({'error': 'Not found'}), 404
    
    @app.errorhandler(500)
    def internal_error(error):
        return jsonify({'error': 'Internal server error'}), 500
    
    # Health check
    @app.route('/')
    def index():
        return jsonify({
            'name': 'TCDB Core API',
            'version': '1.0.0',
            'status': 'operational',
            'rust_available': True  # Will be dynamic
        })
    
    return app

