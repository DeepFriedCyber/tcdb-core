from flask import Blueprint, jsonify
import time

bp = Blueprint('health', __name__, url_prefix='/api/v1')

@bp.route('/health', methods=['GET'])
def health_check():
    """Health check endpoint - no auth required"""
    return jsonify({
        'status': 'healthy',
        'timestamp': time.time(),
        'service': 'TCDB API',
        'version': '1.0.0'
    }), 200
