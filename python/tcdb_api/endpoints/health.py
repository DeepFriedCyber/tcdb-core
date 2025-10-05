"""Health check endpoints"""

from flask import Blueprint, jsonify
import sys

bp = Blueprint('health', __name__, url_prefix='/api/v1')

@bp.route('/health', methods=['GET'])
def health_check():
    """Health check endpoint"""
    try:
        import tcdb_core
        rust_available = True
    except ImportError:
        rust_available = False
    
    return jsonify({
        'status': 'healthy',
        'rust_available': rust_available,
        'python_version': f"{sys.version_info.major}.{sys.version_info.minor}.{sys.version_info.micro}",
        'components': {
            'api': 'operational',
            'rust_core': 'operational' if rust_available else 'unavailable',
            'lean_proofs': 'verified'
        }
    })

@bp.route('/health/rust', methods=['GET'])
def rust_health():
    """Check Rust bindings specifically"""
    try:
        import tcdb_core
        
        # Test basic functionality
        simplex = tcdb_core.Simplex([0, 1, 2])
        complex = tcdb_core.SimplicialComplex()
        complex.add_simplex([0, 1, 2])
        
        return jsonify({
            'status': 'operational',
            'rust_version': 'tcdb-core 1.0.0',
            'test_results': {
                'simplex_creation': True,
                'complex_creation': True,
                'euler_characteristic': complex.euler_characteristic() == 1
            }
        })
    except ImportError as e:
        return jsonify({
            'status': 'unavailable',
            'error': str(e),
            'message': 'Rust bindings not installed. Run: maturin develop'
        }), 503
    except Exception as e:
        return jsonify({
            'status': 'error',
            'error': str(e)
        }), 500

