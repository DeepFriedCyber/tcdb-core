from flask import Blueprint, jsonify
from api.middleware.auth import auth_required

bp = Blueprint('modules', __name__, url_prefix='/api/v1')

@bp.route('/modules', methods=['GET'])
@auth_required
def list_modules():
    """List all available modules"""
    return jsonify({
        'embedding_modules': [
            {
                'name': 'standard',
                'description': 'Standard embedding (identity)',
                'parameters': {}
            },
            {
                'name': 'pca',
                'description': 'PCA dimensionality reduction',
                'parameters': {'n_components': 'int'}
            }
        ],
        'tda_modules': [
            {
                'name': 'rips',
                'description': 'Rips complex for persistent homology',
                'parameters': {
                    'max_edge_length': 'float',
                    'max_dimension': 'int'
                }
            },
            {
                'name': 'alpha',
                'description': 'Alpha complex',
                'parameters': {'max_dimension': 'int'}
            }
        ],
        'downstream_modules': [
            {
                'name': 'classifier',
                'description': 'Random Forest classification',
                'parameters': {
                    'n_estimators': 'int',
                    'cv': 'int'
                }
            },
            {
                'name': 'clustering',
                'description': 'K-means clustering',
                'parameters': {'n_clusters': 'int'}
            }
        ]
    }), 200
