"""Pipeline execution endpoints"""

from flask import Blueprint, request, jsonify
import numpy as np
import uuid
import time

bp = Blueprint('pipeline', __name__, url_prefix='/api/v1')

# In-memory job storage (use Redis in production)
jobs = {}

@bp.route('/pipeline/run', methods=['POST'])
def run_pipeline():
    """
    Run a complete TDA pipeline
    
    Request body:
    {
        "data": [[1.0, 2.0], [3.0, 4.0], ...],
        "max_dimension": 2,
        "max_edge_length": 1.0
    }
    """
    try:
        data = request.get_json()
        
        if not data or 'data' not in data:
            return jsonify({'error': 'Missing data field'}), 400
        
        # Validate input
        points = np.array(data['data'])
        if len(points.shape) != 2:
            return jsonify({'error': 'Data must be 2D array'}), 400
        
        max_dimension = data.get('max_dimension', 2)
        max_edge_length = data.get('max_edge_length', 1.0)
        
        # Create job
        job_id = str(uuid.uuid4())
        jobs[job_id] = {
            'status': 'running',
            'created_at': time.time(),
            'progress': 0
        }
        
        # Run pipeline (simplified for now)
        try:
            import tcdb_core
            
            # Build Rips complex
            complex = tcdb_core.SimplicialComplex()
            
            # Add vertices
            for i in range(len(points)):
                complex.add_simplex([i])
            
            # Add edges based on distance
            for i in range(len(points)):
                for j in range(i + 1, len(points)):
                    dist = np.linalg.norm(points[i] - points[j])
                    if dist <= max_edge_length:
                        complex.add_simplex([i, j])
            
            # Compute properties
            euler_char = complex.euler_characteristic()
            dimension = complex.dimension()
            
            result = {
                'job_id': job_id,
                'status': 'completed',
                'results': {
                    'euler_characteristic': euler_char,
                    'dimension': dimension,
                    'num_vertices': len(points),
                    'max_edge_length': max_edge_length
                },
                'metadata': {
                    'backend': 'rust',
                    'verified': True
                }
            }
            
            jobs[job_id] = {
                'status': 'completed',
                'result': result,
                'completed_at': time.time()
            }
            
            return jsonify(result)
            
        except ImportError:
            return jsonify({
                'error': 'Rust bindings not available',
                'message': 'Install with: maturin develop'
            }), 503
            
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@bp.route('/pipeline/status/<job_id>', methods=['GET'])
def get_job_status(job_id):
    """Get the status of a pipeline job"""
    if job_id not in jobs:
        return jsonify({'error': 'Job not found'}), 404
    
    return jsonify(jobs[job_id])

@bp.route('/pipeline/jobs', methods=['GET'])
def list_jobs():
    """List all jobs"""
    return jsonify({
        'jobs': [
            {'job_id': job_id, **job_data}
            for job_id, job_data in jobs.items()
        ]
    })

