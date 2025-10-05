from flask import Blueprint, request, jsonify
import numpy as np
import uuid
import time
from api.middleware.auth import auth_required
from api.models.pipeline_request import PipelineRequest
from core.validator import CoreValidator
from modules.embeddings.standard import StandardEmbedding
from modules.tda.rips import RipsTDA
from modules.downstream.classifier import ClassificationModule

bp = Blueprint('pipeline', __name__, url_prefix='/api/v1')

# In-memory storage for demo (use Redis/DB in production)
job_results = {}

@bp.route('/pipeline/run', methods=['POST'])
@auth_required
def run_pipeline():
    """Run the TDD pipeline with provided data"""
    try:
        # Validate request
        data = request.get_json()
        if not data:
            return jsonify({'error': 'No JSON data provided'}), 400

        pipeline_req = PipelineRequest.from_dict(data)

        # Validate input data
        validator = CoreValidator(strict_mode=True)
        X = np.array(pipeline_req.data)

        if not validator.validate_embeddings(X):
            return jsonify({
                'error': 'Invalid input data',
                'violations': validator.get_violations()
            }), 400

        # Generate job ID
        job_id = str(uuid.uuid4())

        # Run pipeline
        try:
            # Embedding
            t0 = time.time()
            embedding_module = StandardEmbedding()
            embeddings = embedding_module.fit_transform(X)
            t1 = time.time()

            if not validator.validate_embeddings(embeddings):
                raise ValueError("Embedding validation failed")

            # TDA
            tda_module = RipsTDA(max_edge_length=0.5, max_dimension=2)
            persistence = tda_module.compute_persistence(embeddings)
            t2 = time.time()

            if not validator.validate_persistence(persistence):
                raise ValueError("Persistence validation failed")

            features = tda_module.extract_features(persistence)

            if not validator.validate_features(features):
                raise ValueError("Features validation failed")

            # Downstream (if labels provided)
            downstream_scores = None
            if pipeline_req.labels:
                y = np.array(pipeline_req.labels)
                if len(y) == len(X):
                    classifier = ClassificationModule(n_estimators=50, cv=3)
                    X_feat = np.repeat(
                        np.array([features[k] for k in sorted(features)]).reshape(1, -1),
                        len(y), axis=0
                    )
                    downstream_scores = classifier.evaluate(X_feat, y)

            # Store results
            result = {
                'job_id': job_id,
                'status': 'completed',
                'timestamp': time.time(),
                'embedding_module': pipeline_req.embedding_module,
                'tda_module': pipeline_req.tda_module,
                'embedding_time': t1 - t0,
                'tda_time': t2 - t1,
                'features': features,
                'downstream_scores': downstream_scores,
                'validation_passed': True
            }

            job_results[job_id] = result

            return jsonify(result), 200

        except Exception as e:
            return jsonify({
                'error': 'Pipeline execution failed',
                'message': str(e)
            }), 500

    except Exception as e:
        return jsonify({
            'error': 'Request processing failed',
            'message': str(e)
        }), 400

@bp.route('/results/<job_id>', methods=['GET'])
@auth_required
def get_results(job_id):
    """Get results for a specific job"""
    if job_id not in job_results:
        return jsonify({'error': 'Job not found'}), 404

    return jsonify(job_results[job_id]), 200
