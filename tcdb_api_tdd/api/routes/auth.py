from flask import Blueprint, request, jsonify
from api.middleware.auth import auth_required, verify_clerk_token
import os

bp = Blueprint('auth', __name__, url_prefix='/api/v1/auth')


@bp.route('/verify', methods=['POST'])
def verify_token():
    """
    Verify a Clerk session token.
    
    Request body:
    {
        "token": "clerk_session_token"
    }
    
    Returns user information if token is valid.
    """
    data = request.get_json()
    
    if not data or 'token' not in data:
        return jsonify({
            'error': 'Missing token',
            'message': 'Please provide a token in the request body'
        }), 400
    
    token = data['token']
    user_info = verify_clerk_token(token)
    
    if not user_info:
        return jsonify({
            'error': 'Invalid token',
            'message': 'Token verification failed'
        }), 401
    
    return jsonify({
        'valid': True,
        'user': {
            'id': user_info.get('sub'),
            'email': user_info.get('email'),
            'metadata': user_info.get('metadata', {})
        }
    }), 200


@bp.route('/me', methods=['GET'])
@auth_required
def get_current_user():
    """
    Get information about the currently authenticated user.
    Requires valid Clerk session token in Authorization header.
    """
    user_info = request.user_info
    
    return jsonify({
        'user': {
            'id': user_info.get('sub'),
            'email': user_info.get('email'),
            'email_verified': user_info.get('email_verified', False),
            'metadata': user_info.get('metadata', {}),
            'created_at': user_info.get('iat'),
        }
    }), 200


@bp.route('/config', methods=['GET'])
def get_clerk_config():
    """
    Get Clerk configuration for frontend integration.
    Returns the publishable key (safe to expose to frontend).
    """
    publishable_key = os.getenv('CLERK_PUBLISHABLE_KEY')
    
    if not publishable_key:
        return jsonify({
            'error': 'Clerk not configured',
            'message': 'CLERK_PUBLISHABLE_KEY not set'
        }), 500
    
    return jsonify({
        'publishable_key': publishable_key,
        'sign_in_url': '/sign-in',
        'sign_up_url': '/sign-up',
    }), 200


@bp.route('/session', methods=['GET'])
@auth_required
def get_session_info():
    """
    Get detailed session information for the authenticated user.
    """
    user_info = request.user_info
    
    return jsonify({
        'session': {
            'user_id': user_info.get('sub'),
            'active': True,
            'expires_at': user_info.get('exp'),
            'issued_at': user_info.get('iat'),
        }
    }), 200

