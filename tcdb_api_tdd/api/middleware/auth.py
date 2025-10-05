from functools import wraps
from flask import request, jsonify
import jwt
import os
import requests
from typing import Optional, Dict, Any

# Clerk configuration from environment variables
CLERK_SECRET_KEY = os.getenv('CLERK_SECRET_KEY')
CLERK_PUBLISHABLE_KEY = os.getenv('CLERK_PUBLISHABLE_KEY')
CLERK_JWKS_URL = "https://api.clerk.com/v1/jwks"

# Cache for JWKS (JSON Web Key Set)
_jwks_cache: Optional[Dict[str, Any]] = None


def get_clerk_jwks():
    """Fetch Clerk's JWKS for token verification"""
    global _jwks_cache

    if _jwks_cache is not None:
        return _jwks_cache

    try:
        response = requests.get(CLERK_JWKS_URL, timeout=5)
        response.raise_for_status()
        _jwks_cache = response.json()
        return _jwks_cache
    except Exception as e:
        print(f"Error fetching JWKS: {e}")
        return None


def verify_clerk_token(token: str) -> Optional[Dict[str, Any]]:
    """
    Verify a Clerk JWT token and return the decoded payload.

    Args:
        token: The JWT token from the Authorization header

    Returns:
        Decoded token payload if valid, None otherwise
    """
    if not CLERK_SECRET_KEY:
        # Development mode: Allow test tokens for local testing
        if os.getenv('FLASK_ENV') == 'development' and token.startswith('test_'):
            return {
                'sub': 'test_user_id',
                'email': 'test@example.com',
                'metadata': {'tier': 'free'}
            }
        print("Warning: CLERK_SECRET_KEY not set")
        return None

    try:
        # Decode and verify the JWT token
        # Clerk uses RS256 algorithm
        decoded = jwt.decode(
            token,
            CLERK_SECRET_KEY,
            algorithms=["RS256"],
            options={"verify_signature": True}
        )
        return decoded
    except jwt.ExpiredSignatureError:
        print("Token has expired")
        return None
    except jwt.InvalidTokenError as e:
        print(f"Invalid token: {e}")
        return None
    except Exception as e:
        print(f"Error verifying token: {e}")
        return None


def auth_required(f):
    """
    Decorator to require Clerk authentication for API endpoints.

    Usage:
        @app.route('/protected')
        @auth_required
        def protected_route():
            user_id = request.user_info['sub']
            return {'message': 'Success'}
    """
    @wraps(f)
    def decorated_function(*args, **kwargs):
        auth_header = request.headers.get('Authorization')

        if not auth_header:
            return jsonify({
                'error': 'No authorization header',
                'message': 'Please provide a valid Clerk session token'
            }), 401

        try:
            # Parse Authorization header
            parts = auth_header.split()
            if len(parts) != 2 or parts[0].lower() != 'bearer':
                return jsonify({
                    'error': 'Invalid authorization header format',
                    'message': 'Expected format: Bearer <token>'
                }), 401

            token = parts[1]

            # Verify the token with Clerk
            user_info = verify_clerk_token(token)

            if not user_info:
                return jsonify({
                    'error': 'Invalid or expired token',
                    'message': 'Please sign in again'
                }), 401

            # Attach user info to request for use in route handlers
            request.user_info = user_info
            request.user_id = user_info.get('sub')

        except Exception as e:
            return jsonify({
                'error': 'Authentication failed',
                'message': str(e)
            }), 401

        return f(*args, **kwargs)

    return decorated_function


def optional_auth(f):
    """
    Decorator for endpoints that work with or without authentication.
    If authenticated, user_info is attached to request.
    """
    @wraps(f)
    def decorated_function(*args, **kwargs):
        auth_header = request.headers.get('Authorization')

        if auth_header:
            try:
                parts = auth_header.split()
                if len(parts) == 2 and parts[0].lower() == 'bearer':
                    token = parts[1]
                    user_info = verify_clerk_token(token)
                    if user_info:
                        request.user_info = user_info
                        request.user_id = user_info.get('sub')
            except Exception:
                pass  # Continue without auth

        return f(*args, **kwargs)

    return decorated_function
