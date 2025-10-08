"""
Middleware for API authentication
"""

from fastapi import Request, HTTPException, status, Depends
from sqlalchemy.orm import Session
from datetime import datetime
from typing import Optional

from .database import get_db, APIKey, User
from .auth import validate_api_key_format


async def get_api_key_from_header(request: Request) -> Optional[str]:
    """Extract API key from request headers"""
    # Check X-API-Key header
    api_key = request.headers.get("X-API-Key")
    if api_key:
        return api_key
    
    # Check Authorization header (Bearer token)
    auth_header = request.headers.get("Authorization")
    if auth_header and auth_header.startswith("Bearer "):
        return auth_header[7:]  # Remove "Bearer " prefix
    
    return None


async def verify_api_key(
    request: Request,
    db: Session = Depends(get_db)
) -> User:
    """
    Dependency to verify API key and return the associated user.
    Raises HTTPException if API key is invalid or missing.
    """
    api_key = await get_api_key_from_header(request)
    
    if not api_key:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="API key required. Provide X-API-Key header or Authorization: Bearer <key>",
            headers={"WWW-Authenticate": "Bearer"}
        )
    
    # Validate format
    if not validate_api_key_format(api_key):
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Invalid API key format",
            headers={"WWW-Authenticate": "Bearer"}
        )
    
    # Look up API key in database
    db_api_key = db.query(APIKey).filter(APIKey.key == api_key).first()
    
    if not db_api_key:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Invalid API key",
            headers={"WWW-Authenticate": "Bearer"}
        )
    
    if not db_api_key.is_active:
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="API key has been revoked"
        )
    
    # Update last used timestamp
    db_api_key.last_used_at = datetime.utcnow()
    db.commit()
    
    # Get associated user
    user = db.query(User).filter(User.id == db_api_key.user_id).first()
    
    if not user or not user.is_active:
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="User account is inactive"
        )
    
    return user


async def optional_api_key(
    request: Request,
    db: Session = Depends(get_db)
) -> Optional[User]:
    """
    Optional API key verification.
    Returns user if valid API key is provided, None otherwise.
    Does not raise exception if no API key is provided.
    """
    try:
        return await verify_api_key(request, db)
    except HTTPException:
        return None

