"""
API Keys router for generating, listing, and revoking API keys
"""

from fastapi import APIRouter, Depends, HTTPException, status, Request
from sqlalchemy.orm import Session
from pydantic import BaseModel
from typing import List
from datetime import datetime

from ..database import get_db, User, APIKey
from ..auth import generate_api_key
from .auth import require_login

router = APIRouter(prefix="/keys", tags=["api-keys"])


# Pydantic models
class APIKeyCreate(BaseModel):
    """Request to create a new API key"""
    name: str


class APIKeyResponse(BaseModel):
    """API key response"""
    id: int
    key: str
    name: str
    is_active: bool
    created_at: datetime
    last_used_at: datetime | None

    class Config:
        from_attributes = True


class APIKeyListResponse(BaseModel):
    """API key list response (without showing full key)"""
    id: int
    name: str
    key_preview: str  # Only show first 12 chars
    is_active: bool
    created_at: datetime
    last_used_at: datetime | None

    class Config:
        from_attributes = True


# Routes
@router.post("/", response_model=APIKeyResponse)
async def create_api_key(
    key_data: APIKeyCreate,
    current_user: User = Depends(require_login),
    db: Session = Depends(get_db)
):
    """Create a new API key for the current user"""
    # Generate new API key
    api_key = generate_api_key()
    
    # Create database entry
    new_key = APIKey(
        key=api_key,
        name=key_data.name,
        user_id=current_user.id
    )
    
    db.add(new_key)
    db.commit()
    db.refresh(new_key)
    
    return new_key


@router.get("/", response_model=List[APIKeyListResponse])
async def list_api_keys(
    current_user: User = Depends(require_login),
    db: Session = Depends(get_db)
):
    """List all API keys for the current user"""
    keys = db.query(APIKey).filter(APIKey.user_id == current_user.id).all()
    
    # Convert to list response (hide full key)
    return [
        APIKeyListResponse(
            id=key.id,
            name=key.name,
            key_preview=key.key[:12] + "..." if len(key.key) > 12 else key.key,
            is_active=key.is_active,
            created_at=key.created_at,
            last_used_at=key.last_used_at
        )
        for key in keys
    ]


@router.delete("/{key_id}")
async def revoke_api_key(
    key_id: int,
    current_user: User = Depends(require_login),
    db: Session = Depends(get_db)
):
    """Revoke (deactivate) an API key"""
    # Find the key
    api_key = db.query(APIKey).filter(
        APIKey.id == key_id,
        APIKey.user_id == current_user.id
    ).first()
    
    if not api_key:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="API key not found"
        )
    
    # Deactivate the key
    api_key.is_active = False
    db.commit()
    
    return {"message": "API key revoked successfully"}


@router.post("/{key_id}/activate")
async def activate_api_key(
    key_id: int,
    current_user: User = Depends(require_login),
    db: Session = Depends(get_db)
):
    """Reactivate an API key"""
    # Find the key
    api_key = db.query(APIKey).filter(
        APIKey.id == key_id,
        APIKey.user_id == current_user.id
    ).first()
    
    if not api_key:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="API key not found"
        )
    
    # Activate the key
    api_key.is_active = True
    db.commit()
    
    return {"message": "API key activated successfully"}

