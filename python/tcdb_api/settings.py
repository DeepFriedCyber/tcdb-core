"""
TCDB API Configuration

Centralized configuration management using Pydantic BaseSettings.
Environment variables can be set with TCDB_ prefix.
"""

from pydantic_settings import BaseSettings, SettingsConfigDict
from pydantic import field_validator, Field
from typing import Optional, Any


class Settings(BaseSettings):
    """Application settings with environment variable support."""

    model_config = SettingsConfigDict(
        env_prefix="TCDB_",
        env_file=".env",
        env_file_encoding="utf-8",
        case_sensitive=False
    )

    # Feature flags
    addons: bool = False

    @field_validator('addons', mode='before')
    @classmethod
    def parse_addons(cls, v: Any) -> bool:
        """Parse boolean from various string formats"""
        if isinstance(v, bool):
            return v
        if isinstance(v, str):
            return v.lower() in ('true', '1', 't', 'yes', 'y', 'on')
        return bool(v)

    # API settings
    api_title: str = "TCDB API"
    api_version: str = "1.0.0"
    api_description: str = "Topological Computation Database API"

    # Database settings
    database_url: str = "sqlite:///./tcdb.db"

    # Server settings
    host: str = "127.0.0.1"
    port: int = 8000
    reload: bool = False


# Global settings instance
settings = Settings()

