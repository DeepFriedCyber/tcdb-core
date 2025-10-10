#!/usr/bin/env python3
"""
Reset database and run migrations.

This script:
1. Deletes the existing SQLite database
2. Runs Alembic migrations to create a fresh database

Usage:
    python scripts/reset_db.py
"""

import os
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from alembic.config import Config
from alembic import command


def reset_database():
    """Reset the database and run migrations."""
    # Get paths
    script_dir = Path(__file__).parent
    python_dir = script_dir.parent
    root_dir = python_dir.parent

    # Possible database locations
    db_paths = [
        python_dir / "tcdb.db",
        root_dir / "tcdb.db",
    ]
    alembic_ini = python_dir / "alembic.ini"

    print("🗑️  Resetting database...")

    # Delete existing databases
    deleted_any = False
    for db_path in db_paths:
        if db_path.exists():
            print(f"   Deleting {db_path}")
            db_path.unlink()
            deleted_any = True

    if not deleted_any:
        print(f"   No existing database found")
    
    # Run migrations
    print("\n📦 Running migrations...")
    alembic_cfg = Config(str(alembic_ini))
    
    try:
        command.upgrade(alembic_cfg, "head")
        print("\n✅ Database reset complete!")
        print(f"   Database created at: {python_dir / 'tcdb.db'}")
        
        # Show current version
        print("\n📊 Current migration version:")
        command.current(alembic_cfg)
        
    except Exception as e:
        print(f"\n❌ Error running migrations: {e}")
        sys.exit(1)


if __name__ == "__main__":
    reset_database()

