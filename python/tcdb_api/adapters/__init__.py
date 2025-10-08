"""
Domain-specific adapters for TCDB descriptor API.

These adapters provide high-level interfaces for common use cases:
- LLM: Token embeddings and attention analysis
- Cyber: Network flow and log analysis
- Bio: Protein structure and ensemble analysis
"""

from .common import DescriptorClient
from .llm_adapter import LLMAdapter
from .cyber_adapter import CyberAdapter
from .bio_adapter import BioAdapter

__all__ = [
    "DescriptorClient",
    "LLMAdapter",
    "CyberAdapter",
    "BioAdapter",
]

