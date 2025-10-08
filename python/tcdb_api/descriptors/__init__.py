"""
Topological Descriptors Module

This module provides four patent-clean descriptor families for summarizing
micro→macro structure in a dimensionless way:

1. TID (Topological-Information Descriptor): Topology + information theory
2. DGD (Diffusion-Geometry Descriptor): Heat diffusion on graphs
3. KME-Δ (Kernel Mean Embedding Divergence): RKHS distributional drift
4. GSER (Graph-Scattering Energy Ratio): Wavelet-based signal processing

All descriptors are:
- Dimensionless (built from probabilities or ratios)
- Micro→macro capable (explicit multiscale parameters)
- Implementation-ready (standard libraries)
- Mathematically independent
"""

from .base import Descriptor, DescriptorRegistry
from .tid import TopologicalInformationDescriptor
from .dgd import DiffusionGeometryDescriptor
from .kme_delta import KernelMeanEmbeddingDelta
from .gser import GraphScatteringEnergyRatio

__all__ = [
    'Descriptor',
    'DescriptorRegistry',
    'TopologicalInformationDescriptor',
    'DiffusionGeometryDescriptor',
    'KernelMeanEmbeddingDelta',
    'GraphScatteringEnergyRatio',
]

# Register all descriptors
registry = DescriptorRegistry()
registry.register('tid', TopologicalInformationDescriptor)
registry.register('dgd', DiffusionGeometryDescriptor)
registry.register('kme_delta', KernelMeanEmbeddingDelta)
registry.register('gser', GraphScatteringEnergyRatio)

