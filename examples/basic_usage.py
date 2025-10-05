#!/usr/bin/env python3
"""
Basic usage examples for TCDB Core
"""

import sys
try:
    import tcdb_core
except ImportError:
    print("❌ Rust bindings not available!")
    print("Install with: maturin develop --release")
    sys.exit(1)

print("🦀 TCDB Core - Basic Usage Examples\n")

# Example 1: Create a simplex
print("=" * 60)
print("Example 1: Creating Simplices")
print("=" * 60)

vertex = tcdb_core.Simplex([0])
edge = tcdb_core.Simplex([0, 1])
triangle = tcdb_core.Simplex([0, 1, 2])

print(f"Vertex: {vertex}")
print(f"  Dimension: {vertex.dimension()}")
print(f"  Vertices: {vertex.vertices()}")

print(f"\nEdge: {edge}")
print(f"  Dimension: {edge.dimension()}")
print(f"  Vertices: {edge.vertices()}")

print(f"\nTriangle: {triangle}")
print(f"  Dimension: {triangle.dimension()}")
print(f"  Vertices: {triangle.vertices()}")

# Example 2: Build a simplicial complex
print("\n" + "=" * 60)
print("Example 2: Building a Simplicial Complex")
print("=" * 60)

complex = tcdb_core.SimplicialComplex()
print(f"Empty complex dimension: {complex.dimension()}")

# Add a triangle (automatically adds all faces)
complex.add_simplex([0, 1, 2])
print(f"\nAfter adding triangle [0,1,2]:")
print(f"  Dimension: {complex.dimension()}")
print(f"  Euler characteristic: {complex.euler_characteristic()}")
print(f"  Closure verified: {complex.verify_closure()}")

# Example 3: Euler characteristic
print("\n" + "=" * 60)
print("Example 3: Euler Characteristic")
print("=" * 60)

# Triangle: χ = 3 vertices - 3 edges + 1 face = 1
triangle_complex = tcdb_core.SimplicialComplex()
triangle_complex.add_simplex([0, 1, 2])
print(f"Triangle: χ = {triangle_complex.euler_characteristic()}")

# Tetrahedron (2-sphere): χ = 2
tetrahedron = tcdb_core.SimplicialComplex()
tetrahedron.add_simplex([0, 1, 2])
tetrahedron.add_simplex([0, 1, 3])
tetrahedron.add_simplex([0, 2, 3])
tetrahedron.add_simplex([1, 2, 3])
print(f"Tetrahedron (2-sphere): χ = {tetrahedron.euler_characteristic()}")

# Two disconnected edges: χ = 4 vertices - 2 edges = 2
disconnected = tcdb_core.SimplicialComplex()
disconnected.add_simplex([0, 1])
disconnected.add_simplex([2, 3])
print(f"Two disconnected edges: χ = {disconnected.euler_characteristic()}")

# Example 4: Closure property
print("\n" + "=" * 60)
print("Example 4: Closure Property")
print("=" * 60)

complex = tcdb_core.SimplicialComplex()
complex.add_simplex([0, 1, 2, 3])  # Add a 3-simplex

print("Added 3-simplex [0,1,2,3]")
print("Closure property automatically adds all faces:")
print(f"  - 4 vertices (0-simplices)")
print(f"  - 6 edges (1-simplices)")
print(f"  - 4 triangles (2-simplices)")
print(f"  - 1 tetrahedron (3-simplex)")
print(f"\nClosure verified: {complex.verify_closure()}")
print(f"Dimension: {complex.dimension()}")
print(f"Euler characteristic: {complex.euler_characteristic()}")

print("\n✅ All examples completed successfully!")

