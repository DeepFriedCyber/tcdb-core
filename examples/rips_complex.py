#!/usr/bin/env python3
"""
Example: Building a Rips complex from a point cloud
"""

import sys
import numpy as np

try:
    import tcdb_core
except ImportError:
    print("❌ Rust bindings not available!")
    print("Install with: maturin develop --release")
    sys.exit(1)

print("🦀 TCDB Core - Rips Complex Example\n")

# Generate a simple point cloud
print("=" * 60)
print("Generating Point Cloud")
print("=" * 60)

# Square with 4 corners
points = np.array([
    [0.0, 0.0],
    [1.0, 0.0],
    [0.0, 1.0],
    [1.0, 1.0]
])

print(f"Points:\n{points}\n")

# Build Rips complex
print("=" * 60)
print("Building Rips Complex")
print("=" * 60)

max_distance = 1.5
print(f"Maximum edge length: {max_distance}\n")

complex = tcdb_core.SimplicialComplex()

# Add vertices
print("Adding vertices...")
for i in range(len(points)):
    complex.add_simplex([i])
print(f"  Added {len(points)} vertices")

# Add edges based on distance
print("\nAdding edges...")
edges_added = 0
for i in range(len(points)):
    for j in range(i + 1, len(points)):
        dist = np.linalg.norm(points[i] - points[j])
        if dist <= max_distance:
            complex.add_simplex([i, j])
            edges_added += 1
            print(f"  Edge [{i},{j}]: distance = {dist:.3f}")

print(f"\nTotal edges added: {edges_added}")

# Analyze the complex
print("\n" + "=" * 60)
print("Complex Analysis")
print("=" * 60)

print(f"Dimension: {complex.dimension()}")
print(f"Euler characteristic: {complex.euler_characteristic()}")
print(f"Closure verified: {complex.verify_closure()}")

# Interpret Euler characteristic
chi = complex.euler_characteristic()
num_vertices = len(points)
num_edges = edges_added

print(f"\nTopological interpretation:")
print(f"  χ = V - E + F")
print(f"  {chi} = {num_vertices} - {num_edges} + F")
print(f"  F = {chi - num_vertices + num_edges}")

if chi == 1:
    print("\n  → This is topologically equivalent to a disk or tree")
elif chi == 0:
    print("\n  → This has one loop (like a circle)")
elif chi == 2:
    print("\n  → This is topologically equivalent to a sphere")

# Example with different threshold
print("\n" + "=" * 60)
print("Varying Distance Threshold")
print("=" * 60)

for threshold in [0.5, 1.0, 1.5, 2.0]:
    complex = tcdb_core.SimplicialComplex()
    
    # Add vertices
    for i in range(len(points)):
        complex.add_simplex([i])
    
    # Add edges
    edges = 0
    for i in range(len(points)):
        for j in range(i + 1, len(points)):
            if np.linalg.norm(points[i] - points[j]) <= threshold:
                complex.add_simplex([i, j])
                edges += 1
    
    print(f"Threshold {threshold:.1f}: {edges} edges, χ = {complex.euler_characteristic()}")

# Example with random points
print("\n" + "=" * 60)
print("Random Point Cloud")
print("=" * 60)

np.random.seed(42)
random_points = np.random.randn(20, 2)

complex = tcdb_core.SimplicialComplex()

# Add vertices
for i in range(len(random_points)):
    complex.add_simplex([i])

# Add edges
threshold = 1.0
edges = 0
for i in range(len(random_points)):
    for j in range(i + 1, len(random_points)):
        if np.linalg.norm(random_points[i] - random_points[j]) <= threshold:
            complex.add_simplex([i, j])
            edges += 1

print(f"20 random points, threshold = {threshold}")
print(f"  Edges: {edges}")
print(f"  Dimension: {complex.dimension()}")
print(f"  Euler characteristic: {complex.euler_characteristic()}")
print(f"  Number of components ≈ {complex.euler_characteristic()}")

print("\n✅ Rips complex example completed!")

