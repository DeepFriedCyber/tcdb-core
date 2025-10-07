"""
Euler Characteristic Example

Demonstrates computation of the Euler characteristic,
a fundamental topological invariant.
"""

import tcdb_core


def main():
    print("=" * 60)
    print("Euler Characteristic Examples")
    print("=" * 60)
    
    # Standard complexes
    print("\n1. Standard Complexes:")
    print("-" * 40)
    
    point = tcdb_core.FVector.point()
    print(f"Point: χ = {point.euler_characteristic()}")
    
    interval = tcdb_core.FVector.interval()
    print(f"Interval: χ = {interval.euler_characteristic()}")
    
    triangle = tcdb_core.FVector.triangle()
    print(f"Triangle: χ = {triangle.euler_characteristic()}")
    
    tet = tcdb_core.FVector.tetrahedron()
    print(f"Tetrahedron: χ = {tet.euler_characteristic()}")
    
    # Classical surfaces
    print("\n2. Classical Surfaces:")
    print("-" * 40)
    
    # Sphere (octahedron): 6 vertices, 12 edges, 8 faces
    sphere = tcdb_core.FVector([6, 12, 8])
    print(f"Sphere: χ = {sphere.euler_characteristic()}")
    
    # Torus: 9 vertices, 27 edges, 18 faces
    torus = tcdb_core.FVector([9, 27, 18])
    print(f"Torus: χ = {torus.euler_characteristic()}")
    
    # Projective plane: 6 vertices, 15 edges, 10 faces
    proj_plane = tcdb_core.FVector([6, 15, 10])
    print(f"Projective Plane: χ = {proj_plane.euler_characteristic()}")
    
    # Klein bottle: 8 vertices, 24 edges, 16 faces
    klein = tcdb_core.FVector([8, 24, 16])
    print(f"Klein Bottle: χ = {klein.euler_characteristic()}")
    
    # Disjoint union
    print("\n3. Disjoint Union (Additivity):")
    print("-" * 40)
    
    t1 = tcdb_core.FVector.triangle()
    t2 = tcdb_core.FVector.triangle()
    union = t1.disjoint_union(t2)
    
    print(f"Triangle 1: χ = {t1.euler_characteristic()}")
    print(f"Triangle 2: χ = {t2.euler_characteristic()}")
    print(f"Union: χ = {union.euler_characteristic()}")
    print(f"Additive: {union.euler_characteristic()} = {t1.euler_characteristic()} + {t2.euler_characteristic()}")
    
    # Genus computation
    print("\n4. Genus Computation:")
    print("-" * 40)
    print("For closed orientable surfaces: genus = (2 - χ) / 2")
    
    sphere_genus = (2 - sphere.euler_characteristic()) // 2
    print(f"Sphere: genus = {sphere_genus}")
    
    torus_genus = (2 - torus.euler_characteristic()) // 2
    print(f"Torus: genus = {torus_genus}")
    
    # Component counting
    print("\n5. Component Counting:")
    print("-" * 40)
    
    # 10 disconnected points
    components = tcdb_core.FVector.empty()
    for _ in range(10):
        components = components.disjoint_union(tcdb_core.FVector.point())
    
    print(f"10 disconnected points: χ = {components.euler_characteristic()}")
    print("χ equals the number of connected components!")
    
    print("\n" + "=" * 60)


if __name__ == "__main__":
    main()

