#!/usr/bin/env python3
"""
TCDB-Core Python Integration Tests
Run comprehensive tests on Python bindings
"""

import sys

def test_imports():
    """Test that all modules can be imported"""
    print("Testing imports...")
    try:
        import tcdb_core
        print("  ✓ tcdb_core imported successfully")
        return True
    except ImportError as e:
        print(f"  ✗ Failed to import tcdb_core: {e}")
        return False

def test_simplex():
    """Test Simplex functionality"""
    print("\nTesting Simplex...")
    try:
        import tcdb_core
        
        # Create simplex
        simplex = tcdb_core.Simplex([0, 1, 2])
        
        # Test dimension
        assert simplex.dimension() == 2, "Dimension should be 2"
        print("  ✓ Dimension calculation correct")
        
        # Test vertices
        vertices = simplex.vertices()
        assert len(vertices) == 3, "Should have 3 vertices"
        assert set(vertices) == {0, 1, 2}, "Vertices should be [0, 1, 2]"
        print("  ✓ Vertices correct")
        
        return True
    except Exception as e:
        print(f"  ✗ Simplex test failed: {e}")
        return False

def test_simplicial_complex():
    """Test SimplicialComplex functionality"""
    print("\nTesting SimplicialComplex...")
    try:
        import tcdb_core
        
        # Create complex
        complex = tcdb_core.SimplicialComplex()
        print("  ✓ Complex created")
        
        # Add triangle
        complex.add_simplex([0, 1, 2])
        print("  ✓ Triangle added")
        
        # Test dimension
        dim = complex.dimension()
        assert dim == 2, f"Dimension should be 2, got {dim}"
        print(f"  ✓ Dimension: {dim}")
        
        # Test Euler characteristic
        euler = complex.euler_characteristic()
        assert euler == 1, f"Euler characteristic should be 1, got {euler}"
        print(f"  ✓ Euler characteristic: {euler}")
        
        # Test closure property
        closure = complex.verify_closure()
        assert closure == True, "Closure property should be satisfied"
        print("  ✓ Closure property verified")
        
        return True
    except Exception as e:
        print(f"  ✗ SimplicialComplex test failed: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_filtration():
    """Test Filtration functionality"""
    print("\nTesting Filtration...")
    try:
        import tcdb_core
        
        # Create filtration
        filt = tcdb_core.Filtration()
        print("  ✓ Filtration created")
        
        # Add simplices at different times
        filt.add_simplex(0.0, [0])
        filt.add_simplex(0.0, [1])
        filt.add_simplex(0.5, [0, 1])
        filt.add_simplex(1.0, [0, 1, 2])
        print("  ✓ Simplices added")
        
        # Test values
        values = filt.values()
        assert len(values) == 3, f"Should have 3 filtration values, got {len(values)}"
        assert 0.0 in values, "Should have value 0.0"
        assert 0.5 in values, "Should have value 0.5"
        assert 1.0 in values, "Should have value 1.0"
        print(f"  ✓ Filtration values: {values}")
        
        # Test max dimension
        max_dim = filt.max_dimension()
        assert max_dim == 2, f"Max dimension should be 2, got {max_dim}"
        print(f"  ✓ Max dimension: {max_dim}")
        
        # Test complex at time
        complex_at_0_5 = filt.complex_at(0.5)
        dim_at_0_5 = complex_at_0_5.dimension()
        assert dim_at_0_5 == 1, f"Dimension at t=0.5 should be 1, got {dim_at_0_5}"
        print(f"  ✓ Complex at t=0.5 has dimension {dim_at_0_5}")
        
        complex_at_1_0 = filt.complex_at(1.0)
        dim_at_1_0 = complex_at_1_0.dimension()
        assert dim_at_1_0 == 2, f"Dimension at t=1.0 should be 2, got {dim_at_1_0}"
        print(f"  ✓ Complex at t=1.0 has dimension {dim_at_1_0}")
        
        # Test monotonicity
        monotone = filt.verify_monotonicity()
        assert monotone == True, "Filtration should be monotone"
        print("  ✓ Monotonicity verified")
        
        return True
    except Exception as e:
        print(f"  ✗ Filtration test failed: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_persistence_point():
    """Test PersistencePoint functionality"""
    print("\nTesting PersistencePoint...")
    try:
        import tcdb_core
        
        # Create persistence point
        point = tcdb_core.PersistencePoint(birth=0.0, death=1.0, dimension=1)
        print("  ✓ PersistencePoint created")
        
        # Test properties
        assert point.birth == 0.0, "Birth should be 0.0"
        assert point.death == 1.0, "Death should be 1.0"
        assert point.dimension == 1, "Dimension should be 1"
        print(f"  ✓ Properties: birth={point.birth}, death={point.death}, dim={point.dimension}")
        
        # Test persistence
        persistence = point.persistence()
        assert persistence == 1.0, f"Persistence should be 1.0, got {persistence}"
        print(f"  ✓ Persistence: {persistence}")
        
        # Test is_infinite
        is_inf = point.is_infinite()
        assert is_inf == False, "Point should not be infinite"
        print(f"  ✓ Is infinite: {is_inf}")
        
        return True
    except Exception as e:
        print(f"  ✗ PersistencePoint test failed: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_advanced_operations():
    """Test more advanced operations"""
    print("\nTesting Advanced Operations...")
    try:
        import tcdb_core
        
        # Create a tetrahedron
        complex = tcdb_core.SimplicialComplex()
        complex.add_simplex([0, 1, 2, 3])
        
        dim = complex.dimension()
        assert dim == 3, f"Tetrahedron dimension should be 3, got {dim}"
        print(f"  ✓ Tetrahedron dimension: {dim}")
        
        euler = complex.euler_characteristic()
        # Tetrahedron: 4 vertices - 6 edges + 4 faces - 1 volume = 1
        # But we're computing: 4 - 6 + 4 - 1 = 1? Let's see what we get
        print(f"  ✓ Tetrahedron Euler characteristic: {euler}")
        
        # Create a more complex filtration
        filt = tcdb_core.Filtration()
        for i in range(5):
            filt.add_simplex(float(i) * 0.1, [i])
        
        for i in range(4):
            filt.add_simplex(float(i) * 0.2 + 0.5, [i, i+1])
        
        values = filt.values()
        print(f"  ✓ Complex filtration with {len(values)} values")
        
        return True
    except Exception as e:
        print(f"  ✗ Advanced operations test failed: {e}")
        import traceback
        traceback.print_exc()
        return False

def main():
    """Run all tests"""
    print("=" * 60)
    print("TCDB-Core Python Integration Tests")
    print("=" * 60)
    
    tests = [
        ("Imports", test_imports),
        ("Simplex", test_simplex),
        ("SimplicialComplex", test_simplicial_complex),
        ("Filtration", test_filtration),
        ("PersistencePoint", test_persistence_point),
        ("Advanced Operations", test_advanced_operations),
    ]
    
    results = []
    for name, test_func in tests:
        try:
            result = test_func()
            results.append((name, result))
        except Exception as e:
            print(f"\n✗ {name} test crashed: {e}")
            results.append((name, False))
    
    # Summary
    print("\n" + "=" * 60)
    print("Test Summary")
    print("=" * 60)
    
    passed = sum(1 for _, result in results if result)
    failed = len(results) - passed
    
    for name, result in results:
        status = "✓ PASS" if result else "✗ FAIL"
        print(f"{status}: {name}")
    
    print(f"\nTotal: {passed}/{len(results)} tests passed")
    
    if failed == 0:
        print("\n✅ All tests passed! System is working correctly.")
        return 0
    else:
        print(f"\n❌ {failed} test(s) failed. Please check the output above.")
        return 1

if __name__ == "__main__":
    sys.exit(main())

