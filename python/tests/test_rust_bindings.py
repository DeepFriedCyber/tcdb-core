"""
Tests for Rust bindings

These tests verify that the Python bindings correctly expose Rust functionality.
"""

import pytest

# Skip all tests if Rust bindings not available
pytest.importorskip("tcdb_core")

import tcdb_core


class TestSimplex:
    """Test Simplex bindings"""
    
    def test_simplex_creation(self):
        """Test creating a simplex"""
        simplex = tcdb_core.Simplex([0, 1, 2])
        assert simplex.dimension() == 2
        assert simplex.vertices() == [0, 1, 2]
    
    def test_simplex_deduplication(self):
        """Test that duplicate vertices are removed"""
        simplex = tcdb_core.Simplex([0, 1, 1, 2])
        assert simplex.vertices() == [0, 1, 2]
    
    def test_simplex_sorting(self):
        """Test that vertices are sorted"""
        simplex = tcdb_core.Simplex([2, 0, 1])
        assert simplex.vertices() == [0, 1, 2]
    
    def test_simplex_repr(self):
        """Test string representation"""
        simplex = tcdb_core.Simplex([0, 1])
        repr_str = repr(simplex)
        assert "Simplex" in repr_str


class TestSimplicialComplex:
    """Test SimplicialComplex bindings"""
    
    def test_complex_creation(self):
        """Test creating an empty complex"""
        complex = tcdb_core.SimplicialComplex()
        assert complex.dimension() == 0
    
    def test_add_simplex(self):
        """Test adding a simplex"""
        complex = tcdb_core.SimplicialComplex()
        complex.add_simplex([0, 1, 2])
        assert complex.dimension() == 2
    
    def test_closure_property(self):
        """Test that closure property is maintained"""
        complex = tcdb_core.SimplicialComplex()
        complex.add_simplex([0, 1, 2])
        assert complex.verify_closure()
    
    def test_euler_characteristic_triangle(self):
        """Test Euler characteristic of a triangle"""
        complex = tcdb_core.SimplicialComplex()
        complex.add_simplex([0, 1, 2])
        # Triangle: 3 vertices - 3 edges + 1 face = 1
        assert complex.euler_characteristic() == 1
    
    def test_euler_characteristic_tetrahedron(self):
        """Test Euler characteristic of a tetrahedron (2-sphere)"""
        complex = tcdb_core.SimplicialComplex()
        complex.add_simplex([0, 1, 2])
        complex.add_simplex([0, 1, 3])
        complex.add_simplex([0, 2, 3])
        complex.add_simplex([1, 2, 3])
        # Sphere: χ = 2
        assert complex.euler_characteristic() == 2
    
    def test_complex_repr(self):
        """Test string representation"""
        complex = tcdb_core.SimplicialComplex()
        complex.add_simplex([0, 1])
        repr_str = repr(complex)
        assert "SimplicialComplex" in repr_str


class TestIntegration:
    """Integration tests"""
    
    def test_build_rips_complex(self):
        """Test building a Rips complex"""
        import numpy as np
        
        # Create a simple point cloud
        points = np.array([
            [0.0, 0.0],
            [1.0, 0.0],
            [0.0, 1.0],
        ])
        
        complex = tcdb_core.SimplicialComplex()
        
        # Add vertices
        for i in range(len(points)):
            complex.add_simplex([i])
        
        # Add edges based on distance
        max_dist = 1.5
        for i in range(len(points)):
            for j in range(i + 1, len(points)):
                dist = np.linalg.norm(points[i] - points[j])
                if dist <= max_dist:
                    complex.add_simplex([i, j])
        
        # Should have 3 vertices and 3 edges
        assert complex.dimension() >= 1
        assert complex.verify_closure()
    
    def test_multiple_complexes(self):
        """Test creating multiple independent complexes"""
        complex1 = tcdb_core.SimplicialComplex()
        complex2 = tcdb_core.SimplicialComplex()
        
        complex1.add_simplex([0, 1])
        complex2.add_simplex([0, 1, 2])
        
        assert complex1.dimension() == 1
        assert complex2.dimension() == 2
        assert complex1.euler_characteristic() != complex2.euler_characteristic()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

