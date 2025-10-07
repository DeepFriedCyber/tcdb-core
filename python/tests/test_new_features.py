"""
Tests for new TCDB features: Euler characteristic, Bayesian inference,
streaming filtrations, and landscape embeddings.
"""

import pytest
import tcdb_core


class TestEulerCharacteristic:
    """Tests for Euler characteristic computation."""
    
    def test_empty_has_chi_zero(self):
        """Empty complex has χ = 0."""
        empty = tcdb_core.FVector.empty()
        assert empty.euler_characteristic() == 0
    
    def test_point_has_chi_one(self):
        """Point has χ = 1."""
        point = tcdb_core.FVector.point()
        assert point.euler_characteristic() == 1
    
    def test_interval_has_chi_one(self):
        """Interval has χ = 1."""
        interval = tcdb_core.FVector.interval()
        assert interval.euler_characteristic() == 1
    
    def test_triangle_has_chi_one(self):
        """Triangle has χ = 1."""
        triangle = tcdb_core.FVector.triangle()
        assert triangle.euler_characteristic() == 1
    
    def test_tetrahedron_has_chi_one(self):
        """Tetrahedron has χ = 1."""
        tet = tcdb_core.FVector.tetrahedron()
        assert tet.euler_characteristic() == 1
    
    def test_custom_fvector(self):
        """Custom f-vector."""
        # 5 vertices, 7 edges, 3 faces
        # χ = 5 - 7 + 3 = 1
        fvec = tcdb_core.FVector([5, 7, 3])
        assert fvec.euler_characteristic() == 1
    
    def test_sphere_approximation(self):
        """Sphere has χ = 2."""
        # Octahedron: 6 vertices, 12 edges, 8 faces
        sphere = tcdb_core.FVector([6, 12, 8])
        assert sphere.euler_characteristic() == 2
    
    def test_torus_approximation(self):
        """Torus has χ = 0."""
        # 9 vertices, 27 edges, 18 faces
        torus = tcdb_core.FVector([9, 27, 18])
        assert torus.euler_characteristic() == 0
    
    def test_disjoint_union_additive(self):
        """χ(A ⊔ B) = χ(A) + χ(B)."""
        t1 = tcdb_core.FVector.triangle()
        t2 = tcdb_core.FVector.triangle()
        union = t1.disjoint_union(t2)
        
        chi_union = union.euler_characteristic()
        chi_sum = t1.euler_characteristic() + t2.euler_characteristic()
        
        assert chi_union == chi_sum
    
    def test_face_counts(self):
        """Get face counts."""
        triangle = tcdb_core.FVector.triangle()
        
        assert triangle.get_face_count(0) == 3  # 3 vertices
        assert triangle.get_face_count(1) == 3  # 3 edges
        assert triangle.get_face_count(2) == 1  # 1 face
    
    def test_max_dimension(self):
        """Get maximum dimension."""
        assert tcdb_core.FVector.point().max_dimension() == 0
        assert tcdb_core.FVector.interval().max_dimension() == 1
        assert tcdb_core.FVector.triangle().max_dimension() == 2
        assert tcdb_core.FVector.tetrahedron().max_dimension() == 3


class TestBayesianInference:
    """Tests for Bayesian inference."""
    
    def test_evidence_creation(self):
        """Create evidence."""
        ev = tcdb_core.Evidence(0.9, 0.1)
        assert ev.like_h == 0.9
        assert ev.like_not_h == 0.1
    
    def test_likelihood_ratio(self):
        """Compute likelihood ratio."""
        ev = tcdb_core.Evidence(0.9, 0.1)
        assert ev.likelihood_ratio() == 9.0
    
    def test_supports_h(self):
        """Check if evidence supports H."""
        ev1 = tcdb_core.Evidence(0.9, 0.1)
        assert ev1.supports_h()
        
        ev2 = tcdb_core.Evidence(0.1, 0.9)
        assert not ev2.supports_h()
    
    def test_is_neutral(self):
        """Check if evidence is neutral."""
        ev = tcdb_core.Evidence(0.5, 0.5)
        assert ev.is_neutral(0.01)
    
    def test_posterior_basic(self):
        """Compute posterior."""
        prior = 0.5
        ev = tcdb_core.Evidence(0.9, 0.1)
        post = tcdb_core.py_posterior(prior, ev)
        
        assert post.prior == prior
        assert post.posterior > prior
    
    def test_supportive_evidence_increases_belief(self):
        """Supportive evidence increases belief."""
        prior = 0.5
        ev = tcdb_core.Evidence(0.9, 0.1)
        post = tcdb_core.py_posterior(prior, ev)
        
        assert post.posterior > prior
    
    def test_contradictory_evidence_decreases_belief(self):
        """Contradictory evidence decreases belief."""
        prior = 0.5
        ev = tcdb_core.Evidence(0.1, 0.9)
        post = tcdb_core.py_posterior(prior, ev)
        
        assert post.posterior < prior
    
    def test_neutral_evidence_preserves_belief(self):
        """Neutral evidence preserves belief."""
        prior = 0.5
        ev = tcdb_core.Evidence(0.5, 0.5)
        post = tcdb_core.py_posterior(prior, ev)
        
        assert abs(post.posterior - prior) < 1e-10
    
    def test_belief_change(self):
        """Compute belief change."""
        prior = 0.5
        ev = tcdb_core.Evidence(0.9, 0.1)
        post = tcdb_core.py_posterior(prior, ev)
        
        change = post.belief_change()
        assert change > 0.0
    
    def test_bayes_factor(self):
        """Compute Bayes factor."""
        prior = 0.5
        ev = tcdb_core.Evidence(0.9, 0.1)
        post = tcdb_core.py_posterior(prior, ev)
        
        bf = post.bayes_factor()
        assert bf > 1.0
    
    def test_sequential_update(self):
        """Sequential Bayesian updating."""
        prior = 0.5
        evidence = [
            tcdb_core.Evidence(0.8, 0.2),
            tcdb_core.Evidence(0.9, 0.1),
        ]
        
        post = tcdb_core.py_sequential_update(prior, evidence)
        assert post.posterior > prior


class TestStreamingFiltrations:
    """Tests for streaming filtrations."""
    
    def test_streamer_creation(self):
        """Create streamer."""
        s = tcdb_core.Streamer(10)
        assert s.len() == 0
        assert s.is_empty()
    
    def test_push_samples(self):
        """Push samples to streamer."""
        s = tcdb_core.Streamer(10)
        
        for i in range(5):
            s.push((float(i), float(i)))
        
        assert s.len() == 5
        assert not s.is_empty()
    
    def test_window_size_respected(self):
        """Window size is respected."""
        s = tcdb_core.Streamer(3)
        
        for i in range(5):
            s.push((float(i), float(i)))
        
        assert s.len() == 3
    
    def test_pd_computation(self):
        """Compute persistence diagram."""
        s = tcdb_core.Streamer(10)
        
        for i in range(5):
            s.push((float(i), float(i)))
        
        pd = s.pd()
        assert isinstance(pd, list)
    
    def test_statistics(self):
        """Compute window statistics."""
        s = tcdb_core.Streamer(10)
        
        # Empty window
        assert s.statistics() is None
        
        # Add samples
        for i in range(5):
            s.push((float(i), float(i)))
        
        stats = s.statistics()
        assert stats is not None
        min_val, max_val, mean, std_dev = stats
        assert min_val == 0.0
        assert max_val == 4.0
    
    def test_clear(self):
        """Clear streamer."""
        s = tcdb_core.Streamer(10)
        
        for i in range(5):
            s.push((float(i), float(i)))
        
        s.clear()
        assert s.len() == 0
        assert s.is_empty()


class TestLandscapeEmbeddings:
    """Tests for landscape embeddings."""
    
    def test_landscape_features(self):
        """Compute landscape features."""
        pd = [(0.0, 1.0), (0.5, 1.5), (1.0, 2.0)]
        features = tcdb_core.py_landscape_features(pd, 2, 10, 0.0, 2.0)
        
        assert isinstance(features, list)
        assert len(features) == 2 * 10  # levels × samples
    
    def test_landscape_features_auto(self):
        """Compute landscape features with auto range."""
        pd = [(0.0, 1.0), (0.5, 1.5), (1.0, 2.0)]
        features = tcdb_core.py_landscape_features_auto(pd, 2, 10)
        
        assert isinstance(features, list)
        assert len(features) == 2 * 10
    
    def test_landscape_distance(self):
        """Compute landscape distance."""
        f1 = [1.0, 2.0, 3.0, 4.0]
        f2 = [1.5, 2.5, 3.5, 4.5]
        
        dist = tcdb_core.py_landscape_distance(f1, f2)
        assert dist > 0.0
    
    def test_landscape_similarity(self):
        """Compute landscape similarity."""
        f1 = [1.0, 2.0, 3.0, 4.0]
        f2 = [1.5, 2.5, 3.5, 4.5]
        
        sim = tcdb_core.py_landscape_similarity(f1, f2)
        assert 0.0 <= sim <= 1.0
    
    def test_identical_features_zero_distance(self):
        """Identical features have zero distance."""
        f1 = [1.0, 2.0, 3.0, 4.0]
        f2 = [1.0, 2.0, 3.0, 4.0]
        
        dist = tcdb_core.py_landscape_distance(f1, f2)
        assert dist == 0.0
    
    def test_identical_features_unit_similarity(self):
        """Identical features have similarity 1.0."""
        f1 = [1.0, 2.0, 3.0, 4.0]
        f2 = [1.0, 2.0, 3.0, 4.0]
        
        sim = tcdb_core.py_landscape_similarity(f1, f2)
        assert abs(sim - 1.0) < 1e-10


class TestIntegration:
    """Integration tests combining multiple features."""
    
    def test_euler_and_bayesian(self):
        """Combine Euler characteristic with Bayesian inference."""
        # Compute Euler characteristics
        sphere = tcdb_core.FVector([6, 12, 8])
        torus = tcdb_core.FVector([9, 27, 18])
        
        chi_sphere = sphere.euler_characteristic()
        chi_torus = torus.euler_characteristic()
        
        # Use as evidence for classification
        # Hypothesis: data is sphere-like
        prior = 0.5
        
        # If χ = 2, strong evidence for sphere
        if chi_sphere == 2:
            ev = tcdb_core.Evidence(0.9, 0.1)
        else:
            ev = tcdb_core.Evidence(0.1, 0.9)
        
        post = tcdb_core.py_posterior(prior, ev)
        assert post.posterior > 0.8
    
    def test_streaming_and_landscapes(self):
        """Combine streaming with landscape embeddings."""
        s = tcdb_core.Streamer(20)
        
        # Stream sine wave
        import math
        for i in range(30):
            t = i * 0.1
            value = math.sin(t)
            s.push((t, value))
        
        # Get persistence diagram
        pd = s.pd()
        
        # Compute landscape features
        if len(pd) > 0:
            features = tcdb_core.py_landscape_features_auto(pd, 2, 10)
            assert len(features) == 20


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

