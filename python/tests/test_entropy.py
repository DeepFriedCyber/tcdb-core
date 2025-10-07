"""
Tests for TCDB Entropy Module
TDD tests for Python entropy bindings
"""

import pytest
import math
from tcdb_api.entropy import (
    EntropyAnalyzer,
    TopologicalEntropy,
    DatasetEntropy
)


class TestEntropyAnalyzer:
    """Tests for core entropy functions."""
    
    def test_shannon_entropy_uniform_distribution(self):
        """Uniform distribution should have maximum entropy."""
        probabilities = [0.25, 0.25, 0.25, 0.25]
        entropy = EntropyAnalyzer.shannon_entropy(probabilities)
        assert abs(entropy - 2.0) < 1e-10  # log2(4) = 2
    
    def test_shannon_entropy_deterministic(self):
        """Deterministic distribution should have zero entropy."""
        probabilities = [1.0, 0.0, 0.0, 0.0]
        entropy = EntropyAnalyzer.shannon_entropy(probabilities)
        assert abs(entropy - 0.0) < 1e-10
    
    def test_shannon_entropy_binary(self):
        """Fair coin should have 1 bit of entropy."""
        probabilities = [0.5, 0.5]
        entropy = EntropyAnalyzer.shannon_entropy(probabilities)
        assert abs(entropy - 1.0) < 1e-10
    
    def test_shannon_entropy_different_bases(self):
        """Test entropy with different logarithm bases."""
        probabilities = [0.5, 0.5]
        
        # Bits (base 2)
        entropy_bits = EntropyAnalyzer.shannon_entropy(probabilities, base=2.0)
        assert abs(entropy_bits - 1.0) < 1e-10
        
        # Nats (base e)
        entropy_nats = EntropyAnalyzer.shannon_entropy(probabilities, base=math.e)
        assert abs(entropy_nats - math.log(2)) < 1e-10
    
    def test_normalized_entropy(self):
        """Normalized entropy should be in [0, 1]."""
        # Uniform distribution
        uniform = [0.25, 0.25, 0.25, 0.25]
        norm_uniform = EntropyAnalyzer.normalized_entropy(uniform)
        assert abs(norm_uniform - 1.0) < 1e-10
        
        # Deterministic
        deterministic = [1.0, 0.0, 0.0, 0.0]
        norm_det = EntropyAnalyzer.normalized_entropy(deterministic)
        assert abs(norm_det - 0.0) < 1e-10
    
    def test_self_information(self):
        """Test self-information calculation."""
        # 50% probability = 1 bit
        info_50 = EntropyAnalyzer.self_information(0.5)
        assert abs(info_50 - 1.0) < 1e-10
        
        # 25% probability = 2 bits
        info_25 = EntropyAnalyzer.self_information(0.25)
        assert abs(info_25 - 2.0) < 1e-10
        
        # 100% probability = 0 bits
        info_100 = EntropyAnalyzer.self_information(1.0)
        assert abs(info_100 - 0.0) < 1e-10
    
    def test_self_information_invalid_probability(self):
        """Self-information should reject invalid probabilities."""
        with pytest.raises(ValueError):
            EntropyAnalyzer.self_information(0.0)
        
        with pytest.raises(ValueError):
            EntropyAnalyzer.self_information(1.5)
    
    def test_entropy_from_counts(self):
        """Test entropy computation from count data."""
        # Uniform counts
        counts = [10, 10, 10, 10]
        entropy = EntropyAnalyzer.entropy_from_counts(counts)
        assert abs(entropy - 2.0) < 1e-10
        
        # Dict input
        count_dict = {'a': 10, 'b': 10, 'c': 10, 'd': 10}
        entropy_dict = EntropyAnalyzer.entropy_from_counts(count_dict)
        assert abs(entropy_dict - 2.0) < 1e-10
    
    def test_optimal_encoding_bits(self):
        """Test Source Coding Theorem application."""
        entropy = 1.5  # bits per sample
        n_samples = 100
        optimal_bits = EntropyAnalyzer.optimal_encoding_bits(entropy, n_samples)
        assert optimal_bits == 150
    
    def test_kl_divergence(self):
        """Test KL divergence calculation."""
        # Identical distributions
        p = [0.5, 0.5]
        q = [0.5, 0.5]
        kl = EntropyAnalyzer.kl_divergence(p, q)
        assert abs(kl - 0.0) < 1e-10
        
        # Different distributions
        p = [0.7, 0.3]
        q = [0.5, 0.5]
        kl = EntropyAnalyzer.kl_divergence(p, q)
        assert kl > 0
    
    def test_kl_divergence_asymmetric(self):
        """KL divergence should be asymmetric."""
        p = [0.7, 0.3]
        q = [0.5, 0.5]
        
        kl_pq = EntropyAnalyzer.kl_divergence(p, q)
        kl_qp = EntropyAnalyzer.kl_divergence(q, p)
        
        assert abs(kl_pq - kl_qp) > 1e-6  # Should be different
    
    def test_mutual_information_independent(self):
        """Independent variables should have zero mutual information."""
        prob_x = [0.5, 0.5]
        prob_y = [0.5, 0.5]
        joint_prob = [
            [0.25, 0.25],
            [0.25, 0.25]
        ]
        
        mi = EntropyAnalyzer.mutual_information(prob_x, prob_y, joint_prob)
        assert abs(mi - 0.0) < 1e-10
    
    def test_cross_entropy(self):
        """Test cross-entropy calculation."""
        p = [0.5, 0.5]
        q = [0.6, 0.4]
        
        h_cross = EntropyAnalyzer.cross_entropy(p, q)
        assert h_cross > 0
        
        # Cross-entropy >= entropy
        h_p = EntropyAnalyzer.shannon_entropy(p)
        assert h_cross >= h_p


class TestTopologicalEntropy:
    """Tests for topological entropy functions."""
    
    def test_persistence_entropy(self):
        """Test persistence diagram entropy."""
        # Uniform intervals
        intervals = [1.0, 1.0, 1.0, 1.0]
        entropy = TopologicalEntropy.persistence_entropy(intervals)
        assert abs(entropy - 2.0) < 1e-10
    
    def test_persistence_entropy_empty(self):
        """Empty persistence diagram should have zero entropy."""
        intervals = []
        entropy = TopologicalEntropy.persistence_entropy(intervals)
        assert entropy == 0.0
    
    def test_betti_entropy(self):
        """Test Betti number entropy."""
        # Uniform Betti numbers
        betti_numbers = [5, 5, 5, 5]
        entropy = TopologicalEntropy.betti_entropy(betti_numbers)
        assert abs(entropy - 2.0) < 1e-10
    
    def test_complexity_score(self):
        """Test topological complexity score."""
        intervals = [1.0, 2.0, 3.0]
        betti_numbers = [3, 2, 1]
        
        complexity = TopologicalEntropy.complexity_score(intervals, betti_numbers)
        assert 0.0 <= complexity <= 1.0
    
    def test_complexity_score_empty(self):
        """Empty topology should have zero complexity."""
        intervals = []
        betti_numbers = []
        
        complexity = TopologicalEntropy.complexity_score(intervals, betti_numbers)
        assert complexity == 0.0


class TestDatasetEntropy:
    """Tests for dataset entropy functions."""
    
    def test_compute_entropy_uniform(self):
        """Uniform data should have high entropy."""
        data = list(range(100))  # Uniform distribution
        result = DatasetEntropy.compute_entropy(data, bins=10)
        
        assert result['entropy'] > 0
        assert 0 <= result['normalized_entropy'] <= 1
        assert result['optimal_bits'] > 0
    
    def test_compute_entropy_constant(self):
        """Constant data should have zero entropy."""
        data = [5.0] * 100
        result = DatasetEntropy.compute_entropy(data, bins=10)
        
        assert result['entropy'] == 0.0
        assert result['normalized_entropy'] == 0.0
        assert result['optimal_bits'] == 0
    
    def test_compute_entropy_empty(self):
        """Empty dataset should have zero entropy."""
        data = []
        result = DatasetEntropy.compute_entropy(data, bins=10)
        
        assert result['entropy'] == 0.0
        assert result['normalized_entropy'] == 0.0
        assert result['optimal_bits'] == 0
    
    def test_compute_entropy_bins(self):
        """Test with different bin sizes."""
        data = list(range(100))
        
        result_5 = DatasetEntropy.compute_entropy(data, bins=5)
        result_10 = DatasetEntropy.compute_entropy(data, bins=10)
        
        assert result_5['bins'] == 5
        assert result_10['bins'] == 10


class TestEntropyIntegration:
    """Integration tests for entropy module."""
    
    def test_entropy_workflow(self):
        """Test complete entropy analysis workflow."""
        # Generate sample data
        data = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]
        
        # Compute dataset entropy
        dataset_result = DatasetEntropy.compute_entropy(data, bins=5)
        assert dataset_result['entropy'] > 0
        
        # Compute from counts
        counts = [2, 2, 2, 2, 2]
        count_entropy = EntropyAnalyzer.entropy_from_counts(counts)
        assert count_entropy > 0
        
        # Verify optimal encoding
        optimal_bits = EntropyAnalyzer.optimal_encoding_bits(count_entropy, len(data))
        assert optimal_bits > 0
    
    def test_topological_workflow(self):
        """Test topological entropy workflow."""
        # Simulate persistence diagram
        intervals = [0.5, 1.0, 1.5, 2.0, 2.5]
        betti_numbers = [5, 3, 1]
        
        # Compute entropies
        pers_entropy = TopologicalEntropy.persistence_entropy(intervals)
        betti_entropy = TopologicalEntropy.betti_entropy(betti_numbers)
        complexity = TopologicalEntropy.complexity_score(intervals, betti_numbers)
        
        assert pers_entropy > 0
        assert betti_entropy > 0
        assert 0 <= complexity <= 1
    
    def test_information_theory_properties(self):
        """Test fundamental information theory properties."""
        # H(X) <= log(n) for n outcomes
        probabilities = [0.4, 0.3, 0.2, 0.1]
        entropy = EntropyAnalyzer.shannon_entropy(probabilities)
        max_entropy = math.log2(len(probabilities))
        assert entropy <= max_entropy + 1e-10
        
        # H(X,Y) <= H(X) + H(Y)
        prob_x = [0.5, 0.5]
        prob_y = [0.5, 0.5]
        joint_prob = [[0.25, 0.25], [0.25, 0.25]]
        
        h_x = EntropyAnalyzer.shannon_entropy(prob_x)
        h_y = EntropyAnalyzer.shannon_entropy(prob_y)
        joint_flat = [p for row in joint_prob for p in row]
        h_xy = EntropyAnalyzer.shannon_entropy(joint_flat)
        
        assert h_xy <= h_x + h_y + 1e-10


if __name__ == '__main__':
    pytest.main([__file__, '-v'])

