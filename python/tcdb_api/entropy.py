"""
TCDB Entropy Module - Python Bindings
Provides Python interface to Rust entropy functions
"""

import math
from typing import List, Dict, Tuple, Optional, Union
import numpy as np


class EntropyAnalyzer:
    """
    Python wrapper for TCDB entropy analysis functions.
    Provides information-theoretic analysis capabilities.
    """
    
    @staticmethod
    def shannon_entropy(probabilities: List[float], base: float = 2.0) -> float:
        """
        Compute Shannon entropy of a probability distribution.
        
        Args:
            probabilities: List of probabilities (must sum to 1.0)
            base: Logarithm base (2=bits, e=nats, 10=dits)
        
        Returns:
            Shannon entropy in specified units
        
        Example:
            >>> EntropyAnalyzer.shannon_entropy([0.25, 0.25, 0.25, 0.25])
            2.0  # 2 bits for uniform distribution of 4 outcomes
        """
        if not probabilities:
            return 0.0
        
        # Normalize if needed
        total = sum(probabilities)
        if abs(total - 1.0) > 1e-10:
            probabilities = [p / total for p in probabilities]
        
        entropy = 0.0
        for p in probabilities:
            if p > 0:
                if base == 2.0:
                    entropy -= p * math.log2(p)
                elif base == math.e:
                    entropy -= p * math.log(p)
                else:
                    entropy -= p * (math.log(p) / math.log(base))
        
        return entropy
    
    @staticmethod
    def normalized_entropy(probabilities: List[float]) -> float:
        """
        Compute normalized entropy (uniformness measure).
        
        Returns value in [0, 1] where:
        - 0.0 = deterministic (one outcome)
        - 1.0 = perfectly uniform
        
        Args:
            probabilities: List of probabilities
        
        Returns:
            Normalized entropy in [0, 1]
        """
        if not probabilities or len(probabilities) == 1:
            return 0.0
        
        h = EntropyAnalyzer.shannon_entropy(probabilities)
        h_max = math.log2(len(probabilities))
        
        return h / h_max if h_max > 0 else 0.0
    
    @staticmethod
    def self_information(probability: float) -> float:
        """
        Compute self-information (surprise) of a single event.
        
        Args:
            probability: Probability of the event
        
        Returns:
            Self-information in bits
        
        Example:
            >>> EntropyAnalyzer.self_information(0.25)
            2.0  # 25% probability event has 2 bits of information
        """
        if probability <= 0 or probability > 1:
            raise ValueError("Probability must be in (0, 1]")
        
        return -math.log2(probability)
    
    @staticmethod
    def entropy_from_counts(counts: Union[List[int], Dict[str, int]]) -> float:
        """
        Compute entropy from count data.
        
        Args:
            counts: List of counts or dict mapping outcomes to counts
        
        Returns:
            Shannon entropy in bits
        
        Example:
            >>> EntropyAnalyzer.entropy_from_counts([10, 10, 10, 10])
            2.0  # Uniform distribution
        """
        if isinstance(counts, dict):
            counts = list(counts.values())
        
        if not counts:
            return 0.0
        
        total = sum(counts)
        if total == 0:
            return 0.0
        
        probabilities = [c / total for c in counts]
        return EntropyAnalyzer.shannon_entropy(probabilities)
    
    @staticmethod
    def optimal_encoding_bits(entropy: float, n_samples: int) -> int:
        """
        Compute optimal encoding size using Source Coding Theorem.
        
        Args:
            entropy: Shannon entropy in bits
            n_samples: Number of samples to encode
        
        Returns:
            Minimum number of bits needed
        
        Example:
            >>> EntropyAnalyzer.optimal_encoding_bits(1.5, 100)
            150  # Need at least 150 bits for 100 samples
        """
        return math.ceil(entropy * n_samples)
    
    @staticmethod
    def kl_divergence(p: List[float], q: List[float]) -> float:
        """
        Compute Kullback-Leibler divergence D(P||Q).
        
        Measures how different distribution P is from Q.
        
        Args:
            p: True distribution
            q: Approximating distribution
        
        Returns:
            KL divergence (always >= 0)
        """
        if len(p) != len(q):
            raise ValueError("Distributions must have same length")
        
        divergence = 0.0
        for pi, qi in zip(p, q):
            if pi > 0:
                if qi <= 0:
                    return float('inf')  # Infinite divergence
                divergence += pi * math.log2(pi / qi)
        
        return divergence
    
    @staticmethod
    def mutual_information(
        prob_x: List[float],
        prob_y: List[float],
        joint_prob: List[List[float]]
    ) -> float:
        """
        Compute mutual information I(X;Y).
        
        Measures shared information between X and Y.
        
        Args:
            prob_x: Marginal distribution of X
            prob_y: Marginal distribution of Y
            joint_prob: Joint distribution P(X,Y)
        
        Returns:
            Mutual information in bits
        """
        h_x = EntropyAnalyzer.shannon_entropy(prob_x)
        h_y = EntropyAnalyzer.shannon_entropy(prob_y)
        
        # Compute joint entropy
        joint_flat = [p for row in joint_prob for p in row if p > 0]
        h_xy = EntropyAnalyzer.shannon_entropy(joint_flat)
        
        return h_x + h_y - h_xy
    
    @staticmethod
    def cross_entropy(p: List[float], q: List[float]) -> float:
        """
        Compute cross-entropy H(P, Q).
        
        Used in machine learning loss functions.
        
        Args:
            p: True distribution
            q: Predicted distribution
        
        Returns:
            Cross-entropy in bits
        """
        if len(p) != len(q):
            raise ValueError("Distributions must have same length")
        
        h_cross = 0.0
        for pi, qi in zip(p, q):
            if pi > 0:
                if qi <= 0:
                    return float('inf')
                h_cross -= pi * math.log2(qi)
        
        return h_cross


class TopologicalEntropy:
    """Entropy analysis for topological signatures."""
    
    @staticmethod
    def persistence_entropy(intervals: List[float]) -> float:
        """
        Compute entropy of persistence diagram.
        
        Args:
            intervals: Birth-death intervals from persistence diagram
        
        Returns:
            Persistence entropy in bits
        """
        if not intervals:
            return 0.0
        
        total = sum(intervals)
        if total == 0:
            return 0.0
        
        probabilities = [i / total for i in intervals]
        return EntropyAnalyzer.shannon_entropy(probabilities)
    
    @staticmethod
    def betti_entropy(betti_numbers: List[int]) -> float:
        """
        Compute entropy of Betti number distribution.
        
        Args:
            betti_numbers: Betti numbers for each dimension
        
        Returns:
            Betti entropy in bits
        """
        return EntropyAnalyzer.entropy_from_counts(betti_numbers)
    
    @staticmethod
    def complexity_score(
        persistence_intervals: List[float],
        betti_numbers: List[int]
    ) -> float:
        """
        Compute overall topological complexity score.
        
        Args:
            persistence_intervals: Persistence diagram intervals
            betti_numbers: Betti numbers
        
        Returns:
            Complexity score in [0, 1]
        """
        pers_entropy = TopologicalEntropy.persistence_entropy(persistence_intervals)
        betti_entropy = TopologicalEntropy.betti_entropy(betti_numbers)
        
        # Normalize
        max_pers = math.log2(len(persistence_intervals)) if persistence_intervals else 0
        max_betti = math.log2(len(betti_numbers)) if betti_numbers else 0
        
        norm_pers = pers_entropy / max_pers if max_pers > 0 else 0
        norm_betti = betti_entropy / max_betti if max_betti > 0 else 0
        
        return (norm_pers + norm_betti) / 2.0


class DatasetEntropy:
    """Entropy analysis for datasets."""
    
    @staticmethod
    def compute_entropy(data: List[float], bins: int = 10) -> Dict[str, float]:
        """
        Compute entropy of a dataset using histogram.
        
        Args:
            data: Dataset values
            bins: Number of histogram bins
        
        Returns:
            Dictionary with entropy metrics
        """
        if not data:
            return {
                'entropy': 0.0,
                'normalized_entropy': 0.0,
                'optimal_bits': 0
            }
        
        # Create histogram
        min_val = min(data)
        max_val = max(data)
        
        if abs(max_val - min_val) < 1e-10:
            return {
                'entropy': 0.0,
                'normalized_entropy': 0.0,
                'optimal_bits': 0
            }
        
        bin_width = (max_val - min_val) / bins
        counts = [0] * bins
        
        for value in data:
            bin_idx = min(int((value - min_val) / bin_width), bins - 1)
            counts[bin_idx] += 1
        
        entropy = EntropyAnalyzer.entropy_from_counts(counts)
        max_entropy = math.log2(bins)
        normalized = entropy / max_entropy if max_entropy > 0 else 0
        optimal_bits = EntropyAnalyzer.optimal_encoding_bits(entropy, len(data))
        
        return {
            'entropy': entropy,
            'normalized_entropy': normalized,
            'optimal_bits': optimal_bits,
            'bins': bins
        }

