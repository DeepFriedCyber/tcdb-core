//! Information-theoretic entropy analysis for TCDB
//!
//! This module provides entropy calculations based on Shannon's Information Theory,
//! enabling quantification of information content, surprise, and complexity across
//! all TCDB modules.
//!
//! # Key Concepts
//!
//! - **Shannon Entropy**: Expected information content (surprise) of a distribution
//! - **Topological Entropy**: Entropy of persistence diagrams and topological features
//! - **Optimal Encoding**: Minimum bits needed to encode data (Source Coding Theorem)
//! - **Normalized Entropy**: Entropy relative to maximum possible (uniformness measure)

use std::f64::consts::E;

/// Shannon entropy of a probability distribution
///
/// Computes H(X) = -Σ p(x) log₂ p(x) for a discrete probability distribution.
/// Returns entropy in bits (base-2 logarithm).
///
/// # Arguments
///
/// * `probabilities` - Probability distribution (must sum to 1.0)
///
/// # Returns
///
/// Entropy in bits. Returns 0.0 for deterministic distributions.
///
/// # Examples
///
/// ```
/// use tcdb_core::entropy::shannon_entropy;
///
/// // Uniform distribution has maximum entropy
/// let uniform = vec![0.25, 0.25, 0.25, 0.25];
/// let h = shannon_entropy(&uniform);
/// assert!((h - 2.0).abs() < 1e-10); // log₂(4) = 2 bits
///
/// // Deterministic distribution has zero entropy
/// let deterministic = vec![1.0, 0.0, 0.0, 0.0];
/// let h = shannon_entropy(&deterministic);
/// assert!(h.abs() < 1e-10);
/// ```
pub fn shannon_entropy(probabilities: &[f64]) -> f64 {
    probabilities
        .iter()
        .filter(|&&p| p > 0.0) // Skip zero probabilities (0 log 0 = 0)
        .map(|&p| -p * p.log2())
        .sum()
}

/// Shannon entropy with arbitrary logarithm base
///
/// Allows computing entropy in different units:
/// - Base 2: bits
/// - Base e: nats
/// - Base 10: dits (decimal digits)
///
/// # Arguments
///
/// * `probabilities` - Probability distribution
/// * `base` - Logarithm base (e.g., 2.0 for bits, E for nats)
pub fn shannon_entropy_base(probabilities: &[f64], base: f64) -> f64 {
    probabilities
        .iter()
        .filter(|&&p| p > 0.0)
        .map(|&p| -p * p.log(base))
        .sum()
}

/// Maximum possible entropy for a distribution with n outcomes
///
/// Returns log₂(n), the entropy of a uniform distribution.
pub fn max_entropy(n_outcomes: usize) -> f64 {
    (n_outcomes as f64).log2()
}

/// Normalized entropy (entropy relative to maximum)
///
/// Returns value in [0, 1] where:
/// - 0.0 = deterministic (no uncertainty)
/// - 1.0 = uniform (maximum uncertainty)
///
/// Measures how close a distribution is to being uniform.
pub fn normalized_entropy(probabilities: &[f64]) -> f64 {
    let h = shannon_entropy(probabilities);
    let h_max = max_entropy(probabilities.len());
    if h_max > 0.0 {
        h / h_max
    } else {
        0.0
    }
}

/// Self-information of an event with probability p
///
/// I(p) = -log₂(p)
///
/// Measures the "surprise" of observing an event.
/// Low probability events have high self-information.
pub fn self_information(probability: f64) -> f64 {
    if probability > 0.0 {
        -probability.log2()
    } else {
        f64::INFINITY
    }
}

/// Optimal encoding size according to Shannon's Source Coding Theorem
///
/// Returns the minimum average number of bits needed to encode n samples
/// from a distribution with given entropy.
///
/// # Arguments
///
/// * `entropy` - Shannon entropy of the distribution (in bits)
/// * `n_samples` - Number of samples to encode
///
/// # Returns
///
/// Minimum number of bits needed (rounded up)
pub fn optimal_encoding_bits(entropy: f64, n_samples: usize) -> usize {
    (entropy * n_samples as f64).ceil() as usize
}

/// Compute entropy from a histogram of counts
///
/// Converts counts to probabilities and computes Shannon entropy.
///
/// # Arguments
///
/// * `counts` - Histogram of observed counts
///
/// # Examples
///
/// ```
/// use tcdb_core::entropy::entropy_from_counts;
///
/// let counts = vec![10, 10, 10, 10]; // Uniform
/// let h = entropy_from_counts(&counts);
/// assert!((h - 2.0).abs() < 1e-10);
/// ```
pub fn entropy_from_counts(counts: &[usize]) -> f64 {
    let total: usize = counts.iter().sum();
    if total == 0 {
        return 0.0;
    }

    let probabilities: Vec<f64> = counts.iter().map(|&c| c as f64 / total as f64).collect();
    shannon_entropy(&probabilities)
}

/// Topological entropy from persistence diagram intervals
///
/// Treats birth-death intervals as a probability distribution and computes entropy.
/// High entropy indicates complex, diverse topological features.
///
/// # Arguments
///
/// * `intervals` - Birth-death intervals from persistence diagram
pub fn persistence_entropy(intervals: &[f64]) -> f64 {
    if intervals.is_empty() {
        return 0.0;
    }

    let total: f64 = intervals.iter().sum();
    if total == 0.0 {
        return 0.0;
    }

    let probabilities: Vec<f64> = intervals.iter().map(|&i| i / total).collect();
    shannon_entropy(&probabilities)
}

/// Entropy of Betti numbers across dimensions
///
/// Measures the distribution of topological features across dimensions.
///
/// # Arguments
///
/// * `betti_numbers` - Betti numbers for each dimension [β₀, β₁, β₂, ...]
pub fn betti_entropy(betti_numbers: &[usize]) -> f64 {
    entropy_from_counts(betti_numbers)
}

/// Joint entropy of two distributions
///
/// H(X,Y) = -Σ Σ p(x,y) log₂ p(x,y)
pub fn joint_entropy(joint_probabilities: &[Vec<f64>]) -> f64 {
    joint_probabilities
        .iter()
        .flat_map(|row| row.iter())
        .filter(|&&p| p > 0.0)
        .map(|&p| -p * p.log2())
        .sum()
}

/// Mutual information between two distributions
///
/// I(X;Y) = H(X) + H(Y) - H(X,Y)
///
/// Measures how much information X and Y share.
pub fn mutual_information(
    prob_x: &[f64],
    prob_y: &[f64],
    joint_prob: &[Vec<f64>],
) -> f64 {
    let h_x = shannon_entropy(prob_x);
    let h_y = shannon_entropy(prob_y);
    let h_xy = joint_entropy(joint_prob);
    h_x + h_y - h_xy
}

/// Kullback-Leibler divergence (relative entropy)
///
/// D_KL(P||Q) = Σ p(x) log₂(p(x)/q(x))
///
/// Measures how different distribution P is from reference distribution Q.
/// Returns infinity if Q has zero probability where P doesn't.
pub fn kl_divergence(p: &[f64], q: &[f64]) -> f64 {
    assert_eq!(p.len(), q.len(), "Distributions must have same length");

    p.iter()
        .zip(q.iter())
        .filter(|(&pi, _)| pi > 0.0)
        .map(|(&pi, &qi)| {
            if qi > 0.0 {
                pi * (pi / qi).log2()
            } else {
                f64::INFINITY
            }
        })
        .sum()
}

/// Cross-entropy between two distributions
///
/// H(P,Q) = -Σ p(x) log₂ q(x)
///
/// Used in machine learning loss functions.
pub fn cross_entropy(p: &[f64], q: &[f64]) -> f64 {
    assert_eq!(p.len(), q.len(), "Distributions must have same length");

    p.iter()
        .zip(q.iter())
        .filter(|(&pi, &qi)| pi > 0.0 && qi > 0.0)
        .map(|(&pi, &qi)| -pi * qi.log2())
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uniform_distribution_max_entropy() {
        // Uniform distribution has maximum entropy
        let uniform = vec![0.25, 0.25, 0.25, 0.25];
        let h = shannon_entropy(&uniform);
        assert!((h - 2.0).abs() < 1e-10, "Uniform 4-outcome should have 2 bits entropy");
    }

    #[test]
    fn test_deterministic_zero_entropy() {
        // Deterministic distribution has zero entropy
        let deterministic = vec![1.0, 0.0, 0.0, 0.0];
        let h = shannon_entropy(&deterministic);
        assert!(h.abs() < 1e-10, "Deterministic should have 0 entropy");
    }

    #[test]
    fn test_binary_entropy() {
        // Binary entropy function
        let p = 0.5;
        let binary = vec![p, 1.0 - p];
        let h = shannon_entropy(&binary);
        assert!((h - 1.0).abs() < 1e-10, "Fair coin should have 1 bit entropy");
    }

    #[test]
    fn test_entropy_with_different_bases() {
        let uniform = vec![0.5, 0.5];
        
        // Base 2 (bits)
        let h_bits = shannon_entropy_base(&uniform, 2.0);
        assert!((h_bits - 1.0).abs() < 1e-10);
        
        // Base e (nats)
        let h_nats = shannon_entropy_base(&uniform, E);
        assert!((h_nats - 2.0_f64.ln()).abs() < 1e-10);
    }

    #[test]
    fn test_max_entropy() {
        assert!((max_entropy(2) - 1.0).abs() < 1e-10);
        assert!((max_entropy(4) - 2.0).abs() < 1e-10);
        assert!((max_entropy(8) - 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_normalized_entropy() {
        // Uniform should be 1.0
        let uniform = vec![0.25, 0.25, 0.25, 0.25];
        assert!((normalized_entropy(&uniform) - 1.0).abs() < 1e-10);
        
        // Deterministic should be 0.0
        let deterministic = vec![1.0, 0.0, 0.0, 0.0];
        assert!(normalized_entropy(&deterministic).abs() < 1e-10);
    }

    #[test]
    fn test_self_information() {
        // Certain event (p=1) has 0 information
        assert!(self_information(1.0).abs() < 1e-10);
        
        // 50% event has 1 bit
        assert!((self_information(0.5) - 1.0).abs() < 1e-10);
        
        // 25% event has 2 bits
        assert!((self_information(0.25) - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_optimal_encoding_bits() {
        // 1 bit entropy, 10 samples = 10 bits minimum
        assert_eq!(optimal_encoding_bits(1.0, 10), 10);
        
        // 2 bits entropy, 5 samples = 10 bits minimum
        assert_eq!(optimal_encoding_bits(2.0, 5), 10);
        
        // Fractional entropy rounds up
        assert_eq!(optimal_encoding_bits(1.5, 10), 15);
    }

    #[test]
    fn test_entropy_from_counts() {
        // Uniform counts
        let counts = vec![10, 10, 10, 10];
        let h = entropy_from_counts(&counts);
        assert!((h - 2.0).abs() < 1e-10);
        
        // Skewed counts
        let counts = vec![40, 0, 0, 0];
        let h = entropy_from_counts(&counts);
        assert!(h.abs() < 1e-10);
    }

    #[test]
    fn test_persistence_entropy() {
        // Equal intervals = high entropy
        let intervals = vec![1.0, 1.0, 1.0, 1.0];
        let h = persistence_entropy(&intervals);
        assert!((h - 2.0).abs() < 1e-10);
        
        // One dominant interval = low entropy
        let intervals = vec![10.0, 0.1, 0.1, 0.1];
        let h = persistence_entropy(&intervals);
        assert!(h < 1.0);
    }

    #[test]
    fn test_betti_entropy() {
        let betti = vec![5, 5, 5, 5];
        let h = betti_entropy(&betti);
        assert!((h - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_kl_divergence() {
        // KL(P||P) = 0
        let p = vec![0.5, 0.5];
        assert!(kl_divergence(&p, &p).abs() < 1e-10);
        
        // KL(P||Q) > 0 when P != Q
        let q = vec![0.7, 0.3];
        assert!(kl_divergence(&p, &q) > 0.0);
    }

    #[test]
    fn test_cross_entropy() {
        let p = vec![0.5, 0.5];
        let q = vec![0.5, 0.5];
        
        // Cross-entropy equals entropy when P = Q
        let h_cross = cross_entropy(&p, &q);
        let h = shannon_entropy(&p);
        assert!((h_cross - h).abs() < 1e-10);
    }

    #[test]
    fn test_mutual_information() {
        // Independent variables have zero mutual information
        let px = vec![0.5, 0.5];
        let py = vec![0.5, 0.5];
        let joint = vec![
            vec![0.25, 0.25],
            vec![0.25, 0.25],
        ];
        
        let mi = mutual_information(&px, &py, &joint);
        assert!(mi.abs() < 1e-10);
    }
}

