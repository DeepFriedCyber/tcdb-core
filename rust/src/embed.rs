//! Topology-Aware Embeddings
//!
//! This module provides persistence landscape features for converting
//! persistence diagrams into fixed-dimensional vector representations
//! suitable for machine learning.
//!
//! # Persistence Landscapes
//!
//! Persistence landscapes are a functional representation of persistence
//! diagrams that:
//! - Are stable under perturbations (Lipschitz continuous)
//! - Can be averaged and combined linearly
//! - Provide fixed-dimensional feature vectors
//! - Are permutation-invariant (order of points doesn't matter)
//!
//! # Key Properties
//!
//! 1. **Deterministic**: Same PD → same features
//! 2. **Permutation-invariant**: Order doesn't matter
//! 3. **Differentiable**: Smooth w.r.t. input changes
//! 4. **Localized**: Distant features don't affect local regions
//!
//! # References
//!
//! - Bubenik, "Statistical Topological Data Analysis using Persistence Landscapes" (2015)
//! - Chazal et al., "Stochastic Convergence of Persistence Landscapes and Silhouettes" (2014)

use ordered_float::OrderedFloat;

/// Compute persistence landscape features from a persistence diagram
///
/// This function converts a persistence diagram into a fixed-dimensional
/// feature vector by sampling persistence landscape functions at multiple
/// levels and time points.
///
/// # Algorithm
///
/// For each persistence pair (b, d):
/// 1. Create a "tent" function: λ(t) = min(t-b, d-t) for t ∈ [b,d], else 0
/// 2. At each sample point t, collect all tent values
/// 3. Sort values in descending order
/// 4. Take top L values (L = levels)
/// 5. Concatenate across all sample points
///
/// # Arguments
///
/// * `pd` - Persistence diagram as (birth, death) pairs
/// * `levels` - Number of landscape levels (L)
/// * `samples` - Number of time points to sample (T)
/// * `tmin` - Minimum time value
/// * `tmax` - Maximum time value
///
/// # Returns
///
/// Feature vector of length `levels * samples`
///
/// # Properties
///
/// - **Permutation-invariant**: Reordering PD doesn't change features
/// - **Deterministic**: Same input → same output
/// - **Localized**: Features in [tmin, tmax] unaffected by distant intervals
/// - **Stable**: Small changes in PD → small changes in features
///
/// # Examples
///
/// ```
/// use tcdb_core::embed::landscape_features;
///
/// let pd = vec![(0.0, 1.0), (0.2, 0.9)];
/// let features = landscape_features(&pd, 3, 16, 0.0, 1.0);
///
/// // Features have length levels * samples
/// assert_eq!(features.len(), 3 * 16);
///
/// // Permutation invariant
/// let pd_reversed = vec![(0.2, 0.9), (0.0, 1.0)];
/// let features2 = landscape_features(&pd_reversed, 3, 16, 0.0, 1.0);
/// assert_eq!(features, features2);
/// ```
pub fn landscape_features(
    pd: &[(f64, f64)],
    levels: usize,
    samples: usize,
    tmin: f64,
    tmax: f64,
) -> Vec<f64> {
    // Create tent functions for each persistence pair
    // Each tent is a triangle: rises from b to mid, falls from mid to d
    let triangles: Vec<Box<dyn Fn(f64) -> f64>> = pd
        .iter()
        .map(|&(b, d)| {
            Box::new(move |t: f64| -> f64 {
                if t < b || t > d {
                    0.0
                } else {
                    // Tent function: min(t-b, d-t)
                    // Peaks at midpoint with height (d-b)/2
                    (t - b).min(d - t)
                }
            }) as Box<dyn Fn(f64) -> f64>
        })
        .collect();

    // Generate sample points uniformly in [tmin, tmax]
    let ts: Vec<f64> = (0..samples)
        .map(|i| {
            if samples <= 1 {
                tmin
            } else {
                tmin + (tmax - tmin) * (i as f64) / ((samples - 1) as f64)
            }
        })
        .collect();

    // Compute landscape features
    let mut features = Vec::with_capacity(levels * samples);

    for &t in ts.iter() {
        // Evaluate all tent functions at time t
        let mut values: Vec<OrderedFloat<f64>> = triangles
            .iter()
            .map(|f| OrderedFloat(f(t)))
            .collect();

        // Sort in descending order (largest values first)
        values.sort_by(|a, b| b.cmp(a));

        // Take top L levels
        for l in 0..levels {
            features.push(if l < values.len() {
                values[l].0
            } else {
                0.0
            });
        }
    }

    features
}

/// Compute landscape features with automatic range detection
///
/// Automatically determines tmin and tmax from the persistence diagram.
///
/// # Arguments
///
/// * `pd` - Persistence diagram
/// * `levels` - Number of landscape levels
/// * `samples` - Number of sample points
///
/// # Returns
///
/// Feature vector of length `levels * samples`
///
/// # Examples
///
/// ```
/// use tcdb_core::embed::landscape_features_auto;
///
/// let pd = vec![(0.0, 1.0), (0.5, 2.0)];
/// let features = landscape_features_auto(&pd, 3, 16);
/// assert_eq!(features.len(), 3 * 16);
/// ```
pub fn landscape_features_auto(
    pd: &[(f64, f64)],
    levels: usize,
    samples: usize,
) -> Vec<f64> {
    if pd.is_empty() {
        return vec![0.0; levels * samples];
    }

    // Find range of persistence diagram
    let tmin = pd
        .iter()
        .map(|(b, _)| OrderedFloat(*b))
        .min()
        .map(|x| x.0)
        .unwrap_or(0.0);

    let tmax = pd
        .iter()
        .filter(|(_, d)| d.is_finite())
        .map(|(_, d)| OrderedFloat(*d))
        .max()
        .map(|x| x.0)
        .unwrap_or(1.0);

    // Add small padding
    let padding = (tmax - tmin) * 0.1;
    landscape_features(pd, levels, samples, tmin - padding, tmax + padding)
}

/// Compute L2 distance between two feature vectors
///
/// # Arguments
///
/// * `f1` - First feature vector
/// * `f2` - Second feature vector
///
/// # Returns
///
/// L2 (Euclidean) distance
///
/// # Examples
///
/// ```
/// use tcdb_core::embed::landscape_distance;
///
/// let f1 = vec![1.0, 2.0, 3.0];
/// let f2 = vec![1.0, 2.0, 3.0];
/// assert_eq!(landscape_distance(&f1, &f2), 0.0);
/// ```
pub fn landscape_distance(f1: &[f64], f2: &[f64]) -> f64 {
    assert_eq!(
        f1.len(),
        f2.len(),
        "Feature vectors must have same length"
    );

    f1.iter()
        .zip(f2.iter())
        .map(|(a, b)| (a - b).powi(2))
        .sum::<f64>()
        .sqrt()
}

/// Compute cosine similarity between two feature vectors
///
/// # Arguments
///
/// * `f1` - First feature vector
/// * `f2` - Second feature vector
///
/// # Returns
///
/// Cosine similarity in [-1, 1]
///
/// # Examples
///
/// ```
/// use tcdb_core::embed::landscape_similarity;
///
/// let f1 = vec![1.0, 0.0, 0.0];
/// let f2 = vec![1.0, 0.0, 0.0];
/// assert!((landscape_similarity(&f1, &f2) - 1.0).abs() < 1e-10);
/// ```
pub fn landscape_similarity(f1: &[f64], f2: &[f64]) -> f64 {
    assert_eq!(
        f1.len(),
        f2.len(),
        "Feature vectors must have same length"
    );

    let dot: f64 = f1.iter().zip(f2.iter()).map(|(a, b)| a * b).sum();
    let norm1: f64 = f1.iter().map(|x| x.powi(2)).sum::<f64>().sqrt();
    let norm2: f64 = f2.iter().map(|x| x.powi(2)).sum::<f64>().sqrt();

    if norm1 == 0.0 || norm2 == 0.0 {
        0.0
    } else {
        dot / (norm1 * norm2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_landscape_features_basic() {
        let pd = vec![(0.0, 1.0)];
        let features = landscape_features(&pd, 2, 4, 0.0, 1.0);
        assert_eq!(features.len(), 2 * 4);
    }

    #[test]
    fn test_landscape_features_empty() {
        let pd = vec![];
        let features = landscape_features(&pd, 2, 4, 0.0, 1.0);
        assert_eq!(features.len(), 2 * 4);
        assert!(features.iter().all(|&x| x == 0.0));
    }

    #[test]
    fn test_landscape_features_auto() {
        let pd = vec![(0.0, 1.0), (0.5, 2.0)];
        let features = landscape_features_auto(&pd, 3, 16);
        assert_eq!(features.len(), 3 * 16);
    }

    #[test]
    fn test_landscape_distance() {
        let f1 = vec![1.0, 2.0, 3.0];
        let f2 = vec![1.0, 2.0, 3.0];
        assert_eq!(landscape_distance(&f1, &f2), 0.0);

        let f3 = vec![4.0, 5.0, 6.0];
        assert!(landscape_distance(&f1, &f3) > 0.0);
    }

    #[test]
    fn test_landscape_similarity() {
        let f1 = vec![1.0, 0.0, 0.0];
        let f2 = vec![1.0, 0.0, 0.0];
        assert!((landscape_similarity(&f1, &f2) - 1.0).abs() < 1e-10);

        let f3 = vec![0.0, 1.0, 0.0];
        assert!((landscape_similarity(&f1, &f3) - 0.0).abs() < 1e-10);
    }
}

