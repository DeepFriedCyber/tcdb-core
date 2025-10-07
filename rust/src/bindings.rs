//! Python bindings using PyO3
//!
//! Exposes Rust functionality to Python

use pyo3::prelude::*;
use pyo3::exceptions::PyValueError;
use pyo3::types::PyModule;
use crate::{Simplex, SimplicialComplex, Filtration, PersistenceDiagram};
use crate::persistent_homology::PersistencePoint;
// Reasoner types (for future use)
// use crate::reasoner::{Constraint, BettiCurve, PD, Violation};
use crate::embed::{landscape_features, landscape_features_auto, landscape_distance, landscape_similarity};
use crate::streaming::Streamer;
use crate::bayes::{Evidence, Posterior, posterior, sequential_update};
use crate::euler::FVector;

/// Python wrapper for Simplex
#[pyclass(name = "Simplex")]
pub struct PySimplex {
    inner: Simplex,
}

#[pymethods]
impl PySimplex {
    #[new]
    fn new(vertices: Vec<usize>) -> Self {
        Self {
            inner: Simplex::new(vertices),
        }
    }

    fn dimension(&self) -> usize {
        self.inner.dimension()
    }

    fn vertices(&self) -> Vec<usize> {
        self.inner.vertices().to_vec()
    }

    fn __repr__(&self) -> String {
        format!("Simplex({:?})", self.inner.vertices())
    }
}

/// Python wrapper for SimplicialComplex
#[pyclass(name = "SimplicialComplex")]
pub struct PySimplicialComplex {
    inner: SimplicialComplex,
}

#[pymethods]
impl PySimplicialComplex {
    #[new]
    fn new() -> Self {
        Self {
            inner: SimplicialComplex::new(),
        }
    }

    fn add_simplex(&mut self, vertices: Vec<usize>) -> PyResult<()> {
        let simplex = Simplex::new(vertices);
        self.inner.add_simplex(simplex)
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn dimension(&self) -> usize {
        self.inner.dimension()
    }

    fn euler_characteristic(&self) -> i64 {
        self.inner.euler_characteristic()
    }

    fn verify_closure(&self) -> bool {
        self.inner.verify_closure()
    }

    fn __repr__(&self) -> String {
        format!("SimplicialComplex(dim={})", self.inner.dimension())
    }
}

/// Python wrapper for Filtration
#[pyclass(name = "Filtration")]
pub struct PyFiltration {
    inner: Filtration,
}

#[pymethods]
impl PyFiltration {
    #[new]
    fn new() -> Self {
        Self {
            inner: Filtration::new(),
        }
    }

    fn add_simplex(&mut self, value: f64, vertices: Vec<usize>) -> PyResult<()> {
        let simplex = Simplex::new(vertices);
        self.inner
            .add_simplex(value, simplex)
            .map_err(|e| PyValueError::new_err(e.to_string()))
    }

    fn values(&self) -> Vec<f64> {
        self.inner.values()
    }

    fn max_dimension(&self) -> usize {
        self.inner.max_dimension()
    }

    fn complex_at(&self, value: f64) -> PySimplicialComplex {
        PySimplicialComplex {
            inner: self.inner.complex_at(value),
        }
    }

    fn verify_monotonicity(&self) -> bool {
        self.inner.verify_monotonicity()
    }

    fn __repr__(&self) -> String {
        format!("Filtration(levels={})", self.inner.values().len())
    }
}

/// Python wrapper for PersistencePoint
#[pyclass(name = "PersistencePoint")]
#[derive(Clone)]
pub struct PyPersistencePoint {
    inner: PersistencePoint,
}

#[pymethods]
impl PyPersistencePoint {
    #[new]
    fn new(birth: f64, death: f64, dimension: usize) -> Self {
        Self {
            inner: PersistencePoint {
                birth,
                death,
                dimension,
            },
        }
    }

    #[getter]
    fn birth(&self) -> f64 {
        self.inner.birth
    }

    #[getter]
    fn death(&self) -> f64 {
        self.inner.death
    }

    #[getter]
    fn dimension(&self) -> usize {
        self.inner.dimension
    }

    fn persistence(&self) -> f64 {
        self.inner.persistence()
    }

    fn is_infinite(&self) -> bool {
        self.inner.is_infinite()
    }

    fn __repr__(&self) -> String {
        format!(
            "PersistencePoint(birth={:.2}, death={:.2}, dim={})",
            self.inner.birth, self.inner.death, self.inner.dimension
        )
    }
}

/// Python wrapper for PersistenceDiagram
#[pyclass(name = "PersistenceDiagram")]
pub struct PyPersistenceDiagram {
    inner: PersistenceDiagram,
}

#[pymethods]
impl PyPersistenceDiagram {
    fn dimension(&self) -> usize {
        self.inner.dimension
    }

    fn points(&self) -> Vec<(f64, f64, usize)> {
        self.inner.points
            .iter()
            .map(|p| (p.birth, p.death, p.dimension))
            .collect()
    }

    fn betti_number(&self) -> usize {
        self.inner.betti_number()
    }

    fn significant_points(&self, threshold: f64) -> Vec<(f64, f64, usize)> {
        self.inner.significant_points(threshold)
            .iter()
            .map(|p| (p.birth, p.death, p.dimension))
            .collect()
    }

    fn __repr__(&self) -> String {
        format!("PersistenceDiagram(dim={}, points={})", 
                self.inner.dimension, 
                self.inner.points.len())
    }
}

/// Python wrapper for FVector (Euler characteristic)
#[pyclass(name = "FVector")]
pub struct PyFVector {
    inner: FVector,
}

#[pymethods]
impl PyFVector {
    #[new]
    fn new(faces: Vec<usize>) -> Self {
        Self {
            inner: FVector::new(faces),
        }
    }

    #[staticmethod]
    fn empty() -> Self {
        Self {
            inner: FVector::empty(),
        }
    }

    #[staticmethod]
    fn point() -> Self {
        Self {
            inner: FVector::point(),
        }
    }

    #[staticmethod]
    fn interval() -> Self {
        Self {
            inner: FVector::interval(),
        }
    }

    #[staticmethod]
    fn triangle() -> Self {
        Self {
            inner: FVector::triangle(),
        }
    }

    #[staticmethod]
    fn tetrahedron() -> Self {
        Self {
            inner: FVector::tetrahedron(),
        }
    }

    fn euler_characteristic(&self) -> i64 {
        self.inner.euler_characteristic()
    }

    fn disjoint_union(&self, other: &PyFVector) -> PyFVector {
        PyFVector {
            inner: self.inner.disjoint_union(&other.inner),
        }
    }

    fn get_face_count(&self, k: usize) -> usize {
        self.inner.get_face_count(k)
    }

    fn max_dimension(&self) -> usize {
        self.inner.max_dimension()
    }

    fn __repr__(&self) -> String {
        format!("FVector(chi={})", self.inner.euler_characteristic())
    }
}

/// Python wrapper for Evidence (Bayesian)
#[pyclass(name = "Evidence")]
#[derive(Clone)]
pub struct PyEvidence {
    inner: Evidence,
}

#[pymethods]
impl PyEvidence {
    #[new]
    fn new(like_h: f64, like_not_h: f64) -> Self {
        Self {
            inner: Evidence::new(like_h, like_not_h),
        }
    }

    #[getter]
    fn like_h(&self) -> f64 {
        self.inner.like_h
    }

    #[getter]
    fn like_not_h(&self) -> f64 {
        self.inner.like_not_h
    }

    fn likelihood_ratio(&self) -> f64 {
        self.inner.likelihood_ratio()
    }

    fn supports_h(&self) -> bool {
        self.inner.supports_h()
    }

    fn is_neutral(&self, epsilon: f64) -> bool {
        self.inner.is_neutral(epsilon)
    }

    fn __repr__(&self) -> String {
        format!("Evidence(like_h={:.2}, like_not_h={:.2})",
                self.inner.like_h, self.inner.like_not_h)
    }
}

/// Python wrapper for Posterior (Bayesian)
#[pyclass(name = "Posterior")]
pub struct PyPosterior {
    inner: Posterior,
}

#[pymethods]
impl PyPosterior {
    #[getter]
    fn prior(&self) -> f64 {
        self.inner.prior
    }

    #[getter]
    fn posterior(&self) -> f64 {
        self.inner.posterior
    }

    #[getter]
    fn evidence(&self) -> PyEvidence {
        PyEvidence {
            inner: self.inner.evidence.clone(),
        }
    }

    fn belief_change(&self) -> f64 {
        self.inner.belief_change()
    }

    fn posterior_odds(&self) -> f64 {
        self.inner.posterior_odds()
    }

    fn bayes_factor(&self) -> f64 {
        self.inner.bayes_factor()
    }

    fn __repr__(&self) -> String {
        format!("Posterior(prior={:.2}, posterior={:.2})",
                self.inner.prior, self.inner.posterior)
    }
}

/// Python wrapper for Streamer
#[pyclass(name = "Streamer")]
pub struct PyStreamer {
    inner: Streamer,
}

#[pymethods]
impl PyStreamer {
    #[new]
    fn new(max_len: usize) -> Self {
        Self {
            inner: Streamer::new(max_len),
        }
    }

    fn push(&mut self, sample: (f64, f64)) {
        self.inner.push(sample);
    }

    fn pd(&self) -> Vec<(f64, f64)> {
        self.inner.pd()
    }

    fn statistics(&self) -> Option<(f64, f64, f64, f64)> {
        self.inner.statistics()
    }

    fn len(&self) -> usize {
        self.inner.len()
    }

    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    fn clear(&mut self) {
        self.inner.clear();
    }

    fn __repr__(&self) -> String {
        format!("Streamer(len={})", self.inner.len())
    }
}

/// Python functions for Bayesian inference
#[pyfunction]
fn py_posterior(prior: f64, evidence: &PyEvidence) -> PyPosterior {
    PyPosterior {
        inner: posterior(prior, evidence.inner.clone()),
    }
}

#[pyfunction]
fn py_sequential_update(prior: f64, evidence: Vec<PyEvidence>) -> PyPosterior {
    let evidence_vec: Vec<Evidence> = evidence.iter().map(|e| e.inner.clone()).collect();
    PyPosterior {
        inner: sequential_update(prior, &evidence_vec),
    }
}

/// Python functions for landscape embeddings
#[pyfunction]
fn py_landscape_features(
    pd: Vec<(f64, f64)>,
    levels: usize,
    samples: usize,
    tmin: f64,
    tmax: f64,
) -> Vec<f64> {
    landscape_features(&pd, levels, samples, tmin, tmax)
}

#[pyfunction]
fn py_landscape_features_auto(pd: Vec<(f64, f64)>, levels: usize, samples: usize) -> Vec<f64> {
    landscape_features_auto(&pd, levels, samples)
}

#[pyfunction]
fn py_landscape_distance(f1: Vec<f64>, f2: Vec<f64>) -> f64 {
    landscape_distance(&f1, &f2)
}

#[pyfunction]
fn py_landscape_similarity(f1: Vec<f64>, f2: Vec<f64>) -> f64 {
    landscape_similarity(&f1, &f2)
}

/// Python module definition
#[pymodule]
fn tcdb_core(m: &Bound<'_, PyModule>) -> PyResult<()> {
    // Original classes
    m.add_class::<PySimplex>()?;
    m.add_class::<PySimplicialComplex>()?;
    m.add_class::<PyFiltration>()?;
    m.add_class::<PyPersistencePoint>()?;
    m.add_class::<PyPersistenceDiagram>()?;

    // New classes
    m.add_class::<PyFVector>()?;
    m.add_class::<PyEvidence>()?;
    m.add_class::<PyPosterior>()?;
    m.add_class::<PyStreamer>()?;

    // Functions
    m.add_function(wrap_pyfunction!(py_posterior, m)?)?;
    m.add_function(wrap_pyfunction!(py_sequential_update, m)?)?;
    m.add_function(wrap_pyfunction!(py_landscape_features, m)?)?;
    m.add_function(wrap_pyfunction!(py_landscape_features_auto, m)?)?;
    m.add_function(wrap_pyfunction!(py_landscape_distance, m)?)?;
    m.add_function(wrap_pyfunction!(py_landscape_similarity, m)?)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_py_simplex_creation() {
        let simplex = PySimplex::new(vec![0, 1, 2]);
        assert_eq!(simplex.dimension(), 2);
        assert_eq!(simplex.vertices(), vec![0, 1, 2]);
    }

    #[test]
    fn test_py_complex_creation() {
        let mut complex = PySimplicialComplex::new();
        assert_eq!(complex.dimension(), 0);
        
        complex.add_simplex(vec![0, 1, 2]).unwrap();
        assert_eq!(complex.dimension(), 2);
    }

    #[test]
    fn test_py_complex_euler() {
        let mut complex = PySimplicialComplex::new();
        complex.add_simplex(vec![0, 1, 2]).unwrap();
        assert_eq!(complex.euler_characteristic(), 1);
    }
}

