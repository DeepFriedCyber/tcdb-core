//! Python bindings using PyO3
//!
//! Exposes Rust functionality to Python

use pyo3::prelude::*;
use pyo3::exceptions::PyValueError;
use pyo3::types::PyModule;
use crate::{Simplex, SimplicialComplex, Filtration, PersistenceDiagram};
use crate::persistent_homology::PersistencePoint;

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

/// Python module definition
#[pymodule]
fn tcdb_core(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PySimplex>()?;
    m.add_class::<PySimplicialComplex>()?;
    m.add_class::<PyFiltration>()?;
    m.add_class::<PyPersistencePoint>()?;
    m.add_class::<PyPersistenceDiagram>()?;
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

