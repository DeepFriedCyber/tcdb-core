use pyo3::prelude::*;
use topological_streaming_engine::StreamingPersistence;
use nalgebra::DVector;

#[pyclass]
struct PyStreamingPersistence {
    inner: StreamingPersistence,
}

#[pymethods]
impl PyStreamingPersistence {
    #[new]
    fn new(window_size: usize) -> Self {
        Self {
            inner: StreamingPersistence::new(window_size),
        }
    }

    fn add_point(&mut self, point: Vec<f64>) -> Vec<(f64, f64)> {
        let dvec = DVector::from_vec(point);
        self.inner.add_point(dvec)
    }

    fn detect_anomaly(&self, threshold: f64) -> bool {
        self.inner.detect_anomaly(threshold)
    }
}

#[pymodule]
fn topological_py(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<PyStreamingPersistence>()?;
    Ok(())
}
