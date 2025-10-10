
import numpy as np

def barcode_entropy(lengths: np.ndarray, eps: float=1e-12) -> float:
    lengths = np.array(lengths, dtype=float)
    total = float(lengths.sum())
    if total <= 0:
        return 0.0
    p = np.clip(lengths / total, eps, 1.0)
    return float(-(p*np.log(p)).sum())

def stability_modulus(X: np.ndarray, Y: np.ndarray) -> float:
    X = np.asarray(X, float)
    Y = np.asarray(Y, float)
    if X.shape != Y.shape:
        raise ValueError("X and Y must have the same shape")
    d = float(np.max(np.linalg.norm(X - Y, axis=1)))
    return 1.0 / (d + 1e-6)

def analyze_point_cloud(X: np.ndarray, Y: np.ndarray=None):
    X = np.asarray(X, float)
    n = len(X)
    if n < 2:
        return {"n": int(n), "barcode_entropy": 0.0}
    D = np.linalg.norm(X[:,None,:] - X[None,:,:], axis=2)
    iu = np.triu_indices(n, k=1)
    bars = D[iu]
    ent = barcode_entropy(bars)
    out = {"n": int(n), "barcode_entropy": float(ent)}
    if Y is not None:
        out["stability_modulus"] = stability_modulus(X, np.asarray(Y, float))
    return out
