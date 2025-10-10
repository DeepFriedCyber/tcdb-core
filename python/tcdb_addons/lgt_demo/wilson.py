
import numpy as np
def rectangle_expectation(R: int, T: int, sigma: float=0.2, C: float=0.9, noise: float=0.02, seed: int=0) -> float:
    rng = np.random.default_rng(seed + 1000*R + 10000*T)
    w = C * np.exp(-sigma * R * T) * np.exp(rng.normal(0, noise))
    return float(max(min(w, 1.0), 1e-12))

def grid_expectations(R_vals, T_vals, **kw):
    out = []
    for R in R_vals:
        for T in T_vals:
            out.append({"R": int(R), "T": int(T), "W": rectangle_expectation(R, T, **kw)})
    return out
