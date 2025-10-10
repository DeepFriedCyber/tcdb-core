
from fastapi import APIRouter
from pydantic import BaseModel
import numpy as np

from .topology.tda.phh import analyze_point_cloud
from .geom.info_geometry.fisher_rao import FisherRaoMetric
from .lgt_demo.wilson import grid_expectations

router = APIRouter(prefix="/addons", tags=["tcdb-addons"])

class PointCloud(BaseModel):
    X: list[list[float]]
    Y: list[list[float]] | None = None

class GramRequest(BaseModel):
    X: list[list[float]]

class WilsonRequest(BaseModel):
    R_vals: list[int]
    T_vals: list[int]
    sigma: float = 0.2
    C: float = 0.9
    noise: float = 0.02
    seed: int = 0

@router.post("/tda/analyze")
def tda_analyze(pc: PointCloud):
    X = np.array(pc.X, float)
    Y = np.array(pc.Y, float) if pc.Y is not None else None
    return analyze_point_cloud(X, Y)

@router.post("/metric/fisher_rao/gram")
def fisher_rao_gram(req: GramRequest):
    X = np.array(req.X, float)
    fr = FisherRaoMetric(dist="gaussian")
    G = fr.gram(X)
    return {"n": int(G.shape[0]), "gram": G.tolist()}

@router.post("/lgt/wilson")
def lgt_wilson(req: WilsonRequest):
    grid = grid_expectations(req.R_vals, req.T_vals, sigma=req.sigma, C=req.C, noise=req.noise, seed=req.seed)
    return {"grid": grid}
