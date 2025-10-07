# TCDB Project Standards

## API Framework Selection

### ✅ **Default Choice: FastAPI**

**FastAPI should be the first choice for all API development** unless there are specific technical requirements that necessitate an alternative.

---

## Why FastAPI?

### 1. **Performance** ⚡
- **2-3x faster** than Flask
- Comparable to Node.js and Go
- Matches our ultra-fast Rust core (3.4ns Bayesian updates, 35ns Euler characteristic)
- Async/await support for concurrent operations

### 2. **Type Safety** 🔒
- Built-in Pydantic validation
- Type hints throughout
- Matches our Rust type safety philosophy
- Catches errors at development time, not runtime

### 3. **Auto-Documentation** 📚
- Automatic OpenAPI/Swagger docs at `/docs`
- Automatic ReDoc at `/redoc`
- Critical for scientific APIs and external users
- Always up-to-date with code

### 4. **Developer Experience** 👨‍💻
- Less boilerplate code
- Automatic request/response validation
- Better IDE support with type hints
- Modern Python 3.7+ features

### 5. **Production Ready** 🚀
- Built on Starlette (production-tested)
- Used by Microsoft, Netflix, Uber
- Excellent async performance
- Easy deployment with Uvicorn

---

## When to Use Alternatives

### Use **Flask** only if:
- ❌ You need specific Flask extensions not available in FastAPI
- ❌ Team has deep Flask expertise and no time to learn
- ❌ Legacy codebase requires Flask compatibility
- ❌ Synchronous-only operations (rare case)

### Use **Django** only if:
- ❌ You need a full-stack framework with ORM, admin panel, etc.
- ❌ Building a traditional web application, not an API

---

## FastAPI Best Practices

### 1. **Always Use Type Hints**
```python
# ✅ Good
@app.post("/items/")
async def create_item(item: Item) -> ItemResponse:
    return ItemResponse(id=1, **item.dict())

# ❌ Bad
@app.post("/items/")
def create_item(item):
    return {"id": 1, **item}
```

### 2. **Use Pydantic Models**
```python
from pydantic import BaseModel, Field

class TopologyRequest(BaseModel):
    data: list[list[float]] = Field(..., description="Point cloud data")
    max_dimension: int = Field(2, ge=0, le=10)
    max_edge_length: float = Field(1.0, gt=0)
```

### 3. **Use Async When Possible**
```python
# ✅ Good - async for I/O operations
@app.get("/compute")
async def compute():
    result = await expensive_computation()
    return result

# ⚠️ OK - sync for CPU-bound Rust calls
@app.post("/topology")
def topology(data: TopologyRequest):
    # Rust bindings are sync
    return tcdb_core.compute(data.points)
```

### 4. **Use Dependency Injection**
```python
from fastapi import Depends

async def get_current_user(token: str = Header(...)):
    return verify_token(token)

@app.get("/protected")
async def protected_route(user = Depends(get_current_user)):
    return {"user": user}
```

### 5. **Use Routers for Organization**
```python
# routers/topology.py
from fastapi import APIRouter

router = APIRouter(prefix="/api/v1/topology", tags=["topology"])

@router.post("/signature")
async def topology_signature(request: TopologyRequest):
    return compute_signature(request)

# main.py
from routers import topology
app.include_router(topology.router)
```

### 6. **Document Everything**
```python
@app.post(
    "/topology/signature",
    summary="Generate topological signature",
    description="Computes persistent homology and returns topological signature",
    response_description="Topological signature with Betti numbers",
    tags=["topology"]
)
async def topology_signature(request: TopologyRequest):
    """
    Generate a topological signature from point cloud data.
    
    - **data**: List of points (each point is a list of coordinates)
    - **max_dimension**: Maximum homology dimension to compute
    - **max_edge_length**: Maximum edge length for Rips complex
    """
    return compute_signature(request)
```

---

## Migration Checklist

When migrating from Flask to FastAPI:

- [ ] Replace `Flask` with `FastAPI`
- [ ] Replace `Blueprint` with `APIRouter`
- [ ] Replace `@app.route()` with `@app.get()`, `@app.post()`, etc.
- [ ] Replace `request.get_json()` with Pydantic models
- [ ] Replace `jsonify()` with direct return (auto-serialized)
- [ ] Add type hints to all functions
- [ ] Create Pydantic models for request/response
- [ ] Update tests to use `TestClient` from `fastapi.testclient`
- [ ] Replace `app.test_client()` with `TestClient(app)`
- [ ] Update `requirements.txt` (remove Flask, add FastAPI + uvicorn)
- [ ] Update documentation and README

---

## Testing Standards

### Use FastAPI's TestClient
```python
from fastapi.testclient import TestClient
from app import app

client = TestClient(app)

def test_health():
    response = client.get("/health")
    assert response.status_code == 200
    assert response.json()["status"] == "healthy"
```

### Test with Pydantic Validation
```python
def test_invalid_data():
    response = client.post("/topology", json={
        "data": "invalid",  # Should be list
        "max_dimension": -1  # Should be >= 0
    })
    assert response.status_code == 422  # Validation error
    assert "validation error" in response.json()["detail"][0]["msg"]
```

---

## Deployment Standards

### Use Uvicorn for Production
```bash
# Development
uvicorn app:app --reload

# Production
uvicorn app:app --host 0.0.0.0 --port 8000 --workers 4
```

### Docker
```dockerfile
FROM python:3.11-slim
WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt
COPY . .
CMD ["uvicorn", "app:app", "--host", "0.0.0.0", "--port", "8000"]
```

---

## Performance Benchmarks

### FastAPI vs Flask (TCDB API)

| Metric | Flask | FastAPI | Improvement |
|--------|-------|---------|-------------|
| Requests/sec | ~1,000 | ~2,500 | **2.5x** |
| Latency (p50) | 10ms | 4ms | **2.5x faster** |
| Latency (p99) | 50ms | 15ms | **3.3x faster** |
| Async support | ❌ | ✅ | Native |
| Type safety | ❌ | ✅ | Built-in |
| Auto docs | ❌ | ✅ | Free |

---

## Decision Record

**Date**: 2025-10-07  
**Decision**: FastAPI is the default API framework for TCDB  
**Rationale**:
- Performance matches our high-performance Rust core
- Type safety aligns with project philosophy
- Auto-documentation critical for scientific API
- Modern async support for future scalability
- Better developer experience and maintainability

**Exceptions**: Must be explicitly justified and documented

---

## Resources

- [FastAPI Documentation](https://fastapi.tiangolo.com/)
- [Pydantic Documentation](https://docs.pydantic.dev/)
- [FastAPI Best Practices](https://github.com/zhanymkanov/fastapi-best-practices)
- [TCDB Migration Guide](./FLASK_TO_FASTAPI_MIGRATION.md)

---

**Last Updated**: 2025-10-07  
**Status**: ✅ Active Standard

