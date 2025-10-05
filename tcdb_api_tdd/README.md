# TCDB REST API - Test-Driven Development

## TDD REST API for Topological Knowledge Graph System

**Tests Written FIRST → Implementation Satisfies Tests**

### Quick Start

```bash
# Install dependencies
pip install -r requirements.txt

# Run tests
pytest -v

# Start API server
python run_api.py

# API will be available at: http://localhost:5000
```

### API Endpoints

#### Health Check
```bash
GET /api/v1/health
```

#### Run Pipeline
```bash
POST /api/v1/pipeline/run
Content-Type: application/json

{
  "data": [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]],
  "embedding_module": "standard",
  "tda_module": "rips",
  "downstream_module": "classifier",
  "labels": [0, 1]  // optional
}
```

#### List Available Modules
```bash
GET /api/v1/modules
```

#### Get Pipeline Results
```bash
GET /api/v1/results/{job_id}
```

### Authentication

API uses **Clerk** for secure authentication (no hardcoded keys!):

1. **Setup Clerk** (see `CLERK_SETUP.md` for detailed instructions):
   ```bash
   cp .env.example .env
   # Add your Clerk keys to .env
   ```

2. **Get session token** from Clerk after user signs in

3. **Use token in API calls**:
   ```bash
   Authorization: Bearer <clerk_session_token>
   ```

**Development Mode**: Tokens starting with `test_` work when `FLASK_ENV=development`

### Rate Limiting

- 100 requests per hour per token
- 10 concurrent pipeline executions

### Documentation

- Full API docs: http://localhost:5000/docs
- Interactive testing: http://localhost:5000/swagger

### Testing

```bash
# Run all tests
pytest -v

# Run with coverage
pytest --cov=api --cov-report=html

# Run specific test file
pytest tests/api/test_routes.py -v
```
