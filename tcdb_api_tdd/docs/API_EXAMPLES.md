# API Usage Examples

## Authentication

All API requests (except health check) require authentication:

```bash
curl -H "Authorization: Bearer test_token_12345" \
  http://localhost:5000/api/v1/modules
```

## Example 1: Basic Pipeline

```bash
curl -X POST http://localhost:5000/api/v1/pipeline/run \
  -H "Authorization: Bearer test_token_12345" \
  -H "Content-Type: application/json" \
  -d '{
    "data": [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]],
    "embedding_module": "standard",
    "tda_module": "rips"
  }'
```

## Example 2: Pipeline with Classification

```bash
curl -X POST http://localhost:5000/api/v1/pipeline/run \
  -H "Authorization: Bearer test_token_12345" \
  -H "Content-Type: application/json" \
  -d '{
    "data": [[1.0, 2.0], [2.0, 3.0], [3.0, 4.0], [10.0, 11.0]],
    "labels": [0, 0, 0, 1],
    "embedding_module": "standard",
    "tda_module": "rips",
    "downstream_module": "classifier"
  }'
```

## Example 3: Python Client

```python
import requests
import numpy as np

API_URL = "http://localhost:5000/api/v1"
TOKEN = "test_token_12345"
HEADERS = {"Authorization": f"Bearer {TOKEN}"}

# Generate sample data
X = np.random.rand(50, 3).tolist()
y = np.random.randint(0, 2, 50).tolist()

# Run pipeline
response = requests.post(
    f"{API_URL}/pipeline/run",
    json={
        "data": X,
        "labels": y,
        "embedding_module": "standard",
        "tda_module": "rips",
        "downstream_module": "classifier"
    },
    headers=HEADERS
)

result = response.json()
print(f"Job ID: {result['job_id']}")
print(f"Features: {result['features']}")
print(f"Accuracy: {result['downstream_scores']['mean_accuracy']}")

# Get results later
job_id = result['job_id']
response = requests.get(f"{API_URL}/results/{job_id}", headers=HEADERS)
print(response.json())
```

## Example 4: JavaScript/Node.js Client

```javascript
const axios = require('axios');

const API_URL = 'http://localhost:5000/api/v1';
const TOKEN = 'test_token_12345';

async function runPipeline() {
  try {
    const response = await axios.post(
      `${API_URL}/pipeline/run`,
      {
        data: [[1, 2, 3], [4, 5, 6], [7, 8, 9]],
        embedding_module: 'standard',
        tda_module: 'rips'
      },
      {
        headers: {
          'Authorization': `Bearer ${TOKEN}`,
          'Content-Type': 'application/json'
        }
      }
    );

    console.log('Job ID:', response.data.job_id);
    console.log('Features:', response.data.features);
  } catch (error) {
    console.error('Error:', error.response.data);
  }
}

runPipeline();
```
