# TCDB API Documentation

## Overview

The TCDB API provides access to topological data analysis, provenance tracking, data proofs, and cross-domain reasoning capabilities.

**Base URL**: `https://tcdb.uk/api/v1`

**Authentication**: All endpoints require an API key obtained from the dashboard.

## Authentication

Include your API key in the `Authorization` header:

```
Authorization: Bearer tcdb_your_api_key_here
```

Get your API key at: https://tcdb.uk/dashboard

## Rate Limits

- **Free Plan**: 1,000 requests/month
- **Pro Plan**: 100,000 requests/month
- **Enterprise**: Unlimited

## Endpoints

### 1. Health Check

Check API status and available endpoints.

**Endpoint**: `GET /api/v1/health`

**Authentication**: Required

**Response**:
```json
{
  "status": "healthy",
  "version": "1.0.0",
  "endpoints": [
    "/api/v1/topology/signature",
    "/api/v1/provenance/track",
    "/api/v1/data/proof",
    "/api/v1/cross-domain/reason"
  ]
}
```

**Example**:
```bash
curl https://tcdb.uk/api/v1/health \
  -H "Authorization: Bearer tcdb_your_key"
```

---

### 2. Topological Signature

Generate topological signatures from numerical data using persistent homology.

**Endpoint**: `POST /api/v1/topology/signature`

**Request Body**:
```json
{
  "data": [1.0, 2.5, 3.2, 4.1, 5.0],
  "method": "vietoris_rips",
  "max_dimension": 2
}
```

**Parameters**:
- `data` (required): Array of numbers representing your data points
- `method` (optional): Computation method. Default: `"vietoris_rips"`
- `max_dimension` (optional): Maximum homology dimension. Default: `2`

**Response**:
```json
{
  "success": true,
  "signature": {
    "method": "vietoris_rips",
    "persistence_diagram": [
      {
        "dimension": 0,
        "birth": 0.0,
        "death": 1.5
      },
      {
        "dimension": 1,
        "birth": 0.5,
        "death": 2.3
      }
    ],
    "betti_numbers": {
      "H0": 3,
      "H1": 2,
      "H2": 1
    },
    "statistics": {
      "mean": 3.16,
      "variance": 2.104
    }
  },
  "method": "vietoris_rips",
  "max_dimension": 2,
  "data_points": 5
}
```

**Example (cURL)**:
```bash
curl -X POST https://tcdb.uk/api/v1/topology/signature \
  -H "Authorization: Bearer tcdb_your_key" \
  -H "Content-Type: application/json" \
  -d '{
    "data": [1.0, 2.5, 3.2, 4.1, 5.0],
    "method": "vietoris_rips",
    "max_dimension": 2
  }'
```

**Example (Python)**:
```python
import requests

api_key = "tcdb_your_key"
url = "https://tcdb.uk/api/v1/topology/signature"

response = requests.post(
    url,
    headers={"Authorization": f"Bearer {api_key}"},
    json={
        "data": [1.0, 2.5, 3.2, 4.1, 5.0],
        "method": "vietoris_rips",
        "max_dimension": 2
    }
)

print(response.json())
```

**Example (JavaScript)**:
```javascript
const apiKey = 'tcdb_your_key';
const url = 'https://tcdb.uk/api/v1/topology/signature';

const response = await fetch(url, {
  method: 'POST',
  headers: {
    'Authorization': `Bearer ${apiKey}`,
    'Content-Type': 'application/json'
  },
  body: JSON.stringify({
    data: [1.0, 2.5, 3.2, 4.1, 5.0],
    method: 'vietoris_rips',
    max_dimension: 2
  })
});

const result = await response.json();
console.log(result);
```

---

### 3. Provenance Tracking

Track the provenance of AI reasoning steps with cryptographic signatures.

**Endpoint**: `POST /api/v1/provenance/track`

**Request Body**:
```json
{
  "operation": "model_inference",
  "inputs": ["embedding_data", "model_weights"],
  "outputs": ["prediction", "confidence_score"],
  "metadata": {
    "model": "gpt-4",
    "version": "1.0",
    "timestamp": "2025-01-15T10:30:00Z"
  }
}
```

**Parameters**:
- `operation` (required): Name of the operation
- `inputs` (required): Array of input identifiers
- `outputs` (required): Array of output identifiers
- `metadata` (optional): Additional metadata object

**Response**:
```json
{
  "success": true,
  "provenance_id": "550e8400-e29b-41d4-a716-446655440000",
  "record": {
    "id": "550e8400-e29b-41d4-a716-446655440000",
    "operation": "model_inference",
    "inputs": ["embedding_data", "model_weights"],
    "outputs": ["prediction", "confidence_score"],
    "metadata": {
      "model": "gpt-4",
      "version": "1.0",
      "timestamp": "2025-01-15T10:30:00Z"
    },
    "timestamp": 1705315800000,
    "signature": "a3f5b8c9d2e1f4a7b6c5d8e9f1a2b3c4d5e6f7a8b9c0d1e2f3a4b5c6d7e8f9a0"
  }
}
```

**Example (Python)**:
```python
response = requests.post(
    "https://tcdb.uk/api/v1/provenance/track",
    headers={"Authorization": f"Bearer {api_key}"},
    json={
        "operation": "model_inference",
        "inputs": ["embedding_data", "model_weights"],
        "outputs": ["prediction", "confidence_score"],
        "metadata": {"model": "gpt-4", "version": "1.0"}
    }
)
```

---

### 4. Data Proof

Generate cryptographic proofs of data usage and membership.

**Endpoint**: `POST /api/v1/data/proof`

**Request Body**:
```json
{
  "data": ["item1", "item2", "item3"],
  "proof_type": "membership"
}
```

**Parameters**:
- `data` (required): Array of data items
- `proof_type` (optional): Type of proof. Default: `"membership"`

**Response**:
```json
{
  "success": true,
  "fingerprint": "b5c6d7e8f9a0b1c2d3e4f5a6b7c8d9e0f1a2b3c4d5e6f7a8b9c0d1e2f3a4b5c6",
  "proof_type": "membership",
  "proof": {
    "type": "membership",
    "root": "a1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e9f0a1b2",
    "leaves": [
      "c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8",
      "d5e6f7a8b9c0d1e2f3a4b5c6d7e8f9a0",
      "e7f8a9b0c1d2e3f4a5b6c7d8e9f0a1b2"
    ],
    "total_leaves": 3
  },
  "data_size": 3
}
```

**Example (Python)**:
```python
response = requests.post(
    "https://tcdb.uk/api/v1/data/proof",
    headers={"Authorization": f"Bearer {api_key}"},
    json={
        "data": ["item1", "item2", "item3"],
        "proof_type": "membership"
    }
)
```

---

### 5. Cross-Domain Reasoning

Discover hidden connections between different domains using topological similarity.

**Endpoint**: `POST /api/v1/cross-domain/reason`

**Request Body**:
```json
{
  "domain_a": "neural_networks",
  "domain_b": "power_grids",
  "data_a": [0.5, 0.8, 0.3, 0.9],
  "data_b": [0.6, 0.7, 0.4, 0.8]
}
```

**Parameters**:
- `domain_a` (required): Name of first domain
- `domain_b` (required): Name of second domain
- `data_a` (required): Array of numerical data from domain A
- `data_b` (required): Array of numerical data from domain B

**Response**:
```json
{
  "success": true,
  "domain_a": "neural_networks",
  "domain_b": "power_grids",
  "similarity_score": 0.85,
  "connections": [
    {
      "type": "topological_similarity",
      "strength": 0.85,
      "description": "neural_networks and power_grids share similar topological structures"
    },
    {
      "type": "principle_transfer",
      "applicable": true,
      "description": "Principles from neural_networks can be transferred to power_grids"
    }
  ],
  "transferable": true
}
```

**Example (Python)**:
```python
response = requests.post(
    "https://tcdb.uk/api/v1/cross-domain/reason",
    headers={"Authorization": f"Bearer {api_key}"},
    json={
        "domain_a": "neural_networks",
        "domain_b": "power_grids",
        "data_a": [0.5, 0.8, 0.3, 0.9],
        "data_b": [0.6, 0.7, 0.4, 0.8]
    }
)
```

---

## Error Responses

All endpoints return standard error responses:

**401 Unauthorized**:
```json
{
  "error": "Unauthorized. Please provide a valid API key."
}
```

**400 Bad Request**:
```json
{
  "error": "Invalid input. Expected array of numbers."
}
```

**404 Not Found**:
```json
{
  "error": "Endpoint not found"
}
```

**500 Internal Server Error**:
```json
{
  "error": "Internal server error message"
}
```

---

## Usage Tracking

All API calls are tracked and displayed on your dashboard at https://tcdb.uk/dashboard

Track:
- Total API calls
- Calls per endpoint
- Daily/monthly usage
- Remaining quota

---

## SDKs

### Python SDK (Coming Soon)

```python
from tcdb import TCDBClient

client = TCDBClient(api_key="tcdb_your_key")

# Topological signature
signature = client.topology.signature(
    data=[1.0, 2.5, 3.2, 4.1, 5.0],
    method="vietoris_rips"
)

# Provenance tracking
provenance = client.provenance.track(
    operation="model_inference",
    inputs=["data"],
    outputs=["result"]
)
```

### JavaScript SDK (Coming Soon)

```javascript
import { TCDBClient } from '@tcdb/client';

const client = new TCDBClient({ apiKey: 'tcdb_your_key' });

const signature = await client.topology.signature({
  data: [1.0, 2.5, 3.2, 4.1, 5.0],
  method: 'vietoris_rips'
});
```

---

## Support

- **Documentation**: https://tcdb.uk/docs
- **GitHub**: https://github.com/DeepFriedCyber/tcdb-core
- **Email**: support@tcdb.uk
- **Dashboard**: https://tcdb.uk/dashboard

---

## Changelog

### v1.0.0 (2025-01-15)
- Initial API release
- Topological signature generation
- Provenance tracking
- Data proofs
- Cross-domain reasoning

