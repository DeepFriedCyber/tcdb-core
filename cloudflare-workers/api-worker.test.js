/**
 * TDD Tests for TCDB API Worker
 * Run with: npm test
 */

import { describe, it, expect, beforeEach } from 'vitest';

// Mock environment
const mockEnv = {
  API_KEYS: {
    async get(key) {
      if (key === 'key:tcdb_valid_key') return 'test@example.com';
      return null;
    }
  },
  USAGE: {
    async get(key) {
      return JSON.stringify({ total: 0, endpoints: {} });
    },
    async put(key, value, options) {
      return true;
    }
  },
  PROVENANCE: {
    async put(key, value) {
      return true;
    }
  }
};

// Helper to create request
function createRequest(path, method = 'GET', body = null, apiKey = 'tcdb_valid_key') {
  const headers = new Headers({
    'Content-Type': 'application/json'
  });
  
  if (apiKey) {
    headers.set('Authorization', `Bearer ${apiKey}`);
  }

  return new Request(`https://tcdb.uk${path}`, {
    method,
    headers,
    body: body ? JSON.stringify(body) : null
  });
}

describe('API Authentication', () => {
  it('should reject requests without API key', async () => {
    const request = createRequest('/api/v1/health', 'GET', null, null);
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(401);
    const data = await response.json();
    expect(data.error).toContain('Unauthorized');
  });

  it('should reject requests with invalid API key', async () => {
    const request = createRequest('/api/v1/health', 'GET', null, 'invalid_key');
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(401);
  });

  it('should accept requests with valid API key', async () => {
    const request = createRequest('/api/v1/health', 'GET');
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(200);
  });
});

describe('Health Check Endpoint', () => {
  it('should return healthy status', async () => {
    const request = createRequest('/api/v1/health', 'GET');
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.status).toBe('healthy');
    expect(data.version).toBeDefined();
    expect(Array.isArray(data.endpoints)).toBe(true);
  });

  it('should list all available endpoints', async () => {
    const request = createRequest('/api/v1/health', 'GET');
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    const data = await response.json();
    expect(data.endpoints).toContain('/api/v1/topology/signature');
    expect(data.endpoints).toContain('/api/v1/provenance/track');
    expect(data.endpoints).toContain('/api/v1/data/proof');
    expect(data.endpoints).toContain('/api/v1/cross-domain/reason');
  });
});

describe('Topological Signature Endpoint', () => {
  it('should reject requests without data', async () => {
    const request = createRequest('/api/v1/topology/signature', 'POST', {});
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(400);
    const data = await response.json();
    expect(data.error).toContain('Invalid input');
  });

  it('should reject non-array data', async () => {
    const request = createRequest('/api/v1/topology/signature', 'POST', {
      data: "not an array"
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(400);
  });

  it('should compute signature for valid data', async () => {
    const request = createRequest('/api/v1/topology/signature', 'POST', {
      data: [1.0, 2.5, 3.2, 4.1, 5.0]
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.signature).toBeDefined();
    expect(data.signature.persistence_diagram).toBeDefined();
    expect(data.signature.betti_numbers).toBeDefined();
  });

  it('should use default method if not specified', async () => {
    const request = createRequest('/api/v1/topology/signature', 'POST', {
      data: [1, 2, 3]
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    const data = await response.json();
    expect(data.method).toBe('vietoris_rips');
  });

  it('should respect max_dimension parameter', async () => {
    const request = createRequest('/api/v1/topology/signature', 'POST', {
      data: [1, 2, 3],
      max_dimension: 3
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    const data = await response.json();
    expect(data.max_dimension).toBe(3);
  });

  it('should return correct data point count', async () => {
    const testData = [1, 2, 3, 4, 5, 6, 7, 8];
    const request = createRequest('/api/v1/topology/signature', 'POST', {
      data: testData
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    const data = await response.json();
    expect(data.data_points).toBe(testData.length);
  });
});

describe('Provenance Tracking Endpoint', () => {
  it('should reject requests without required fields', async () => {
    const request = createRequest('/api/v1/provenance/track', 'POST', {});
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(400);
    const data = await response.json();
    expect(data.error).toContain('Required');
  });

  it('should create provenance record with all fields', async () => {
    const request = createRequest('/api/v1/provenance/track', 'POST', {
      operation: 'test_operation',
      inputs: ['input1', 'input2'],
      outputs: ['output1']
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.provenance_id).toBeDefined();
    expect(data.record.operation).toBe('test_operation');
    expect(data.record.signature).toBeDefined();
  });

  it('should include metadata if provided', async () => {
    const metadata = { model: 'gpt-4', version: '1.0' };
    const request = createRequest('/api/v1/provenance/track', 'POST', {
      operation: 'inference',
      inputs: ['data'],
      outputs: ['result'],
      metadata
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    const data = await response.json();
    expect(data.record.metadata).toEqual(metadata);
  });

  it('should generate unique provenance IDs', async () => {
    const worker = await import('./api-worker.js');
    const body = {
      operation: 'test',
      inputs: ['a'],
      outputs: ['b']
    };
    
    const response1 = await worker.default.fetch(
      createRequest('/api/v1/provenance/track', 'POST', body),
      mockEnv
    );
    const response2 = await worker.default.fetch(
      createRequest('/api/v1/provenance/track', 'POST', body),
      mockEnv
    );
    
    const data1 = await response1.json();
    const data2 = await response2.json();
    
    expect(data1.provenance_id).not.toBe(data2.provenance_id);
  });
});

describe('Data Proof Endpoint', () => {
  it('should reject requests without data', async () => {
    const request = createRequest('/api/v1/data/proof', 'POST', {});
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(400);
  });

  it('should generate fingerprint for valid data', async () => {
    const request = createRequest('/api/v1/data/proof', 'POST', {
      data: ['item1', 'item2', 'item3']
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.fingerprint).toBeDefined();
    expect(typeof data.fingerprint).toBe('string');
  });

  it('should generate proof with correct structure', async () => {
    const request = createRequest('/api/v1/data/proof', 'POST', {
      data: ['a', 'b', 'c']
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    const data = await response.json();
    expect(data.proof.type).toBeDefined();
    expect(data.proof.root).toBeDefined();
    expect(data.proof.leaves).toBeDefined();
    expect(data.proof.total_leaves).toBe(3);
  });

  it('should use default proof type if not specified', async () => {
    const request = createRequest('/api/v1/data/proof', 'POST', {
      data: ['x', 'y']
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    const data = await response.json();
    expect(data.proof_type).toBe('membership');
  });
});

describe('Cross-Domain Reasoning Endpoint', () => {
  it('should reject requests without required fields', async () => {
    const request = createRequest('/api/v1/cross-domain/reason', 'POST', {
      domain_a: 'test'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(400);
  });

  it('should compute similarity for valid domains', async () => {
    const request = createRequest('/api/v1/cross-domain/reason', 'POST', {
      domain_a: 'neural_networks',
      domain_b: 'power_grids',
      data_a: [0.5, 0.8, 0.3],
      data_b: [0.6, 0.7, 0.4]
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.similarity_score).toBeDefined();
    expect(typeof data.similarity_score).toBe('number');
  });

  it('should return connections array', async () => {
    const request = createRequest('/api/v1/cross-domain/reason', 'POST', {
      domain_a: 'a',
      domain_b: 'b',
      data_a: [1, 2],
      data_b: [1, 2]
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    const data = await response.json();
    expect(Array.isArray(data.connections)).toBe(true);
    expect(data.connections.length).toBeGreaterThan(0);
  });

  it('should indicate transferability based on similarity', async () => {
    const request = createRequest('/api/v1/cross-domain/reason', 'POST', {
      domain_a: 'a',
      domain_b: 'b',
      data_a: [1, 2, 3],
      data_b: [1, 2, 3]
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    const data = await response.json();
    expect(typeof data.transferable).toBe('boolean');
  });
});

describe('CORS Support', () => {
  it('should handle OPTIONS preflight requests', async () => {
    const request = new Request('https://tcdb.uk/api/v1/health', {
      method: 'OPTIONS'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(200);
    expect(response.headers.get('Access-Control-Allow-Origin')).toBeDefined();
  });

  it('should include CORS headers in responses', async () => {
    const request = createRequest('/api/v1/health', 'GET');
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.headers.get('Access-Control-Allow-Origin')).toBe('*');
  });
});

describe('Error Handling', () => {
  it('should return 404 for unknown endpoints', async () => {
    const request = createRequest('/api/v1/unknown', 'GET');
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);
    
    expect(response.status).toBe(404);
    const data = await response.json();
    expect(data.error).toContain('not found');
  });

  it('should handle malformed JSON gracefully', async () => {
    const request = new Request('https://tcdb.uk/api/v1/topology/signature', {
      method: 'POST',
      headers: {
        'Authorization': 'Bearer tcdb_valid_key',
        'Content-Type': 'application/json'
      },
      body: 'invalid json{'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBeGreaterThanOrEqual(400);
  });
});

describe('Entropy Analysis Endpoint', () => {
  it('should compute Shannon entropy for probability distribution', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      data: [0.25, 0.25, 0.25, 0.25],
      analysis_type: 'shannon'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.result.shannon_entropy).toBeCloseTo(2.0, 1); // log2(4) = 2
    expect(data.result.normalized_entropy).toBeCloseTo(1.0, 1);
  });

  it('should compute Shannon entropy from count data', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      data: [1, 1, 1, 1, 2, 2, 2, 2],
      analysis_type: 'shannon'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.result.shannon_entropy).toBeCloseTo(1.0, 1); // Binary distribution
  });

  it('should compute topological entropy', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      data: [1.0, 2.0, 3.0, 4.0, 5.0],
      analysis_type: 'topological'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.result.persistence_entropy).toBeGreaterThan(0);
    expect(data.result.complexity_score).toBeGreaterThanOrEqual(0);
    expect(data.result.complexity_score).toBeLessThanOrEqual(1);
  });

  it('should compute provenance entropy', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      data: {
        operations: [
          { type: 'generation' },
          { type: 'retrieval' },
          { type: 'generation' },
          { type: 'transformation' }
        ]
      },
      analysis_type: 'provenance'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.result.operation_entropy).toBeGreaterThan(0);
    expect(data.result.operation_types).toBe(3);
  });

  it('should compute dataset entropy', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      data: [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0],
      analysis_type: 'dataset'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.result.dataset_entropy).toBeGreaterThan(0);
    expect(data.result.optimal_proof_bits).toBeGreaterThan(0);
  });

  it('should run comprehensive entropy analysis', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      data: [1.0, 2.0, 3.0, 4.0, 5.0],
      analysis_type: 'comprehensive'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.success).toBe(true);
    expect(data.result.shannon).toBeDefined();
    expect(data.result.topological).toBeDefined();
    expect(data.result.dataset).toBeDefined();
  });

  it('should reject invalid analysis type', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      data: [1, 2, 3],
      analysis_type: 'invalid_type'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(400);
    const data = await response.json();
    expect(data.error).toContain('Unknown analysis type');
  });

  it('should reject missing data', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      analysis_type: 'shannon'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(400);
    const data = await response.json();
    expect(data.error).toContain('Required: data');
  });

  it('should include interpretation in results', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      data: [0.5, 0.5],
      analysis_type: 'shannon'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.result.interpretation).toBeDefined();
    expect(typeof data.result.interpretation).toBe('string');
  });

  it('should handle zero entropy case', async () => {
    const request = createRequest('/api/v1/entropy/analyze', 'POST', {
      data: [1.0], // Single probability = deterministic
      analysis_type: 'shannon'
    });
    const worker = await import('./api-worker.js');
    const response = await worker.default.fetch(request, mockEnv);

    expect(response.status).toBe(200);
    const data = await response.json();
    expect(data.result.shannon_entropy).toBe(0);
  });
});

