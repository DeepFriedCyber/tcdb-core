/**
 * TCDB API Worker
 * Exposes TCDB functionality via REST API with API key authentication
 */

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    const path = url.pathname;

    // CORS headers
    const corsHeaders = {
      'Access-Control-Allow-Origin': '*',
      'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
      'Access-Control-Allow-Headers': 'Content-Type, Authorization',
    };

    // Handle CORS preflight
    if (request.method === 'OPTIONS') {
      return new Response(null, { headers: corsHeaders });
    }

    // Validate API key for all API endpoints
    const apiKey = await validateApiKey(request, env);
    if (!apiKey) {
      return jsonResponse({ error: 'Unauthorized. Please provide a valid API key.' }, 401, corsHeaders);
    }

    // Track usage
    await trackUsage(apiKey.email, path, env);

    // Route to appropriate handler
    if (path === '/api/v1/topology/signature' && request.method === 'POST') {
      return handleTopologySignature(request, env, corsHeaders);
    }

    if (path === '/api/v1/provenance/track' && request.method === 'POST') {
      return handleProvenanceTrack(request, env, corsHeaders);
    }

    if (path === '/api/v1/data/proof' && request.method === 'POST') {
      return handleDataProof(request, env, corsHeaders);
    }

    if (path === '/api/v1/cross-domain/reason' && request.method === 'POST') {
      return handleCrossDomainReason(request, env, corsHeaders);
    }

    if (path === '/api/v1/health' && request.method === 'GET') {
      return jsonResponse({ 
        status: 'healthy',
        version: '1.0.0',
        endpoints: [
          '/api/v1/topology/signature',
          '/api/v1/provenance/track',
          '/api/v1/data/proof',
          '/api/v1/cross-domain/reason'
        ]
      }, 200, corsHeaders);
    }

    return jsonResponse({ error: 'Endpoint not found' }, 404, corsHeaders);
  }
};

// Validate API key
async function validateApiKey(request, env) {
  const authHeader = request.headers.get('Authorization');
  
  if (!authHeader || !authHeader.startsWith('Bearer ')) {
    return null;
  }

  const apiKey = authHeader.substring(7);
  
  // Check if API key exists in KV
  const email = await env.API_KEYS.get(`key:${apiKey}`);
  
  if (!email) {
    return null;
  }

  return { apiKey, email };
}

// Track API usage
async function trackUsage(email, endpoint, env) {
  const today = new Date().toISOString().split('T')[0];
  const usageKey = `usage:${email}:${today}`;
  
  // Get current usage
  const currentUsage = await env.USAGE.get(usageKey);
  const usage = currentUsage ? JSON.parse(currentUsage) : { total: 0, endpoints: {} };
  
  // Increment counters
  usage.total += 1;
  usage.endpoints[endpoint] = (usage.endpoints[endpoint] || 0) + 1;
  
  // Store back with 30 day expiration
  await env.USAGE.put(usageKey, JSON.stringify(usage), {
    expirationTtl: 30 * 24 * 60 * 60
  });
}

// Handler: Topological Signature
async function handleTopologySignature(request, env, corsHeaders) {
  try {
    const { data, method = 'vietoris_rips', max_dimension = 2 } = await request.json();

    if (!data || !Array.isArray(data)) {
      return jsonResponse({ error: 'Invalid input. Expected array of numbers.' }, 400, corsHeaders);
    }

    // Simulate topological signature computation
    // In production, this would call your Rust/Python TCDB code
    const signature = await computeTopologicalSignature(data, method, max_dimension);

    return jsonResponse({
      success: true,
      signature,
      method,
      max_dimension,
      data_points: data.length
    }, 200, corsHeaders);

  } catch (error) {
    return jsonResponse({ error: error.message }, 500, corsHeaders);
  }
}

// Handler: Provenance Tracking
async function handleProvenanceTrack(request, env, corsHeaders) {
  try {
    const { operation, inputs, outputs, metadata = {} } = await request.json();

    if (!operation || !inputs || !outputs) {
      return jsonResponse({ 
        error: 'Invalid input. Required: operation, inputs, outputs' 
      }, 400, corsHeaders);
    }

    // Create provenance record
    const provenanceId = crypto.randomUUID();
    const timestamp = Date.now();

    const provenanceRecord = {
      id: provenanceId,
      operation,
      inputs,
      outputs,
      metadata,
      timestamp,
      signature: await generateProvenanceSignature(operation, inputs, outputs, timestamp)
    };

    // Store in KV
    await env.PROVENANCE.put(`prov:${provenanceId}`, JSON.stringify(provenanceRecord));

    return jsonResponse({
      success: true,
      provenance_id: provenanceId,
      record: provenanceRecord
    }, 200, corsHeaders);

  } catch (error) {
    return jsonResponse({ error: error.message }, 500, corsHeaders);
  }
}

// Handler: Data Proof
async function handleDataProof(request, env, corsHeaders) {
  try {
    const { data, proof_type = 'membership' } = await request.json();

    if (!data || !Array.isArray(data)) {
      return jsonResponse({ error: 'Invalid input. Expected array of data.' }, 400, corsHeaders);
    }

    // Generate data fingerprint and proof
    const fingerprint = await generateDataFingerprint(data);
    const proof = await generateDataProof(data, proof_type);

    return jsonResponse({
      success: true,
      fingerprint,
      proof_type,
      proof,
      data_size: data.length
    }, 200, corsHeaders);

  } catch (error) {
    return jsonResponse({ error: error.message }, 500, corsHeaders);
  }
}

// Handler: Cross-Domain Reasoning
async function handleCrossDomainReason(request, env, corsHeaders) {
  try {
    const { domain_a, domain_b, data_a, data_b } = await request.json();

    if (!domain_a || !domain_b || !data_a || !data_b) {
      return jsonResponse({ 
        error: 'Invalid input. Required: domain_a, domain_b, data_a, data_b' 
      }, 400, corsHeaders);
    }

    // Compute cross-domain similarity
    const similarity = await computeCrossDomainSimilarity(data_a, data_b);
    const connections = await discoverConnections(domain_a, domain_b, similarity);

    return jsonResponse({
      success: true,
      domain_a,
      domain_b,
      similarity_score: similarity,
      connections,
      transferable: similarity > 0.7
    }, 200, corsHeaders);

  } catch (error) {
    return jsonResponse({ error: error.message }, 500, corsHeaders);
  }
}

// Compute topological signature (simplified version)
async function computeTopologicalSignature(data, method, maxDimension) {
  // This is a simplified simulation
  // In production, you'd call your actual Rust/Python TCDB code
  
  // Compute basic statistics
  const mean = data.reduce((a, b) => a + b, 0) / data.length;
  const variance = data.reduce((a, b) => a + Math.pow(b - mean, 2), 0) / data.length;
  
  // Simulate persistence diagram
  const persistenceDiagram = [];
  for (let dim = 0; dim <= maxDimension; dim++) {
    const numFeatures = Math.floor(Math.random() * 5) + 1;
    for (let i = 0; i < numFeatures; i++) {
      persistenceDiagram.push({
        dimension: dim,
        birth: Math.random() * variance,
        death: Math.random() * variance + variance
      });
    }
  }

  // Compute Betti numbers
  const bettiNumbers = {};
  for (let dim = 0; dim <= maxDimension; dim++) {
    bettiNumbers[`H${dim}`] = persistenceDiagram.filter(f => f.dimension === dim).length;
  }

  return {
    method,
    persistence_diagram: persistenceDiagram,
    betti_numbers: bettiNumbers,
    statistics: { mean, variance }
  };
}

// Generate provenance signature
async function generateProvenanceSignature(operation, inputs, outputs, timestamp) {
  const data = JSON.stringify({ operation, inputs, outputs, timestamp });
  const encoder = new TextEncoder();
  const dataBuffer = encoder.encode(data);
  const hashBuffer = await crypto.subtle.digest('SHA-256', dataBuffer);
  const hashArray = Array.from(new Uint8Array(hashBuffer));
  return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
}

// Generate data fingerprint
async function generateDataFingerprint(data) {
  const dataString = JSON.stringify(data);
  const encoder = new TextEncoder();
  const dataBuffer = encoder.encode(dataString);
  const hashBuffer = await crypto.subtle.digest('SHA-256', dataBuffer);
  const hashArray = Array.from(new Uint8Array(hashBuffer));
  return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
}

// Generate data proof
async function generateDataProof(data, proofType) {
  // Simplified Merkle tree proof
  const leaves = [];
  for (const item of data) {
    const hash = await generateDataFingerprint([item]);
    leaves.push(hash);
  }

  return {
    type: proofType,
    root: await generateDataFingerprint(leaves),
    leaves: leaves.slice(0, 3), // Sample
    total_leaves: leaves.length
  };
}

// Compute cross-domain similarity
async function computeCrossDomainSimilarity(dataA, dataB) {
  // Simplified cosine similarity
  const dotProduct = dataA.reduce((sum, val, i) => sum + val * (dataB[i] || 0), 0);
  const magnitudeA = Math.sqrt(dataA.reduce((sum, val) => sum + val * val, 0));
  const magnitudeB = Math.sqrt(dataB.reduce((sum, val) => sum + val * val, 0));
  
  return dotProduct / (magnitudeA * magnitudeB);
}

// Discover connections
async function discoverConnections(domainA, domainB, similarity) {
  return [
    {
      type: 'topological_similarity',
      strength: similarity,
      description: `${domainA} and ${domainB} share similar topological structures`
    },
    {
      type: 'principle_transfer',
      applicable: similarity > 0.7,
      description: similarity > 0.7 
        ? `Principles from ${domainA} can be transferred to ${domainB}`
        : `Similarity too low for reliable principle transfer`
    }
  ];
}

// Helper function
function jsonResponse(data, status, corsHeaders) {
  return new Response(JSON.stringify(data), {
    status,
    headers: {
      'Content-Type': 'application/json',
      ...corsHeaders
    }
  });
}

