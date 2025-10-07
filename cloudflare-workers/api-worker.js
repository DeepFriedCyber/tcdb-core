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

    if (path === '/api/v1/entropy/analyze' && request.method === 'POST') {
      return handleEntropyAnalysis(request, env, corsHeaders);
    }

    if (path === '/api/v1/health' && request.method === 'GET') {
      return jsonResponse({
        status: 'healthy',
        version: '1.1.0',
        endpoints: [
          '/api/v1/topology/signature',
          '/api/v1/provenance/track',
          '/api/v1/data/proof',
          '/api/v1/cross-domain/reason',
          '/api/v1/entropy/analyze'
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

// Handler: Entropy Analysis
async function handleEntropyAnalysis(request, env, corsHeaders) {
  try {
    const {
      data,
      analysis_type = 'shannon',
      options = {}
    } = await request.json();

    if (!data) {
      return jsonResponse({
        error: 'Invalid input. Required: data (array or object)'
      }, 400, corsHeaders);
    }

    let result = {};

    // Handle different analysis types
    switch (analysis_type) {
      case 'shannon':
        result = await analyzeShannon(data, options);
        break;

      case 'topological':
        result = await analyzeTopologicalEntropy(data, options);
        break;

      case 'provenance':
        result = await analyzeProvenanceEntropy(data, options);
        break;

      case 'dataset':
        result = await analyzeDatasetEntropy(data, options);
        break;

      case 'comprehensive':
        // Run all analyses
        result = {
          shannon: await analyzeShannon(data, options),
          topological: await analyzeTopologicalEntropy(data, options),
          dataset: await analyzeDatasetEntropy(data, options)
        };
        break;

      default:
        return jsonResponse({
          error: `Unknown analysis type: ${analysis_type}. Valid types: shannon, topological, provenance, dataset, comprehensive`
        }, 400, corsHeaders);
    }

    return jsonResponse({
      success: true,
      analysis_type,
      result,
      timestamp: Date.now()
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

// Entropy Analysis Functions

// Shannon entropy analysis
async function analyzeShannon(data, options) {
  let probabilities = [];

  if (Array.isArray(data)) {
    // Convert data to probability distribution
    if (data.every(x => typeof x === 'number' && x >= 0 && x <= 1)) {
      // Already probabilities
      probabilities = data;
    } else {
      // Create histogram
      const counts = {};
      data.forEach(x => counts[x] = (counts[x] || 0) + 1);
      const total = data.length;
      probabilities = Object.values(counts).map(c => c / total);
    }
  } else if (typeof data === 'object') {
    // Assume object with counts
    const total = Object.values(data).reduce((a, b) => a + b, 0);
    probabilities = Object.values(data).map(c => c / total);
  }

  // Compute Shannon entropy
  const entropy = shannonEntropy(probabilities);
  const maxEntropy = Math.log2(probabilities.length);
  const normalized = maxEntropy > 0 ? entropy / maxEntropy : 0;

  return {
    shannon_entropy: entropy,
    max_entropy: maxEntropy,
    normalized_entropy: normalized,
    num_outcomes: probabilities.length,
    interpretation: interpretEntropy(normalized),
    optimal_encoding_bits: Math.ceil(entropy * data.length)
  };
}

// Topological entropy analysis
async function analyzeTopologicalEntropy(data, options) {
  if (!Array.isArray(data)) {
    throw new Error('Topological entropy requires array data');
  }

  // Compute persistence intervals (simplified)
  const intervals = [];
  for (let i = 0; i < data.length - 1; i++) {
    intervals.push(Math.abs(data[i+1] - data[i]));
  }

  const persistenceEntropy = persistenceEntropyCalc(intervals);

  // Simulate Betti numbers
  const bettiNumbers = [
    Math.floor(data.length / 3),
    Math.floor(data.length / 5),
    Math.floor(data.length / 10)
  ];

  const totalBetti = bettiNumbers.reduce((a, c) => a + c, 0);
  const bettiEntropy = totalBetti > 0
    ? shannonEntropy(bettiNumbers.map(b => b / totalBetti))
    : 0;

  // Normalize entropies
  const maxPersEntropy = intervals.length > 0 ? Math.log2(intervals.length) : 1;
  const maxBettiEntropy = bettiNumbers.length > 0 ? Math.log2(bettiNumbers.length) : 1;

  const normPers = maxPersEntropy > 0 ? persistenceEntropy / maxPersEntropy : 0;
  const normBetti = maxBettiEntropy > 0 ? bettiEntropy / maxBettiEntropy : 0;

  const complexity = (normPers + normBetti) / 2;

  return {
    persistence_entropy: persistenceEntropy,
    betti_entropy: bettiEntropy,
    complexity_score: Math.min(1.0, Math.max(0.0, complexity)),
    betti_numbers: bettiNumbers,
    interpretation: interpretComplexity(complexity)
  };
}

// Provenance entropy analysis
async function analyzeProvenanceEntropy(data, options) {
  if (!data.operations || !Array.isArray(data.operations)) {
    throw new Error('Provenance entropy requires operations array');
  }

  // Count operation types
  const opCounts = {};
  data.operations.forEach(op => {
    opCounts[op.type] = (opCounts[op.type] || 0) + 1;
  });

  const total = data.operations.length;
  const probabilities = Object.values(opCounts).map(c => c / total);

  const operationEntropy = shannonEntropy(probabilities);
  const maxOpEntropy = Math.log2(Object.keys(opCounts).length);

  return {
    operation_entropy: operationEntropy,
    max_operation_entropy: maxOpEntropy,
    normalized_entropy: maxOpEntropy > 0 ? operationEntropy / maxOpEntropy : 0,
    operation_types: Object.keys(opCounts).length,
    total_operations: total,
    interpretation: interpretDiversity(operationEntropy)
  };
}

// Dataset entropy analysis
async function analyzeDatasetEntropy(data, options) {
  if (!Array.isArray(data)) {
    throw new Error('Dataset entropy requires array data');
  }

  // Create histogram (10 bins)
  const bins = options.bins || 10;
  const min = Math.min(...data);
  const max = Math.max(...data);
  const binWidth = (max - min) / bins;

  const counts = new Array(bins).fill(0);
  data.forEach(value => {
    const bin = Math.min(Math.floor((value - min) / binWidth), bins - 1);
    counts[bin]++;
  });

  const probabilities = counts.map(c => c / data.length);
  const entropy = shannonEntropy(probabilities);
  const maxEntropy = Math.log2(bins);

  return {
    dataset_entropy: entropy,
    max_entropy: maxEntropy,
    normalized_entropy: maxEntropy > 0 ? entropy / maxEntropy : 0,
    bins: bins,
    data_points: data.length,
    optimal_proof_bits: Math.ceil(entropy * data.length),
    interpretation: interpretDataComplexity(entropy)
  };
}

// Core Shannon entropy calculation
function shannonEntropy(probabilities) {
  return probabilities
    .filter(p => p > 0)
    .reduce((sum, p) => sum - p * Math.log2(p), 0);
}

// Persistence entropy calculation
function persistenceEntropyCalc(intervals) {
  if (intervals.length === 0) return 0;
  const total = intervals.reduce((a, b) => a + b, 0);
  if (total === 0) return 0;
  const probabilities = intervals.map(i => i / total);
  return shannonEntropy(probabilities);
}

// Interpretation functions
function interpretEntropy(normalized) {
  if (normalized > 0.9) return 'Very high entropy - highly uniform distribution';
  if (normalized > 0.7) return 'High entropy - diverse distribution';
  if (normalized > 0.5) return 'Moderate entropy - some structure present';
  if (normalized > 0.3) return 'Low entropy - clear patterns';
  return 'Very low entropy - highly structured/deterministic';
}

function interpretComplexity(score) {
  if (score > 0.8) return 'Very complex topology with diverse features';
  if (score > 0.6) return 'Complex topology with multiple features';
  if (score > 0.4) return 'Moderate topological complexity';
  if (score > 0.2) return 'Simple topology with few features';
  return 'Very simple topology';
}

function interpretDiversity(entropy) {
  if (entropy > 2.0) return 'Highly diverse operations';
  if (entropy > 1.5) return 'Diverse operations';
  if (entropy > 1.0) return 'Moderate diversity';
  if (entropy > 0.5) return 'Low diversity';
  return 'Very low diversity - repetitive operations';
}

function interpretDataComplexity(entropy) {
  if (entropy > 3.0) return 'Highly complex data with diverse values';
  if (entropy > 2.0) return 'Complex data distribution';
  if (entropy > 1.0) return 'Moderate data complexity';
  if (entropy > 0.5) return 'Simple data distribution';
  return 'Very simple or uniform data';
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

