/**
 * TCDB Edge Worker
 * 
 * Cloudflare Worker that:
 * 1. Adds HMAC signature to requests (x-signature header)
 * 2. Rate limits requests per API key
 * 3. Proxies to origin FastAPI server
 */

export interface Env {
  ORIGIN_URL: string;
  EDGE_HMAC_SECRET: string;
  RATE_DO: DurableObjectNamespace;
}

/**
 * Durable Object for rate limiting
 * Tracks requests per API key with sliding window
 */
export class RateLimiter {
  private state: DurableObjectState;
  private requests: Map<string, number[]>;

  constructor(state: DurableObjectState, env: Env) {
    this.state = state;
    this.requests = new Map();
  }

  async fetch(request: Request): Promise<Response> {
    const url = new URL(request.url);
    const key = url.searchParams.get("key") || "anonymous";
    const limit = parseInt(url.searchParams.get("limit") || "300");
    const window = parseInt(url.searchParams.get("window") || "60"); // seconds

    // Get current timestamp
    const now = Date.now();
    const windowMs = window * 1000;

    // Get or create request log for this key
    let log = this.requests.get(key) || [];
    
    // Remove requests outside the window
    log = log.filter(timestamp => now - timestamp < windowMs);
    
    // Check if limit exceeded
    if (log.length >= limit) {
      return new Response(JSON.stringify({
        allowed: false,
        limit,
        window,
        current: log.length
      }), {
        status: 429,
        headers: { "content-type": "application/json" }
      });
    }

    // Add current request
    log.push(now);
    this.requests.set(key, log);

    return new Response(JSON.stringify({
      allowed: true,
      limit,
      window,
      current: log.length
    }), {
      headers: { "content-type": "application/json" }
    });
  }
}

/**
 * Compute HMAC-SHA256 signature
 */
async function computeHMAC(secret: string, message: string): Promise<string> {
  const encoder = new TextEncoder();
  const keyData = encoder.encode(secret);
  const messageData = encoder.encode(message);

  const key = await crypto.subtle.importKey(
    "raw",
    keyData,
    { name: "HMAC", hash: "SHA-256" },
    false,
    ["sign"]
  );

  const signature = await crypto.subtle.sign("HMAC", key, messageData);
  
  // Convert to hex string
  return Array.from(new Uint8Array(signature))
    .map(b => b.toString(16).padStart(2, "0"))
    .join("");
}

/**
 * Check rate limit for API key
 */
async function checkRateLimit(
  env: Env,
  apiKey: string,
  limit: number = 300,
  window: number = 60
): Promise<{ allowed: boolean; current: number }> {
  // Get Durable Object ID for this API key
  const id = env.RATE_DO.idFromName(apiKey);
  const stub = env.RATE_DO.get(id);

  // Call the Durable Object
  const url = `https://rate-limiter/?key=${apiKey}&limit=${limit}&window=${window}`;
  const response = await stub.fetch(url);
  const data = await response.json() as any;

  return {
    allowed: data.allowed,
    current: data.current
  };
}

/**
 * Main worker handler
 */
export default {
  async fetch(request: Request, env: Env, ctx: ExecutionContext): Promise<Response> {
    const url = new URL(request.url);
    
    // Extract API key from query parameter
    const apiKey = url.searchParams.get("k") || "anonymous";

    // Check rate limit (300 requests per minute per key)
    const rateLimit = await checkRateLimit(env, apiKey, 300, 60);
    
    if (!rateLimit.allowed) {
      return new Response(JSON.stringify({
        error: "Rate limit exceeded",
        limit: 300,
        window: 60,
        current: rateLimit.current
      }), {
        status: 429,
        headers: {
          "content-type": "application/json",
          "x-ratelimit-limit": "300",
          "x-ratelimit-remaining": String(Math.max(0, 300 - rateLimit.current)),
          "x-ratelimit-reset": String(Math.floor(Date.now() / 1000) + 60)
        }
      });
    }

    // Read request body for HMAC signing
    const body = await request.text();

    // Compute HMAC signature if secret is configured
    let signature = "";
    if (env.EDGE_HMAC_SECRET) {
      signature = await computeHMAC(env.EDGE_HMAC_SECRET, body);
    }

    // Build origin URL
    const originUrl = new URL(url.pathname + url.search, env.ORIGIN_URL);

    // Forward request to origin with HMAC signature
    const originRequest = new Request(originUrl.toString(), {
      method: request.method,
      headers: {
        ...Object.fromEntries(request.headers),
        "x-signature": signature,
        "x-api-key": apiKey,
        "x-forwarded-for": request.headers.get("cf-connecting-ip") || "",
        "x-real-ip": request.headers.get("cf-connecting-ip") || ""
      },
      body: body || undefined
    });

    // Fetch from origin
    const response = await fetch(originRequest);

    // Add CORS headers
    const corsHeaders = {
      "access-control-allow-origin": "*",
      "access-control-allow-methods": "GET, POST, PUT, DELETE, OPTIONS",
      "access-control-allow-headers": "content-type, x-api-key",
      "access-control-max-age": "86400"
    };

    // Handle OPTIONS preflight
    if (request.method === "OPTIONS") {
      return new Response(null, {
        status: 204,
        headers: corsHeaders
      });
    }

    // Return response with CORS headers
    return new Response(response.body, {
      status: response.status,
      statusText: response.statusText,
      headers: {
        ...Object.fromEntries(response.headers),
        ...corsHeaders,
        "x-ratelimit-limit": "300",
        "x-ratelimit-remaining": String(Math.max(0, 300 - rateLimit.current))
      }
    });
  }
};

