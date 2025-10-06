/**
 * Cloudflare Workers Auth Handler
 * Simple email-based authentication with API key generation
 */

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    const path = url.pathname;

    // CORS headers
    const corsHeaders = {
      'Access-Control-Allow-Origin': 'https://tcdb.uk',
      'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
      'Access-Control-Allow-Headers': 'Content-Type, Authorization',
    };

    // Handle CORS preflight
    if (request.method === 'OPTIONS') {
      return new Response(null, { headers: corsHeaders });
    }

    // Routes
    if (path === '/api/auth/signup' && request.method === 'POST') {
      return handleSignup(request, env, corsHeaders);
    }

    if (path === '/api/auth/login' && request.method === 'POST') {
      return handleLogin(request, env, corsHeaders);
    }

    if (path === '/api/auth/verify' && request.method === 'POST') {
      return handleVerify(request, env, corsHeaders);
    }

    if (path === '/api/keys' && request.method === 'GET') {
      return handleGetKeys(request, env, corsHeaders);
    }

    if (path === '/api/keys/generate' && request.method === 'POST') {
      return handleGenerateKey(request, env, corsHeaders);
    }

    return new Response('Not Found', { status: 404 });
  }
};

// Sign up - send magic link
async function handleSignup(request, env, corsHeaders) {
  try {
    const { email } = await request.json();

    if (!email || !isValidEmail(email)) {
      return jsonResponse({ error: 'Invalid email' }, 400, corsHeaders);
    }

    // Generate verification token
    const token = await generateToken();
    const expiresAt = Date.now() + 15 * 60 * 1000; // 15 minutes

    // Store in KV
    await env.AUTH_TOKENS.put(`verify:${token}`, JSON.stringify({
      email,
      expiresAt,
      type: 'signup'
    }), { expirationTtl: 900 }); // 15 minutes

    // Send magic link email (using Cloudflare Email Workers or external service)
    const magicLink = `https://tcdb.uk/verify?token=${token}`;
    
    // For now, return the link (in production, send via email)
    return jsonResponse({
      success: true,
      message: 'Verification email sent',
      // Remove this in production:
      magicLink: magicLink
    }, 200, corsHeaders);

  } catch (error) {
    return jsonResponse({ error: 'Signup failed' }, 500, corsHeaders);
  }
}

// Login - send magic link
async function handleLogin(request, env, corsHeaders) {
  try {
    const { email } = await request.json();

    if (!email || !isValidEmail(email)) {
      return jsonResponse({ error: 'Invalid email' }, 400, corsHeaders);
    }

    // Check if user exists
    const userExists = await env.USERS.get(`user:${email}`);
    if (!userExists) {
      return jsonResponse({ error: 'User not found. Please sign up first.' }, 404, corsHeaders);
    }

    // Generate verification token
    const token = await generateToken();
    const expiresAt = Date.now() + 15 * 60 * 1000;

    await env.AUTH_TOKENS.put(`verify:${token}`, JSON.stringify({
      email,
      expiresAt,
      type: 'login'
    }), { expirationTtl: 900 });

    const magicLink = `https://tcdb.uk/verify?token=${token}`;

    return jsonResponse({
      success: true,
      message: 'Login link sent to your email',
      // Remove this in production:
      magicLink: magicLink
    }, 200, corsHeaders);

  } catch (error) {
    return jsonResponse({ error: 'Login failed' }, 500, corsHeaders);
  }
}

// Verify token and create session
async function handleVerify(request, env, corsHeaders) {
  try {
    const { token } = await request.json();

    // Get token data
    const tokenData = await env.AUTH_TOKENS.get(`verify:${token}`);
    if (!tokenData) {
      return jsonResponse({ error: 'Invalid or expired token' }, 401, corsHeaders);
    }

    const { email, expiresAt, type } = JSON.parse(tokenData);

    if (Date.now() > expiresAt) {
      return jsonResponse({ error: 'Token expired' }, 401, corsHeaders);
    }

    // Create or get user
    let user = await env.USERS.get(`user:${email}`);
    
    if (!user) {
      // Create new user
      const userId = crypto.randomUUID();
      const apiKey = await generateApiKey();
      
      user = JSON.stringify({
        id: userId,
        email,
        apiKey,
        createdAt: Date.now(),
        plan: 'free'
      });

      await env.USERS.put(`user:${email}`, user);
      await env.API_KEYS.put(`key:${apiKey}`, email);
    }

    const userData = JSON.parse(user);

    // Create session token
    const sessionToken = await generateToken();
    await env.SESSIONS.put(`session:${sessionToken}`, email, {
      expirationTtl: 7 * 24 * 60 * 60 // 7 days
    });

    // Delete verification token
    await env.AUTH_TOKENS.delete(`verify:${token}`);

    return jsonResponse({
      success: true,
      sessionToken,
      user: {
        email: userData.email,
        apiKey: userData.apiKey,
        plan: userData.plan
      }
    }, 200, corsHeaders);

  } catch (error) {
    return jsonResponse({ error: 'Verification failed' }, 500, corsHeaders);
  }
}

// Get user's API keys
async function handleGetKeys(request, env, corsHeaders) {
  try {
    const email = await authenticateRequest(request, env);
    if (!email) {
      return jsonResponse({ error: 'Unauthorized' }, 401, corsHeaders);
    }

    const user = await env.USERS.get(`user:${email}`);
    if (!user) {
      return jsonResponse({ error: 'User not found' }, 404, corsHeaders);
    }

    const userData = JSON.parse(user);

    return jsonResponse({
      apiKey: userData.apiKey,
      plan: userData.plan,
      createdAt: userData.createdAt
    }, 200, corsHeaders);

  } catch (error) {
    return jsonResponse({ error: 'Failed to get keys' }, 500, corsHeaders);
  }
}

// Generate new API key
async function handleGenerateKey(request, env, corsHeaders) {
  try {
    const email = await authenticateRequest(request, env);
    if (!email) {
      return jsonResponse({ error: 'Unauthorized' }, 401, corsHeaders);
    }

    const user = await env.USERS.get(`user:${email}`);
    if (!user) {
      return jsonResponse({ error: 'User not found' }, 404, corsHeaders);
    }

    const userData = JSON.parse(user);

    // Delete old API key
    await env.API_KEYS.delete(`key:${userData.apiKey}`);

    // Generate new API key
    const newApiKey = await generateApiKey();
    userData.apiKey = newApiKey;

    // Update user
    await env.USERS.put(`user:${email}`, JSON.stringify(userData));
    await env.API_KEYS.put(`key:${newApiKey}`, email);

    return jsonResponse({
      apiKey: newApiKey
    }, 200, corsHeaders);

  } catch (error) {
    return jsonResponse({ error: 'Failed to generate key' }, 500, corsHeaders);
  }
}

// Helper functions
async function authenticateRequest(request, env) {
  const authHeader = request.headers.get('Authorization');
  if (!authHeader || !authHeader.startsWith('Bearer ')) {
    return null;
  }

  const sessionToken = authHeader.substring(7);
  const email = await env.SESSIONS.get(`session:${sessionToken}`);
  
  return email;
}

async function generateToken() {
  const array = new Uint8Array(32);
  crypto.getRandomValues(array);
  return Array.from(array, byte => byte.toString(16).padStart(2, '0')).join('');
}

async function generateApiKey() {
  const prefix = 'tcdb';
  const array = new Uint8Array(24);
  crypto.getRandomValues(array);
  const random = Array.from(array, byte => byte.toString(16).padStart(2, '0')).join('');
  return `${prefix}_${random}`;
}

function isValidEmail(email) {
  return /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email);
}

function jsonResponse(data, status, corsHeaders) {
  return new Response(JSON.stringify(data), {
    status,
    headers: {
      'Content-Type': 'application/json',
      ...corsHeaders
    }
  });
}

