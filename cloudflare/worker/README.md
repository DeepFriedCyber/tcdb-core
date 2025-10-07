# TCDB Edge Worker

Cloudflare Worker that provides:
- **HMAC request signing** - Adds `x-signature` header for request authentication
- **Rate limiting** - 300 requests/minute per API key using Durable Objects
- **CORS handling** - Automatic CORS headers for browser requests
- **Request proxying** - Forwards to origin FastAPI server

## Architecture

```
Client → Cloudflare Edge → HMAC + Rate Limit → Origin FastAPI Server
```

**Benefits:**
- ⚡ **Global edge deployment** - Low latency worldwide
- 🔒 **Edge-level security** - HMAC signing before reaching origin
- 🚦 **Distributed rate limiting** - Durable Objects track per-key limits
- 🌍 **CORS handling** - Automatic preflight responses

## Setup

### 1. Install Dependencies

```bash
cd cloudflare/worker
npm install
```

### 2. Build TypeScript

```bash
npm run build
```

This compiles `src/index.ts` → `dist/index.js`

### 3. Run Tests

```bash
npm test
```

Tests use **Miniflare** to simulate the Cloudflare Workers environment locally.

### 4. Local Development

```bash
npm run dev
```

Starts local development server with hot reload.

## Configuration

### Environment Variables

Set in `wrangler.toml`:

```toml
[vars]
ORIGIN_URL = "https://api.tcdb.uk"  # Your FastAPI backend
```

### Secrets

Set via Wrangler CLI (not in wrangler.toml):

```bash
wrangler secret put EDGE_HMAC_SECRET
# Enter your secret when prompted
```

## Deployment

### Deploy to Cloudflare

```bash
wrangler deploy
```

### Set Production Secret

```bash
wrangler secret put EDGE_HMAC_SECRET --env production
```

### Configure Routes

Uncomment routes in `wrangler.toml`:

```toml
[[routes]]
pattern = "tcdb.uk/api/*"
zone_name = "tcdb.uk"
```

## API Usage

### With API Key

```bash
curl -X POST "https://tcdb.uk/api/evidence/certificate?k=YOUR_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"data_cid": "cid:test", "code_rev": "v1.0", "pd": [[0.1, 0.9]]}'
```

### Rate Limit Headers

Response includes:
- `x-ratelimit-limit: 300` - Max requests per window
- `x-ratelimit-remaining: 295` - Remaining requests
- `x-ratelimit-reset: 1234567890` - Unix timestamp when limit resets

### Rate Limit Exceeded

```json
{
  "error": "Rate limit exceeded",
  "limit": 300,
  "window": 60,
  "current": 301
}
```

## Testing

### Test Structure

```
test/
  worker.spec.ts  - Main worker tests
```

### Test Coverage

- ✅ HMAC signature generation
- ✅ Rate limiting per API key
- ✅ Request proxying to origin
- ✅ CORS header injection

### Run Tests

```bash
# Run all tests
npm test

# Run with coverage
npm test -- --coverage

# Watch mode
npm test -- --watch
```

## How It Works

### 1. HMAC Signing

```typescript
// Compute HMAC-SHA256 of request body
const signature = await computeHMAC(env.EDGE_HMAC_SECRET, body);

// Add to forwarded request
headers["x-signature"] = signature;
```

Origin can verify:
```python
import hmac
import hashlib

def verify_signature(body: bytes, signature: str, secret: str) -> bool:
    expected = hmac.new(
        secret.encode(),
        body,
        hashlib.sha256
    ).hexdigest()
    return hmac.compare_digest(expected, signature)
```

### 2. Rate Limiting

Uses **Durable Objects** for distributed state:

```typescript
// Get Durable Object for this API key
const id = env.RATE_DO.idFromName(apiKey);
const stub = env.RATE_DO.get(id);

// Check rate limit
const response = await stub.fetch(url);
```

Each API key gets its own Durable Object instance that tracks requests in a sliding window.

### 3. Request Flow

```
1. Client sends request with ?k=API_KEY
2. Worker checks rate limit (Durable Object)
3. If allowed, compute HMAC signature
4. Forward to origin with x-signature header
5. Return response with CORS + rate limit headers
```

## Development

### Project Structure

```
cloudflare/worker/
├── src/
│   └── index.ts          # Main worker code
├── test/
│   └── worker.spec.ts    # Vitest tests
├── dist/                 # Compiled output (gitignored)
├── package.json          # Dependencies
├── tsconfig.json         # TypeScript config
├── vitest.config.ts      # Test config
└── wrangler.toml         # Cloudflare config
```

### TypeScript Configuration

- **Target:** ES2022
- **Module:** ES2022
- **Strict mode:** Enabled
- **Types:** @cloudflare/workers-types

### Adding New Features

1. Edit `src/index.ts`
2. Add tests in `test/worker.spec.ts`
3. Run `npm run build && npm test`
4. Deploy with `wrangler deploy`

## Monitoring

### Cloudflare Dashboard

View metrics at:
- https://dash.cloudflare.com/

Metrics include:
- Requests per second
- Error rate
- CPU time
- Durable Object usage

### Logs

View real-time logs:

```bash
wrangler tail
```

## Troubleshooting

### Build Errors

```bash
# Clean and rebuild
rm -rf dist node_modules
npm install
npm run build
```

### Test Failures

```bash
# Ensure build is up to date
npm run build
npm test
```

### Deployment Issues

```bash
# Check wrangler auth
wrangler whoami

# Login if needed
wrangler login
```

## Performance

- **Cold start:** ~5ms
- **HMAC computation:** ~1ms
- **Rate limit check:** ~2ms (Durable Object)
- **Total overhead:** ~8ms

## Security

- ✅ HMAC-SHA256 request signing
- ✅ Per-key rate limiting
- ✅ Secrets stored in Cloudflare (not in code)
- ✅ CORS protection
- ✅ IP forwarding headers

## License

MIT

