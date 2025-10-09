# Cloudflare Deployment Guide 🚀

## Overview

TCDB Core can be deployed to Cloudflare in multiple ways:

1. **Edge Proxy** (Recommended) - Cloudflare Worker proxies to your FastAPI origin
2. **Cloudflare Pages** - Static frontend with serverless functions
3. **Hybrid** - Pages for frontend, Worker for API proxy

## Option 1: Edge Proxy (Recommended) ⭐

This is the **current setup** - a Cloudflare Worker that:
- ✅ Adds HMAC signatures for security
- ✅ Rate limits requests (300/min per API key)
- ✅ Proxies to your FastAPI origin server
- ✅ Adds CORS headers
- ✅ Global edge caching

### Prerequisites

```bash
# Install Wrangler CLI
npm install -g wrangler

# Login to Cloudflare
wrangler login
```

### Step 1: Configure Origin Server

You need a publicly accessible FastAPI server. Options:

**A. Deploy FastAPI to a VPS/Cloud**
```bash
# Example: Deploy to DigitalOcean, AWS, GCP, etc.
# Your origin URL: https://api.tcdb.uk
```

**B. Use Cloudflare Tunnel (Free!)**
```bash
# Install cloudflared
# Download from: https://developers.cloudflare.com/cloudflare-one/connections/connect-apps/install-and-setup/installation/

# Create tunnel
cloudflared tunnel create tcdb-api

# Configure tunnel
cat > ~/.cloudflared/config.yml << EOF
tunnel: <TUNNEL_ID>
credentials-file: /path/to/<TUNNEL_ID>.json

ingress:
  - hostname: api.tcdb.uk
    service: http://localhost:8000
  - service: http_status:404
EOF

# Run tunnel
cloudflared tunnel run tcdb-api
```

### Step 2: Update Worker Configuration

Edit `cloudflare/worker/wrangler.toml`:

```toml
name = "tcdb-edge"
main = "dist/index.js"
compatibility_date = "2024-01-01"

[vars]
ORIGIN_URL = "https://api.tcdb.uk"  # Your origin server

# Uncomment to map to your domain
[[routes]]
pattern = "tcdb.uk/api/*"
zone_name = "tcdb.uk"
```

### Step 3: Set Secrets

```bash
cd cloudflare/worker

# Set HMAC secret for request signing
wrangler secret put EDGE_HMAC_SECRET
# Enter a strong random secret when prompted
```

### Step 4: Build and Deploy

```bash
cd cloudflare/worker

# Install dependencies
npm install

# Build TypeScript
npm run build

# Deploy to Cloudflare
wrangler deploy
```

### Step 5: Test Deployment

```bash
# Test the worker
curl https://tcdb-edge.<your-subdomain>.workers.dev/api/v1/health

# Or with your custom domain
curl https://tcdb.uk/api/v1/health
```

### Step 6: Update FastAPI to Verify HMAC

Add HMAC verification middleware to `python/tcdb_api/middleware.py`:

```python
from fastapi import Request, HTTPException
import hmac
import hashlib
import os

EDGE_HMAC_SECRET = os.getenv("EDGE_HMAC_SECRET", "")

async def verify_edge_signature(request: Request, call_next):
    """Verify HMAC signature from edge worker"""
    if not EDGE_HMAC_SECRET:
        return await call_next(request)
    
    signature = request.headers.get("x-signature", "")
    if not signature:
        raise HTTPException(401, "Missing edge signature")
    
    body = await request.body()
    expected = hmac.new(
        EDGE_HMAC_SECRET.encode(),
        body,
        hashlib.sha256
    ).hexdigest()
    
    if not hmac.compare_digest(signature, expected):
        raise HTTPException(401, "Invalid edge signature")
    
    return await call_next(request)
```

## Option 2: Cloudflare Pages (Static Frontend)

Deploy the homepage and static assets to Cloudflare Pages.

### Step 1: Create Pages Project

```bash
# Install Wrangler
npm install -g wrangler

# Create a new Pages project
wrangler pages project create tcdb-core
```

### Step 2: Build Static Site

Create a static build of the homepage:

```bash
# Create static directory
mkdir -p static-build

# Copy templates and static files
cp -r python/tcdb_api/templates/* static-build/
cp -r python/tcdb_api/static static-build/

# Convert Jinja2 templates to static HTML
# (You'll need to render templates server-side first)
```

### Step 3: Deploy to Pages

```bash
# Deploy to Cloudflare Pages
wrangler pages deploy static-build --project-name tcdb-core
```

### Step 4: Configure Custom Domain

```bash
# Add custom domain
wrangler pages deployment create tcdb-core --branch main
```

## Option 3: Hybrid Deployment (Best of Both)

Combine Pages for frontend and Worker for API:

```
Frontend (Pages):     https://tcdb.uk
API (Worker Proxy):   https://api.tcdb.uk
Origin (FastAPI):     https://origin.tcdb.uk (via Tunnel)
```

### Architecture

```
User Request
    ↓
Cloudflare Pages (Frontend)
    ↓ (API calls)
Cloudflare Worker (Edge Proxy)
    ↓ (HMAC signed)
Cloudflare Tunnel
    ↓
FastAPI Origin (Your Server)
```

### Benefits

✅ **Global CDN** - Static assets served from edge  
✅ **Rate Limiting** - 300 req/min per API key  
✅ **HMAC Security** - Signed requests  
✅ **DDoS Protection** - Cloudflare's network  
✅ **Zero Cold Starts** - Always warm  
✅ **Free Tier** - 100k requests/day  

## Quick Deploy Script

Create `deploy.sh`:

```bash
#!/bin/bash

echo "🚀 Deploying TCDB Core to Cloudflare"

# 1. Build worker
echo "📦 Building edge worker..."
cd cloudflare/worker
npm install
npm run build

# 2. Deploy worker
echo "🌍 Deploying worker..."
wrangler deploy

# 3. Test deployment
echo "✅ Testing deployment..."
curl https://tcdb-edge.<your-subdomain>.workers.dev/descriptor/health

echo "🎉 Deployment complete!"
```

## Environment Variables

Set these in Cloudflare dashboard or via Wrangler:

```bash
# Required
wrangler secret put EDGE_HMAC_SECRET

# Optional
wrangler secret put DATABASE_URL
wrangler secret put JWT_SECRET
```

## Monitoring

### View Logs

```bash
# Tail worker logs
wrangler tail

# View analytics
wrangler pages deployment list
```

### Metrics

Cloudflare Dashboard shows:
- Request count
- Error rate
- Response time
- Bandwidth usage
- Cache hit ratio

## Cost Estimate

### Free Tier (Generous!)

- **Workers**: 100,000 requests/day
- **Pages**: Unlimited requests
- **Bandwidth**: 100 GB/month
- **Durable Objects**: 1 million reads/day

### Paid Plan ($5/month)

- **Workers**: 10 million requests/month
- **Bandwidth**: Unlimited
- **Durable Objects**: Unlimited

## Current Setup Status

✅ Worker code ready (`cloudflare/worker/src/index.ts`)  
✅ Rate limiting with Durable Objects  
✅ HMAC signing implemented  
✅ CORS headers configured  
⏳ Origin server needed (use Cloudflare Tunnel)  
⏳ Custom domain configuration  
⏳ Secrets configuration  

## Next Steps

1. **Set up origin server**:
   - Option A: Deploy FastAPI to VPS
   - Option B: Use Cloudflare Tunnel (free!)

2. **Configure domain**:
   ```bash
   # Add DNS records in Cloudflare dashboard
   A    api.tcdb.uk    → <worker-ip>
   CNAME www.tcdb.uk   → tcdb.uk
   ```

3. **Deploy worker**:
   ```bash
   cd cloudflare/worker
   npm install
   npm run build
   wrangler deploy
   ```

4. **Test**:
   ```bash
   curl https://api.tcdb.uk/descriptor/health
   ```

## Troubleshooting

### Worker not deploying

```bash
# Check wrangler version
wrangler --version

# Update wrangler
npm install -g wrangler@latest

# Check authentication
wrangler whoami
```

### Origin connection issues

```bash
# Test origin directly
curl https://api.tcdb.uk/api/v1/health

# Check tunnel status
cloudflared tunnel info tcdb-api
```

### Rate limiting not working

```bash
# Check Durable Objects binding
wrangler tail

# Verify DO is created
wrangler durable-objects list
```

## Resources

- [Cloudflare Workers Docs](https://developers.cloudflare.com/workers/)
- [Cloudflare Pages Docs](https://developers.cloudflare.com/pages/)
- [Cloudflare Tunnel Docs](https://developers.cloudflare.com/cloudflare-one/connections/connect-apps/)
- [Wrangler CLI Docs](https://developers.cloudflare.com/workers/wrangler/)

## Summary

**Recommended Approach**: Edge Proxy with Cloudflare Tunnel

1. ✅ Run FastAPI locally or on VPS
2. ✅ Expose via Cloudflare Tunnel (free!)
3. ✅ Deploy Worker as edge proxy
4. ✅ Configure custom domain
5. ✅ Enjoy global edge deployment!

**Total Cost**: $0 (Free tier) or $5/month (Paid)

---

Ready to deploy? Run:

```bash
cd cloudflare/worker
npm install
npm run build
wrangler deploy
```

🚀 **Your API will be live on Cloudflare's global edge network!**

