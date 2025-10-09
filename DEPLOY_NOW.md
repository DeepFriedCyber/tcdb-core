# Deploy TCDB Core to Cloudflare NOW! 🚀

## Quick Start (5 Minutes)

### Step 1: Install Wrangler

```bash
npm install -g wrangler
```

### Step 2: Login to Cloudflare

```bash
wrangler login
```

This will open your browser to authenticate.

### Step 3: Deploy!

**On Windows:**
```powershell
.\deploy-cloudflare.ps1
```

**On Mac/Linux:**
```bash
chmod +x deploy-cloudflare.sh
./deploy-cloudflare.sh
```

**Or manually:**
```bash
cd cloudflare/worker
npm install
npm run build
wrangler deploy
```

### Step 4: Test

```bash
# Your worker URL will be shown after deployment
curl https://tcdb-edge.<your-subdomain>.workers.dev/descriptor/health
```

## What Gets Deployed?

✅ **Edge Worker** - Cloudflare Worker with:
- Rate limiting (300 req/min per API key)
- HMAC request signing
- CORS headers
- Request proxying to origin

✅ **Durable Objects** - For distributed rate limiting

✅ **Global Edge Network** - Deployed to 300+ cities worldwide

## Current Configuration

The worker is configured to proxy to:
```
ORIGIN_URL = "https://api.tcdb.uk"
```

**You need to set up your origin server!**

## Option A: Use Cloudflare Tunnel (Recommended, Free!)

### 1. Install cloudflared

**Windows:**
```powershell
# Download from: https://github.com/cloudflare/cloudflared/releases
# Or use winget:
winget install --id Cloudflare.cloudflared
```

**Mac:**
```bash
brew install cloudflare/cloudflare/cloudflared
```

**Linux:**
```bash
wget https://github.com/cloudflare/cloudflared/releases/latest/download/cloudflared-linux-amd64.deb
sudo dpkg -i cloudflared-linux-amd64.deb
```

### 2. Authenticate

```bash
cloudflared tunnel login
```

### 3. Create Tunnel

```bash
cloudflared tunnel create tcdb-api
```

This creates a tunnel and gives you a tunnel ID.

### 4. Configure Tunnel

Create `~/.cloudflared/config.yml`:

```yaml
tunnel: <YOUR_TUNNEL_ID>
credentials-file: /path/to/<YOUR_TUNNEL_ID>.json

ingress:
  - hostname: api.tcdb.uk
    service: http://localhost:8000
  - service: http_status:404
```

### 5. Add DNS Record

```bash
cloudflared tunnel route dns tcdb-api api.tcdb.uk
```

### 6. Run Tunnel

```bash
# Start your FastAPI server
cd python
python -m uvicorn tcdb_api.app:app --host 0.0.0.0 --port 8000

# In another terminal, start tunnel
cloudflared tunnel run tcdb-api
```

### 7. Test

```bash
curl https://api.tcdb.uk/descriptor/health
```

## Option B: Deploy FastAPI to VPS

Deploy your FastAPI server to any cloud provider:

- **DigitalOcean** - $6/month droplet
- **AWS EC2** - Free tier available
- **Google Cloud** - Free tier available
- **Heroku** - Free tier (with limitations)
- **Railway** - Free tier available

Then update `wrangler.toml`:

```toml
[vars]
ORIGIN_URL = "https://your-server.com"
```

## Configure Secrets

```bash
cd cloudflare/worker

# Set HMAC secret for request signing
wrangler secret put EDGE_HMAC_SECRET
# Enter a strong random secret (e.g., generate with: openssl rand -hex 32)
```

## Configure Custom Domain

### 1. Add Domain to Cloudflare

1. Go to Cloudflare Dashboard
2. Add your domain (e.g., `tcdb.uk`)
3. Update nameservers at your registrar

### 2. Update wrangler.toml

Uncomment the routes section:

```toml
[[routes]]
pattern = "tcdb.uk/api/*"
zone_name = "tcdb.uk"
```

### 3. Redeploy

```bash
wrangler deploy
```

### 4. Test

```bash
curl https://tcdb.uk/api/descriptor/health
```

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    User Request                              │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│         Cloudflare Edge (300+ locations)                     │
│  ┌──────────────────────────────────────────────────────┐   │
│  │  Edge Worker (tcdb-edge)                             │   │
│  │  - Rate Limiting (Durable Objects)                   │   │
│  │  - HMAC Signing                                      │   │
│  │  - CORS Headers                                      │   │
│  └──────────────────────────────────────────────────────┘   │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│         Cloudflare Tunnel (Optional)                         │
│  - Secure connection to origin                               │
│  - No public IP needed                                       │
│  - Free!                                                     │
└─────────────────────┬───────────────────────────────────────┘
                      │
                      ▼
┌─────────────────────────────────────────────────────────────┐
│         Origin Server (Your FastAPI)                         │
│  - Running on localhost:8000 or VPS                          │
│  - Verifies HMAC signatures                                  │
│  - Processes descriptor requests                             │
└─────────────────────────────────────────────────────────────┘
```

## Monitoring

### View Logs

```bash
# Tail worker logs in real-time
wrangler tail
```

### View Analytics

```bash
# Open Cloudflare dashboard
wrangler dashboard
```

Or visit: https://dash.cloudflare.com

### Metrics Available

- Request count
- Error rate
- Response time (p50, p95, p99)
- Bandwidth usage
- Cache hit ratio
- Rate limit hits

## Cost

### Free Tier (Generous!)

- ✅ 100,000 requests/day
- ✅ Unlimited bandwidth
- ✅ 1 million Durable Object operations/day
- ✅ 300+ edge locations
- ✅ DDoS protection

### Paid Plan ($5/month)

- ✅ 10 million requests/month
- ✅ Unlimited bandwidth
- ✅ Unlimited Durable Objects
- ✅ Advanced analytics

**For most use cases, the free tier is sufficient!**

## Troubleshooting

### "Not authenticated"

```bash
wrangler login
```

### "Build failed"

```bash
cd cloudflare/worker
npm install
npm run build
```

### "Origin not responding"

Check your origin server is running:
```bash
curl http://localhost:8000/descriptor/health
```

If using tunnel, check tunnel status:
```bash
cloudflared tunnel info tcdb-api
```

### "Rate limit not working"

Durable Objects need to be enabled in your Cloudflare account.
Check: https://dash.cloudflare.com → Workers → Durable Objects

## Next Steps After Deployment

1. ✅ **Test the deployment**
   ```bash
   curl https://tcdb-edge.<subdomain>.workers.dev/descriptor/compute \
     -X POST \
     -H "Content-Type: application/json" \
     -d '{"name":"kme_delta","params":{},"X":[[0,0],[1,0],[0,1]]}'
   ```

2. ✅ **Set up monitoring**
   - Enable email alerts in Cloudflare dashboard
   - Set up uptime monitoring (e.g., UptimeRobot)

3. ✅ **Configure custom domain**
   - Add your domain to Cloudflare
   - Update DNS records
   - Enable SSL/TLS

4. ✅ **Update homepage**
   - Point API calls to your Cloudflare Worker URL
   - Update documentation with new endpoints

5. ✅ **Test LLM integration**
   ```bash
   python examples/quick_llm_test.py
   ```

## Summary

**Fastest Path to Production:**

1. Install Wrangler: `npm install -g wrangler`
2. Login: `wrangler login`
3. Deploy: `.\deploy-cloudflare.ps1` (Windows) or `./deploy-cloudflare.sh` (Mac/Linux)
4. Set up origin with Cloudflare Tunnel (free!)
5. Test: `curl https://your-worker.workers.dev/descriptor/health`

**Total Time**: ~5-10 minutes  
**Total Cost**: $0 (free tier)

🚀 **Your TCDB API will be live on Cloudflare's global edge network!**

---

Need help? Check:
- [Cloudflare Workers Docs](https://developers.cloudflare.com/workers/)
- [Cloudflare Tunnel Docs](https://developers.cloudflare.com/cloudflare-one/connections/connect-apps/)
- [CLOUDFLARE_DEPLOYMENT.md](./CLOUDFLARE_DEPLOYMENT.md) - Full deployment guide

