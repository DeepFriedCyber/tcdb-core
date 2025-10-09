# Cloudflare Tunnel Setup - Complete Guide 🚀

## Why Cloudflare Tunnel?

Since your domain is already on Cloudflare, this is the **perfect solution**:

✅ **100% Free** - No additional costs  
✅ **Secure** - Encrypted tunnel, no open ports  
✅ **Your Domain** - Use api.tcdb.uk  
✅ **Integrated** - Everything in Cloudflare ecosystem  
✅ **Fast** - Direct Cloudflare network connection  
✅ **No VPS needed** - Run from your local machine  

## Architecture

```
User → Cloudflare Worker → Cloudflare Tunnel → Your Local FastAPI
       (Edge proxy)         (Secure tunnel)     (localhost:8000)
```

**Everything stays in Cloudflare!**

## Setup Steps

### Step 1: Restart Terminal

**IMPORTANT:** Close this PowerShell terminal and open a **NEW** one to refresh the PATH.

Then navigate back:
```powershell
cd C:\Users\aps33\Projects\tcdb-core
```

### Step 2: Verify cloudflared

```powershell
cloudflared --version
```

**If it doesn't work:**
```powershell
# Add to PATH for this session
$env:Path += ";C:\Program Files\cloudflared"
cloudflared --version
```

**Still doesn't work?** Restart your computer (Windows needs this to update PATH).

### Step 3: Authenticate with Cloudflare

```powershell
cloudflared tunnel login
```

This opens your browser. Login to your Cloudflare account.

### Step 4: Create Tunnel

```powershell
cloudflared tunnel create tcdb-api
```

This creates a tunnel and shows output like:
```
Created tunnel tcdb-api with id abc123-def456-ghi789
```

**Copy the tunnel ID!**

### Step 5: List Tunnels (to get ID)

```powershell
cloudflared tunnel list
```

Output shows:
```
ID                                   NAME      CREATED
abc123-def456-ghi789                 tcdb-api  2025-10-09T06:00:00Z
```

Copy the ID from the first column.

### Step 6: Create Config File

Create file: `C:\Users\aps33\.cloudflared\config.yml`

```yaml
tunnel: abc123-def456-ghi789
credentials-file: C:\Users\aps33\.cloudflared\abc123-def456-ghi789.json

ingress:
  - hostname: api.tcdb.uk
    service: http://localhost:8000
  - service: http_status:404
```

**Replace `abc123-def456-ghi789` with YOUR tunnel ID!**

### Step 7: Route DNS

```powershell
cloudflared tunnel route dns tcdb-api api.tcdb.uk
```

This creates a CNAME record in your Cloudflare DNS pointing `api.tcdb.uk` to your tunnel.

### Step 8: Start FastAPI

**Terminal 1:**
```powershell
cd C:\Users\aps33\Projects\tcdb-core
.\start-api.ps1
```

Keep this running!

### Step 9: Start Tunnel

**Terminal 2 (NEW terminal):**
```powershell
cd C:\Users\aps33\Projects\tcdb-core
cloudflared tunnel run tcdb-api
```

Keep this running too!

### Step 10: Test

```powershell
# Test origin directly
curl https://api.tcdb.uk/descriptor/health

# Test through Cloudflare Worker
curl https://tcdb-edge.aps330.workers.dev/descriptor/health
```

## What Each Component Does

### 1. FastAPI Server (localhost:8000)
- Your TCDB API
- Runs locally on your machine
- Processes descriptor requests

### 2. Cloudflare Tunnel
- Secure encrypted connection
- Exposes localhost:8000 as api.tcdb.uk
- No open ports needed
- Free!

### 3. Cloudflare Worker (tcdb-edge)
- Edge proxy at 300+ locations
- Rate limiting (300 req/min)
- HMAC signing
- CORS headers
- Proxies to api.tcdb.uk

### 4. Your Domain (tcdb.uk)
- Already in Cloudflare
- DNS managed by Cloudflare
- SSL/TLS automatic

## Complete Flow

```
1. User makes request to:
   https://tcdb-edge.aps330.workers.dev/descriptor/compute

2. Cloudflare Worker receives it at edge (nearest location)
   - Checks rate limit
   - Adds HMAC signature
   - Adds CORS headers

3. Worker proxies to:
   https://api.tcdb.uk/descriptor/compute

4. Cloudflare Tunnel receives it
   - Decrypts secure tunnel
   - Forwards to localhost:8000

5. Your FastAPI processes request
   - Computes descriptors
   - Returns response

6. Response flows back through tunnel → worker → user
```

## Benefits of This Setup

✅ **No VPS costs** - Everything runs locally  
✅ **No Railway/Render** - Don't need third-party services  
✅ **All Cloudflare** - Integrated ecosystem  
✅ **Your domain** - Use api.tcdb.uk  
✅ **Secure** - Encrypted tunnel  
✅ **Fast** - Global edge network  
✅ **Free** - $0 cost  

## Troubleshooting

### "cloudflared not found"

**Solution 1:** Close terminal, open NEW terminal  
**Solution 2:** Restart computer  
**Solution 3:** Add to PATH:
```powershell
$env:Path += ";C:\Program Files\cloudflared"
```

### "Tunnel already exists"

That's fine! Just use it:
```powershell
cloudflared tunnel list
cloudflared tunnel run tcdb-api
```

### "DNS not resolving"

Wait 1-2 minutes for DNS propagation. Check in Cloudflare dashboard:
- Go to https://dash.cloudflare.com
- Select your domain (tcdb.uk)
- Click "DNS"
- You should see a CNAME record for `api` pointing to your tunnel

### "Connection refused"

Make sure FastAPI is running:
```powershell
curl http://localhost:8000/descriptor/health
```

### "Worker returns 1016"

This means the tunnel isn't running or DNS hasn't propagated yet.

1. Check tunnel is running: `cloudflared tunnel info tcdb-api`
2. Check DNS: `nslookup api.tcdb.uk`
3. Wait a few minutes for DNS propagation

## Monitoring

### View Tunnel Status
```powershell
cloudflared tunnel info tcdb-api
```

### View Tunnel Logs
The tunnel terminal shows live logs of all requests.

### View Worker Logs
```powershell
cd cloudflare/worker
wrangler tail
```

### Cloudflare Dashboard
- Tunnel analytics: https://one.dash.cloudflare.com
- Worker analytics: https://dash.cloudflare.com → Workers
- DNS settings: https://dash.cloudflare.com → Your domain → DNS

## Running in Production

### Option 1: Keep Terminals Open
- Terminal 1: FastAPI
- Terminal 2: Tunnel

### Option 2: Run as Windows Service

Install tunnel as a service:
```powershell
cloudflared service install
```

Then it runs automatically on startup!

### Option 3: Use Task Scheduler

Create scheduled tasks to start:
1. FastAPI on boot
2. Tunnel on boot

## Cost Comparison

### Your Setup (Cloudflare Tunnel)
- **Cost:** $0
- **Bandwidth:** Unlimited
- **Requests:** 100k/day (free tier)
- **Locations:** 300+ edge locations

### Railway/Render Alternative
- **Cost:** $0-$5/month (free tier limited)
- **Bandwidth:** Limited on free tier
- **Requests:** Limited
- **Locations:** Single region

**Cloudflare Tunnel is clearly better for you!** ✅

## Summary

You **don't need** Railway or Render because:

1. ✅ Your domain is already on Cloudflare
2. ✅ Cloudflare Tunnel is free
3. ✅ Everything stays in Cloudflare ecosystem
4. ✅ More secure (encrypted tunnel)
5. ✅ Faster (direct Cloudflare network)
6. ✅ No additional services needed

**Next step:** Close this terminal, open a NEW one, and run:

```powershell
cd C:\Users\aps33\Projects\tcdb-core
cloudflared --version
```

If that works, continue with the setup steps above!

---

**Architecture:**
```
Your Local Machine → Cloudflare Tunnel → Cloudflare Network → Users
     (FastAPI)         (Free, secure)      (Edge workers)
```

**Everything in Cloudflare. Nothing else needed!** 🎉

