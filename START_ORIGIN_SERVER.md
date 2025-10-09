# Start Origin Server - Quick Guide 🚀

## Option 1: Simple Local Testing (Fastest)

For quick testing, we can temporarily point the worker to localhost.

### Step 1: Update Worker Configuration

Edit `cloudflare/worker/wrangler.toml`:

```toml
[vars]
# Change from:
ORIGIN_URL = "https://api.tcdb.uk"

# To:
ORIGIN_URL = "http://localhost:8000"
```

### Step 2: Redeploy Worker

```powershell
.\deploy-cloudflare.ps1
```

### Step 3: Start FastAPI

```powershell
cd python
python -m uvicorn tcdb_api.app:app --host 0.0.0.0 --port 8000
```

### Step 4: Test

```powershell
curl http://localhost:8000/descriptor/health
```

**Note:** This only works for local testing. The Cloudflare Worker can't reach your localhost.

---

## Option 2: Cloudflare Tunnel (Recommended for Production)

This exposes your local server securely to the internet.

### Step 1: Refresh Your Terminal

Close and reopen your PowerShell terminal to refresh the PATH, then verify:

```powershell
cloudflared --version
```

If it still doesn't work, restart your computer or add to PATH manually:

```powershell
$env:Path += ";C:\Program Files\cloudflared"
cloudflared --version
```

### Step 2: Authenticate

```powershell
cloudflared tunnel login
```

This opens your browser. Login to Cloudflare.

### Step 3: Create Tunnel

```powershell
cloudflared tunnel create tcdb-api
```

This creates a tunnel and shows you the tunnel ID.

### Step 4: Get Tunnel ID

```powershell
cloudflared tunnel list
```

Copy the tunnel ID (first column).

### Step 5: Create Config File

Create `C:\Users\aps33\.cloudflared\config.yml`:

```yaml
tunnel: YOUR_TUNNEL_ID_HERE
credentials-file: C:\Users\aps33\.cloudflared\YOUR_TUNNEL_ID_HERE.json

ingress:
  - hostname: api.tcdb.uk
    service: http://localhost:8000
  - service: http_status:404
```

Replace `YOUR_TUNNEL_ID_HERE` with your actual tunnel ID.

### Step 6: Route DNS

```powershell
cloudflared tunnel route dns tcdb-api api.tcdb.uk
```

### Step 7: Start FastAPI

**Terminal 1:**
```powershell
cd python
python -m uvicorn tcdb_api.app:app --host 0.0.0.0 --port 8000
```

### Step 8: Start Tunnel

**Terminal 2:**
```powershell
cloudflared tunnel run tcdb-api
```

### Step 9: Test

```powershell
# Test origin directly
curl https://api.tcdb.uk/descriptor/health

# Test through Cloudflare Worker
curl https://tcdb-edge.aps330.workers.dev/descriptor/health
```

---

## Option 3: Use ngrok (Alternative)

If Cloudflare Tunnel doesn't work, use ngrok:

### Step 1: Install ngrok

```powershell
winget install ngrok
```

### Step 2: Start FastAPI

```powershell
cd python
python -m uvicorn tcdb_api.app:app --host 0.0.0.0 --port 8000
```

### Step 3: Start ngrok

```powershell
ngrok http 8000
```

This gives you a public URL like: `https://abc123.ngrok.io`

### Step 4: Update Worker

Edit `cloudflare/worker/wrangler.toml`:

```toml
[vars]
ORIGIN_URL = "https://abc123.ngrok.io"
```

### Step 5: Redeploy

```powershell
.\deploy-cloudflare.ps1
```

### Step 6: Test

```powershell
curl https://tcdb-edge.aps330.workers.dev/descriptor/health
```

---

## Option 4: Deploy to Cloud (Production)

Deploy FastAPI to a cloud provider:

### Railway (Free Tier)

1. Go to https://railway.app
2. Connect your GitHub repo
3. Deploy `python` directory
4. Set start command: `uvicorn tcdb_api.app:app --host 0.0.0.0 --port $PORT`
5. Get your Railway URL
6. Update `wrangler.toml` with Railway URL
7. Redeploy worker

### Render (Free Tier)

1. Go to https://render.com
2. Create new Web Service
3. Connect GitHub repo
4. Build command: `pip install -e .`
5. Start command: `cd python && uvicorn tcdb_api.app:app --host 0.0.0.0 --port $PORT`
6. Get your Render URL
7. Update `wrangler.toml`
8. Redeploy worker

---

## Quick Start (Recommended Path)

**For immediate testing:**

1. **Close and reopen your terminal** (to refresh PATH)
2. **Run the setup script:**
   ```powershell
   .\setup-tunnel.ps1
   ```
3. **Start FastAPI:**
   ```powershell
   cd python
   python -m uvicorn tcdb_api.app:app --host 0.0.0.0 --port 8000
   ```
4. **Start tunnel (new terminal):**
   ```powershell
   cloudflared tunnel run tcdb-api
   ```
5. **Test:**
   ```powershell
   curl https://tcdb-edge.aps330.workers.dev/descriptor/health
   ```

---

## Troubleshooting

### "cloudflared not found"

**Solution 1:** Restart your terminal
**Solution 2:** Restart your computer
**Solution 3:** Add to PATH manually:

```powershell
$env:Path += ";C:\Program Files\cloudflared"
```

### "Tunnel already exists"

That's fine! Just use the existing tunnel:

```powershell
cloudflared tunnel list
cloudflared tunnel run tcdb-api
```

### "Origin not responding"

Make sure FastAPI is running:

```powershell
curl http://localhost:8000/descriptor/health
```

### "DNS not resolving"

Wait a few minutes for DNS propagation, or use the tunnel's direct URL:

```powershell
cloudflared tunnel info tcdb-api
```

---

## Summary

**Fastest for testing:** Option 3 (ngrok)  
**Best for production:** Option 2 (Cloudflare Tunnel)  
**Most reliable:** Option 4 (Cloud deployment)

**Recommended:** Close your terminal, reopen it, and run:

```powershell
.\setup-tunnel.ps1
```

Then follow the on-screen instructions!

