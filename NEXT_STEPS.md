# ✅ Origin Server Running! Next Steps 🚀

## Current Status

✅ **FastAPI Server**: Running on http://localhost:8000  
✅ **Cloudflare Worker**: Deployed at https://tcdb-edge.aps330.workers.dev  
⏳ **Tunnel**: Needs setup to connect them  

## What's Working

Your FastAPI server is **LIVE** locally:

```json
{
  "status": "healthy",
  "service": "descriptor-api-simple",
  "descriptors_available": 4
}
```

**Test it:**
- Homepage: http://localhost:8000
- API Docs: http://localhost:8000/docs
- Health: http://localhost:8000/descriptor/health

## Next: Connect to Cloudflare

You have 3 options to expose your local server:

---

## Option 1: Cloudflare Tunnel (Recommended) ⭐

### Step 1: Refresh PATH

**Close this terminal and open a NEW PowerShell terminal**, then:

```powershell
cd C:\Users\aps33\Projects\tcdb-core
cloudflared --version
```

If it works, continue. If not, try:

```powershell
# Add to PATH for this session
$env:Path += ";C:\Program Files\cloudflared"
cloudflared --version
```

### Step 2: Run Setup Script

```powershell
.\setup-tunnel.ps1
```

This will:
1. Authenticate with Cloudflare
2. Create tunnel "tcdb-api"
3. Configure DNS for api.tcdb.uk
4. Create config file

### Step 3: Start Tunnel

**In a NEW terminal:**

```powershell
cloudflared tunnel run tcdb-api
```

Keep this running!

### Step 4: Test

```powershell
# Test origin
curl https://api.tcdb.uk/descriptor/health

# Test through worker
curl https://tcdb-edge.aps330.workers.dev/descriptor/health
```

---

## Option 2: ngrok (Easiest Alternative) 🚀

If Cloudflare Tunnel is giving you trouble, use ngrok:

### Step 1: Install ngrok

```powershell
winget install ngrok
```

### Step 2: Start ngrok

**In a NEW terminal:**

```powershell
ngrok http 8000
```

This shows you a URL like: `https://abc123.ngrok.io`

### Step 3: Update Worker

Edit `cloudflare/worker/wrangler.toml`:

```toml
[vars]
ORIGIN_URL = "https://abc123.ngrok.io"  # Use YOUR ngrok URL
```

### Step 4: Redeploy Worker

```powershell
.\deploy-cloudflare.ps1
```

### Step 5: Test

```powershell
curl https://tcdb-edge.aps330.workers.dev/descriptor/health
```

**Note:** ngrok URLs change each time you restart. For permanent URLs, upgrade to ngrok paid plan or use Cloudflare Tunnel.

---

## Option 3: Deploy to Cloud (Production) ☁️

For a permanent solution, deploy to a cloud provider:

### Railway (Free Tier)

1. Go to https://railway.app
2. Sign up with GitHub
3. Click "New Project" → "Deploy from GitHub repo"
4. Select `tcdb-core` repo
5. Set root directory: `python`
6. Set start command: `uvicorn tcdb_api.app:app --host 0.0.0.0 --port $PORT`
7. Deploy!
8. Get your Railway URL (e.g., `https://tcdb-api.railway.app`)
9. Update `wrangler.toml` with Railway URL
10. Redeploy worker: `.\deploy-cloudflare.ps1`

### Render (Free Tier)

1. Go to https://render.com
2. Sign up with GitHub
3. Click "New" → "Web Service"
4. Connect `tcdb-core` repo
5. Settings:
   - **Root Directory**: `python`
   - **Build Command**: `pip install -e ..`
   - **Start Command**: `uvicorn tcdb_api.app:app --host 0.0.0.0 --port $PORT`
6. Deploy!
7. Get your Render URL
8. Update `wrangler.toml`
9. Redeploy worker

---

## Recommended Path

**For quick testing (5 minutes):**
→ Use **Option 2 (ngrok)**

**For production (10 minutes):**
→ Use **Option 1 (Cloudflare Tunnel)**

**For permanent deployment (15 minutes):**
→ Use **Option 3 (Cloud deployment)**

---

## Quick Commands Reference

### Check if FastAPI is running
```powershell
curl http://localhost:8000/descriptor/health
```

### Start FastAPI (if stopped)
```powershell
.\start-api.ps1
```

### Setup Cloudflare Tunnel
```powershell
# In a NEW terminal (to refresh PATH)
.\setup-tunnel.ps1
```

### Run Cloudflare Tunnel
```powershell
cloudflared tunnel run tcdb-api
```

### Deploy Worker
```powershell
.\deploy-cloudflare.ps1
```

### Test Everything
```powershell
# Local
curl http://localhost:8000/descriptor/health

# Origin (if using tunnel)
curl https://api.tcdb.uk/descriptor/health

# Worker
curl https://tcdb-edge.aps330.workers.dev/descriptor/health
```

---

## Current Terminal Status

**Terminal 13**: FastAPI server running (keep it running!)

**You need**: 
- NEW terminal for tunnel/ngrok
- Keep FastAPI terminal running

---

## Troubleshooting

### "cloudflared not found"

1. Close ALL terminals
2. Open NEW PowerShell
3. Try: `cloudflared --version`
4. If still fails: Restart computer

### "Port 8000 already in use"

```powershell
# Find process using port 8000
netstat -ano | findstr :8000

# Kill it (replace PID with actual number)
taskkill /F /PID <PID>

# Restart FastAPI
.\start-api.ps1
```

### "Worker returns 1016 error"

This means the origin server isn't reachable. Make sure:
1. FastAPI is running
2. Tunnel/ngrok is running
3. `ORIGIN_URL` in `wrangler.toml` is correct
4. Worker is redeployed after changing `ORIGIN_URL`

---

## What to Do Now

**Recommended:** Use ngrok for quick testing

1. **Open a NEW terminal**
2. **Install ngrok:**
   ```powershell
   winget install ngrok
   ```
3. **Start ngrok:**
   ```powershell
   ngrok http 8000
   ```
4. **Copy the ngrok URL** (e.g., `https://abc123.ngrok.io`)
5. **Update `cloudflare/worker/wrangler.toml`:**
   ```toml
   [vars]
   ORIGIN_URL = "https://abc123.ngrok.io"
   ```
6. **Redeploy:**
   ```powershell
   .\deploy-cloudflare.ps1
   ```
7. **Test:**
   ```powershell
   curl https://tcdb-edge.aps330.workers.dev/descriptor/health
   ```

**Done!** Your API will be live on Cloudflare's global network! 🎉

---

## Summary

✅ FastAPI running locally  
✅ Cloudflare Worker deployed  
⏳ Need to connect them (use ngrok or tunnel)  

**Next:** Follow Option 2 (ngrok) above for fastest results!

