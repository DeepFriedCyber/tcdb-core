# Quick Start - TCDB Edge Worker

## 🚀 Get Started in 3 Steps

### 1. Install & Build

```bash
cd cloudflare/worker
npm install
npm run build
```

### 2. Run Tests

```bash
npm test
```

**Expected output:**
```
✓ test/worker.spec.ts (2)
  ✓ tcdb-edge worker (2)
    ✓ adds x-signature header (HMAC over body)
    ✓ rate limits after N requests/min/key

Test Files  1 passed (1)
     Tests  2 passed (2)
```

### 3. Local Development

```bash
npm run dev
```

Server starts at: http://localhost:8787

## 🧪 Test the Worker

### Test HMAC Signing

```bash
curl -X POST "http://localhost:8787/evidence/certificate?k=testkey" \
  -H "Content-Type: application/json" \
  -d '{"data_cid": "cid:test", "code_rev": "v1.0", "pd": [[0.1, 0.9]]}'
```

### Test Rate Limiting

```bash
# Send 10 requests rapidly
for i in {1..10}; do
  curl -X POST "http://localhost:8787/reasoner/check?k=ratetest" \
    -H "Content-Type: application/json" \
    -d '{"constraints": ["DeathGeBirth"], "pd": [[0.2, 0.9]]}'
done
```

## 📦 Deploy to Cloudflare

### 1. Login to Cloudflare

```bash
wrangler login
```

### 2. Set Secret

```bash
wrangler secret put EDGE_HMAC_SECRET
# Enter your secret when prompted
```

### 3. Deploy

```bash
wrangler deploy
```

Your worker is now live at: `https://tcdb-edge.<your-subdomain>.workers.dev`

## 🔧 Configuration

### Update Origin URL

Edit `wrangler.toml`:

```toml
[vars]
ORIGIN_URL = "https://your-api-domain.com"
```

### Configure Custom Domain

Edit `wrangler.toml`:

```toml
[[routes]]
pattern = "yourdomain.com/api/*"
zone_name = "yourdomain.com"
```

## 📊 Monitor

### View Logs

```bash
wrangler tail
```

### View Metrics

Visit: https://dash.cloudflare.com/

## ✅ Checklist

- [ ] `npm install` - Install dependencies
- [ ] `npm run build` - Build TypeScript
- [ ] `npm test` - Run tests (should pass)
- [ ] `npm run dev` - Test locally
- [ ] `wrangler login` - Authenticate
- [ ] `wrangler secret put EDGE_HMAC_SECRET` - Set secret
- [ ] Update `ORIGIN_URL` in wrangler.toml
- [ ] `wrangler deploy` - Deploy to production

## 🎯 Next Steps

1. **Update origin URL** to point to your FastAPI server
2. **Configure custom domain** in wrangler.toml
3. **Set up monitoring** in Cloudflare dashboard
4. **Test production deployment** with real API calls

## 📚 Documentation

- Full README: `README.md`
- Worker code: `src/index.ts`
- Tests: `test/worker.spec.ts`
- Config: `wrangler.toml`

---

**Status:** ✅ Ready to deploy!

