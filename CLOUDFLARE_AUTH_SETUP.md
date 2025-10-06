# Cloudflare Workers Authentication Setup

## Overview

This guide sets up a complete authentication system using Cloudflare Workers with:
- ✅ **Magic link authentication** (no passwords!)
- ✅ **API key generation** for each user
- ✅ **Dashboard** to view/manage API keys
- ✅ **Serverless** - No backend servers needed
- ✅ **Free tier** - Cloudflare Workers free plan

## Architecture

```
tcdb.uk (Homepage)
  ↓
Cloudflare Workers (Auth API)
  ↓
Cloudflare KV (User Data Storage)
  ↓
Dashboard (Show API Keys)
```

## Step 1: Create KV Namespaces

1. Go to: https://dash.cloudflare.com/40a53c1f1212af3e51e8e1277bb4c5f5/workers/kv/namespaces
2. Click **"Create namespace"** 4 times to create:
   - `tcdb-users` - Store user data
   - `tcdb-sessions` - Store active sessions
   - `tcdb-auth-tokens` - Store verification tokens
   - `tcdb-api-keys` - Map API keys to users

3. Copy the namespace IDs (you'll need them)

## Step 2: Deploy Auth Worker

### Install Wrangler CLI

```bash
npm install -g wrangler
```

### Login to Cloudflare

```bash
wrangler login
```

### Update wrangler.toml

Edit `cloudflare-workers/wrangler.toml` and replace the KV namespace IDs:

```toml
[[kv_namespaces]]
binding = "USERS"
id = "your-users-namespace-id-here"

[[kv_namespaces]]
binding = "SESSIONS"
id = "your-sessions-namespace-id-here"

[[kv_namespaces]]
binding = "AUTH_TOKENS"
id = "your-auth-tokens-namespace-id-here"

[[kv_namespaces]]
binding = "API_KEYS"
id = "your-api-keys-namespace-id-here"
```

### Deploy the Worker

```bash
cd cloudflare-workers
wrangler deploy
```

The worker will be deployed to: `https://tcdb-auth.your-subdomain.workers.dev`

## Step 3: Configure Routes

1. Go to: https://dash.cloudflare.com/40a53c1f1212af3e51e8e1277bb4c5f5/workers/overview
2. Click on your **tcdb-auth** worker
3. Go to **"Triggers"** tab
4. Click **"Add route"**
5. Add these routes:
   - `tcdb.uk/api/auth/*` → tcdb-auth worker
   - `tcdb.uk/api/keys/*` → tcdb-auth worker

## Step 4: Update Homepage with Auth

I'll create an updated `docs/index.html` with:
- Sign In / Sign Up buttons
- Auth modal
- Session management
- Redirect to dashboard after login

## Step 5: Create Dashboard Page

Create `docs/dashboard.html` to show:
- User's API key
- Usage statistics
- Regenerate key button
- Documentation links

## API Endpoints

### POST /api/auth/signup
Sign up with email - sends magic link

**Request:**
```json
{
  "email": "user@example.com"
}
```

**Response:**
```json
{
  "success": true,
  "message": "Verification email sent"
}
```

### POST /api/auth/login
Login with email - sends magic link

**Request:**
```json
{
  "email": "user@example.com"
}
```

**Response:**
```json
{
  "success": true,
  "message": "Login link sent to your email"
}
```

### POST /api/auth/verify
Verify magic link token

**Request:**
```json
{
  "token": "verification-token-from-email"
}
```

**Response:**
```json
{
  "success": true,
  "sessionToken": "session-token-here",
  "user": {
    "email": "user@example.com",
    "apiKey": "tcdb_abc123...",
    "plan": "free"
  }
}
```

### GET /api/keys
Get user's API keys (requires auth)

**Headers:**
```
Authorization: Bearer <session-token>
```

**Response:**
```json
{
  "apiKey": "tcdb_abc123...",
  "plan": "free",
  "createdAt": 1234567890
}
```

### POST /api/keys/generate
Generate new API key (requires auth)

**Headers:**
```
Authorization: Bearer <session-token>
```

**Response:**
```json
{
  "apiKey": "tcdb_new_key_here..."
}
```

## Authentication Flow

1. **User clicks "Sign In" or "Get API Access"**
   - Modal opens asking for email

2. **User enters email and submits**
   - POST to `/api/auth/signup` or `/api/auth/login`
   - Magic link sent to email (or shown in console for dev)

3. **User clicks magic link**
   - Redirected to `tcdb.uk/verify?token=...`
   - POST to `/api/auth/verify` with token
   - Session token stored in localStorage
   - User redirected to dashboard

4. **Dashboard loads**
   - GET `/api/keys` with session token
   - Display API key
   - Show usage stats

## Email Integration (Optional)

For production, integrate with an email service:

### Option 1: Cloudflare Email Workers
- Free email sending
- Configure in Cloudflare dashboard

### Option 2: SendGrid/Mailgun
- Add API key to Worker secrets
- Send emails via their API

### Option 3: Resend
- Modern email API
- Great developer experience

## Security Features

- ✅ **Magic links** - No password storage
- ✅ **Token expiration** - 15 minutes for verification
- ✅ **Session expiration** - 7 days
- ✅ **CORS protection** - Only tcdb.uk allowed
- ✅ **Rate limiting** - Can add Cloudflare rate limiting rules

## Cost

**Cloudflare Workers Free Tier:**
- 100,000 requests/day
- 10ms CPU time per request
- KV: 100,000 reads/day, 1,000 writes/day

**For most use cases: FREE!**

## Next Steps

1. ✅ Create KV namespaces
2. ✅ Deploy auth worker
3. ✅ Configure routes
4. ✅ Update homepage with auth UI
5. ✅ Create dashboard page
6. ✅ Test authentication flow
7. ✅ (Optional) Add email service

## Testing

### Test Signup
```bash
curl -X POST https://tcdb.uk/api/auth/signup \
  -H "Content-Type: application/json" \
  -d '{"email":"test@example.com"}'
```

### Test Login
```bash
curl -X POST https://tcdb.uk/api/auth/login \
  -H "Content-Type: application/json" \
  -d '{"email":"test@example.com"}'
```

### Test Get Keys
```bash
curl https://tcdb.uk/api/keys \
  -H "Authorization: Bearer your-session-token"
```

## Advantages Over Clerk

**Cloudflare Workers:**
- ✅ Completely free (within limits)
- ✅ No external dependencies
- ✅ Full control over data
- ✅ Integrated with your domain
- ✅ Serverless - no maintenance

**Clerk:**
- ❌ $25/month for production
- ❌ External service dependency
- ❌ Data stored on their servers

## Support

- Cloudflare Workers Docs: https://developers.cloudflare.com/workers
- KV Storage Docs: https://developers.cloudflare.com/kv
- Wrangler CLI Docs: https://developers.cloudflare.com/workers/wrangler

Ready to deploy? Let me know and I'll help you through each step!

