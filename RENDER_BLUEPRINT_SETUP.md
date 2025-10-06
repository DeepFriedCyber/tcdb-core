# Render Setup Using Blueprint (render.yaml)

## The Problem

When you manually configure a static site in Render's UI, it ignores the `render.yaml` file and tries to auto-detect the project type. Since there's a `pyproject.toml` in the root, it thinks it's a Python project and tries to install dependencies.

## The Solution: Use Blueprint

Instead of manually creating a static site, use Render's **Blueprint** feature which reads the `render.yaml` file directly.

## Step-by-Step Instructions

### Step 1: Delete Existing Site (If You Created One)

1. Go to: https://dashboard.render.com
2. Click on your **tcdb-core** site (if it exists)
3. Click **"Settings"** tab (bottom left)
4. Scroll to bottom → **"Delete Web Service"**
5. Type the service name to confirm
6. Click **"Delete"**

### Step 2: Create New Service Using Blueprint

1. Go to: https://dashboard.render.com
2. Click **"New +"** button (top right)
3. Select **"Blueprint"** (NOT "Static Site")
4. You'll see "Connect a repository"
5. Find and click **"Connect"** next to **tcdb-core**

### Step 3: Render Detects render.yaml

1. Render will automatically detect the `render.yaml` file
2. You'll see a preview showing:
   ```
   Services to create:
   - tcdb-core-homepage (Static Site)
     Root Directory: docs
     Build Command: bash build.sh
     Publish Directory: .
   ```
3. Click **"Apply"** button

### Step 4: Wait for Deployment

1. Render will create the service automatically
2. Watch the deployment log
3. Should see:
   ```
   ==> Cloning repository...
   ==> Checking out in docs directory
   ==> Running: bash build.sh
   Static site - no build required
   ==> Build successful 🎉
   ==> Deploying...
   ==> Your service is live 🎉
   ```

### Step 5: Get Your URL

Your site will be live at:
**https://tcdb-core-homepage.onrender.com**

(or similar - check the dashboard for exact URL)

## Why This Works

**Blueprint Method:**
- ✅ Reads `render.yaml` directly
- ✅ Respects `rootDir: docs` setting
- ✅ Only looks in docs/ folder
- ✅ Never sees pyproject.toml
- ✅ No Python detection

**Manual Method (doesn't work):**
- ❌ Ignores render.yaml
- ❌ Auto-detects from root directory
- ❌ Finds pyproject.toml
- ❌ Tries to build Python
- ❌ Fails on numpy

## Alternative: If Blueprint Doesn't Work

If you can't find the Blueprint option or it doesn't work, try **Netlify** or **Vercel** instead - they're simpler for static sites.

### Quick Netlify Setup:

1. Go to: https://netlify.com
2. Sign up with GitHub
3. Click "Add new site" → "Import an existing project"
4. Choose GitHub → Select tcdb-core
5. Settings:
   - **Base directory**: `docs`
   - **Build command**: (leave empty)
   - **Publish directory**: `.`
6. Click "Deploy"

### Quick Vercel Setup:

1. Go to: https://vercel.com
2. Sign up with GitHub
3. Click "Add New" → "Project"
4. Import tcdb-core
5. Settings:
   - **Root Directory**: `docs`
   - **Build Command**: (leave empty)
   - **Output Directory**: `.`
6. Click "Deploy"

Both Netlify and Vercel:
- ✅ Work with private repos
- ✅ Free tier
- ✅ Auto-deploy on push
- ✅ Custom domains
- ✅ Simpler configuration

## Current Files Ready

- ✅ `render.yaml` - Blueprint configuration
- ✅ `docs/index.html` - Your homepage
- ✅ `docs/build.sh` - Empty build script
- ✅ `docs/.render-buildpacks.json` - Disables buildpacks

## Recommendation

**Try this order:**

1. **First**: Try Render Blueprint method (above)
2. **If that fails**: Try Netlify (simpler, very reliable)
3. **If that fails**: Try Vercel (also simple and reliable)

All three work with private repos and are free for static sites!

## Need Help?

Let me know which platform you want to try and I can provide more detailed instructions.

