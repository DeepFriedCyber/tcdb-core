# Deploy TCDB Core Homepage to Render

## Why Render?

- ✅ **Works with private repositories** (no need to make repo public)
- ✅ **Free tier available** for static sites
- ✅ **Automatic deployments** from GitHub
- ✅ **Custom domains** supported
- ✅ **HTTPS** included automatically
- ✅ **Fast CDN** for global delivery

## Quick Setup (5 minutes)

### Step 1: Create Render Account

1. Go to: https://render.com
2. Click **"Get Started"** or **"Sign Up"**
3. Choose **"Sign up with GitHub"** (recommended)
4. Authorize Render to access your GitHub account

### Step 2: Connect Your Repository

1. After signing in, you'll be on the Render Dashboard
2. Click **"New +"** button (top right)
3. Select **"Static Site"**
4. You'll see a list of your repositories
5. Find **"tcdb-core"** and click **"Connect"**

   **Note**: If you don't see your repository:
   - Click **"Configure account"** link
   - Grant Render access to the repository
   - Come back and refresh

### Step 3: Configure the Static Site

Fill in the following settings:

**Name**: `tcdb-core` (or any name you prefer)

**Branch**: `main`

**Build Command**: Leave empty or use: `echo "No build needed"`

**Publish Directory**: `docs`

**Auto-Deploy**: `Yes` (enabled by default)

Click **"Create Static Site"**

### Step 4: Wait for Deployment

- Render will automatically deploy your site
- First deployment takes 1-2 minutes
- You'll see a progress log
- Wait for "Deploy succeeded" message

### Step 5: Access Your Site

Once deployed, Render will provide a URL like:

**https://tcdb-core.onrender.com**

or

**https://tcdb-core-[random-string].onrender.com**

You can find your URL:
- On the deployment page (top of the page)
- In the Render dashboard under your site

## Using the render.yaml File

I've created a `render.yaml` file in your repository. This allows Render to automatically configure your site.

### Benefits:
- ✅ Automatic configuration
- ✅ Version controlled settings
- ✅ Easy to replicate

### To use it:

1. Commit and push the render.yaml file (I'll do this for you)
2. When creating the static site on Render, it will automatically detect the configuration
3. Just click "Apply" and "Create Static Site"

## Automatic Deployments

Once set up, Render will automatically deploy whenever you push to the `main` branch:

1. Make changes to `docs/index.html`
2. Commit and push to GitHub
3. Render automatically detects the change
4. Site redeploys in 1-2 minutes
5. Changes are live!

## Custom Domain (Optional)

To use your own domain:

1. Go to your site in Render Dashboard
2. Click **"Settings"** tab
3. Scroll to **"Custom Domain"**
4. Click **"Add Custom Domain"**
5. Enter your domain (e.g., `tcdb.yourdomain.com`)
6. Follow the DNS configuration instructions
7. Render will automatically provision SSL certificate

## Environment Variables (If Needed)

If you need to add environment variables:

1. Go to **"Environment"** tab in your site settings
2. Click **"Add Environment Variable"**
3. Add key-value pairs
4. Click **"Save Changes"**

## Monitoring & Logs

View deployment logs:
1. Go to your site in Render Dashboard
2. Click **"Logs"** tab
3. See real-time deployment and access logs

## Pricing

**Free Tier Includes:**
- ✅ Static sites (unlimited)
- ✅ Automatic SSL
- ✅ Global CDN
- ✅ Automatic deployments
- ✅ Custom domains

**Note**: Free tier static sites may spin down after inactivity, but they wake up instantly when accessed.

## Troubleshooting

### Site shows 404 error

**Cause**: Publish directory might be wrong

**Fix**:
1. Go to **"Settings"** tab
2. Check **"Publish Directory"** is set to `docs`
3. Click **"Save Changes"**
4. Trigger a manual deploy

### Repository not showing up

**Cause**: Render doesn't have access

**Fix**:
1. Go to: https://render.com/account
2. Click **"GitHub"** under "Connected Accounts"
3. Click **"Configure"**
4. Grant access to tcdb-core repository
5. Go back and try connecting again

### Deployment fails

**Cause**: Build command or publish directory issue

**Fix**:
1. Check the deployment logs for errors
2. Verify `docs/index.html` exists in your repository
3. Set Build Command to empty or `echo "No build needed"`
4. Set Publish Directory to `docs`
5. Trigger manual redeploy

### Changes not showing up

**Cause**: Browser cache or deployment not triggered

**Fix**:
1. Hard refresh browser (Ctrl+F5 or Cmd+Shift+R)
2. Check Render dashboard for recent deployments
3. Manually trigger a deploy if needed

## Manual Deploy

To manually trigger a deployment:

1. Go to your site in Render Dashboard
2. Click **"Manual Deploy"** button (top right)
3. Select **"Deploy latest commit"**
4. Click **"Deploy"**

## Comparison: Render vs GitHub Pages

| Feature | Render | GitHub Pages |
|---------|--------|--------------|
| Private repos | ✅ Yes | ❌ No (requires Pro) |
| Custom domains | ✅ Yes | ✅ Yes |
| Auto SSL | ✅ Yes | ✅ Yes |
| Auto deploy | ✅ Yes | ✅ Yes |
| Build time | ~1-2 min | ~1-2 min |
| Free tier | ✅ Yes | ✅ Yes |
| CDN | ✅ Global | ✅ Global |

## Next Steps After Deployment

1. ✅ Test the site at your Render URL
2. ✅ Share the URL with your team
3. ✅ (Optional) Set up custom domain
4. ✅ Update README.md with the live URL
5. ✅ Continue developing - auto-deploys on push!

## Quick Commands

```bash
# Commit the render.yaml file
git add render.yaml RENDER_DEPLOYMENT.md
git commit -m "Add Render deployment configuration"
git push origin main

# After pushing, Render will auto-deploy if already connected
```

## Support

- Render Documentation: https://render.com/docs/static-sites
- Render Community: https://community.render.com
- Status Page: https://status.render.com

## Your Site Details

Once deployed, your TCDB Core homepage will showcase:

- ✅ 146 comprehensive tests
- ✅ 4 core modules (Topology, Provenance, Data Proofs, Cross-Domain)
- ✅ Complete TDD implementation
- ✅ API documentation and examples
- ✅ Professional design with Tailwind CSS

**Estimated Time**: 5 minutes from start to live site!

