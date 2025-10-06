# GitHub Pages Setup Instructions

## ✅ Files Created

The following files have been created and pushed to your repository:

- `docs/index.html` - Your homepage (copied from shared/TopoPersist Homepage.html)
- `docs/README.md` - Documentation for the docs directory
- `.github/workflows/deploy-pages.yml` - GitHub Actions workflow for automatic deployment

## 🚀 Enable GitHub Pages

To enable GitHub Pages for your repository, follow these steps:

### Step 1: Go to Repository Settings

1. Open your browser and go to: https://github.com/DeepFriedCyber/tcdb-core
2. Click on **Settings** (top right, near the repository name)

### Step 2: Navigate to Pages Settings

1. In the left sidebar, scroll down and click on **Pages** (under "Code and automation")

### Step 3: Configure Source

1. Under **Build and deployment**, find the **Source** dropdown
2. Select **GitHub Actions** (not "Deploy from a branch")
3. The page will automatically save

### Step 4: Trigger Deployment

The GitHub Actions workflow will automatically run when you push to main. Since we just pushed, it should already be running!

To check the deployment status:

1. Go to the **Actions** tab in your repository: https://github.com/DeepFriedCyber/tcdb-core/actions
2. Look for the "Deploy to GitHub Pages" workflow
3. Click on the most recent run to see the progress

### Step 5: Access Your Site

Once the deployment completes (usually takes 1-2 minutes), your site will be live at:

**🌐 https://deepfriedcyber.github.io/tcdb-core**

## 🔄 Automatic Updates

From now on, whenever you push changes to the `main` branch that affect the `docs/` directory, GitHub Actions will automatically redeploy your site.

### To Update the Homepage:

1. Edit `shared/TopoPersist Homepage.html`
2. Copy it to `docs/index.html`:
   ```bash
   Copy-Item "shared/TopoPersist Homepage.html" -Destination "docs/index.html" -Force
   ```
3. Commit and push:
   ```bash
   git add docs/index.html
   git commit -m "Update homepage"
   git push origin main
   ```
4. GitHub Actions will automatically deploy the changes

## 🎯 What's Deployed

Your homepage showcases:

- ✅ **146 comprehensive tests** (56 Rust + 90 Python)
- ✅ **4 core modules**: Topological Signatures, Provenance Tracking, Data Proofs, Cross-Domain Reasoning
- ✅ **TDD-verified implementation** with property-based testing
- ✅ **Complete API documentation** and code examples
- ✅ **Use cases** for Research, Cybersecurity, and Finance
- ✅ **Direct GitHub integration** with working links

## 🐛 Troubleshooting

### If the site doesn't appear:

1. Check that GitHub Pages is enabled in Settings → Pages
2. Verify the source is set to "GitHub Actions"
3. Check the Actions tab for any deployment errors
4. Wait a few minutes - initial deployment can take 2-5 minutes

### If you see a 404 error:

1. Make sure `docs/index.html` exists in your repository
2. Check that the GitHub Actions workflow completed successfully
3. Try triggering a manual deployment:
   - Go to Actions tab
   - Click "Deploy to GitHub Pages" workflow
   - Click "Run workflow" button

### If the workflow fails:

1. Check the Actions tab for error messages
2. Ensure the repository has Pages enabled
3. Verify the workflow file is in `.github/workflows/deploy-pages.yml`

## 📝 Custom Domain (Optional)

If you want to use a custom domain:

1. Go to Settings → Pages
2. Under "Custom domain", enter your domain (e.g., `tcdb.example.com`)
3. Add a CNAME record in your DNS settings pointing to `deepfriedcyber.github.io`
4. Wait for DNS propagation (can take up to 24 hours)

## 🔒 HTTPS

GitHub Pages automatically provides HTTPS for your site. Once deployed, your site will be accessible via:

- HTTP: http://deepfriedcyber.github.io/tcdb-core
- HTTPS: https://deepfriedcyber.github.io/tcdb-core (recommended)

## 📊 Analytics (Optional)

To add Google Analytics or other tracking:

1. Edit `docs/index.html`
2. Add your tracking code in the `<head>` section
3. Commit and push

## ✨ Next Steps

After your site is live:

1. ✅ Share the URL: https://deepfriedcyber.github.io/tcdb-core
2. ✅ Add the URL to your repository description
3. ✅ Update README.md with a link to the live site
4. ✅ Share on social media, forums, etc.

## 🎉 Success!

Once you complete these steps, your TCDB Core homepage will be live and accessible to the world!

The site will showcase your comprehensive TDD implementation with all 146 tests, 4 core modules, and complete AI grounding system.

