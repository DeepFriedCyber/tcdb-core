# Enable GitHub Pages - Quick Fix Guide

## Issue: Site Not Live Yet

The GitHub Pages site is not live because it needs to be manually enabled in the repository settings.

## Quick Fix Steps

### Step 1: Make Repository Public (If Private)

GitHub Pages requires a public repository (unless you have GitHub Pro/Enterprise).

1. Go to: https://github.com/DeepFriedCyber/tcdb-core/settings
2. Scroll to the bottom to the **"Danger Zone"** section
3. Click **"Change visibility"**
4. Select **"Make public"**
5. Type the repository name to confirm
6. Click **"I understand, change repository visibility"**

### Step 2: Enable GitHub Pages

1. Go to: https://github.com/DeepFriedCyber/tcdb-core/settings/pages
2. Under **"Build and deployment"**:
   - **Source**: Select **"GitHub Actions"** from the dropdown
3. The page will auto-save

### Step 3: Trigger Deployment

Option A - Automatic (Recommended):
```bash
# Make a small change to trigger deployment
cd C:\Users\aps33\Projects\tcdb-core
git commit --allow-empty -m "Trigger GitHub Pages deployment"
git push origin main
```

Option B - Manual:
1. Go to: https://github.com/DeepFriedCyber/tcdb-core/actions
2. Click on **"Deploy to GitHub Pages"** workflow (left sidebar)
3. Click **"Run workflow"** button (right side)
4. Click the green **"Run workflow"** button in the dropdown

### Step 4: Wait for Deployment

1. Go to: https://github.com/DeepFriedCyber/tcdb-core/actions
2. Watch the **"Deploy to GitHub Pages"** workflow
3. Wait for the green checkmark (usually 1-2 minutes)

### Step 5: Access Your Site

Once deployment completes, visit:
**https://deepfriedcyber.github.io/tcdb-core**

## Troubleshooting

### If you see "404 - Page not found"

**Cause**: Repository is private or Pages not enabled

**Fix**:
1. Make repository public (see Step 1 above)
2. Enable GitHub Pages (see Step 2 above)
3. Wait for deployment to complete

### If you see "Actions" tab but no workflows

**Cause**: GitHub Actions might be disabled

**Fix**:
1. Go to: https://github.com/DeepFriedCyber/tcdb-core/settings/actions
2. Under **"Actions permissions"**, select **"Allow all actions and reusable workflows"**
3. Click **"Save"**
4. Go back and trigger deployment (Step 3)

### If workflow fails with permissions error

**Cause**: Workflow doesn't have Pages permissions

**Fix**:
1. Go to: https://github.com/DeepFriedCyber/tcdb-core/settings/actions
2. Scroll to **"Workflow permissions"**
3. Select **"Read and write permissions"**
4. Check **"Allow GitHub Actions to create and approve pull requests"**
5. Click **"Save"**
6. Re-run the workflow

### If you can't access Settings

**Cause**: You need admin access to the repository

**Fix**: Make sure you're logged into GitHub with the account that owns the repository (DeepFriedCyber)

## Alternative: Simple Branch Deployment

If GitHub Actions doesn't work, you can use the simpler branch deployment:

1. Go to: https://github.com/DeepFriedCyber/tcdb-core/settings/pages
2. Under **"Build and deployment"**:
   - **Source**: Select **"Deploy from a branch"**
   - **Branch**: Select **"main"** and **"/docs"**
3. Click **"Save"**
4. Wait 1-2 minutes
5. Visit: https://deepfriedcyber.github.io/tcdb-core

## Verification Commands

Run these to verify your setup:

```bash
# Check if docs/index.html exists
ls docs/index.html

# Check if workflow file exists
ls .github/workflows/deploy-pages.yml

# Check git status
git status

# Check remote URL
git remote -v
```

## Expected Output

When everything is working:

1. ✅ Repository is public
2. ✅ GitHub Pages is enabled with source "GitHub Actions"
3. ✅ Workflow runs successfully (green checkmark)
4. ✅ Site is live at https://deepfriedcyber.github.io/tcdb-core

## Need More Help?

If you're still having issues:

1. Check the Actions tab for error messages
2. Verify the repository is public
3. Make sure you're logged in as the repository owner
4. Try the "Deploy from a branch" method as an alternative

## Quick Command to Trigger Deployment

```bash
cd C:\Users\aps33\Projects\tcdb-core
git commit --allow-empty -m "Trigger Pages deployment"
git push origin main
```

Then check: https://github.com/DeepFriedCyber/tcdb-core/actions

