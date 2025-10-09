#!/bin/bash

# TCDB Core - Cloudflare Deployment Script
# This script deploys the edge worker to Cloudflare

set -e  # Exit on error

echo "======================================================================="
echo "🚀 TCDB Core - Cloudflare Edge Worker Deployment"
echo "======================================================================="
echo ""

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Check if wrangler is installed
if ! command -v wrangler &> /dev/null; then
    echo -e "${RED}❌ Error: Wrangler CLI not found${NC}"
    echo ""
    echo "Install with:"
    echo "  npm install -g wrangler"
    echo ""
    exit 1
fi

echo -e "${GREEN}✅ Wrangler CLI found${NC}"
echo ""

# Check if logged in
if ! wrangler whoami &> /dev/null; then
    echo -e "${YELLOW}⚠️  Not logged in to Cloudflare${NC}"
    echo ""
    echo "Logging in..."
    wrangler login
    echo ""
fi

echo -e "${GREEN}✅ Authenticated with Cloudflare${NC}"
echo ""

# Navigate to worker directory
cd cloudflare/worker

echo -e "${BLUE}📦 Installing dependencies...${NC}"
npm install
echo ""

echo -e "${BLUE}🔨 Building TypeScript...${NC}"
npm run build
echo ""

echo -e "${GREEN}✅ Build complete${NC}"
echo ""

# Check if secrets are set
echo -e "${BLUE}🔐 Checking secrets...${NC}"
echo ""
echo "Note: You need to set EDGE_HMAC_SECRET if not already set"
echo "Run: wrangler secret put EDGE_HMAC_SECRET"
echo ""

# Deploy
echo -e "${BLUE}🌍 Deploying to Cloudflare...${NC}"
echo ""

wrangler deploy

echo ""
echo "======================================================================="
echo -e "${GREEN}🎉 Deployment Complete!${NC}"
echo "======================================================================="
echo ""
echo "Your worker is now live!"
echo ""
echo "Test it with:"
echo "  curl https://tcdb-edge.<your-subdomain>.workers.dev/descriptor/health"
echo ""
echo "Next steps:"
echo "  1. Set up your origin server (FastAPI)"
echo "  2. Configure EDGE_HMAC_SECRET: wrangler secret put EDGE_HMAC_SECRET"
echo "  3. Update ORIGIN_URL in wrangler.toml"
echo "  4. Configure custom domain in Cloudflare dashboard"
echo ""
echo "======================================================================="

