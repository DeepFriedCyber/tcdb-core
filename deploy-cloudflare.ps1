# TCDB Core - Cloudflare Deployment Script
$ErrorActionPreference = 'Stop'

Write-Host '====================================================================' -ForegroundColor Cyan
Write-Host 'TCDB Core - Cloudflare Edge Worker Deployment' -ForegroundColor Cyan
Write-Host '====================================================================' -ForegroundColor Cyan
Write-Host ''

# Check if wrangler is installed
try {
    $null = Get-Command wrangler -ErrorAction Stop
    Write-Host 'Wrangler CLI found' -ForegroundColor Green
    Write-Host ''
} catch {
    Write-Host 'Error: Wrangler CLI not found' -ForegroundColor Red
    Write-Host ''
    Write-Host 'Install with: npm install -g wrangler'
    exit 1
}

# Check if logged in
try {
    wrangler whoami 2>&1 | Out-Null
    Write-Host 'Authenticated with Cloudflare' -ForegroundColor Green
} catch {
    Write-Host 'Not logged in - logging in...' -ForegroundColor Yellow
    wrangler login
}

# Navigate to worker directory
Set-Location cloudflare/worker

Write-Host 'Installing dependencies...' -ForegroundColor Blue
npm install

Write-Host 'Building TypeScript...' -ForegroundColor Blue
npm run build

Write-Host 'Deploying to Cloudflare...' -ForegroundColor Blue
wrangler deploy

Write-Host ''
Write-Host '====================================================================' -ForegroundColor Cyan
Write-Host 'Deployment Complete!' -ForegroundColor Green
Write-Host '====================================================================' -ForegroundColor Cyan

# Return to root
Set-Location ../..
