# TCDB Core - Cloudflare Tunnel Setup Script
# This script sets up a Cloudflare Tunnel to expose your local FastAPI server

$ErrorActionPreference = "Stop"

Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host "TCDB Core - Cloudflare Tunnel Setup" -ForegroundColor Cyan
Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host ""

# Check if cloudflared is installed
try {
    $version = cloudflared --version
    Write-Host "Cloudflared found: $version" -ForegroundColor Green
    Write-Host ""
} catch {
    Write-Host "Error: cloudflared not found" -ForegroundColor Red
    Write-Host "Install with: winget install --id Cloudflare.cloudflared" -ForegroundColor Yellow
    exit 1
}

# Step 1: Authenticate
Write-Host "Step 1: Authenticating with Cloudflare..." -ForegroundColor Blue
Write-Host "This will open your browser. Please login to Cloudflare." -ForegroundColor Yellow
Write-Host ""

cloudflared tunnel login

if ($LASTEXITCODE -ne 0) {
    Write-Host "Authentication failed" -ForegroundColor Red
    exit 1
}

Write-Host ""
Write-Host "Authentication successful!" -ForegroundColor Green
Write-Host ""

# Step 2: Create tunnel
Write-Host "Step 2: Creating tunnel 'tcdb-api'..." -ForegroundColor Blue
Write-Host ""

$tunnelOutput = cloudflared tunnel create tcdb-api 2>&1

if ($LASTEXITCODE -ne 0) {
    if ($tunnelOutput -match "already exists") {
        Write-Host "Tunnel 'tcdb-api' already exists. Using existing tunnel." -ForegroundColor Yellow
    } else {
        Write-Host "Failed to create tunnel" -ForegroundColor Red
        Write-Host $tunnelOutput
        exit 1
    }
} else {
    Write-Host "Tunnel created successfully!" -ForegroundColor Green
}

Write-Host ""

# Step 3: Get tunnel info
Write-Host "Step 3: Getting tunnel information..." -ForegroundColor Blue
Write-Host ""

$tunnelInfo = cloudflared tunnel list | Select-String "tcdb-api"
Write-Host $tunnelInfo
Write-Host ""

# Extract tunnel ID
$tunnelId = ($tunnelInfo -split '\s+')[0]
Write-Host "Tunnel ID: $tunnelId" -ForegroundColor Green
Write-Host ""

# Step 4: Create config file
Write-Host "Step 4: Creating tunnel configuration..." -ForegroundColor Blue
Write-Host ""

$configDir = "$env:USERPROFILE\.cloudflared"
$configFile = "$configDir\config.yml"
$credentialsFile = "$configDir\$tunnelId.json"

# Create config content
$configContent = @"
tunnel: $tunnelId
credentials-file: $credentialsFile

ingress:
  - hostname: api.tcdb.uk
    service: http://localhost:8000
  - service: http_status:404
"@

# Write config file
New-Item -ItemType Directory -Force -Path $configDir | Out-Null
$configContent | Out-File -FilePath $configFile -Encoding UTF8

Write-Host "Config file created: $configFile" -ForegroundColor Green
Write-Host ""

# Step 5: Route DNS
Write-Host "Step 5: Setting up DNS routing..." -ForegroundColor Blue
Write-Host ""

$dnsOutput = cloudflared tunnel route dns tcdb-api api.tcdb.uk 2>&1

if ($LASTEXITCODE -ne 0) {
    if ($dnsOutput -match "already exists") {
        Write-Host "DNS route already exists" -ForegroundColor Yellow
    } else {
        Write-Host "Warning: DNS routing may have failed" -ForegroundColor Yellow
        Write-Host $dnsOutput
    }
} else {
    Write-Host "DNS route created successfully!" -ForegroundColor Green
}

Write-Host ""
Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host "Tunnel Setup Complete!" -ForegroundColor Green
Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host ""
Write-Host "Next steps:" -ForegroundColor Yellow
Write-Host ""
Write-Host "1. Start your FastAPI server:" -ForegroundColor White
Write-Host "   cd python" -ForegroundColor Gray
Write-Host "   python -m uvicorn tcdb_api.app:app --host 0.0.0.0 --port 8000" -ForegroundColor Gray
Write-Host ""
Write-Host "2. In another terminal, start the tunnel:" -ForegroundColor White
Write-Host "   cloudflared tunnel run tcdb-api" -ForegroundColor Gray
Write-Host ""
Write-Host "3. Test your deployment:" -ForegroundColor White
Write-Host "   curl https://api.tcdb.uk/descriptor/health" -ForegroundColor Gray
Write-Host "   curl https://tcdb-edge.aps330.workers.dev/descriptor/health" -ForegroundColor Gray
Write-Host ""
Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host ""
Write-Host "Tunnel ID: $tunnelId" -ForegroundColor Cyan
Write-Host "Config:    $configFile" -ForegroundColor Cyan
Write-Host "Hostname:  api.tcdb.uk" -ForegroundColor Cyan
Write-Host ""

