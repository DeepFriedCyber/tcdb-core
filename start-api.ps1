# Start TCDB FastAPI Server

$ErrorActionPreference = "Stop"

Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host "Starting TCDB FastAPI Server" -ForegroundColor Cyan
Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host ""

# Navigate to python directory
Set-Location python

Write-Host "Starting FastAPI on http://localhost:8000" -ForegroundColor Green
Write-Host ""
Write-Host "API Endpoints:" -ForegroundColor Yellow
Write-Host "  Homepage:        http://localhost:8000" -ForegroundColor White
Write-Host "  API Docs:        http://localhost:8000/docs" -ForegroundColor White
Write-Host "  Health Check:    http://localhost:8000/descriptor/health" -ForegroundColor White
Write-Host "  Simple API:      http://localhost:8000/descriptor/compute" -ForegroundColor White
Write-Host ""
Write-Host "Press Ctrl+C to stop the server" -ForegroundColor Gray
Write-Host "====================================================================" -ForegroundColor Cyan
Write-Host ""

# Start uvicorn
python -m uvicorn tcdb_api.app:app --host 0.0.0.0 --port 8000 --reload

