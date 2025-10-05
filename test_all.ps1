# TCDB-Core Comprehensive Test Suite (PowerShell)
# Run all tests to verify the system is working

Write-Host "🧪 TCDB-Core Test Suite" -ForegroundColor Cyan
Write-Host "=======================" -ForegroundColor Cyan
Write-Host ""

$TestsPassed = 0
$TestsFailed = 0

function Test-Result {
    param($TestName)
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✓ $TestName" -ForegroundColor Green
        $script:TestsPassed++
    } else {
        Write-Host "✗ $TestName" -ForegroundColor Red
        $script:TestsFailed++
    }
}

# 1. Rust Tests
Write-Host "1️⃣  Running Rust Tests..." -ForegroundColor Yellow
Write-Host "------------------------"
Push-Location rust
cargo test --lib 2>&1 | Select-Object -Last 5
Test-Result "Rust unit tests"
Pop-Location
Write-Host ""

# 2. Rust Build
Write-Host "2️⃣  Building Rust Library..." -ForegroundColor Yellow
Write-Host "----------------------------"
Push-Location rust
cargo build --release 2>&1 | Out-Null
Test-Result "Rust release build"
Pop-Location
Write-Host ""

# 3. Lean Verification
Write-Host "3️⃣  Verifying Lean Proofs..." -ForegroundColor Yellow
Write-Host "----------------------------"
Push-Location lean
lake build 2>&1 | Out-Null
Test-Result "Lean proof verification"
Pop-Location
Write-Host ""

# 4. Python Bindings
Write-Host "4️⃣  Building Python Bindings..." -ForegroundColor Yellow
Write-Host "--------------------------------"
maturin develop --release 2>&1 | Out-Null
Test-Result "Python bindings build"
Write-Host ""

# 5. Python Import Test
Write-Host "5️⃣  Testing Python Imports..." -ForegroundColor Yellow
Write-Host "-----------------------------"
python -c "import tcdb_core; print('Import successful')" 2>&1 | Out-Null
Test-Result "Python import"
Write-Host ""

# 6. Python Functionality Tests
Write-Host "6️⃣  Testing Python Functionality..." -ForegroundColor Yellow
Write-Host "------------------------------------"

# Test Simplex
python -c @"
import tcdb_core
s = tcdb_core.Simplex([0, 1, 2])
assert s.dimension() == 2
print('Simplex: OK')
"@ 2>&1 | Out-Null
Test-Result "Simplex operations"

# Test SimplicialComplex
python -c @"
import tcdb_core
c = tcdb_core.SimplicialComplex()
c.add_simplex([0, 1, 2])
assert c.dimension() == 2
assert c.euler_characteristic() == 1
print('SimplicialComplex: OK')
"@ 2>&1 | Out-Null
Test-Result "SimplicialComplex operations"

# Test Filtration
python -c @"
import tcdb_core
f = tcdb_core.Filtration()
f.add_simplex(0.0, [0])
f.add_simplex(0.5, [0, 1])
assert len(f.values()) == 2
print('Filtration: OK')
"@ 2>&1 | Out-Null
Test-Result "Filtration operations"

# Test PersistencePoint
python -c @"
import tcdb_core
p = tcdb_core.PersistencePoint(0.0, 1.0, 1)
assert p.persistence() == 1.0
print('PersistencePoint: OK')
"@ 2>&1 | Out-Null
Test-Result "PersistencePoint operations"

Write-Host ""

# 7. Examples
Write-Host "7️⃣  Running Examples..." -ForegroundColor Yellow
Write-Host "-----------------------"
if (Test-Path "examples/basic_usage.py") {
    python examples/basic_usage.py 2>&1 | Out-Null
    Test-Result "Basic usage example"
} else {
    Write-Host "⊘ Basic usage example not found" -ForegroundColor Yellow
}
Write-Host ""

# Summary
Write-Host "📊 Test Summary" -ForegroundColor Cyan
Write-Host "===============" -ForegroundColor Cyan
Write-Host "Tests passed: $TestsPassed" -ForegroundColor Green
Write-Host "Tests failed: $TestsFailed" -ForegroundColor Red
Write-Host ""

if ($TestsFailed -eq 0) {
    Write-Host "✅ All tests passed! System is working correctly." -ForegroundColor Green
    exit 0
} else {
    Write-Host "❌ Some tests failed. Please check the output above." -ForegroundColor Red
    exit 1
}

