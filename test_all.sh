#!/bin/bash
# TCDB-Core Comprehensive Test Suite
# Run all tests to verify the system is working

set -e  # Exit on error

echo "🧪 TCDB-Core Test Suite"
echo "======================="
echo ""

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Test counter
TESTS_PASSED=0
TESTS_FAILED=0

# Function to print test result
test_result() {
    if [ $? -eq 0 ]; then
        echo -e "${GREEN}✓ $1${NC}"
        ((TESTS_PASSED++))
    else
        echo -e "${RED}✗ $1${NC}"
        ((TESTS_FAILED++))
    fi
}

# 1. Rust Tests
echo "1️⃣  Running Rust Tests..."
echo "------------------------"
cd rust
cargo test --lib 2>&1 | tail -n 5
test_result "Rust unit tests"
cd ..
echo ""

# 2. Rust Build
echo "2️⃣  Building Rust Library..."
echo "----------------------------"
cd rust
cargo build --release > /dev/null 2>&1
test_result "Rust release build"
cd ..
echo ""

# 3. Lean Verification
echo "3️⃣  Verifying Lean Proofs..."
echo "----------------------------"
cd lean
lake build > /dev/null 2>&1
test_result "Lean proof verification"
cd ..
echo ""

# 4. Python Bindings
echo "4️⃣  Building Python Bindings..."
echo "--------------------------------"
maturin develop --release > /dev/null 2>&1
test_result "Python bindings build"
echo ""

# 5. Python Import Test
echo "5️⃣  Testing Python Imports..."
echo "-----------------------------"
python -c "import tcdb_core; print('Import successful')" > /dev/null 2>&1
test_result "Python import"
echo ""

# 6. Python Functionality Tests
echo "6️⃣  Testing Python Functionality..."
echo "------------------------------------"

# Test Simplex
python -c "
import tcdb_core
s = tcdb_core.Simplex([0, 1, 2])
assert s.dimension() == 2
print('Simplex: OK')
" > /dev/null 2>&1
test_result "Simplex operations"

# Test SimplicialComplex
python -c "
import tcdb_core
c = tcdb_core.SimplicialComplex()
c.add_simplex([0, 1, 2])
assert c.dimension() == 2
assert c.euler_characteristic() == 1
print('SimplicialComplex: OK')
" > /dev/null 2>&1
test_result "SimplicialComplex operations"

# Test Filtration
python -c "
import tcdb_core
f = tcdb_core.Filtration()
f.add_simplex(0.0, [0])
f.add_simplex(0.5, [0, 1])
assert len(f.values()) == 2
print('Filtration: OK')
" > /dev/null 2>&1
test_result "Filtration operations"

# Test PersistencePoint
python -c "
import tcdb_core
p = tcdb_core.PersistencePoint(0.0, 1.0, 1)
assert p.persistence() == 1.0
print('PersistencePoint: OK')
" > /dev/null 2>&1
test_result "PersistencePoint operations"

echo ""

# 7. Examples
echo "7️⃣  Running Examples..."
echo "-----------------------"
if [ -f "examples/basic_usage.py" ]; then
    python examples/basic_usage.py > /dev/null 2>&1
    test_result "Basic usage example"
else
    echo -e "${YELLOW}⊘ Basic usage example not found${NC}"
fi
echo ""

# Summary
echo "📊 Test Summary"
echo "==============="
echo -e "Tests passed: ${GREEN}${TESTS_PASSED}${NC}"
echo -e "Tests failed: ${RED}${TESTS_FAILED}${NC}"
echo ""

if [ $TESTS_FAILED -eq 0 ]; then
    echo -e "${GREEN}✅ All tests passed! System is working correctly.${NC}"
    exit 0
else
    echo -e "${RED}❌ Some tests failed. Please check the output above.${NC}"
    exit 1
fi

