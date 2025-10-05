# TDD Knowledge Graph with Topological Data Analysis

## Test-Driven Development Architecture

**Tests Written FIRST → Implementation Satisfies Tests**

### Core Principles
- ✅ Core tests MUST always pass (rock-solid foundation)
- ⚠️ Module tests CAN fail (experimental, isolated)
- 🔄 Red → Green → Refactor (TDD cycle)

## Quick Start

```bash
pip install -r requirements.txt
pytest -v
python examples/basic_usage.py
```

## Structure

- `tests/` - Tests written FIRST
- `core/` - Rock-solid core implementation
- `modules/` - Pluggable modules
- `modular_harness.py` - Benchmarking harness

See TDD_GUIDE.md for detailed workflow.