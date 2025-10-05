.PHONY: help build test clean install dev rust-test python-test lean-check all

help:
	@echo "🦀🔬 TCDB Core - Rust + Lean TDA System"
	@echo ""
	@echo "Available targets:"
	@echo "  make build        - Build Rust library and Python bindings"
	@echo "  make test         - Run all tests (Rust + Python)"
	@echo "  make rust-test    - Run Rust tests only"
	@echo "  make python-test  - Run Python tests only"
	@echo "  make lean-check   - Verify Lean proofs"
	@echo "  make install      - Install Python package"
	@echo "  make dev          - Install in development mode"
	@echo "  make clean        - Clean build artifacts"
	@echo "  make all          - Build everything and run all tests"

build:
	@echo "🔨 Building Rust library..."
	cd rust && cargo build --release
	@echo "🐍 Building Python bindings..."
	maturin develop --release

rust-test:
	@echo "🧪 Running Rust tests..."
	cd rust && cargo test --all-features

python-test:
	@echo "🐍 Running Python tests..."
	pytest python/tests -v

lean-check:
	@echo "🔬 Verifying Lean proofs..."
	cd lean && lake build

test: rust-test python-test
	@echo "✅ All tests passed!"

install:
	@echo "📦 Installing tcdb-core..."
	maturin build --release
	pip install target/wheels/*.whl

dev:
	@echo "🔧 Installing in development mode..."
	maturin develop
	pip install -e ".[dev]"

clean:
	@echo "🧹 Cleaning build artifacts..."
	cd rust && cargo clean
	rm -rf target/
	rm -rf python/tcdb_api/__pycache__/
	rm -rf python/tests/__pycache__/
	rm -rf .pytest_cache/
	rm -rf *.egg-info/
	cd lean && lake clean

all: build test lean-check
	@echo "✅ Build and verification complete!"

# Development helpers
format:
	@echo "🎨 Formatting code..."
	cd rust && cargo fmt
	black python/

lint:
	@echo "🔍 Linting code..."
	cd rust && cargo clippy
	ruff check python/

bench:
	@echo "⚡ Running benchmarks..."
	cd rust && cargo bench

docs:
	@echo "📚 Building documentation..."
	cd rust && cargo doc --no-deps --open

