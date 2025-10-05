#!/bin/bash

echo "🚀 Setting up Topological Streaming Engine..."

# Build Rust core
echo "Building Rust core..."
cd rust_core
cargo build --release
cargo test
cd ..

# Build Python bindings
echo "Building Python bindings..."
cd python_bindings
pip install maturin
maturin develop --release
cd ..

# Install Python dependencies
echo "Installing Python dependencies..."
pip install numpy

# Run tests
echo "Running tests..."
python tests/integration_test.py

# Run example
echo "Running flash crash detector..."
python examples/flash_crash_detector.py

echo "✅ Setup complete!"
