# Topological Streaming Engine

Real-time flash crash detection using streaming persistent homology.

## Quick Start

### Rust Core
```bash
cd rust_core
cargo build --release
cargo test
```

### Python Bindings
```bash
cd python_bindings
pip install maturin
maturin develop
```

### Run Flash Crash Detector
```bash
python examples/flash_crash_detector.py
```

## Architecture

- **Rust Core**: High-performance streaming persistent homology
- **Python Bindings**: PyO3-based interface
- **Flash Crash Detection**: Real-time market anomaly detection
- **Dashboard**: React-based monitoring UI

## Components

1. `rust_core/` - Core Rust implementation
2. `python_bindings/` - Python interface via PyO3
3. `examples/` - Usage examples
4. `dashboard/` - React monitoring dashboard
5. `tests/` - Integration tests

## License

MIT
