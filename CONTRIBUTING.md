# Contributing to TCDB-Core

Thank you for your interest in contributing to TCDB-Core! This document provides guidelines and instructions for contributing.

## 🎯 Code of Conduct

- Be respectful and inclusive
- Focus on constructive feedback
- Help others learn and grow
- Follow the project's coding standards

## 🚀 Getting Started

### Prerequisites

- **Rust** 1.70 or higher
- **Python** 3.9 or higher
- **Lean 4** (optional, for formal verification)
- **Git** for version control

### Development Setup

1. **Clone the repository**:
   ```bash
   git clone https://github.com/DeepFriedCyber/tcdb-core.git
   cd tcdb-core
   ```

2. **Set up Python virtual environment**:
   ```bash
   python -m venv .venv
   source .venv/bin/activate  # On Windows: .venv\Scripts\activate
   ```

3. **Install dependencies**:
   ```bash
   # Install Python dependencies
   pip install -e ".[dev]"
   
   # Install maturin for building Python bindings
   pip install maturin
   ```

4. **Build Rust components**:
   ```bash
   cd rust
   cargo build
   cargo test
   ```

5. **Build Python bindings**:
   ```bash
   maturin develop --release
   ```

## 🧪 Testing

### Run All Tests

```bash
# PowerShell (Windows)
.\test_all.ps1

# Bash (Linux/macOS)
./test_all.sh
```

### Run Specific Test Suites

**Rust Tests**:
```bash
cd rust
cargo test
cargo test --release  # Optimized build
```

**Python Tests**:
```bash
python test_python.py
```

**Integration Tests**:
```bash
cd rust
cargo test --test integration_test
```

### Test Coverage

We aim for:
- **Rust**: 100% coverage for core algorithms
- **Python**: 100% coverage for API endpoints
- **Integration**: All major workflows tested

## 📝 Coding Standards

### Rust

- Follow [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- Use `cargo fmt` for formatting
- Use `cargo clippy` for linting
- Document all public APIs with doc comments
- Write tests for all new functionality

Example:
```rust
/// Computes the Euler characteristic of a simplicial complex.
///
/// # Arguments
///
/// * `complex` - The simplicial complex to analyze
///
/// # Returns
///
/// The Euler characteristic as an i64
///
/// # Examples
///
/// ```
/// use tcdb_core::SimplicialComplex;
/// let complex = SimplicialComplex::new();
/// let chi = complex.euler_characteristic();
/// ```
pub fn euler_characteristic(&self) -> i64 {
    // Implementation
}
```

### Python

- Follow [PEP 8](https://pep8.org/)
- Use type hints for all functions
- Write docstrings for all public APIs
- Use `black` for formatting
- Use `ruff` for linting

Example:
```python
def compute_persistence(
    filtration: Filtration,
    dimension: int = 2
) -> PersistenceDiagram:
    """
    Compute persistent homology for a filtration.
    
    Args:
        filtration: The filtration to analyze
        dimension: Maximum homology dimension to compute
        
    Returns:
        A persistence diagram containing birth-death pairs
        
    Raises:
        ValueError: If dimension is negative
    """
    # Implementation
```

### Lean

- Follow Lean 4 conventions
- Document all theorems and definitions
- Provide proof sketches for complex theorems
- Use mathlib4 when possible

## 🔄 Contribution Workflow

### 1. Create an Issue

Before starting work, create an issue describing:
- The problem or feature
- Proposed solution
- Any breaking changes

### 2. Fork and Branch

```bash
# Fork the repository on GitHub
git clone https://github.com/YOUR_USERNAME/tcdb-core.git
cd tcdb-core

# Create a feature branch
git checkout -b feature/your-feature-name
```

### 3. Make Changes

- Write code following the coding standards
- Add tests for new functionality
- Update documentation as needed
- Ensure all tests pass

### 4. Commit

Use conventional commit messages:

```bash
git commit -m "feat: add Rips complex construction"
git commit -m "fix: correct Euler characteristic for empty complex"
git commit -m "docs: update API documentation"
git commit -m "test: add tests for filtration monotonicity"
```

**Commit Types**:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `test`: Test additions or changes
- `refactor`: Code refactoring
- `perf`: Performance improvements
- `chore`: Build process or auxiliary tool changes

### 5. Push and Create Pull Request

```bash
git push origin feature/your-feature-name
```

Then create a pull request on GitHub with:
- Clear description of changes
- Link to related issues
- Screenshots (if UI changes)
- Test results

### 6. Code Review

- Address reviewer feedback
- Keep the PR focused and small
- Be responsive to comments
- Update tests and docs as needed

## 🏗️ Project Structure

```
tcdb-core/
├── rust/               # Rust core library
│   ├── src/
│   │   ├── lib.rs
│   │   ├── simplicial_complex.rs
│   │   ├── filtration.rs
│   │   ├── persistent_homology.rs
│   │   └── bindings.rs
│   └── tests/
├── python/             # Python API
│   ├── tcdb_api/
│   └── tests/
├── lean/               # Lean formal verification
│   └── Tcdb/
├── examples/           # Example programs
├── docs/               # Documentation
└── tests/              # Integration tests
```

## 🐛 Reporting Bugs

When reporting bugs, include:

1. **Description**: Clear description of the bug
2. **Steps to Reproduce**: Minimal example to reproduce
3. **Expected Behavior**: What should happen
4. **Actual Behavior**: What actually happens
5. **Environment**: OS, Rust version, Python version
6. **Logs**: Relevant error messages or stack traces

## 💡 Feature Requests

When requesting features, include:

1. **Use Case**: Why is this feature needed?
2. **Proposed Solution**: How should it work?
3. **Alternatives**: Other approaches considered
4. **Breaking Changes**: Will this break existing code?

## 📚 Documentation

### Types of Documentation

1. **API Documentation**: In-code doc comments
2. **User Guides**: Markdown files in `docs/`
3. **Examples**: Working code in `examples/`
4. **Architecture**: High-level design docs

### Building Documentation

**Rust**:
```bash
cargo doc --open
```

**Python**:
```bash
cd python
pdoc tcdb_api --html --output-dir docs
```

## 🎓 Learning Resources

### Topological Data Analysis
- [Computational Topology](https://www.maths.ed.ac.uk/~v1ranick/papers/edelcomp.pdf)
- [Persistent Homology Tutorial](https://www.math.upenn.edu/~ghrist/preprints/barcodes.pdf)

### Rust
- [The Rust Book](https://doc.rust-lang.org/book/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)

### Lean
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)

## ✅ Checklist Before Submitting PR

- [ ] Code follows project style guidelines
- [ ] All tests pass locally
- [ ] New tests added for new functionality
- [ ] Documentation updated
- [ ] Commit messages follow conventional format
- [ ] No merge conflicts with main branch
- [ ] PR description is clear and complete

## 🙏 Thank You!

Your contributions make TCDB-Core better for everyone. We appreciate your time and effort!

## 📧 Contact

- **Issues**: [GitHub Issues](https://github.com/DeepFriedCyber/tcdb-core/issues)
- **Discussions**: [GitHub Discussions](https://github.com/DeepFriedCyber/tcdb-core/discussions)

---

**Happy Contributing! 🚀**

