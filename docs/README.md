# TCDB Core - GitHub Pages

This directory contains the GitHub Pages deployment for the TCDB Core project.

## Homepage

The homepage showcases the TCDB AI Grounding System with:

- **146 comprehensive tests** (56 Rust unit tests + 90 Python integration tests)
- **4 core modules**: Topological Signatures, Provenance Tracking, Data Proofs, Cross-Domain Reasoning
- **TDD-verified implementation** with property-based testing
- **Complete documentation** and code examples

## Deployment

The site is automatically deployed to GitHub Pages via GitHub Actions whenever changes are pushed to the `main` branch.

**Live URL**: https://deepfriedcyber.github.io/tcdb-core

## Local Development

To view the homepage locally:

```bash
# Open in browser
open docs/index.html

# Or use a local server
cd docs
python -m http.server 8000
# Visit http://localhost:8000
```

## Updates

To update the homepage:

1. Edit `shared/TopoPersist Homepage.html`
2. Copy to `docs/index.html`
3. Commit and push to `main` branch
4. GitHub Actions will automatically deploy

## Source

The homepage source is maintained in `shared/TopoPersist Homepage.html` and copied to this directory for GitHub Pages deployment.

