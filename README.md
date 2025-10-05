# TCDB Core - Topological Data Analysis System

Pure topological analysis framework with no application-specific logic.

## Features

-  Knowledge Graph TDA
-  REST API for topological analysis
-  Streaming persistent homology
-  100% TDD coverage

## Installation

`ash
pip install tcdb-core
`

Or for development:

`ash
git clone https://github.com/DeepFriedCyber/tcdb-core.git
cd tcdb-core
pip install -e ".[dev]"
`

## Quick Start

`python
from tcdb_api_tdd.app import create_app

app = create_app()
app.run()
`

## Testing

`ash
pytest tests/ -v
`

## License

MIT License
