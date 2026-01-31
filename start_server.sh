#!/bin/bash
# Start the orchestrator server

cd "$(dirname "$0")"

# Ensure dependencies are installed
pip install -r requirements.txt -q

# Start server
echo "Starting Orchestrator API on port 8000..."
python -m orchestrator.server
