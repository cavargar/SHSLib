#!/usr/bin/env bash
# Build the API documentation locally the way CI does (scripts/build_api_docs.sh), then serve it at
# http://localhost:8000.
#
# Usage: scripts/preview_docs.sh [--no-serve]
#
# Source links point at the current commit on GitHub, so they work once that commit is pushed.
set -euo pipefail

cd "$(dirname "$0")/.."
scripts/build_api_docs.sh

if [[ ${1:-} != --no-serve ]]; then
  echo "Serving the docs at http://localhost:8000 (Ctrl-C to stop)"
  python3 -m http.server --directory docbuild/.lake/api/doc 8000
fi
