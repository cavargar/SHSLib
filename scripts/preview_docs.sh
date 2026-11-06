#!/usr/bin/env bash
# Build the API documentation locally the way CI does (leanprover-community/docgen-action's
# scripts/build_docs.sh), then serve it at http://localhost:8000.
#
# Usage: scripts/preview_docs.sh [--no-serve]
#
# The first run documents the whole import closure (Lean core and the part of Mathlib that SHSLib
# imports), which takes a while; later runs redo only what changed. `docbuild/` shares
# `.lake/packages` with the library, as doc-gen4's README recommends. Source links point at the
# current commit on GitHub, so they work once that commit is pushed.
set -euo pipefail

cd "$(dirname "$0")/.."

# doc-gen4 is tagged per Lean release: use the tag that matches lean-toolchain (e.g. v4.28.0).
toolchain=$(<lean-toolchain)
rev=${toolchain#*:}

mkdir -p docbuild/docs
cat > docbuild/lakefile.toml <<TOML
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "$rev"

[[require]]
name = "SHSLib"
path = "../"
TOML

# doc-gen4 reads the bibliography from docs/references.bib of the package it runs in.
cp references.bib docbuild/docs/references.bib

# doc-gen4's C dependencies (md4c, the Unicode tables) are compiled with `cc`. Without one, fall
# back to the clang that ships with the Lean toolchain, with its builtin headers; the C library
# headers still come from the system (/usr/include).
if ! command -v cc >/dev/null; then
  lean_prefix=$(lean --print-prefix)
  mkdir -p docbuild/.cc
  printf '#!/bin/sh\nexec "%s/bin/clang" -isystem "%s/include/clang" "$@"\n' \
    "$lean_prefix" "$lean_prefix" > docbuild/.cc/cc
  chmod +x docbuild/.cc/cc
  export PATH="$PWD/docbuild/.cc:$PATH"
fi

cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update SHSLib
lake build SHSLib:docs

if [[ ${1:-} != --no-serve ]]; then
  echo "Serving the docs at http://localhost:8000 (Ctrl-C to stop)"
  python3 -m http.server --directory .lake/build/doc 8000
fi
