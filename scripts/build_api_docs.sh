#!/usr/bin/env bash
# Build the API documentation of SHSLib into docbuild/.lake/api/doc.
#
# doc-gen4's Lake facet (`lake build SHSLib:docs`) also documents every module SHSLib imports:
# Mathlib, Batteries and Lean core, about 8,600 modules and 1.3 GB of HTML. This script runs doc-gen4
# only on the modules this site publishes: SHSLib, and the BrownianMotion and KolmogorovExtension4
# modules it imports. Links into Mathlib, Batteries and Lean core then go to the Mathlib
# documentation, https://leanprover-community.github.io/mathlib4_docs/ (see scripts/api_docs.py).
#
# It calls doc-gen4's command line in the order its Lake facet does: `bibPrepass`, `single` for each
# module, then `index`. That command line is the one of doc-gen4 v4.28.0, the tag that matches
# lean-toolchain. Newer doc-gen4 versions write the HTML from a database instead, so check this
# script again whenever lean-toolchain changes.
#
# Usage: scripts/build_api_docs.sh
#   DOCS_JOBS=N     run N doc-gen4 processes at a time (default: the number of CPUs). Each one loads
#                   the part of Mathlib its module imports, which takes several GB of memory.
#   DOCS_OFFLINE=1  don't download the Mathlib documentation's index; link declarations through
#                   its find page instead.
#
# CI (.github/workflows/docs.yml) and scripts/preview_docs.sh both run this script. SHSLib itself
# must already be built (`lake build`).
set -euo pipefail

cd "$(dirname "$0")/.."

# doc-gen4 is tagged per Lean release: use the tag that matches lean-toolchain (e.g. v4.28.0).
toolchain=$(<lean-toolchain)
rev=${toolchain#*:}

# A separate Lake package that requires doc-gen4 and SHSLib, sharing `.lake/packages` with the
# library, as doc-gen4's README recommends.
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
lake build doc-gen4
docgen=../.lake/packages/doc-gen4/.lake/build/bin/doc-gen4

# Start from an empty output: `index` lists every page it finds there.
rm -rf .lake/api
lake env "$docgen" bibPrepass --build .lake/api docs/references.bib

modules=$(python3 ../scripts/api_docs.py modules)
jobs=${DOCS_JOBS:-$(nproc)}
echo "Documenting $(wc -l <<< "$modules") modules, $jobs at a time"
lake env xargs -P "$jobs" -L 1 "$docgen" single --build .lake/api <<< "$modules"

lake env "$docgen" index --build .lake/api
python3 ../scripts/api_docs.py link .lake/api/doc ${DOCS_OFFLINE:+--offline}
python3 ../scripts/api_docs.py check .lake/api/doc
echo "API documentation written to docbuild/.lake/api/doc"
