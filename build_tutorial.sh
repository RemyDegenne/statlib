#!/usr/bin/env bash
# Build the Verso tutorial and replace the contents of tutorial/ with the output.
# Requires elan/lean to be installed (see https://lean-lang.org/install/).
set -euo pipefail
set -x

ROOT_DIR="$(cd "$(dirname "$0")" && pwd)"
WEBSITE_DIR="${WEBSITE_DIR:-"$ROOT_DIR/../stat-lib.github.io"}"

cd "$ROOT_DIR"

if [[ ! -d "$WEBSITE_DIR" ]]; then
  echo "Website directory not found: $WEBSITE_DIR" >&2
  exit 1
fi

# Type-check the Lean library used by the tutorial examples.
lake build Statlib.Inference.Inference

cd tutorial-manual

# Type-check the Verso source.
lake build

# Generate HTML via Verso.
rm -rf _out/site
lake exe manual --output _out/site

# Copy static files (CSS, JS) into the generated site.
mkdir -p _out/site/html-multi/static
cp static_files/* _out/site/html-multi/static

cd ..

# Replace the published tutorial output in the website repo.
rm -rf "$WEBSITE_DIR/tutorial"
mkdir -p "$WEBSITE_DIR/tutorial"
cp -r tutorial-manual/_out/site/html-multi/* "$WEBSITE_DIR/tutorial/"

echo
echo "Build complete. Open $WEBSITE_DIR/tutorial/index.html in a browser via the local static server."
