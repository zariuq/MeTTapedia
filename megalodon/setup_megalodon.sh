#!/bin/bash
# Setup script for Megalodon proof assistant
# Downloads and builds Megalodon from CIIRC grid01

set -e

MEGALODON_URL="http://grid01.ciirc.cvut.cz/~chad/megalodon-1.13.tgz"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "=== Megalodon Setup ==="

# Check if already built
if [ -f "$SCRIPT_DIR/bin/megalodon" ]; then
    echo "Megalodon already built at $SCRIPT_DIR/bin/megalodon"
    echo "To rebuild, delete bin/megalodon and run this script again."
    exit 0
fi

# Check for OCaml
if ! command -v ocamlc &> /dev/null; then
    echo "OCaml not found. Installing..."
    if command -v apt-get &> /dev/null; then
        sudo apt-get update -qq && sudo apt-get install -y ocaml
    elif command -v brew &> /dev/null; then
        brew install ocaml
    else
        echo "Please install OCaml manually and run this script again."
        exit 1
    fi
fi

echo "OCaml version: $(ocamlc -version)"

# Download if needed
if [ ! -f "$SCRIPT_DIR/src/megalodon.ml" ]; then
    echo "Downloading Megalodon..."
    cd "$SCRIPT_DIR"
    curl -LO "$MEGALODON_URL"
    tar xzf megalodon-1.13.tgz --strip-components=1
    rm -f megalodon-1.13.tgz
fi

# Build
echo "Building Megalodon..."
cd "$SCRIPT_DIR"
./makebytecode

if [ -f "$SCRIPT_DIR/bin/megalodon" ]; then
    echo "=== Success! ==="
    echo "Megalodon built at: $SCRIPT_DIR/bin/megalodon"
    echo ""
    echo "Usage example:"
    echo "  $SCRIPT_DIR/bin/megalodon -I examples/egal/PfgEMay2021Preamble.mgs yourfile.mg"
else
    echo "Build failed. Check the output above for errors."
    exit 1
fi
