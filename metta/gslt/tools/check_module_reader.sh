#!/usr/bin/env bash
# Check CeTTa's grammar-driven readings against Lean's independent .module reader.
# Usage from metta/gslt: CETTA_BIN=<cetta> tools/check_module_reader.sh
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
cetta=${CETTA_BIN:?set CETTA_BIN to a CeTTa binary}
output=${MODULE_READER_OUT:-"$here/tools/out"}
mkdir -p "$output"
output=$(cd "$output" && pwd)
python3 "$here/tools/emit_module_read_packets.py" "$cetta" "$output"
cd "$here/../../lean/mettapedia"
lake env lean --run ../../metta/gslt/tools/check_module_reader.lean "$output/module_reads.metta"
