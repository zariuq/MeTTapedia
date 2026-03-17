#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RESULTS_PATH="${1:-$ROOT_DIR/artifacts/conformance/he_io_results_latest.jsonl}"
CONDA_ENV="${CONDA_ENV:-hyperon}"
COMPARE_LEAN="${HE_IO_COMPARE_LEAN:-0}"
REQUIRE_LEAN_PARITY="${HE_IO_REQUIRE_LEAN_PARITY:-0}"
BASELINE_CHECK="${HE_IO_BASELINE_CHECK:-1}"
BASELINE_PATH="${HE_IO_BASELINE_PATH:-$ROOT_DIR/scripts/conformance/he_io_baseline_hyperon_0.2.10.json}"

cd "$ROOT_DIR"
ulimit -v 6291456
python3 scripts/conformance/check_he_io_lean_anchors.py
RUN_ARGS=(
  --conda-env "$CONDA_ENV"
  --results "$RESULTS_PATH"
)
if [[ "$COMPARE_LEAN" == "1" ]]; then
  RUN_ARGS+=(--compare-lean)
fi
if [[ "$REQUIRE_LEAN_PARITY" == "1" ]]; then
  RUN_ARGS+=(--require-lean-parity)
fi
python3 scripts/conformance/run_he_io_conformance.py \
  "${RUN_ARGS[@]}"

if [[ "$BASELINE_CHECK" == "1" ]]; then
  python3 scripts/conformance/check_he_io_baseline.py \
    --results "$RESULTS_PATH" \
    --baseline "$BASELINE_PATH"
fi
