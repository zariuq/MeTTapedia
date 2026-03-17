#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HYPERON_DIR="${HYPERON_DIR:-$ROOT_DIR/../../hyperon}"
PETTA_DIR="${PETTA_DIR:-$HYPERON_DIR/PeTTa}"
LOGTALK_ROOT="${1:-}"

SUMMARY_DIR="$ROOT_DIR/artifacts/conformance"
SUMMARY_FILE="$SUMMARY_DIR/unified_conformance_summary_latest.txt"
PROLOG_RESULTS="$ROOT_DIR/artifacts/prolog/swi_fixture_results_unified.jsonl"

mkdir -p "$SUMMARY_DIR"

step() {
  local name="$1"
  shift
  local log="$SUMMARY_DIR/${name}.log"
  echo "=== $name ===" | tee "$log"
  "$@" 2>&1 | tee -a "$log"
}

require_file() {
  local path="$1"
  if [[ ! -e "$path" ]]; then
    echo "missing required path: $path" >&2
    exit 2
  fi
}

require_file "$ROOT_DIR/scripts/prolog/run_conformance.sh"
require_file "$ROOT_DIR/scripts/conformance/run_he_io_conformance.sh"
require_file "$ROOT_DIR/scripts/conformance/check_simple_runtime_perf_gate.py"
require_file "$ROOT_DIR/Mettapedia/Conformance/SimpleHE.lean"
require_file "$PETTA_DIR/unit/run_petta_unit_69.sh"
require_file "$PETTA_DIR/unit/run_he_suite_like_petta.sh"

START_UTC="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"

step "prolog_conformance" \
  "$ROOT_DIR/scripts/prolog/run_conformance.sh" \
  "$PROLOG_RESULTS" \
  "$LOGTALK_ROOT"

step "simplehe_build" bash -lc "cd '$ROOT_DIR' && ulimit -v 6291456 && lake build Mettapedia.Conformance.SimpleHE"
if ! grep -Fq '("allChecksPass", true)' "$SUMMARY_DIR/simplehe_build.log"; then
  echo "SimpleHE gate failed: expected ('allChecksPass', true) in build log" >&2
  exit 1
fi

step "he_io_conformance" bash -lc "cd '$ROOT_DIR' && ./scripts/conformance/run_he_io_conformance.sh"
step "simple_runtime_perf_gate" \
  bash -lc "cd '$ROOT_DIR' && ulimit -v 10485760 && python3 scripts/conformance/check_simple_runtime_perf_gate.py"

step "petta_runtime_suite" bash -lc "cd '$PETTA_DIR' && ./unit/run_petta_unit_69.sh"
step "he_runtime_suite" bash -lc "cd '$PETTA_DIR' && ./unit/run_he_suite_like_petta.sh"

END_UTC="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"

cat > "$SUMMARY_FILE" <<REPORT
Unified conformance summary
started_utc: $START_UTC
finished_utc: $END_UTC
status: PASS

components:
- prolog: PASS (scripts/prolog/run_conformance.sh)
- simplehe: PASS (lake build Mettapedia.Conformance.SimpleHE + allChecksPass=true)
- he_io: PASS (scripts/conformance/run_he_io_conformance.sh, bag-equivalence comparator + baseline drift check)
- simple_runtime_perf_gate: PASS (scripts/conformance/check_simple_runtime_perf_gate.py, threshold <=10x)
- petta_runtime: PASS (unit/run_petta_unit_69.sh)
- he_runtime: PASS (unit/run_he_suite_like_petta.sh)

artifacts:
- $PROLOG_RESULTS
- $SUMMARY_DIR/prolog_conformance.log
- $SUMMARY_DIR/simplehe_build.log
- $SUMMARY_DIR/he_io_conformance.log
- $SUMMARY_DIR/simple_runtime_perf_gate.log
- $SUMMARY_DIR/petta_runtime_suite.log
- $SUMMARY_DIR/he_runtime_suite.log
REPORT

echo "Unified conformance: PASS"
echo "Summary: $SUMMARY_FILE"
