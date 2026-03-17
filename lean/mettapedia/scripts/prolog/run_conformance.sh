#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RESULTS_PATH="${1:-$ROOT_DIR/artifacts/prolog/swi_fixture_results_latest.jsonl}"
LOGTALK_ROOT="${2:-}"

mkdir -p "$(dirname "$RESULTS_PATH")"

pushd "$ROOT_DIR" >/dev/null

swipl -q -s scripts/prolog/swi_fixture_runner.pl -- "$RESULTS_PATH"
python3 scripts/prolog/check_lean_swi_parity.py \
  --lean-file Mettapedia/Logic/Prolog/FixtureCorpus.lean \
  --cases-file scripts/prolog/swi_fixture_cases.pl \
  --results-file "$RESULTS_PATH"
python3 scripts/prolog/check_iso_probe_error_cases.py \
  --results-file "$RESULTS_PATH"

if [[ -n "$LOGTALK_ROOT" ]]; then
  python3 scripts/prolog/report_logtalk_iso_coverage.py \
    --logtalk-root "$LOGTALK_ROOT" \
    --require-lean-theorem-exact 63 \
    --require-lean-case-exact 63 \
    --require-lean-theorem-normalized 63 \
    --require-lean-case-normalized 63
fi

echo "Prolog conformance: PASS"
echo "  results: $RESULTS_PATH"
if [[ -n "$LOGTALK_ROOT" ]]; then
  echo "  logtalk root: $LOGTALK_ROOT"
fi

popd >/dev/null
