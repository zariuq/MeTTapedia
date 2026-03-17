#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LOG_DIR="$ROOT_DIR/artifacts/conformance"
LOG_FILE="$LOG_DIR/simplehe_conformance_ci.log"

mkdir -p "$LOG_DIR"

cd "$ROOT_DIR"
ulimit -v 6291456
lake build Mettapedia.Conformance.SimpleHE 2>&1 | tee "$LOG_FILE"

if ! grep -Fq '("allChecksPass", true)' "$LOG_FILE"; then
  echo "SimpleHE conformance gate failed: expected (\"allChecksPass\", true) in log" >&2
  exit 1
fi

echo "SimpleHE conformance gate: PASS"
echo "  log: $LOG_FILE"
