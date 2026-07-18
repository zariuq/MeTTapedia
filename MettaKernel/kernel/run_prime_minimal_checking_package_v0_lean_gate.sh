#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPOSITORY="$(cd "$ROOT/../.." && pwd)"
LEAN_ROOT="${PRIME_LEAN_ROOT:-$REPOSITORY/lean/mettapedia}"
SOURCE_REL="Mettapedia/Languages/MeTTa/Prime/MinimalCheckingPackage.lean"
SOURCE="$LEAN_ROOT/$SOURCE_REL"
LOGDIR="$ROOT/parity_logs"
LOG="$LOGDIR/prime_minimal_checking_package_v0_lean.log"

mkdir -p "$LOGDIR"

if [[ ! -f "$SOURCE" ]]; then
  echo "PRIME MINIMAL CHECKING PACKAGE V0 LEAN GATE: FAIL (Lean witness source absent; set PRIME_LEAN_ROOT to the tree containing it)"
  exit 1
fi

if grep -Eq '\b(sorry|admit|axiom|native_decide|theorem_wanted)\b|_wanted' \
    "$SOURCE"; then
  echo "PRIME MINIMAL CHECKING PACKAGE V0 LEAN GATE: FAIL (forbidden proof placeholder or axiom token)"
  exit 1
fi

if ! (cd "$LEAN_ROOT" && lake env lean "$SOURCE_REL") >"$LOG" 2>&1; then
  echo "PRIME MINIMAL CHECKING PACKAGE V0 LEAN GATE: FAIL (Lean check failed; log: $LOG)"
  exit 1
fi

if grep -Eq '(^|[[:space:]])(error:|warning:)' "$LOG"; then
  echo "PRIME MINIMAL CHECKING PACKAGE V0 LEAN GATE: FAIL (Lean diagnostic found; log: $LOG)"
  exit 1
fi

echo "PRIME MINIMAL CHECKING PACKAGE V0 LEAN GATE: PASS (MP, DTT, HOTG, isolation, and cache projection)"
