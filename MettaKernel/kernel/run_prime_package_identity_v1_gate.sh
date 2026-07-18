#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPOSITORY="$(cd "$ROOT/../.." && pwd)"
AIHUB="${AIHUB:-$(cd "$REPOSITORY/.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/cetta-he-prime-dtt-chainer-20260715/cetta}"
LEAN_ROOT="${PRIME_LEAN_ROOT:-$REPOSITORY/lean/mettapedia}"
SOURCE="$ROOT/prime_package_identity_v1.metta"
LEAN_REL="Mettapedia/Languages/MeTTa/Prime/PackageIdentityV1.lean"
LEAN_SOURCE="$LEAN_ROOT/$LEAN_REL"
LOGDIR="$ROOT/parity_logs"
CETTA_LOG="$LOGDIR/prime_package_identity_v1_cetta.log"
LEAN_CHECK_LOG="$LOGDIR/prime_package_identity_v1_lean_check.log"
LEAN_RUN_LOG="$LOGDIR/prime_package_identity_v1_lean_run.log"
EXPECTED_ASSERTIONS=14

mkdir -p "$LOGDIR"

if [[ "$(grep -c '^!(assertEqual' "$SOURCE")" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (assertion census changed)"
  exit 1
fi

if ! "$CETTA" --lang prime "$SOURCE" >"$CETTA_LOG" 2>&1; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (CeTTa execution failed; log: $CETTA_LOG)"
  exit 1
fi
if grep -q 'Error\|❌' "$CETTA_LOG"; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (CeTTa assertion failed; log: $CETTA_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimePackageIdentitySummaryV1 14 14 0)' "$CETTA_LOG")" -ne 1 ]]; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (CeTTa summary absent or duplicated)"
  exit 1
fi

if grep -Eq '\b(sorry|admit|axiom|native_decide|theorem_wanted)\b|_wanted' \
    "$LEAN_SOURCE"; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (forbidden Lean proof token)"
  exit 1
fi
if ! (cd "$LEAN_ROOT" && lake env lean "$LEAN_REL") \
    >"$LEAN_CHECK_LOG" 2>&1; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (Lean check failed; log: $LEAN_CHECK_LOG)"
  exit 1
fi
if grep -Eq '(^|[[:space:]])(error:|warning:)' "$LEAN_CHECK_LOG"; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (Lean diagnostic found; log: $LEAN_CHECK_LOG)"
  exit 1
fi
if ! (cd "$LEAN_ROOT" && lake env lean --run "$LEAN_REL") \
    >"$LEAN_RUN_LOG" 2>&1; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (Lean admission run failed; log: $LEAN_RUN_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimePackageIdentityLeanSummaryV1 8 8 0)' "$LEAN_RUN_LOG")" -ne 1 ]]; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (Lean summary absent or duplicated)"
  exit 1
fi

extract_payload() {
  local begin="$1"
  local end="$2"
  local log="$3"
  awk -v begin="$begin" -v end="$end" '
    $0 == begin { active = 1; next }
    $0 == end { active = 0; exit }
    active { print }
  ' "$log"
}

cetta_bytes="$(extract_payload PRIME_PACKAGE_CANONICAL_BEGIN PRIME_PACKAGE_CANONICAL_END "$CETTA_LOG")"
lean_bytes="$(extract_payload PRIME_PACKAGE_CANONICAL_BEGIN PRIME_PACKAGE_CANONICAL_END "$LEAN_RUN_LOG")"
cetta_digest="$(extract_payload PRIME_PACKAGE_DIGEST_BEGIN PRIME_PACKAGE_DIGEST_END "$CETTA_LOG")"
lean_digest="$(extract_payload PRIME_PACKAGE_DIGEST_BEGIN PRIME_PACKAGE_DIGEST_END "$LEAN_RUN_LOG")"

if [[ -z "$cetta_bytes" || "$cetta_bytes" != "$lean_bytes" ]]; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (canonical bytes disagree)"
  exit 1
fi
if [[ -z "$cetta_digest" || "$cetta_digest" != "$lean_digest" ]]; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (computed digests disagree)"
  exit 1
fi
shell_digest="$(printf '%s' "$cetta_bytes" | sha256sum | awk '{print $1}')"
if [[ "$cetta_digest" != "$shell_digest" ]]; then
  echo "PRIME PACKAGE IDENTITY V1 GATE: FAIL (SHA-256 oracle disagrees)"
  exit 1
fi

echo "PRIME PACKAGE IDENTITY V1 GATE: PASS (14/14 MeTTa mutations, 8/8 Lean admission checks, byte-identical serialization, three-way SHA-256 agreement)"
