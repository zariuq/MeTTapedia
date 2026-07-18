#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPOSITORY="$(cd "$ROOT/../.." && pwd)"
AIHUB="${AIHUB:-$(cd "$REPOSITORY/.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/cetta-he-prime-dtt-chainer-20260715/cetta}"
LEAN_ROOT="${PRIME_LEAN_ROOT:-$REPOSITORY/lean/mettapedia}"
SOURCE="$ROOT/prime_certificate_boundary_v1.metta"
LEAN_REL="Mettapedia/Languages/MeTTa/Prime/CertificateBoundaryV1.lean"
LEAN_SOURCE="$LEAN_ROOT/$LEAN_REL"
LOGDIR="$ROOT/parity_logs"
CETTA_LOG="$LOGDIR/prime_certificate_boundary_v1_cetta.log"
LEAN_LOG="$LOGDIR/prime_certificate_boundary_v1_lean.log"
EXPECTED_ASSERTIONS=8

mkdir -p "$LOGDIR"

if [[ "$(grep -c '^!(assertEqual' "$SOURCE")" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (assertion census changed)"
  exit 1
fi

if ! "$CETTA" --lang prime "$SOURCE" >"$CETTA_LOG" 2>&1; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (CeTTa execution failed; log: $CETTA_LOG)"
  exit 1
fi
if grep -q 'Error\|❌' "$CETTA_LOG"; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (CeTTa assertion failed; log: $CETTA_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimeCertificateBoundaryMeTTaSummaryV1 8 8 0)' "$CETTA_LOG")" -ne 1 ]]; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (CeTTa summary absent or duplicated)"
  exit 1
fi

if grep -Eq '\b(sorry|admit|axiom|native_decide|theorem_wanted)\b|_wanted' \
    "$LEAN_SOURCE"; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (forbidden Lean proof token)"
  exit 1
fi
if ! (cd "$LEAN_ROOT" && lake env lean "$LEAN_REL") >"$LEAN_LOG" 2>&1; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (Lean check failed; log: $LEAN_LOG)"
  exit 1
fi
if grep -Eq '(^|[[:space:]])(error:|warning:)' "$LEAN_LOG"; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (Lean diagnostic found; log: $LEAN_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimeCertificateBoundaryLeanSummaryV1 8 8 0)' "$LEAN_LOG")" -ne 1 ]]; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (Lean summary absent or duplicated)"
  exit 1
fi

if [[ "$(grep -Fc 'depends on axioms: [propext,' "$LEAN_LOG")" -ne 2 ]] ||
   [[ "$(grep -Fxc ' Classical.choice,' "$LEAN_LOG")" -ne 2 ]] ||
   [[ "$(grep -Fxc ' Quot.sound]' "$LEAN_LOG")" -ne 2 ]]; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (Lean axiom footprint changed)"
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

cetta_bytes="$(extract_payload PRIME_CERTIFICATE_CANONICAL_BEGIN \
  PRIME_CERTIFICATE_CANONICAL_END "$CETTA_LOG")"
lean_bytes="$(extract_payload PRIME_CERTIFICATE_CANONICAL_BEGIN \
  PRIME_CERTIFICATE_CANONICAL_END "$LEAN_LOG")"
cetta_digest="$(extract_payload PRIME_CERTIFICATE_DIGEST_BEGIN \
  PRIME_CERTIFICATE_DIGEST_END "$CETTA_LOG")"
lean_digest="$(extract_payload PRIME_CERTIFICATE_DIGEST_BEGIN \
  PRIME_CERTIFICATE_DIGEST_END "$LEAN_LOG")"

if [[ -z "$cetta_bytes" || "$cetta_bytes" != "$lean_bytes" ]]; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (certificate bytes disagree)"
  exit 1
fi
if [[ -z "$cetta_digest" || "$cetta_digest" != "$lean_digest" ]]; then
  echo "PRIME CERTIFICATE BOUNDARY V1 GATE: FAIL (certificate digests disagree)"
  exit 1
fi

echo "PRIME CERTIFICATE BOUNDARY V1 GATE: PASS (8/8 mutations in each runtime, byte-identical authenticated certificate, matching digest, and certificate-existence iff evaluator-membership theorem)"
