#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPOSITORY="$(cd "$ROOT/../.." && pwd)"
AIHUB="${AIHUB:-$(cd "$REPOSITORY/.." && pwd)}"
CETTA="${CETTA:-$AIHUB/hyperon/cetta-he-prime-dtt-chainer-20260715/cetta}"
LEAN_ROOT="${PRIME_LEAN_ROOT:-$REPOSITORY/lean/mettapedia}"
SOURCE="$ROOT/prime_fragment_adequacy_v1.metta"
LEAN_REL="Mettapedia/Languages/MeTTa/Prime/FragmentAdequacyV1.lean"
LEAN_SOURCE="$LEAN_ROOT/$LEAN_REL"
LEAN_OLEAN="$LEAN_ROOT/.lake/build/lib/lean/${LEAN_REL%.lean}.olean"
LOGDIR="$ROOT/parity_logs"
CETTA_LOG="$LOGDIR/prime_fragment_adequacy_v1_cetta.log"
LEAN_LOG="$LOGDIR/prime_fragment_adequacy_v1_lean.log"
EXPECTED_ASSERTIONS=18

mkdir -p "$LOGDIR"

if [[ "$(grep -c '^!(assertEqual' "$SOURCE")" -ne "$EXPECTED_ASSERTIONS" ]]; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (assertion census changed)"
  exit 1
fi

if ! "$CETTA" --lang prime "$SOURCE" >"$CETTA_LOG" 2>&1; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (CeTTa execution failed; log: $CETTA_LOG)"
  exit 1
fi
if grep -q 'Error\|❌' "$CETTA_LOG"; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (CeTTa assertion failed; log: $CETTA_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimeFragmentAdequacyMeTTaSummaryV1 18 18 0)' "$CETTA_LOG")" -ne 1 ]]; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (CeTTa summary absent or duplicated)"
  exit 1
fi

if grep -Eq '\b(sorry|admit|axiom|native_decide|theorem_wanted)\b|_wanted' \
    "$LEAN_SOURCE"; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (forbidden Lean proof token)"
  exit 1
fi
mkdir -p "$(dirname "$LEAN_OLEAN")"
if ! (cd "$LEAN_ROOT" && lake env lean -o "$LEAN_OLEAN" "$LEAN_REL") \
    >"$LEAN_LOG" 2>&1; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (Lean check failed; log: $LEAN_LOG)"
  exit 1
fi
if grep -Eq '(^|[[:space:]])(error:|warning:)' "$LEAN_LOG"; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (Lean diagnostic found; log: $LEAN_LOG)"
  exit 1
fi
if [[ "$(grep -Fxc '(PrimeFragmentAdequacyLeanSummaryV1 8 8 0)' "$LEAN_LOG")" -ne 1 ]]; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (Lean summary absent or duplicated)"
  exit 1
fi

# The theorem audit is intentionally exact.  These are Lean's standard
# extensionality/quotient assumptions inherited from the generic presentation
# checker; any additional dependency fails the gate.
if [[ "$(grep -Fc 'depends on axioms: [propext,' "$LEAN_LOG")" -ne 2 ]] ||
   [[ "$(grep -Fxc ' Classical.choice,' "$LEAN_LOG")" -ne 2 ]] ||
   [[ "$(grep -Fxc ' Quot.sound]' "$LEAN_LOG")" -ne 2 ]]; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (Lean axiom footprint changed)"
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

cetta_bytes="$(extract_payload PRIME_FRAGMENT_PACKAGE_CANONICAL_BEGIN \
  PRIME_FRAGMENT_PACKAGE_CANONICAL_END "$CETTA_LOG")"
lean_bytes="$(extract_payload PRIME_FRAGMENT_PACKAGE_CANONICAL_BEGIN \
  PRIME_FRAGMENT_PACKAGE_CANONICAL_END "$LEAN_LOG")"
if [[ -z "$cetta_bytes" || "$cetta_bytes" != "$lean_bytes" ]]; then
  echo "PRIME FRAGMENT ADEQUACY V1 GATE: FAIL (compiled package bytes disagree)"
  exit 1
fi

echo "PRIME FRAGMENT ADEQUACY V1 GATE: PASS (18/18 MeTTa checks, 8/8 Lean checks, two-way typed adequacy, exact cache projection, byte-identical compiled package, mutation negatives, audited theorem dependencies)"
