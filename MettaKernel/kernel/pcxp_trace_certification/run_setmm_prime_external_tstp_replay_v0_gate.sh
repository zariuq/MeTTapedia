#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="${CETTA:-cetta}"
EPROVER="${EPROVER:-eprover}"
VAMPIRE="${VAMPIRE:-vampire}"

CETTA="$CETTA" EPROVER="$EPROVER" \
  "$ROOT/run_setmm_prime_e_tstp_replay_v0_gate.sh"

CETTA="$CETTA" EPROVER="$EPROVER" \
  "$ROOT/run_setmm_prime_e_frontier_tstp_replay_v0_gate.sh"

python3 "$ROOT/setmm_prime_vampire_tstp_replay_tools.py" \
  --check --self-test --live-vampire "$VAMPIRE"

vampire_output="$($CETTA --lang prime \
  "$ROOT/setmm_prime_vampire_ja_resolution_replay_v0.metta" 2>&1)"
printf '%s\n' "$vampire_output"

if printf '%s\n' "$vampire_output" | grep -Fq '(Error '; then
  echo 'SET.MM PRIME EXTERNAL TSTP REPLAY V0 GATE: FAIL (Vampire replay assertion error)' >&2
  exit 1
fi

if ! printf '%s\n' "$vampire_output" \
    | grep -Fq '(SetMMPrimeVampireTSTPReplaySummary ja 9 9 0)'; then
  echo 'SET.MM PRIME EXTERNAL TSTP REPLAY V0 GATE: FAIL (missing Vampire 9/9 summary)' >&2
  exit 1
fi

CETTA="$CETTA" EPROVER="$EPROVER" VAMPIRE="$VAMPIRE" \
  "$ROOT/run_setmm_prime_external_equality_tstp_replay_v0_gate.sh"

echo 'SET.MM PRIME EXTERNAL TSTP REPLAY V0 GATE: PASS (ja + pm2.61iii resolution and equality conformance across live E and Vampire proofs)'
