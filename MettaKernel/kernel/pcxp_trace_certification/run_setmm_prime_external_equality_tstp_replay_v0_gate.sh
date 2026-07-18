#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="${CETTA:-cetta}"
EPROVER="${EPROVER:-eprover}"
VAMPIRE="${VAMPIRE:-vampire}"
FIXTURE="$ROOT/setmm_prime_external_equality_replay_v0.metta"

python3 "$ROOT/setmm_prime_equality_tstp_replay_tools.py" \
  --check --self-test --live-e "$EPROVER" --live-vampire "$VAMPIRE"

output="$($CETTA --lang prime "$FIXTURE" 2>&1)"
printf '%s\n' "$output"

if printf '%s\n' "$output" | grep -Fq '(Error '; then
  echo 'SET.MM PRIME EXTERNAL EQUALITY TSTP REPLAY V0 GATE: FAIL (Prime assertion error)' >&2
  exit 1
fi

if ! printf '%s\n' "$output" \
    | grep -Fq '(SetMMPrimeExternalEqualityReplaySummary equality_transport 2 11 11 0)'; then
  echo 'SET.MM PRIME EXTERNAL EQUALITY TSTP REPLAY V0 GATE: FAIL (missing 11/11 summary)' >&2
  exit 1
fi

echo 'SET.MM PRIME EXTERNAL EQUALITY TSTP REPLAY V0 GATE: PASS (live E rw + Vampire ordered superposition, 6 extractor mutations, 11 Prime checks)'
