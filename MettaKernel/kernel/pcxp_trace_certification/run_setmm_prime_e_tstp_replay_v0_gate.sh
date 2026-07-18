#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="${CETTA:-cetta}"
EPROVER="${EPROVER:-eprover}"
FIXTURE="$ROOT/setmm_prime_e_ja_resolution_replay_v0.metta"

python3 "$ROOT/setmm_prime_e_tstp_replay_tools.py" \
  --check --self-test --live-e "$EPROVER"

output="$($CETTA --lang prime "$FIXTURE" 2>&1)"
printf '%s\n' "$output"

if printf '%s\n' "$output" | grep -Fq '(Error '; then
  echo 'SET.MM PRIME E TSTP REPLAY V0 GATE: FAIL (Prime assertion error)' >&2
  exit 1
fi

if ! printf '%s\n' "$output" \
    | grep -Fq '(SetMMPrimeETSTPReplaySummary ja 7 7 0)'; then
  echo 'SET.MM PRIME E TSTP REPLAY V0 GATE: FAIL (missing 7/7 summary)' >&2
  exit 1
fi

echo 'SET.MM PRIME E TSTP REPLAY V0 GATE: PASS (live E proof, 4 resolution steps, 3 extractor mutations, 2 replay mutations, 1 Prime proof check)'
