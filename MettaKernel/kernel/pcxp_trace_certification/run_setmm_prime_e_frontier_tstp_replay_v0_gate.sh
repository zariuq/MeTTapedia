#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="${CETTA:-cetta}"
EPROVER="${EPROVER:-eprover}"
FIXTURE="$ROOT/setmm_prime_e_pm2_61iii_resolution_replay_v0.metta"

python3 "$ROOT/setmm_prime_e_frontier_tstp_replay_tools.py" \
  --check --self-test --live-e "$EPROVER"

output="$($CETTA --lang prime "$FIXTURE" 2>&1)"
printf '%s\n' "$output"

if printf '%s\n' "$output" | grep -Fq '(Error '; then
  echo 'SET.MM PRIME E FRONTIER TSTP REPLAY V0 GATE: FAIL (Prime assertion error)' >&2
  exit 1
fi

if ! printf '%s\n' "$output" \
    | grep -Fq '(SetMMPrimeEFrontierTSTPReplaySummary pm2.61iii 14 14 0)'; then
  echo 'SET.MM PRIME E FRONTIER TSTP REPLAY V0 GATE: FAIL (missing 14/14 summary)' >&2
  exit 1
fi

echo 'SET.MM PRIME E FRONTIER TSTP REPLAY V0 GATE: PASS (live E proof, 12 resolution steps, 3 extractor mutations, 1 replay mutation, 1 Prime proof check)'
