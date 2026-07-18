#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="${CETTA:-cetta}"
SETMM="${SETMM:?set SETMM to the pinned set.mm source file}"
SETMM_REVISION="${SETMM_REVISION:-47e6e06b87581cd630d210dc41cf83b02eea78ea}"
SETMM_SHA256="${SETMM_SHA256:-3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a}"
OUT="${OUT:-$ROOT/parity_logs/setmm_prime_chronological_v0}"

actual_sha="$(sha256sum "$SETMM" | awk '{print $1}')"
if [[ "$actual_sha" != "$SETMM_SHA256" ]]; then
  echo "SET.MM PRIME CHRONOLOGICAL V0 GATE: FAIL (set.mm SHA-256 mismatch)" >&2
  exit 1
fi

mkdir -p "$OUT"
PYTHONDONTWRITEBYTECODE=1 python3 "$ROOT/setmm_prime_chronological_tools.py" \
  --setmm "$SETMM" \
  --source-revision "$SETMM_REVISION" \
  --output-dir "$OUT" \
  --self-test

fixture="$OUT/setmm_prime_chronological_181_183_v0.metta"
receipt="$OUT/setmm_prime_chronological_selection_v0.json"

cmp "$fixture" "$ROOT/setmm_prime_chronological_181_183_v0.metta"
cmp "$receipt" "$ROOT/setmm_prime_chronological_selection_v0.json"

output="$($CETTA --lang prime "$fixture" 2>&1)"
printf '%s\n' "$output"

for label in pm2.61nii pm2.61iii ja; do
  if ! printf '%s\n' "$output" | rg -q "^\[\(PASS $label "; then
    echo "SET.MM PRIME CHRONOLOGICAL V0 GATE: FAIL ($label missing checked proof)" >&2
    exit 1
  fi
done

if printf '%s\n' "$output" | rg -q '\(FAIL |\(INCOMPLETE |\(UNEXPECTED |\(Error '; then
  echo "SET.MM PRIME CHRONOLOGICAL V0 GATE: FAIL (non-accepting verdict)" >&2
  exit 1
fi

jq -e '
  .schema == "setmm-prime-chronological-selection-v0" and
  .source.sha256 == $sha and
  (.targets | length) == 3 and
  all(.targets[];
    .training_prefix_last_index == (.index - 1) and
    .selected_count == (.selected_labels | length) and
    .selected_count > 0)
' --arg sha "$SETMM_SHA256" "$receipt" >/dev/null

echo 'SET.MM PRIME CHRONOLOGICAL V0 GATE: PASS (3/3 source-prefix-selected, searched, and replay-checked)'
