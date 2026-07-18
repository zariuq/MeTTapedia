#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SETMM_REVISION="${SETMM_REVISION:-47e6e06b87581cd630d210dc41cf83b02eea78ea}"
SETMM_SHA256="${SETMM_SHA256:-3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a}"
SETMM="${SETMM:?set SETMM to set.mm at revision $SETMM_REVISION}"
EPROVER="${EPROVER:-eprover}"
VAMPIRE="${VAMPIRE:-vampire}"
TIME_LIMIT="${TIME_LIMIT:-}"
LOGDIR="${LOGDIR:-$ROOT/parity_logs/setmm_prime_atp_oracles_v0}"

mkdir -p "$LOGDIR"

actual_sha="$(sha256sum "$SETMM" | awk '{print $1}')"
if [[ "$actual_sha" != "$SETMM_SHA256" ]]; then
  echo "SET.MM PRIME ATP ORACLES V0: FAIL (expected set.mm SHA-256 $SETMM_SHA256, found $actual_sha)" >&2
  exit 1
fi

python3 "$ROOT/setmm_prime_atp_tools.py" \
  --setmm "$SETMM" \
  --source-revision "$SETMM_REVISION" \
  --output-dir "$ROOT"

printf 'problem\te\tvampire\n' > "$LOGDIR/results.tsv"
passed=0
total=0

problems=(
  "$ROOT"/tptp/ja_*.p
  "$ROOT"/tptp/pm2_61iii_*.p
  "$ROOT"/tptp/pm2_61nii_*.p
)

for problem in "${problems[@]}"; do
  name="$(basename "$problem" .p)"
  e_log="$LOGDIR/$name.e.log"
  vampire_log="$LOGDIR/$name.vampire.log"

  e_args=(--auto --tstp-format --proof-object)
  vampire_args=(--mode casc --proof tptp)
  if [[ -n "$TIME_LIMIT" ]]; then
    e_args+=("--cpu-limit=$TIME_LIMIT")
    vampire_args+=(--time_limit "$TIME_LIMIT")
  fi

  "$EPROVER" "${e_args[@]}" "$problem" > "$e_log" 2>&1 || true
  "$VAMPIRE" "${vampire_args[@]}" "$problem" > "$vampire_log" 2>&1 || true

  e_status=FAIL
  vampire_status=FAIL
  if rg -q '^# Proof found!|^# SZS status Theorem|^% SZS status Theorem' "$e_log"; then
    e_status=Theorem
  fi
  if rg -q '^% SZS status Theorem' "$vampire_log"; then
    vampire_status=Theorem
  fi

  printf '%s\t%s\t%s\n' "$name" "$e_status" "$vampire_status" \
    | tee -a "$LOGDIR/results.tsv"
  total=$((total + 2))
  [[ "$e_status" == Theorem ]] && passed=$((passed + 1))
  [[ "$vampire_status" == Theorem ]] && passed=$((passed + 1))
done

if [[ "$passed" -ne "$total" ]]; then
  echo "SET.MM PRIME ATP ORACLES V0: FAIL ($passed/$total final theorem statuses)" >&2
  exit 1
fi

echo "SET.MM PRIME ATP ORACLES V0: PASS ($passed/$total final theorem statuses; 12 source-derived problems across E and Vampire)"
