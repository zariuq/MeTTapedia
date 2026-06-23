#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="/home/aimama/aihub/hyperon/CeTTa/cetta"
HYPERON="/home/aimama/aihub/hyperon/hyperon-experimental/target/debug/metta-repl"
LOGDIR="$ROOT/logs"
mkdir -p "$LOGDIR"

direct="pi_infer_direct_divergence.metta"
factored="pi_infer_factored_control.metta"

run_one() {
  local engine="$1" bin="$2" file="$3" log="$4"
  timeout 90 "$bin" "$ROOT/$file" >"$log" 2>&1
  local rc=$?
  printf '%-12s %-34s rc=%s log=%s\n' "$engine" "$file" "$rc" "$log"
}

run_one "CeTTa" "$CETTA" "$direct"   "$LOGDIR/cetta_direct.log"
run_one "CeTTa" "$CETTA" "$factored" "$LOGDIR/cetta_factored.log"
run_one "Hyperon" "$HYPERON" "$direct"   "$LOGDIR/hyperon_direct.log"
run_one "Hyperon" "$HYPERON" "$factored" "$LOGDIR/hyperon_factored.log"

fails=0

for pair in \
  "$LOGDIR/cetta_direct.log:CeTTa direct" \
  "$LOGDIR/cetta_factored.log:CeTTa factored" \
  "$LOGDIR/hyperon_direct.log:Hyperon direct" \
  "$LOGDIR/hyperon_factored.log:Hyperon factored"
do
  log="${pair%%:*}"
  label="${pair#*:}"
  if grep -Fxq '[()]' "$log"; then
    echo "pass: $label"
  else
    echo "UNEXPECTED: $label did not pass"
    fails=$((fails + 1))
  fi
done

if [[ $fails -eq 0 ]]; then
  echo "ENGINE PI RECURSION REGRESSION: PASS"
else
  echo "ENGINE PI RECURSION REGRESSION: FAIL ($fails unexpected result(s))"
fi

exit "$fails"
