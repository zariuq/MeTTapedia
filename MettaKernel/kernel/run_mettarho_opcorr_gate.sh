#!/usr/bin/env bash
# run_mettarho_opcorr_gate.sh — MeTTa2rho Operational-Correspondence Shadow v1 gate.
#
# mettarho_opcorr_shadow_v1.metta pins the bounded operational correspondence
# (ob:opcorr): the desugaring's ∂T-transitions correspond to the GSLT rewrites,
# each on its location channel c(l)=quote(l), with injective channels.  This gate
# proves the teeth BITE: each injected DESUGARING break (channel collision; wrong
# location; dropped re-emit) must turn the oracle red.  Throwaway repo-local copy
# only; literal (non-regex) replacement keeps the edits exact.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="/home/aimama/aihub/hyperon/CeTTa/cetta"
ORACLE="$ROOT/mettarho_opcorr_shadow_v1.metta"
EXPECTED_BASE=19
TMP="$(mktemp -d "$ROOT/.opcorr_mutation.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

pass_count() { timeout 150 "$CETTA" "$1" 2>/dev/null | grep -cE '\[\(\)\]'; }
lit_replace() {
  python3 -c 'import sys
s=open(sys.argv[1]).read()
for i in range(3,len(sys.argv),2):
    s=s.replace(sys.argv[i],sys.argv[i+1])
open(sys.argv[2],"w").write(s)' "$@"
}

BASE=$(pass_count "$ORACLE")
echo "MeTTa2rho Operational-Correspondence Shadow v1 — mutation gate"
echo "baseline: oracle = $BASE pass"
if [[ "$BASE" -ne "$EXPECTED_BASE" ]]; then
  echo "OPCORR GATE: FAIL (expected baseline $EXPECTED_BASE pass, got $BASE)"
  exit 1
fi
echo
printf '%-48s | %-16s | %s\n' "mutation (desugaring break)" "oracle suite" "verdict"
printf '%-48s-+-%-16s-+-%s\n' "$(printf '%.0s-' {1..48})" "----------------" "-------"

missed=0
run_mut() {
  local name="$1"; shift
  local f="$TMP/mut.metta"
  lit_replace "$ORACLE" "$f" "$@"
  local pf; pf=$(pass_count "$f")
  local st="green($pf)" caught="MISSED"
  [[ "$pf" -lt "$BASE" ]] && { st="RED($pf<$BASE)"; caught="caught"; }
  [[ "$caught" == "MISSED" ]] && missed=$((missed+1))
  printf '%-48s | %-16s | %s\n' "$name" "$st" "$caught"
}

# M1 channel collision: c(l) becomes constant -> distinct redexes collapse onto one channel.
run_mut "M1 desugar: channel collision (c(l) constant)" \
  '(= (chan $loc) (Chan $loc))' \
  '(= (chan $loc) (Chan collide))'
# M2 wrong location: the A2 child is annotated at the A1 location.
run_mut "M2 desugar: wrong location (A2 child at A1)" \
  '(dsg-at (psnoc $loc A2) $y))' \
  '(dsg-at (psnoc $loc A1) $y))'
# M3 dropped re-emit on add-z: A(Z,y) re-emits Z instead of y.
run_mut "M3 desugar: dropped re-emit (add-z => Z)" \
  '(dhead (DA $c (DZ $cz) $dy)) (TCons (Tr $c (undsg $dy)) TNil))' \
  '(dhead (DA $c (DZ $cz) $dy)) (TCons (Tr $c Z) TNil))'
# M4 wrong re-emit on add-s: A(S x,y) re-emits add(x,y) without the surrounding S.
run_mut "M4 desugar: wrong re-emit (add-s drops S)" \
  '(dhead (DA $c (DS $cs $dx) $dy)) (TCons (Tr $c (S (A (undsg $dx) (undsg $dy)))) TNil))' \
  '(dhead (DA $c (DS $cs $dx) $dy)) (TCons (Tr $c (A (undsg $dx) (undsg $dy))) TNil))'

echo
if [[ "$missed" -eq 0 ]]; then
  echo "OPCORR GATE: PASS (mutation-complete — every desugaring break caught)"
else
  echo "OPCORR GATE: FAIL ($missed mutation(s) MISSED — a hole in the correspondence probe)"
fi
exit "$missed"
