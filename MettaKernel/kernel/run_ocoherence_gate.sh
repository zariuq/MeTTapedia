#!/usr/bin/env bash
# run_ocoherence_gate.sh — <>-Coherence / HM-Adequacy Shadow v1 mutation gate.
#
# ocoherence_hm_adequacy_v1.metta pins a bounded HM-adequacy shadow: OSLF
# modalities <F>phi are tested against context bisimulation with adequacy
# positives plus explicit separating witnesses for the listed ~/~ pairs.  This
# gate proves the teeth BITE: each injected modal break (a modality that ignores
# its action label; a vacuously-true diamond; a dropped conjunct) or ~ over-match
# must turn the oracle red.  Throwaway repo-local copy only; literal (non-regex)
# replacement keeps the edits exact.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="/home/aimama/aihub/hyperon/CeTTa/cetta"
ORACLE="$ROOT/ocoherence_hm_adequacy_v1.metta"
EXPECTED_BASE=24
TMP="$(mktemp -d "$ROOT/.ocoherence_mutation.XXXXXX")"
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
echo "<>-Coherence / HM-Adequacy Shadow v1 — mutation gate"
echo "baseline: oracle = $BASE pass"
if [[ "$BASE" -ne "$EXPECTED_BASE" ]]; then
  echo "OCOHERENCE GATE: FAIL (expected baseline $EXPECTED_BASE pass, got $BASE)"
  exit 1
fi
echo
printf '%-46s | %-16s | %s\n' "mutation (modal / ~ break)" "oracle suite" "verdict"
printf '%-46s-+-%-16s-+-%s\n' "$(printf '%.0s-' {1..46})" "----------------" "-------"

missed=0
run_mut() {
  local name="$1"; shift
  local f="$TMP/mut.metta"
  lit_replace "$ORACLE" "$f" "$@"
  local pf; pf=$(pass_count "$f")
  local st="green($pf)" caught="MISSED"
  [[ "$pf" -lt "$BASE" ]] && { st="RED($pf<$BASE)"; caught="caught"; }
  [[ "$caught" == "MISSED" ]] && missed=$((missed+1))
  printf '%-46s | %-16s | %s\n' "$name" "$st" "$caught"
}

# M1 modality ignores its action label (the diamond matches ANY transition).
run_mut "M1 modal: <a> ignores the action label" \
  '(if (== $a $b)
       (if (sat $n $P1 $phi) True (dia-search $n $a $phi $rest))
       (dia-search $n $a $phi $rest))' \
  '(if (sat $n $P1 $phi) True (dia-search $n $a $phi $rest))'
# M2 vacuously-true diamond (a transition always exists).
run_mut "M2 modal: vacuous diamond (sat <a> always)" \
  '(= (dia-search $n $a $phi LNil) False)' \
  '(= (dia-search $n $a $phi LNil) True)'
# M3 conjunction drops its second conjunct.
run_mut "M3 modal: FAnd drops second conjunct" \
  '(= (sat $n $P (FAnd $phi $psi)) (if (sat $n $P $phi) (sat $n $P $psi) False))' \
  '(= (sat $n $P (FAnd $phi $psi)) (sat $n $P $phi))'
# M4 ~ over-match (bisim over-identifies) -- ties the ~ side of adequacy.
run_mut "M4 bisim: vacuous match (~ over-identifies)" \
  '(= (has-match $n $a $P1 LNil) False)' \
  '(= (has-match $n $a $P1 LNil) True)'

echo
if [[ "$missed" -eq 0 ]]; then
  echo "OCOHERENCE GATE: PASS (mutation-complete — every modal/~ break caught)"
else
  echo "OCOHERENCE GATE: FAIL ($missed mutation(s) MISSED — a hole in the adequacy probe)"
fi
exit "$missed"
