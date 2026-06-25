#!/usr/bin/env bash
# run_conv_soundness_gate.sh — Conv-Soundness Shadow v1 mutation gate.
#
# conv_soundness_shadow_v1.metta pins conv (XS) ~ : conv is a SOUND decidable
# shadow of context-bisimulation (conv => ~), the strict gap is exhibited, and no
# conv-equal pair is ~-distinct.  This gate proves those teeth BITE: each injected
# UNSOUND conv coarsening (conv identifying a ~-distinct pair) or ~ over-match must
# turn the oracle red.  Mutations hit a THROWAWAY copy only -- the live file is
# never modified.  Literal (non-regex) string replacement keeps the edits exact.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="/home/aimama/aihub/hyperon/CeTTa/cetta"
ORACLE="$ROOT/conv_soundness_shadow_v1.metta"
TMP="$(mktemp -d)"
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
echo "Conv-Soundness Shadow v1 — mutation gate"
echo "baseline: oracle = $BASE pass"
echo
printf '%-46s | %-16s | %s\n' "mutation (unsound conv coarsening / ~ over-match)" "oracle suite" "verdict"
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

# C1 conv unsound: + left-absorbs (a+b == a), which is NOT bisimulation-sound.
run_mut "C1 conv: Sum left-absorb (a+b == a)" \
  '(= (mk-sum $P $Q) (if (== $P Nil) $Q (if (== $Q Nil) $P (Sum $P $Q))))' \
  '(= (mk-sum $P $Q) $P)'
# C2 conv unsound: | left-absorbs (a|b == a).
run_mut "C2 conv: Par left-absorb (a|b == a)" \
  '(= (mk-par $P $Q) (if (== $P Nil) $Q (if (== $Q Nil) $P (Par $P $Q))))' \
  '(= (mk-par $P $Q) $P)'
# C3 conv unsound: prefix collapses its continuation (a.b == a.c).
run_mut "C3 conv: prefix collapse (a.b == a.c)" \
  '(= (cnf (Pre $a $P)) (Pre $a (cnf $P)))' \
  '(= (cnf (Pre $a $P)) (Pre $a Nil))'
# B1 ~ over-match: a transition always finds a partner, so ~ over-identifies.
run_mut "B1 bisim: vacuous match (~ over-identifies)" \
  '(= (has-match $n $a $P1 LNil) False)' \
  '(= (has-match $n $a $P1 LNil) True)'

echo
if [[ "$missed" -eq 0 ]]; then
  echo "CONV-SOUNDNESS GATE: PASS (mutation-complete — every unsound conv/~ break caught)"
else
  echo "CONV-SOUNDNESS GATE: FAIL ($missed mutation(s) MISSED — a hole in the soundness probe)"
fi
exit "$missed"
