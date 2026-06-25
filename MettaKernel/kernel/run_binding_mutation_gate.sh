#!/usr/bin/env bash
# run_binding_mutation_gate.sh — Binding Capture Spec v1 mutation gate.
#
# Tri-runtime parity catches output DIVERGENCE, not binding CORRECTNESS: a
# capture bug is silent.  This gate proves the BINDING CAPTURE SPEC v1 rows in
# kernel_signature_lf_indexed_v0.metta actually BITE — each injected binding
# break must turn the suite red.  For each live waist mutation we also run the
# PRE-CAPTURE engine (the assertions before the spec section).  Before the live
# waist route this isolated capture-only teeth; after the route, many waist
# corruptions correctly break earlier typing/admission checks too.  Mutations
# are applied to THROWAWAY copies only — the live engine is never modified.
# Literal string replacement (no regex) keeps the edits exact.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="/home/aimama/aihub/hyperon/CeTTa/cetta"
ENGINE="$ROOT/kernel_signature_lf_indexed_v0.metta"
LF_ENGINE="$ROOT/kernel_signature_lf_v0.metta"
NATREC_ENGINE="$ROOT/kernel_signature_lf_natrec_v0.metta"
CURR_ENGINE="$ROOT/curriculum_lf_demo.metta"
BREAK_ENGINE="$ROOT/break_probes.metta"
EXP2_ENGINE="$ROOT/exp2_dtt_wall.metta"
EXP3_ENGINE="$ROOT/exp3_hotg_both_ways.metta"
EVAL_ENGINE="$ROOT/evaluator_ground_recursion_invariant.metta"
BIND_WAIST="$ROOT/kernel_binding_waist_v1.metta"
BIND_DECL="$ROOT/kernel_binding_decl_v1.metta"
REPLAY="$ROOT/kernel_binding_abtg_replay_v1.metta"
MIN_FULL=116
MIN_PRE_CAPTURE=102
MIN_LF=23
MIN_NATREC=32
MIN_CURR=19
MIN_BREAK=9
MIN_EXP2=15
MIN_EXP3=14
MIN_EVAL=7
MIN_REPLAY=46
TMP="$(mktemp -d "$ROOT/.binding_mutation.XXXXXX")"
BASE101="$ROOT/kernel_signature_lf_indexed_base101_$$.metta"
MUT_BASE101="$ROOT/kernel_signature_lf_indexed_base101_mut_$$.metta"
MUT_INDEXED="$ROOT/kernel_signature_lf_indexed_mut_$$.metta"
MUT_LF="$ROOT/kernel_signature_lf_v0_mut_$$.metta"
MUT_NATREC="$ROOT/kernel_signature_lf_natrec_v0_mut_$$.metta"
MUT_CURR="$ROOT/curriculum_lf_demo_mut_$$.metta"
MUT_BREAK="$ROOT/break_probes_mut_$$.metta"
MUT_EXP2="$ROOT/exp2_dtt_wall_mut_$$.metta"
MUT_EXP3="$ROOT/exp3_hotg_both_ways_mut_$$.metta"
MUT_EVAL="$ROOT/evaluator_ground_recursion_invariant_mut_$$.metta"
MUT_WAIST="$ROOT/kernel_binding_waist_mut_$$.metta"
MUT_DECL="$ROOT/kernel_binding_decl_mut_$$.metta"
MUT_REPLAY="$ROOT/kernel_binding_abtg_replay_mut_$$.metta"
cleanup() { rm -rf "$TMP" "$BASE101" "$MUT_BASE101" "$MUT_INDEXED" "$MUT_LF" "$MUT_NATREC" "$MUT_CURR" "$MUT_BREAK" "$MUT_EXP2" "$MUT_EXP3" "$MUT_EVAL" "$MUT_WAIST" "$MUT_DECL" "$MUT_REPLAY"; }
trap cleanup EXIT

pass_count() { timeout 150 "$CETTA" "$1" 2>/dev/null | grep -cE '\[\(\)\]'; }
# literal (non-regex) replace: replace in out search replace
lit_replace() {
  python3 -c 'import sys
s=open(sys.argv[1]).read()
for i in range(3,len(sys.argv),2):
    s=s.replace(sys.argv[i],sys.argv[i+1])
open(sys.argv[2],"w").write(s)' "$@"
}

# Baselines.
FULL=$(pass_count "$ENGINE")
LFBASE=$(pass_count "$LF_ENGINE")
NATRECBASE=$(pass_count "$NATREC_ENGINE")
CURRBASE=$(pass_count "$CURR_ENGINE")
BREAKBASE=$(pass_count "$BREAK_ENGINE")
EXP2BASE=$(pass_count "$EXP2_ENGINE")
EXP3BASE=$(pass_count "$EXP3_ENGINE")
EVALBASE=$(pass_count "$EVAL_ENGINE")
RFULL=$(pass_count "$REPLAY")
sed '/BINDING CAPTURE SPEC v1/,$d' "$ENGINE" > "$BASE101"
N101=$(pass_count "$BASE101")
echo "Binding Capture Spec v1 — mutation gate"
echo "baseline: full engine = $FULL pass ; pre-capture engine = $N101 pass"
echo "baseline: lf_v0 = $LFBASE pass ; natrec_v0 = $NATRECBASE pass"
echo "baseline: curriculum = $CURRBASE pass ; break = $BREAKBASE pass ; exp2 = $EXP2BASE pass ; exp3 = $EXP3BASE pass ; evaluator = $EVALBASE pass"
echo "baseline: ABT generic replay = $RFULL pass"
echo
baseline_bad=0
if [[ "$FULL" -lt "$MIN_FULL" ]]; then
  echo "baseline guard: FAIL full engine dropped below $MIN_FULL ($FULL)"
  baseline_bad=1
fi
if [[ "$N101" -lt "$MIN_PRE_CAPTURE" ]]; then
  echo "baseline guard: FAIL pre-capture engine dropped below $MIN_PRE_CAPTURE ($N101)"
  baseline_bad=1
fi
if [[ "$LFBASE" -lt "$MIN_LF" ]]; then
  echo "baseline guard: FAIL lf_v0 dropped below $MIN_LF ($LFBASE)"
  baseline_bad=1
fi
if [[ "$NATRECBASE" -lt "$MIN_NATREC" ]]; then
  echo "baseline guard: FAIL natrec_v0 dropped below $MIN_NATREC ($NATRECBASE)"
  baseline_bad=1
fi
if [[ "$CURRBASE" -lt "$MIN_CURR" ]]; then
  echo "baseline guard: FAIL curriculum_lf_demo dropped below $MIN_CURR ($CURRBASE)"
  baseline_bad=1
fi
if [[ "$BREAKBASE" -lt "$MIN_BREAK" ]]; then
  echo "baseline guard: FAIL break_probes dropped below $MIN_BREAK ($BREAKBASE)"
  baseline_bad=1
fi
if [[ "$EXP2BASE" -lt "$MIN_EXP2" ]]; then
  echo "baseline guard: FAIL exp2_dtt_wall dropped below $MIN_EXP2 ($EXP2BASE)"
  baseline_bad=1
fi
if [[ "$EXP3BASE" -lt "$MIN_EXP3" ]]; then
  echo "baseline guard: FAIL exp3_hotg_both_ways dropped below $MIN_EXP3 ($EXP3BASE)"
  baseline_bad=1
fi
if [[ "$EVALBASE" -lt "$MIN_EVAL" ]]; then
  echo "baseline guard: FAIL evaluator invariant dropped below $MIN_EVAL ($EVALBASE)"
  baseline_bad=1
fi
if [[ "$RFULL" -lt "$MIN_REPLAY" ]]; then
  echo "baseline guard: FAIL ABT generic replay dropped below $MIN_REPLAY ($RFULL)"
  baseline_bad=1
fi
if [[ "$baseline_bad" -ne 0 ]]; then
  echo "BINDING MUTATION GATE: FAIL (baseline coverage weakened before mutation testing)"
  exit 1
fi
printf '%-44s | %-18s | %-18s | %s\n' "mutation (injected binding break)" "full suite" "pre-capture suite" "verdict"
printf '%-44s-+-%-18s-+-%-18s-+-%s\n' "$(printf '%.0s-' {1..44})" "------------------" "------------------" "-------"

missed=0
run_live_waist_mut() {
  local name="$1"; shift
  local mut_waist_mod="kernel_binding_waist_mut_$$"
  local f="$MUT_INDEXED" b="$MUT_BASE101"
  lit_replace "$BIND_WAIST" "$MUT_WAIST" "$@"
  python3 -c 'import sys
src=open(sys.argv[1]).read()
src=src.replace("kernel_binding_waist_v1", sys.argv[3])
open(sys.argv[2],"w").write(src)' "$ENGINE" "$f" "$mut_waist_mod"
  python3 -c 'import sys
src=open(sys.argv[1]).read()
src=src.replace("kernel_binding_waist_v1", sys.argv[3])
open(sys.argv[2],"w").write(src)' "$BASE101" "$b" "$mut_waist_mod"
  local pf pb
  pf=$(pass_count "$f"); pb=$(pass_count "$b")
  rm -f "$MUT_WAIST"
  local full="green($pf)" base="green($pb)" caught="MISSED"
  [[ "$pf" -lt "$FULL" ]] && { full="RED($pf<$FULL)"; caught="caught"; }
  [[ "$pb" -lt "$N101" ]] && base="RED($pb<$N101)" || base="green($pb)"
  [[ "$caught" == "MISSED" ]] && missed=$((missed+1))
  local teeth=""
  [[ "$caught" == "caught" && "$pb" -ge "$N101" ]] && teeth="  <- only capture rows catch it"
  printf '%-44s | %-18s | %-18s | %s%s\n' "$name" "$full" "$base" "$caught" "$teeth"
}

# M1 capturing subst: drop the under-binder (shift 1 0 $s) so a substituted free var is captured.
run_live_waist_mut "M1 capturing subst (no under-binder shift)" \
  '(bind-subst $j1 $s1 $t)' '(bind-subst $j1 $s $t)'
# M2 drop the subst index decrement: strictly-higher free vars no longer decrement.
run_live_waist_mut "M2 subst: no index decrement" \
  '(Var (- $k 1))' '(Var $k)'
# M3 drop the shift under-binder increment: cutoff not raised under Pi/Lam.
run_live_waist_mut "M3 shift: no under-binder cutoff bump" \
  '(let $c1 (+ $c 1) (bind-shift $d $c1 $t))' '(bind-shift $d $c $t)'
# M4 off-by-one in the shift cutoff comparison: a var at the cutoff is treated as bound.
run_live_waist_mut "M4 shift: off-by-one cutoff (< k c+1)" \
  '(< $k $c)' '(< $k (+ $c 1))'
# M5 shift-cases stops recursing into the case body.
run_live_waist_mut "M5 shift-cases: body not shifted" \
  '(Case $cn (bindg-shift-under $d $c $b0 $body))' '(Case $cn $body)'

echo
echo "Lower active-kernel client mutations"
printf '%-44s | %-18s | %-18s | %s\n' "mutation (waist break)" "lf_v0 suite" "natrec suite" "verdict"
printf '%-44s-+-%-18s-+-%-18s-+-%s\n' "$(printf '%.0s-' {1..44})" "------------------" "------------------" "-------"

run_lower_client_mut() {
  local name="$1" expect_lf="$2" expect_natrec="$3"; shift 3
  local mut_waist_mod="kernel_binding_waist_mut_$$"
  local lf="$MUT_LF" natrec="$MUT_NATREC"
  lit_replace "$BIND_WAIST" "$MUT_WAIST" "$@"
  python3 -c 'import sys
src=open(sys.argv[1]).read()
src=src.replace("kernel_binding_waist_v1", sys.argv[3])
open(sys.argv[2],"w").write(src)' "$LF_ENGINE" "$lf" "$mut_waist_mod"
  python3 -c 'import sys
src=open(sys.argv[1]).read()
src=src.replace("kernel_binding_waist_v1", sys.argv[3])
open(sys.argv[2],"w").write(src)' "$NATREC_ENGINE" "$natrec" "$mut_waist_mod"
  local pl pn
  pl=$(pass_count "$lf"); pn=$(pass_count "$natrec")
  rm -f "$MUT_WAIST"
  local lf_status="n/a($pl)" natrec_status="n/a($pn)" local_missed=0
  if [[ "$expect_lf" -eq 1 ]]; then
    if [[ "$pl" -lt "$LFBASE" ]]; then lf_status="RED($pl<$LFBASE)"; else lf_status="green($pl)"; local_missed=1; fi
  fi
  if [[ "$expect_natrec" -eq 1 ]]; then
    if [[ "$pn" -lt "$NATRECBASE" ]]; then natrec_status="RED($pn<$NATRECBASE)"; else natrec_status="green($pn)"; local_missed=1; fi
  fi
  local caught="caught"
  if [[ "$local_missed" -ne 0 ]]; then caught="MISSED"; missed=$((missed+1)); fi
  printf '%-44s | %-18s | %-18s | %s\n' "$name" "$lf_status" "$natrec_status" "$caught"
}

run_lower_client_mut "L1 subst: no under-binder shift" 1 1 \
  '(bind-subst $j1 $s1 $t)' '(bind-subst $j1 $s $t)'
run_lower_client_mut "L2 subst: no index decrement" 1 1 \
  '(Var (- $k 1))' '(Var $k)'
run_lower_client_mut "L3 shift: no under-binder cutoff bump" 1 1 \
  '(let $c1 (+ $c 1) (bind-shift $d $c1 $t))' '(bind-shift $d $c $t)'
run_lower_client_mut "L4 shift: off-by-one cutoff" 1 1 \
  '(< $k $c)' '(< $k (+ $c 1))'
run_lower_client_mut "L5 NatRec: motive child not shifted" 0 1 \
  '(bindg-shift-under $d $c $b0 $P)' '$P'

echo
echo "Parity demo/probe client mutations"
printf '%-44s | %-12s | %-12s | %-12s | %-12s | %-12s | %s\n' "mutation (waist break)" "curriculum" "break" "exp2" "exp3" "evaluator" "verdict"
printf '%-44s-+-%-12s-+-%-12s-+-%-12s-+-%-12s-+-%-12s-+-%s\n' "$(printf '%.0s-' {1..44})" "------------" "------------" "------------" "------------" "------------" "-------"

run_parity_client_mut() {
  local name="$1"; shift
  local mut_waist_mod="kernel_binding_waist_mut_$$"
  lit_replace "$BIND_WAIST" "$MUT_WAIST" "$@"
  for pair in \
    "$CURR_ENGINE:$MUT_CURR" \
    "$BREAK_ENGINE:$MUT_BREAK" \
    "$EXP2_ENGINE:$MUT_EXP2" \
    "$EXP3_ENGINE:$MUT_EXP3" \
    "$EVAL_ENGINE:$MUT_EVAL"; do
    local src="${pair%%:*}" dst="${pair#*:}"
    python3 -c 'import sys
src=open(sys.argv[1]).read()
src=src.replace("kernel_binding_waist_v1", sys.argv[3])
open(sys.argv[2],"w").write(src)' "$src" "$dst" "$mut_waist_mod"
  done
  local pc pb pe p3 pv
  pc=$(pass_count "$MUT_CURR"); pb=$(pass_count "$MUT_BREAK")
  pe=$(pass_count "$MUT_EXP2"); p3=$(pass_count "$MUT_EXP3"); pv=$(pass_count "$MUT_EVAL")
  rm -f "$MUT_WAIST"
  local sc sb se s3 sv local_missed=0
  if [[ "$pc" -lt "$CURRBASE" ]]; then sc="RED($pc<$CURRBASE)"; else sc="green($pc)"; local_missed=1; fi
  if [[ "$pb" -lt "$BREAKBASE" ]]; then sb="RED($pb<$BREAKBASE)"; else sb="green($pb)"; local_missed=1; fi
  if [[ "$pe" -lt "$EXP2BASE" ]]; then se="RED($pe<$EXP2BASE)"; else se="green($pe)"; local_missed=1; fi
  if [[ "$p3" -lt "$EXP3BASE" ]]; then s3="RED($p3<$EXP3BASE)"; else s3="green($p3)"; local_missed=1; fi
  if [[ "$pv" -lt "$EVALBASE" ]]; then sv="RED($pv<$EVALBASE)"; else sv="green($pv)"; local_missed=1; fi
  local caught="caught"
  if [[ "$local_missed" -ne 0 ]]; then caught="MISSED"; missed=$((missed+1)); fi
  printf '%-44s | %-12s | %-12s | %-12s | %-12s | %-12s | %s\n' "$name" "$sc" "$sb" "$se" "$s3" "$sv" "$caught"
}

run_parity_client_mut "P1 subst: no under-binder shift" \
  '(bind-subst $j1 $s1 $t)' '(bind-subst $j1 $s $t)'
run_parity_client_mut "P2 subst: no index decrement" \
  '(Var (- $k 1))' '(Var $k)'
run_parity_client_mut "P3 shift: no under-binder cutoff bump" \
  '(let $c1 (+ $c 1) (bind-shift $d $c1 $t))' '(bind-shift $d $c $t)'
run_parity_client_mut "P4 shift: off-by-one cutoff" \
  '(< $k $c)' '(< $k (+ $c 1))'

echo
echo "ABT generic replay mutations"
printf '%-44s | %-18s | %s\n' "mutation (injected generic binding break)" "replay suite" "verdict"
printf '%-44s-+-%-18s-+-%s\n' "$(printf '%.0s-' {1..44})" "------------------" "-------"

run_waist_mut() {
  local name="$1"; shift
  local mut_waist_mod="kernel_binding_waist_mut_$$"
  lit_replace "$BIND_WAIST" "$MUT_WAIST" "$@"
  python3 -c 'import sys
src=open(sys.argv[1]).read()
src=src.replace("kernel_binding_waist_v1", sys.argv[3])
open(sys.argv[2],"w").write(src)' "$REPLAY" "$MUT_REPLAY" "$mut_waist_mod"
  local pf
  pf=$(pass_count "$MUT_REPLAY")
  rm -f "$MUT_WAIST" "$MUT_REPLAY"
  local status="green($pf)" caught="MISSED"
  [[ "$pf" -lt "$RFULL" ]] && { status="RED($pf<$RFULL)"; caught="caught"; }
  [[ "$caught" == "MISSED" ]] && missed=$((missed+1))
  printf '%-44s | %-18s | %s\n' "$name" "$status" "$caught"
}

run_decl_mut() {
  local name="$1"; shift
  local mut_decl_mod="kernel_binding_decl_mut_$$"
  lit_replace "$BIND_DECL" "$MUT_DECL" "$@"
  python3 -c 'import sys
src=open(sys.argv[1]).read()
src=src.replace("kernel_binding_decl_v1", sys.argv[3])
open(sys.argv[2],"w").write(src)' "$REPLAY" "$MUT_REPLAY" "$mut_decl_mod"
  local pf
  pf=$(pass_count "$MUT_REPLAY")
  rm -f "$MUT_DECL" "$MUT_REPLAY"
  local status="green($pf)" caught="MISSED"
  [[ "$pf" -lt "$RFULL" ]] && { status="RED($pf<$RFULL)"; caught="caught"; }
  [[ "$caught" == "MISSED" ]] && missed=$((missed+1))
  printf '%-44s | %-18s | %s\n' "$name" "$status" "$caught"
}

run_waist_mut "G1 generic subst: no under-binder shift" \
  '(bind-subst $j1 $s1 $t)' '(bind-subst $j1 $s $t)'
run_waist_mut "G2 generic subst: no index decrement" \
  '(Var (- $k 1))' '(Var $k)'
run_waist_mut "G3 generic shift: no cutoff bump" \
  '(let $c1 (+ $c 1) (bind-shift $d $c1 $t))' '(bind-shift $d $c $t)'
run_waist_mut "G4 generic shift: off-by-one cutoff" \
  '(< $k $c)' '(< $k (+ $c 1))'
run_waist_mut "G5 generic shift-cases: body not shifted" \
  '(Case $cn (bindg-shift-under $d $c $b0 $body))' '(Case $cn $body)'
run_waist_mut "G6 arity table: Pi codomain not binding" \
  '(= (bind-arity PiF  1) 1)' '(= (bind-arity PiF  1) 0)'
run_waist_mut "G7 arity table: Lam body not binding" \
  '(= (bind-arity LamF 1) 1)' '(= (bind-arity LamF 1) 0)'
run_waist_mut "G8 arity table: App arg spuriously binding" \
  '(= (bind-arity AppF 1) 0)' '(= (bind-arity AppF 1) 1)'
run_waist_mut "G9 arity table: Args child spuriously binding" \
  '(= (bind-arity ArgsF 0) 0)' '(= (bind-arity ArgsF 0) 1)'
run_waist_mut "G10 arity table: Case body spuriously binding" \
  '(= (bind-arity CasesF 0) 0)' '(= (bind-arity CasesF 0) 1)'
run_decl_mut "G11 BindingDecl: duplicate field admitted" \
  '(if (binding-field-member $field $rest)
     False
     (if (binding-depth-ok $depth) (binding-fields-admitted $rest) False))' \
  '(if (binding-field-member $field $rest)
     True
     (if (binding-depth-ok $depth) (binding-fields-admitted $rest) False))'
run_decl_mut "G12 BindingDecl: Pi codomain not binding" \
  '(if (== $field $domain) 0
     (if (== $field $codomain) 1 (Bad undeclared-binding-field)))' \
  '(if (== $field $domain) 0
     (if (== $field $codomain) 0 (Bad undeclared-binding-field)))'
run_decl_mut "G13 BindingDecl recursive shift: no cutoff bump" \
  '(binding-shift-under-depth $d (+ $c 1) (- $depth 1) $t)' \
  '(binding-shift-under-depth $d $c (- $depth 1) $t)'
run_decl_mut "G14 BindingDecl recursive subst: no term shift" \
  '(bind-shift 1 0 $s)' \
  '$s'
run_decl_mut "G15 BindingDecl fields: missing field defaults to 0" \
  '(= (binding-field-depth BNil $field) (Bad undeclared-binding-field))' \
  '(= (binding-field-depth BNil $field) 0)'
run_decl_mut "G16 BindingDecl Bind1: unknown field defaults to 0" \
  '(if (== $field $body) 1 (Bad undeclared-binding-field))' \
  '(if (== $field $body) 1 0)'

echo
if [[ "$missed" -eq 0 ]]; then
  echo "BINDING MUTATION GATE: PASS (mutation-complete — every injected break caught, live + ABT generic)"
else
  echo "BINDING MUTATION GATE: FAIL ($missed mutation(s) MISSED — a hole in the capture spec)"
fi
exit "$missed"
