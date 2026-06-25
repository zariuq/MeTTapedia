#!/usr/bin/env bash
# run_sr_admission_gate.sh — generated-iota SR admission gate mutation teeth.
#
# Mutations are applied to temporary copies only.  The gate is deliberately narrow:
# it proves the new SR-admission predicates in kernel_signature_lf_indexed_v0.metta
# are load-bearing without claiming the universal SR/confluence metatheorem.
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CETTA="${CETTA:-/home/aimama/aihub/hyperon/CeTTa/cetta}"
ENGINE="$ROOT/kernel_signature_lf_indexed_v0.metta"
TMP="$(mktemp -d "$ROOT/.sr_admission_mutation.XXXXXX")"
MUT_INDEXED="$ROOT/kernel_signature_lf_indexed_sr_mut_$$.metta"
EXACT_DEFS="$ROOT/kernel_signature_lf_indexed_sr_exact_defs_$$.metta"
trap 'rm -rf "$TMP" "$MUT_INDEXED" "$EXACT_DEFS"' EXIT

pass_count() {
  timeout 180 prlimit --as=17179869184 -- "$CETTA" "$1" 2>/dev/null | grep -cE '\[\(\)\]'
}

lit_replace() {
  python3 -c 'import sys
s=open(sys.argv[1]).read()
for i in range(3,len(sys.argv),2):
    s=s.replace(sys.argv[i],sys.argv[i+1])
open(sys.argv[2],"w").write(s)' "$@"
}

run_exact() {
  local name="$1"; shift
  local log="$TMP/exact_reason.log"
  lit_replace "$ENGINE" "$EXACT_DEFS" "$@" \
    '!(assertEqual (dindg-iota-preservation-status (good-sig-G) (good-sig-G)) (Ok sr-iota-preserves-type))' \
    '!(println! (dindg-iota-preservation-status (good-sig-G) (good-sig-G)))
!(println! (sig-admitted-with-elims (good-sig-G)))' \
    '!(assertEqual (dindg-iota-preservation-status (pair-sig-G) (pair-sig-G)) (Ok sr-iota-preserves-type))' \
    '!(assertEqual (dindg-iota-preservation-status (pair-sig-G) (pair-sig-G)) (Bad sr-iota-mismatch))' \
    '!(assertEqual (sig-admitted-with-elims (good-sig-G)) True)' \
    '!(assertEqual (sig-admitted-with-elims (good-sig-G)) False)' \
    '!(assertEqual (sig-admitted-with-elims (pair-sig-G)) True)' \
    '!(assertEqual (sig-admitted-with-elims (pair-sig-G)) False)' \
    '!(assertEqual
   (kernel-check (good-sig-G) (id-j-indg-typed) (Con nat))
   (Ok (CheckedPrf ANil (id-j-indg-typed) (Con nat))))' \
    '!(println! (kernel-check (good-sig-G) (id-j-indg-typed) (Con nat)))'
  timeout 180 prlimit --as=17179869184 -- "$CETTA" "$EXACT_DEFS" >"$log" 2>&1
  local status verdict
  status="reason-missing"
  verdict="MISSED"
  if grep -Fxq '(Bad sr-iota-mismatch)' "$log" \
     && grep -Fxq 'False' "$log" \
     && grep -Fxq '(Err signature-not-admitted)' "$log"; then
    status="reason-ok"
    verdict="caught"
  else
    missed=$((missed+1))
  fi
  printf '%-52s | %-18s | %s\n' "$name" "$status" "$verdict"
}

BASE=$(pass_count "$ENGINE")
MIN_BASE=127

echo "Subject-Reduction-as-Admission Gate v2 — mutation gate"
echo "baseline: indexed engine = $BASE pass"
echo

if [[ "$BASE" -lt "$MIN_BASE" ]]; then
  echo "SR ADMISSION GATE: FAIL (baseline below $MIN_BASE)"
  exit 1
fi

missed=0
printf '%-52s | %-18s | %s\n' "mutation (injected SR-gate break)" "indexed suite" "verdict"
printf '%-52s-+-%-18s-+-%s\n' "$(printf '%.0s-' {1..52})" "------------------" "-------"

run_mut() {
  local name="$1"; shift
  local f="$MUT_INDEXED"
  lit_replace "$ENGINE" "$f" "$@"
  local p status verdict
  p=$(pass_count "$f")
  status="green($p)"
  verdict="MISSED"
  if [[ "$p" -lt "$BASE" ]]; then
    status="RED($p<$BASE)"
    verdict="caught"
  else
    missed=$((missed+1))
  fi
  printf '%-52s | %-18s | %s\n' "$name" "$status" "$verdict"
}

run_mut "SR1 duplicate ctor orthogonality accepted" \
  '(= (dindg-orthogonality-status (SCons (DIndG $n $pT $iT $ctors) $rest))
   (if (unique-gctors $ctors)
     (dindg-orthogonality-status $rest)
     (Bad confluence-via-checked-orthogonality)))' \
  '(= (dindg-orthogonality-status (SCons (DIndG $n $pT $iT $ctors) $rest))
   (if (unique-gctors $ctors)
     (dindg-orthogonality-status $rest)
     (Ok orthogonal)))'

run_mut "SR2 iota-preservation gate rejects good signature" \
  '(= (dindg-iota-preservation-ok $sig)
   (status-ok (dindg-iota-preservation-status $sig $sig)))' \
  '(= (dindg-iota-preservation-ok $sig)
   False)'

run_mut "SR3 generated iota RHS corrupted at admission" \
  '(branch-apply-g $sig $name $params $motive $cases $body
                 (inst-tel-args $ct $params)
                 $args)' \
  '(Con nat)'

run_exact "SR3 reason: bad RHS rejects admission/check" \
  '(branch-apply-g $sig $name $params $motive $cases $body
                 (inst-tel-args $ct $params)
                 $args)' \
  '(Con nat)'

run_mut "SR4 bad iota target ignores constructor head" \
  '(if (== (app-head $ctorApp) $ctor)
       (Ok sr-iota-preserves-type)
       (Bad sr-iota-mismatch))' \
  '(Ok sr-iota-preserves-type)'

run_mut "SR5 iota rule type mismatch accepted" \
  '(case (conv $sig $a $b)
         ((True (Ok sr-iota-preserves-type))
          (False (Bad sr-iota-mismatch))
          ($_ (Bad sr-iota-mismatch))))' \
  '(Ok sr-iota-preserves-type)'

echo
if [[ "$missed" -eq 0 ]]; then
  echo "SR ADMISSION GATE: PASS (mutation-complete — every injected SR break caught)"
else
  echo "SR ADMISSION GATE: FAIL ($missed mutation(s) MISSED — SR gate not load-bearing)"
fi
exit "$missed"
