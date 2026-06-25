#!/usr/bin/env bash
# Mutation checks for the Notation/LanguageDef L0 oracle.
#
# These are deliberately destructive edits applied only to temporary copies.
# Each mutation represents a bug the notation gate must catch.  If a mutated
# file still passes CeTTa, the notation lane is too weak and this script fails.
set -u

DIR="$(cd "$(dirname "$0")" && pwd)"
CETTA="${CETTA:-/home/aimama/aihub/hyperon/CeTTa/cetta}"
CETTA_EXTRA_ARGS="${CETTA_EXTRA_ARGS---eval-hashcons}"
CETTA_AS_LIMIT_BYTES="${CETTA_AS_LIMIT_BYTES:-25769803776}"
CETTA_TIMEOUT_SECONDS="${CETTA_TIMEOUT_SECONDS:-240}"
read -r -a CETTA_EXTRA_ARGV <<< "$CETTA_EXTRA_ARGS"
KERNEL="$(cd "$DIR/../../kernel" && pwd)"
BIND_WAIST="$KERNEL/kernel_binding_waist_v1.metta"
LF_V0_IMPORT="../../../kernel/kernel_signature_lf_v0.metta"
BIND_WAIST_IMPORT="../../../kernel/kernel_binding_waist_v1.metta"
BIND_DECL_IMPORT="../../../kernel/kernel_binding_decl_v1.metta"
work="$(mktemp -d "$DIR/.mutation.XXXXXX")"
trap 'rm -rf "$work"' EXIT

failures=0

run_cetta_capped() {
  local file="$1"
  timeout "$CETTA_TIMEOUT_SECONDS" prlimit --as="$CETTA_AS_LIMIT_BYTES" -- "$CETTA" "${CETTA_EXTRA_ARGV[@]}" "$file"
}

expect_accept() {
  local name="$1"
  local file="$2"
  if run_cetta_capped "$file" >"$work/$name.out" 2>&1 && ! grep -q '(Error' "$work/$name.out"; then
    echo "  [baseline] $name  passed"
  else
    echo "  [baseline] $name  FAILED (mutation setup is invalid)"
    tail -20 "$work/$name.out" | sed 's/^/    /'
    failures=$((failures + 1))
  fi
}

expect_reject() {
  local name="$1"
  local file="$2"
  if ! run_cetta_capped "$file" >"$work/$name.out" 2>&1; then
    echo "  [mutation] $name  caught"
  elif grep -q '(Error' "$work/$name.out"; then
    echo "  [mutation] $name  caught"
  else
    echo "  [mutation] $name  MISSED (mutated file still passed)"
    failures=$((failures + 1))
  fi
}

rewrite_abt_imports() {
  local file="$1"
  local waist_import="$2"
  python3 - "$file" "$LF_V0_IMPORT" "$waist_import" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
lf_v0_import = sys.argv[2]
waist_import = sys.argv[3]
text = path.read_text()
text = text.replace(
    "!(import! &self ../../kernel/kernel_signature_lf_v0.metta)",
    f"!(import! &self {lf_v0_import})",
)
text = text.replace(
    "!(import! &self ../../kernel/kernel_binding_waist_v1.metta)",
    f"!(import! &self {waist_import})",
)
path.write_text(text)
PY
}

copy_abt_with_imports() {
  local target="$1"
  local waist_import="$2"
  cp "$DIR/05_abt_binding_admission.metta" "$target"
  rewrite_abt_imports "$target" "$waist_import"
}

rewrite_alf_imports() {
  local file="$1"
  python3 - "$file" "$LF_V0_IMPORT" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
lf_v0_import = sys.argv[2]
text = path.read_text()
text = text.replace(
    "!(import! &self ../../kernel/kernel_signature_lf_v0.metta)",
    f"!(import! &self {lf_v0_import})",
)
path.write_text(text)
PY
}

copy_alf_with_imports() {
  local target="$1"
  cp "$DIR/07_abt_lf_concrete_syntax_hook.metta" "$target"
  rewrite_alf_imports "$target"
}

rewrite_hol_imports() {
  local file="$1"
  python3 - "$file" "$LF_V0_IMPORT" "$BIND_DECL_IMPORT" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
lf_v0_import = sys.argv[2]
bind_decl_import = sys.argv[3]
text = path.read_text()
text = text.replace(
    "!(import! &self ../../kernel/kernel_signature_lf_v0.metta)",
    f"!(import! &self {lf_v0_import})",
)
text = text.replace(
    "!(import! &self ../../kernel/kernel_binding_decl_v1.metta)",
    f"!(import! &self {bind_decl_import})",
)
path.write_text(text)
PY
}

copy_hol_with_imports() {
  local target="$1"
  cp "$DIR/08_hol_core_concrete_syntax.metta" "$target"
  rewrite_hol_imports "$target"
}

copy_hleq_with_imports() {
  local target="$1"
  cp "$DIR/09_hol_light_eq_kernel.metta" "$target"
  rewrite_hol_imports "$target"
}

copy_hls_with_imports() {
  local target="$1"
  copy_hleq_with_imports "$work/09_hol_light_eq_kernel.metta"
  cp "$DIR/10_hol_light_concrete_syntax.metta" "$target"
}

copy_hshow_with_imports() {
  local target="$1"
  cp "$DIR/11_hol_side_by_side_showcase.metta" "$target"
  rewrite_hol_imports "$target"
}

mutate_file_exact() {
  local file="$1"
  local needle="$2"
  local repl="$3"
  python3 - "$file" "$needle" "$repl" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
needle = sys.argv[2]
repl = sys.argv[3]
text = path.read_text()
if needle not in text:
    raise SystemExit(f"mutation needle not found in {path}: {needle!r}")
path.write_text(text.replace(needle, repl, 1))
PY
}

copy_abt_with_mutated_waist() {
  local target="$1"
  local mut_waist="$2"
  local needle="$3"
  local repl="$4"
  cp "$BIND_WAIST" "$mut_waist"
  mutate_file_exact "$mut_waist" "$needle" "$repl"
  copy_abt_with_imports "$target" "$(basename "$mut_waist")"
}

cp "$DIR/01_invertible_mixfix.metta" "$work/noninjective_admission.metta"
perl -0pi -e 's/\(= \(admit \(Cons \(Note \$c \$f\) \$r\)\) \(if \(dup-form \$f \$r\) False \(admit \$r\)\)\)/\(= \(admit \(Cons \(Note \$c \$f\) \$r\)\) \(admit \$r\)\)/' "$work/noninjective_admission.metta"
expect_reject "non-injective-admission" "$work/noninjective_admission.metta"

cp "$DIR/02_precedence_assoc.metta" "$work/mixed_assoc_admission.metta"
perl -0pi -e 's/\(if \(sym-dup \$s \$r\)\n     False\n     \(if \(assoc-conflict \$p \$a \$r\) False \(admitFix \$r\)\)\)/\(if \(sym-dup \$s \$r\)\n     False\n     \(admitFix \$r\)\)/' "$work/mixed_assoc_admission.metta"
expect_reject "mixed-assoc-admission" "$work/mixed_assoc_admission.metta"

cp "$DIR/01_invertible_mixfix.metta" "$work/capture_unsafe_print.metta"
perl -0pi -e 's/\(let \$nm \(vn \(len \$ctx\)\)/\(let \$nm a0/g' "$work/capture_unsafe_print.metta"
expect_reject "capture-unsafe-print" "$work/capture_unsafe_print.metta"

cp "$DIR/01_invertible_mixfix.metta" "$work/broken_roundtrip.metta"
perl -0pi -e 's/\(= \(idx \$x \(Cons \$y \$ys\) \$i\) \(if \(== \$x \$y\) \$i \(idx \$x \$ys \(\+ \$i 1\)\)\)\)/\(= \(idx \$x \(Cons \$y \$ys\) \$i\) NF\)/' "$work/broken_roundtrip.metta"
expect_reject "broken-prsT-prT-roundtrip" "$work/broken_roundtrip.metta"

copy_abt_with_imports "$work/abt_baseline.metta" "$BIND_WAIST_IMPORT"
expect_accept "abt-baseline-copy" "$work/abt_baseline.metta"

copy_abt_with_mutated_waist \
  "$work/abt_missing_shift.metta" \
  "$work/abt_missing_shift_waist.metta" \
  '(= (bindg-subst-under $j $s 1 $t)
   (let $j1 (+ $j 1)
     (let $s1 (bind-shift 1 0 $s)
       (bind-subst $j1 $s1 $t))))' \
  '(= (bindg-subst-under $j $s 1 $t)
   (let $j1 (+ $j 1)
     (bind-subst $j1 $s $t)))'
expect_reject "abt-missing-shift-under-binder" "$work/abt_missing_shift.metta"

copy_abt_with_mutated_waist \
  "$work/abt_missing_decrement.metta" \
  "$work/abt_missing_decrement_waist.metta" \
  '(Var (- $k 1))' \
  '(Var $k)'
expect_reject "abt-missing-index-decrement" "$work/abt_missing_decrement.metta"

copy_abt_with_imports "$work/abt_capture_unsafe_print.metta" "$BIND_WAIST_IMPORT"
perl -0pi -e 's/\(let \$n \(abt-len \$ctx\)\n     \(let \$nm \(abtvn \$n\)/(let $n (abt-len $ctx)\n     (let $nm a0/' "$work/abt_capture_unsafe_print.metta"
expect_reject "abt-capture-unsafe-print" "$work/abt_capture_unsafe_print.metta"

cp "$DIR/06_metta_self_concrete_syntax.metta" "$work/metta_self_baseline.metta"
expect_accept "metta-self-baseline-copy" "$work/metta_self_baseline.metta"

cp "$DIR/06_metta_self_concrete_syntax.metta" "$work/metta_self_broken_desugar.metta"
mutate_file_exact "$work/metta_self_broken_desugar.metta" \
  '(ms-cns $op
         (ms-cns (ms-desugar (ms-hd $e))' \
  '(ms-cns (ms-hd $e)
         (ms-cns (ms-desugar (ms-hd $e))'
expect_reject "metta-self-broken-desugar" "$work/metta_self_broken_desugar.metta"

cp "$DIR/06_metta_self_concrete_syntax.metta" "$work/metta_self_broken_resugar.metta"
mutate_file_exact "$work/metta_self_broken_resugar.metta" \
  '(= (ms-wr $e) (let $s (ms-resugar $e) (repr $s)))' \
  '(= (ms-wr $e) (repr $e))'
expect_reject "metta-self-broken-resugar" "$work/metta_self_broken_resugar.metta"

cp "$DIR/06_metta_self_concrete_syntax.metta" "$work/metta_self_noninjective_admission.metta"
mutate_file_exact "$work/metta_self_noninjective_admission.metta" \
  '(if (ms-token-member? (ms-token $n) $r)
     False
     (if (ms-head-member? (ms-head $n) $r) False (ms-admit $r)))' \
  '(if False
     False
     (if (ms-head-member? (ms-head $n) $r) False (ms-admit $r)))'
expect_reject "metta-self-noninjective-admission" "$work/metta_self_noninjective_admission.metta"

cp "$DIR/06_metta_self_concrete_syntax.metta" "$work/metta_self_parser_trust_bypass.metta"
mutate_file_exact "$work/metta_self_parser_trust_bypass.metta" \
  '(= (ms-concrete-syntax-eval $s) (ms-eval (ms-rd $s)))' \
  '(= (ms-concrete-syntax-eval $s) (ms-eval-ok (ms-rd $s)))'
expect_reject "metta-self-parser-trust-bypass" "$work/metta_self_parser_trust_bypass.metta"

copy_alf_with_imports "$work/alf_baseline.metta"
expect_accept "abt-lf-baseline-copy" "$work/alf_baseline.metta"

copy_alf_with_imports "$work/alf_binding_shape_drift.metta"
mutate_file_exact "$work/alf_binding_shape_drift.metta" \
  '(= (alf-bind-ok $c $b)
   (if (== $c LamF)
     (== $b (Bind1 body))' \
  '(= (alf-bind-ok $c $b)
   (if (== $c LamF)
     (== $b Bind0)'
expect_reject "abt-lf-binding-shape-drift" "$work/alf_binding_shape_drift.metta"

copy_alf_with_imports "$work/alf_bad_canonical_acceptance.metta"
mutate_file_exact "$work/alf_bad_canonical_acceptance.metta" \
  '(Cons (Reject (App (Con z) (Con z)) (Con nat))' \
  '(Cons (Accept (App (Con z) (Con z)) (Con nat))'
expect_reject "abt-lf-bad-canonical-acceptance" "$work/alf_bad_canonical_acceptance.metta"

copy_hol_with_imports "$work/hol_baseline.metta"
expect_accept "hol-core-baseline-copy" "$work/hol_baseline.metta"

copy_hol_with_imports "$work/hol_disch_binder_corrupt.metta"
mutate_file_exact "$work/hol_disch_binder_corrupt.metta" \
  '(= (hol-make-disch $A0 $B0 $body0)
   (App (App (App (Con impI) $A0) $B0)
        (Lam (App (Con prf) $A0) $body0)))' \
  '(= (hol-make-disch $A0 $B0 $body0)
   (App (App (App (Con impI) $A0) $B0)
       (Lam (App (Con prf) $B0) $body0)))'
expect_reject "hol-core-disch-binder-corrupt" "$work/hol_disch_binder_corrupt.metta"

copy_hol_with_imports "$work/hol_binddecl_depth_corrupt.metta"
mutate_file_exact "$work/hol_binddecl_depth_corrupt.metta" \
  '(= (hol-binding-depth-in $tbl $c $field)
   (binding-decl-depth (hol-bind-of-in $tbl $c) $field))' \
  '(= (hol-binding-depth-in $tbl $c $field) 0)'
expect_reject "hol-core-binddecl-depth-corrupt" "$work/hol_binddecl_depth_corrupt.metta"

copy_hol_with_imports "$work/hol_free_var_bypass.metta"
mutate_file_exact "$work/hol_free_var_bypass.metta" \
  '(if (== $i NF) (Ok (HBad free-assumption) $rest) (Ok (HAssume $i) $rest))' \
  '(if (== $i NF) (Ok (HAssume 0) $rest) (Ok (HAssume $i) $rest))'
expect_reject "hol-core-free-var-bypass" "$work/hol_free_var_bypass.metta"

copy_hol_with_imports "$work/hol_mp_corrupt.metta"
mutate_file_exact "$work/hol_mp_corrupt.metta" \
  '(App (App (App (App (Con impE) $A0) $B0) $f0) $x0)' \
  '(App (App (App (App (Con impI) $A0) $B0) $f0) $x0)'
expect_reject "hol-core-mp-corrupt" "$work/hol_mp_corrupt.metta"

copy_hol_with_imports "$work/hol_refl_corrupt.metta"
mutate_file_exact "$work/hol_refl_corrupt.metta" \
  '(if (== $A0 (Con nat)) (App (Con rfl) $t0) (Err unsupported-eq-type))' \
  '(if (== $A0 (Con nat)) (Con z) (Err unsupported-eq-type))'
expect_reject "hol-core-refl-corrupt" "$work/hol_refl_corrupt.metta"

copy_hol_with_imports "$work/hol_checker_bypass.metta"
mutate_file_exact "$work/hol_checker_bypass.metta" \
  '(= (hol-concrete-syntax-check $proof-toks $prop-toks)
   (kernel-check (good-sig) (hol-lowerProofT $proof-toks) (hol-proof-typeT $prop-toks)))' \
  '(= (hol-concrete-syntax-check $proof-toks $prop-toks)
   (Ok (CheckedPrf ANil (hol-lowerProofT $proof-toks) (hol-proof-typeT $prop-toks))))'
expect_reject "hol-core-checker-bypass" "$work/hol_checker_bypass.metta"

copy_hleq_with_imports "$work/hleq_baseline.metta"
expect_accept "hol-light-eq-baseline-copy" "$work/hleq_baseline.metta"

copy_hleq_with_imports "$work/hleq_refl_corrupt.metta"
mutate_file_exact "$work/hleq_refl_corrupt.metta" \
  '(= (hl-refl-A)
   (App (Con hl_REFL) (Con A)))' \
  '(= (hl-refl-A)
   (App (Con hl_REFL) (Con B)))'
expect_reject "hol-light-eq-REFL-corrupt" "$work/hleq_refl_corrupt.metta"

copy_hleq_with_imports "$work/hleq_trans_corrupt.metta"
mutate_file_exact "$work/hleq_trans_corrupt.metta" \
  '(App (Con hl_TRANS) (Con A))' \
  '(App (Con hl_TRANS) (Con B))'
expect_reject "hol-light-eq-TRANS-corrupt" "$work/hleq_trans_corrupt.metta"

copy_hleq_with_imports "$work/hleq_abs_corrupt.metta"
mutate_file_exact "$work/hleq_abs_corrupt.metta" \
  '(Lam (Con o) (App (Con hl_REFL) (Var 0)))' \
  '(Lam (Con o) (App (Con hl_REFL) (Con A)))'
expect_reject "hol-light-eq-ABS-corrupt" "$work/hleq_abs_corrupt.metta"

copy_hleq_with_imports "$work/hleq_mk_comb_corrupt.metta"
mutate_file_exact "$work/hleq_mk_comb_corrupt.metta" \
  '(App (Con hl_MK_COMB) (hl-id))' \
  '(App (Con hl_MK_COMB) (Lam (Con o) (Con B)))'
expect_reject "hol-light-eq-MK_COMB-corrupt" "$work/hleq_mk_comb_corrupt.metta"

copy_hleq_with_imports "$work/hleq_beta_corrupt.metta"
mutate_file_exact "$work/hleq_beta_corrupt.metta" \
  '(= (hl-beta-A)
   (App (Con hl_BETA) (Con A)))' \
  '(= (hl-beta-A)
   (App (Con hl_BETA) (Con B)))'
expect_reject "hol-light-eq-BETA-corrupt" "$work/hleq_beta_corrupt.metta"

copy_hleq_with_imports "$work/hleq_assume_corrupt.metta"
mutate_file_exact "$work/hleq_assume_corrupt.metta" \
  '(= (hl-assume-id-A)
   (Lam (hl-prf (Con A)) (Var 0)))' \
  '(= (hl-assume-id-A)
   (Lam (hl-prf (Con A)) (hl-refl-A)))'
expect_reject "hol-light-eq-ASSUME-corrupt" "$work/hleq_assume_corrupt.metta"

copy_hleq_with_imports "$work/hleq_deduct_corrupt.metta"
mutate_file_exact "$work/hleq_deduct_corrupt.metta" \
  '(App (Con hl_DEDUCT_ANTISYM) (Con A))' \
  '(App (Con hl_DEDUCT_ANTISYM) (Con B))'
expect_reject "hol-light-eq-DEDUCT_ANTISYM-corrupt" "$work/hleq_deduct_corrupt.metta"

copy_hleq_with_imports "$work/hleq_eq_mp_corrupt.metta"
mutate_file_exact "$work/hleq_eq_mp_corrupt.metta" \
  '(hl-refl-A)))' \
  '(hl-refl-eqAA)))'
expect_reject "hol-light-eq-EQ_MP-corrupt" "$work/hleq_eq_mp_corrupt.metta"

copy_hleq_with_imports "$work/hleq_imp_def_use_corrupt.metta"
mutate_file_exact "$work/hleq_imp_def_use_corrupt.metta" \
  '(= (hl-imp-def-AB)
   (App (App (Con hl_IMP_DEF) (Con A)) (Con B)))' \
  '(= (hl-imp-def-AB)
   (App (App (Con hl_IMP_DEF) (Con B)) (Con A)))'
expect_reject "hol-light-eq-IMP_DEF-use-corrupt" "$work/hleq_imp_def_use_corrupt.metta"

copy_hleq_with_imports "$work/hleq_derived_eqt_intro_corrupt.metta"
mutate_file_exact "$work/hleq_derived_eqt_intro_corrupt.metta" \
  '(Lam (hl-prf (Con hl_T)) (Var 1))' \
  '(Lam (hl-prf (Con hl_T)) (Var 0))'
expect_reject "hol-light-eq-derived-EQT_INTRO-corrupt" "$work/hleq_derived_eqt_intro_corrupt.metta"

copy_hleq_with_imports "$work/hleq_abs_pred2_corrupt.metta"
mutate_file_exact "$work/hleq_abs_pred2_corrupt.metta" \
  '(App (Con hl_ABS_PRED2) (hl-and-pred (Con A) (Con A)))' \
  '(App (Con hl_ABS_PRED2) (hl-and-pred (Con B) (Con A)))'
expect_reject "hol-light-eq-ABS_PRED2-corrupt" "$work/hleq_abs_pred2_corrupt.metta"

copy_hleq_with_imports "$work/hleq_derived_sym_eqt_corrupt.metta"
mutate_file_exact "$work/hleq_derived_sym_eqt_corrupt.metta" \
  '(hl-sym-from (Con A) (Con hl_T) $h)' \
  '(hl-sym-from (Con hl_T) (Con A) $h)'
expect_reject "hol-light-eq-derived-SYM-EQT-corrupt" "$work/hleq_derived_sym_eqt_corrupt.metta"

copy_hleq_with_imports "$work/hleq_and_def_ap_corrupt.metta"
mutate_file_exact "$work/hleq_and_def_ap_corrupt.metta" \
  '(App (Con hl_MK_COMB_PRED2) (hl-and-pred (Con A) (Con A)))' \
  '(App (Con hl_MK_COMB_PRED2) (hl-and-pred (Con B) (Con A)))'
expect_reject "hol-light-eq-AND_DEF-application-corrupt" "$work/hleq_and_def_ap_corrupt.metta"

copy_hleq_with_imports "$work/hleq_disch_dthm_corrupt.metta"
mutate_file_exact "$work/hleq_disch_dthm_corrupt.metta" \
  '(SCons (DThm hl_DISCH_AA_CORE
             (hl-prf (hl-eq (hl-and-AA) (Con A)))
             (hl-disch-AA-core))' \
  '(SCons (DThm hl_DISCH_AA_CORE
             (hl-prf (hl-eq (hl-and-AA) (Con A)))
             (hl-conjunct1-AA))'
expect_reject "hol-light-eq-derived-DISCH-DThm-corrupt" "$work/hleq_disch_dthm_corrupt.metta"

copy_hleq_with_imports "$work/hleq_self_imp_dthm_corrupt.metta"
mutate_file_exact "$work/hleq_self_imp_dthm_corrupt.metta" \
  '(SCons (DThm hl_SELF_IMP_A
             (hl-prf (hl-imp (Con A) (Con A)))
             (hl-self-imp-derived))' \
  '(SCons (DThm hl_SELF_IMP_A
             (hl-prf (hl-imp (Con A) (Con A)))
             (hl-refl-A))'
expect_reject "hol-light-eq-derived-SELF-IMP-DThm-corrupt" "$work/hleq_self_imp_dthm_corrupt.metta"

copy_hleq_with_imports "$work/hleq_mp_dthm_corrupt.metta"
mutate_file_exact "$work/hleq_mp_dthm_corrupt.metta" \
  '(SCons (DThm hl_MP_AB
             (Pi (hl-prf (hl-impAB)) (Pi (hl-prf (Con A)) (hl-prf (Con B))))
             (hl-mp-AB))' \
  '(SCons (DThm hl_MP_AB
             (Pi (hl-prf (hl-impAB)) (Pi (hl-prf (Con A)) (hl-prf (Con B))))
             (hl-conjunct2-PQ (Con A) (Con B)))'
expect_reject "hol-light-eq-derived-MP-DThm-corrupt" "$work/hleq_mp_dthm_corrupt.metta"

copy_hleq_with_imports "$work/hleq_expanded_ab_dthm_corrupt.metta"
mutate_file_exact "$work/hleq_expanded_ab_dthm_corrupt.metta" \
  '(SCons (DThm hl_AND_EXPANDED_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-expanded-PQ (Con A) (Con B)))))
             (hl-and-expanded-PQ-from-proofs (Con A) (Con B)))' \
  '(SCons (DThm hl_AND_EXPANDED_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-expanded-PQ (Con A) (Con B)))))
             (hl-conjunct1-PQ (Con A) (Con B)))'
expect_reject "hol-light-eq-derived-EXPANDED-AB-DThm-corrupt" "$work/hleq_expanded_ab_dthm_corrupt.metta"

copy_hleq_with_imports "$work/hleq_conj_ab_dthm_corrupt.metta"
mutate_file_exact "$work/hleq_conj_ab_dthm_corrupt.metta" \
  '(SCons (DThm hl_CONJ_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-AB))))
             (hl-conj-AB-from-proofs-sharded))' \
  '(SCons (DThm hl_CONJ_AB_FROM_PROOFS
             (Pi (hl-prf (Con A)) (Pi (hl-prf (Con B)) (hl-prf (hl-and-AB))))
             (hl-conjunct1-PQ (Con A) (Con B)))'
expect_reject "hol-light-eq-derived-CONJ-AB-DThm-corrupt" "$work/hleq_conj_ab_dthm_corrupt.metta"

copy_hleq_with_imports "$work/hleq_conjunct1_ab_dthm_corrupt.metta"
mutate_file_exact "$work/hleq_conjunct1_ab_dthm_corrupt.metta" \
  '(SCons (DThm hl_CONJUNCT1_AB
             (Pi (hl-prf (hl-and-AB)) (hl-prf (Con A)))
             (hl-conjunct1-PQ (Con A) (Con B)))' \
  '(SCons (DThm hl_CONJUNCT1_AB
             (Pi (hl-prf (hl-and-AB)) (hl-prf (Con A)))
             (hl-conjunct2-PQ (Con A) (Con B)))'
expect_reject "hol-light-eq-derived-CONJUNCT1-AB-DThm-corrupt" "$work/hleq_conjunct1_ab_dthm_corrupt.metta"

copy_hleq_with_imports "$work/hleq_disch_ab_dthm_corrupt.metta"
mutate_file_exact "$work/hleq_disch_ab_dthm_corrupt.metta" \
  '(SCons (DThm hl_DISCH_AB_UNDER_IMPAB
             (Pi (hl-prf (hl-impAB)) (hl-prf (hl-impAB)))
             (hl-disch-AB-under-impAB-sharded))' \
  '(SCons (DThm hl_DISCH_AB_UNDER_IMPAB
             (Pi (hl-prf (hl-impAB)) (hl-prf (hl-impAB)))
             (hl-refl-A))'
expect_reject "hol-light-eq-derived-DISCH-AB-DThm-corrupt" "$work/hleq_disch_ab_dthm_corrupt.metta"

copy_hleq_with_imports "$work/hleq_old_mp_dthm_corrupt.metta"
mutate_file_exact "$work/hleq_old_mp_dthm_corrupt.metta" \
  '(SCons (DThm hl_OLD_MP_REPLAY
             (hl-prf (hl-impAB-self))
             (hl-old-mp-replay-sharded))' \
  '(SCons (DThm hl_OLD_MP_REPLAY
             (hl-prf (hl-impAB-self))
             (hl-refl-A))'
expect_reject "hol-light-eq-derived-OLD-MP-DThm-corrupt" "$work/hleq_old_mp_dthm_corrupt.metta"

copy_hls_with_imports "$work/hls_baseline.metta"
expect_accept "hol-light-concrete-syntax-baseline-copy" "$work/hls_baseline.metta"

copy_hls_with_imports "$work/hls_imp_lowering_corrupt.metta"
mutate_file_exact "$work/hls_imp_lowering_corrupt.metta" \
  '(= (hls-lower-prop (HImp $P $Q)) (hl-imp (hls-lower-prop $P) (hls-lower-prop $Q)))' \
  '(= (hls-lower-prop (HImp $P $Q)) (hl-and (hls-lower-prop $P) (hls-lower-prop $Q)))'
expect_reject "hol-light-concrete-syntax-IMP-lowering-corrupt" "$work/hls_imp_lowering_corrupt.metta"

copy_hls_with_imports "$work/hls_lambda_binder_corrupt.metta"
mutate_file_exact "$work/hls_lambda_binder_corrupt.metta" \
  '(= (hls-lambda-decl) (Bind1 body))' \
  '(= (hls-lambda-decl) Bind0)'
expect_reject "hol-light-concrete-syntax-lambda-binder-corrupt" "$work/hls_lambda_binder_corrupt.metta"

copy_hls_with_imports "$work/hls_parser_trust_bypass.metta"
mutate_file_exact "$work/hls_parser_trust_bypass.metta" \
  '(if (== $toks (hls-bad-refl-for-imp-concrete-syntax)) (Ok (HLS refl (HThm (HImp HA HA))))' \
  '(if (== $toks (hls-bad-refl-for-imp-concrete-syntax)) (Ok (HLS self_imp (HThm (HImp HA HA))))'
expect_reject "hol-light-concrete-syntax-parser-trust-bypass" "$work/hls_parser_trust_bypass.metta"

copy_hshow_with_imports "$work/hshow_baseline.metta"
expect_accept "hol-side-by-side-showcase-baseline-copy" "$work/hshow_baseline.metta"

copy_hshow_with_imports "$work/hshow_imp_lowering_corrupt.metta"
mutate_file_exact "$work/hshow_imp_lowering_corrupt.metta" \
  '(= (hshow-lower-prop (==> $P $Q)) (hl-imp (hshow-lower-prop $P) (hshow-lower-prop $Q)))' \
  '(= (hshow-lower-prop (==> $P $Q)) (hl-and (hshow-lower-prop $P) (hshow-lower-prop $Q)))'
expect_reject "hol-side-by-side-showcase-IMP-lowering-corrupt" "$work/hshow_imp_lowering_corrupt.metta"

copy_hshow_with_imports "$work/hshow_refl_mapping_corrupt.metta"
mutate_file_exact "$work/hshow_refl_mapping_corrupt.metta" \
  '(Ok (hshow-cert hl-check-core-prim-def-batch hl_REFL_A (HThm (= HP HP))))' \
  '(Ok (hshow-cert hl-check-core-prim-def-batch hl_TRANS_AAA (HThm (= HP HP))))'
expect_reject "hol-side-by-side-showcase-REFL-mapping-corrupt" "$work/hshow_refl_mapping_corrupt.metta"

copy_hshow_with_imports "$work/hshow_lambda_binder_corrupt.metta"
mutate_file_exact "$work/hshow_lambda_binder_corrupt.metta" \
  '(= (hshow-lambda-decl) (Bind1 body))' \
  '(= (hshow-lambda-decl) Bind0)'
expect_reject "hol-side-by-side-showcase-lambda-binder-corrupt" "$work/hshow_lambda_binder_corrupt.metta"

copy_hshow_with_imports "$work/hshow_nested_lambda_binder_corrupt.metta"
mutate_file_exact "$work/hshow_nested_lambda_binder_corrupt.metta" \
  '(BindFields (BCons (BField body 2) BNil))' \
  '(BindFields (BCons (BField body 1) BNil))'
expect_reject "hol-side-by-side-showcase-nested-lambda-binder-corrupt" "$work/hshow_nested_lambda_binder_corrupt.metta"

copy_hshow_with_imports "$work/hshow_parser_trust_bypass.metta"
mutate_file_exact "$work/hshow_parser_trust_bypass.metta" \
  '(if (== $form (hshow-bad-refl-for-imp-form)) (Ok (HShow REFL (HThm (==> HP HP))))' \
  '(if (== $form (hshow-bad-refl-for-imp-form)) (Ok (HShow DISCH_ASSUME (HThm (==> HP HP))))'
expect_reject "hol-side-by-side-showcase-parser-trust-bypass" "$work/hshow_parser_trust_bypass.metta"

if [ "$failures" -eq 0 ]; then
  echo "  [mutation] all notation mutations caught"
  exit 0
else
  echo "  [mutation] missed=$failures"
  exit 1
fi
