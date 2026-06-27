#!/usr/bin/env bash
# Mutation checks for the Dedukti-as-guest micro-coverage lane.
#
# These edits are applied only to temporary copies.  Each mutated file must go
# red: parser success is not proof success, rewrite obligations must be tracked,
# and guest binders must route through the shared BindingDecl layer.
set -u

DIR="$(cd "$(dirname "$0")" && pwd)"
CETTA="${CETTA:-/home/aimama/aihub/hyperon/CeTTa/cetta}"
CETTA_EXTRA_ARGS="${CETTA_EXTRA_ARGS---eval-hashcons}"
CETTA_AS_LIMIT_BYTES="${CETTA_AS_LIMIT_BYTES:-8589934592}"
CETTA_TIMEOUT_SECONDS="${CETTA_TIMEOUT_SECONDS:-120}"
read -r -a CETTA_EXTRA_ARGV <<< "$CETTA_EXTRA_ARGS"
work="$(mktemp -d "$DIR/.dedukti_mutation.XXXXXX")"
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

rewrite_kernel_imports() {
  local target="$1"
  python3 - "$target" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
text = path.read_text()
text = text.replace(
    "!(import! &self ../../kernel/kernel_signature_lf_v0.metta)",
    "!(import! &self ../../../kernel/kernel_signature_lf_v0.metta)",
)
text = text.replace(
    "!(import! &self ../../kernel/kernel_binding_decl_v1.metta)",
    "!(import! &self ../../../kernel/kernel_binding_decl_v1.metta)",
)
path.write_text(text)
PY
}

copy_guest() {
  local target="$1"
  cp "$DIR/01_dedukti_guest_micro.metta" "$target"
  rewrite_kernel_imports "$target"
}

copy_cic_stage3_guest() {
  local target="$1"
  local target_dir
  target_dir="$(dirname "$target")"
  cp "$DIR/02_cic_guest_sorts_pi_micro.metta" "$target_dir/02_cic_guest_sorts_pi_micro.metta"
  cp "$DIR/04_cic_guest_universes_micro.metta" "$target"
  rewrite_kernel_imports "$target_dir/02_cic_guest_sorts_pi_micro.metta"
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

copy_guest "$work/dk_guest_baseline.metta"
expect_accept "dedukti-guest-baseline-copy" "$work/dk_guest_baseline.metta"

copy_guest "$work/dk_wrong_plus_rule.metta"
mutate_file_exact "$work/dk_wrong_plus_rule.metta" \
  '(dk-nf $rewrites (dkS (dkS $m)))' \
  '(dk-nf $rewrites (dkS $m))'
expect_reject "dedukti-guest-wrong-plus-rewrite" "$work/dk_wrong_plus_rule.metta"

copy_guest "$work/dk_lambda_binder_corrupt.metta"
mutate_file_exact "$work/dk_lambda_binder_corrupt.metta" \
  '(= (dk-lambda-decl) (Bind1 body))' \
  '(= (dk-lambda-decl) Bind0)'
expect_reject "dedukti-guest-lambda-binder-corrupt" "$work/dk_lambda_binder_corrupt.metta"

copy_guest "$work/dk_wrong_proof_type_accept.metta"
mutate_file_exact "$work/dk_wrong_proof_type_accept.metta" \
  '(Reject (Con tt) (dk-prf (Con false)))' \
  '(Accept (Con tt) (dk-prf (Con false)))'
expect_reject "dedukti-guest-wrong-proof-type-accept" "$work/dk_wrong_proof_type_accept.metta"

copy_guest "$work/dk_parser_trust_bypass.metta"
mutate_file_exact "$work/dk_parser_trust_bypass.metta" \
  '(= (dk-proof-check-parsed (Ok $proof))
   (kernel-check (dk-fo-sig) (dk-lower (dk-proof-term $proof)) (dk-lower (dk-proof-type $proof))))' \
  '(= (dk-proof-check-parsed (Ok $proof))
   (Ok (CheckedPrf ANil (dk-lower (dk-proof-term $proof)) (dk-lower (dk-proof-type $proof)))))'
expect_reject "dedukti-guest-parser-trust-bypass" "$work/dk_parser_trust_bypass.metta"

copy_guest "$work/dk_untracked_rewrite_accept.metta"
mutate_file_exact "$work/dk_untracked_rewrite_accept.metta" \
  '(Err untracked-rewrite-obligation)' \
  'True'
expect_reject "dedukti-guest-untracked-rewrite-obligation-accept" "$work/dk_untracked_rewrite_accept.metta"

copy_cic_stage3_guest "$work/cic_stage3_baseline.metta"
expect_accept "cic-stage3-baseline-copy" "$work/cic_stage3_baseline.metta"

copy_cic_stage3_guest "$work/cic_stage3_wrong_max_rule.metta"
mutate_file_exact "$work/cic_stage3_wrong_max_rule.metta" \
  '      ((App (Con max) $lhs)
        (case $a
          (((Con prop) (cic-stage3-nf $lhs))
           ($rhs
             (case $lhs
               (((Con prop) $rhs)
                ((App (Con type) $i)
                  (case $rhs
                    (((App (Con type) $j)
                       (App (Con type) (cic-nat-nf (App (App (Con m) $i) $j))))
                     ($other (App $f $a)))))
                ($other (App $f $a))))))))' \
  '      ((App (Con max) $lhs)
        (case $a
          (((Con prop) (cic-stage3-nf $lhs))
           ($rhs
             (case $lhs
               (((Con prop) $rhs)
                ((App (Con type) $i)
                  (case $rhs
                    (((App (Con type) $j)
                       (Con prop))
                     ($other (App $f $a)))))
                ($other (App $f $a))))))))'
expect_reject "cic-stage3-wrong-max-rule" "$work/cic_stage3_wrong_max_rule.metta"

copy_cic_stage3_guest "$work/cic_stage3_wrong_lift_id.metta"
mutate_file_exact "$work/cic_stage3_wrong_lift_id.metta" \
  '(if (== $s1 $s2)
          $a
          (App $f $a)))' \
  '(if (== $s1 $s2)
          (App $f $a)
          (App $f $a)))'
expect_reject "cic-stage3-wrong-lift-id" "$work/cic_stage3_wrong_lift_id.metta"

copy_cic_stage3_guest "$work/cic_stage3_wrong_term_lift.metta"
mutate_file_exact "$work/cic_stage3_wrong_term_lift.metta" \
  '           ((App (App (App (Con lift) $s1) $s2) $u)
             (cic-stage3-nf
               (App (App (Con Term) $s1) $u)))' \
  '           ((App (App (App (Con lift) $s1) $s2) $u)
             (cic-stage3-nf
               (App (App (Con Term) $s2) $u)))'
expect_reject "cic-stage3-wrong-term-lift" "$work/cic_stage3_wrong_term_lift.metta"

copy_cic_stage3_guest "$work/cic_stage3_untracked_rewrite_accept.metta"
mutate_file_exact "$work/cic_stage3_untracked_rewrite_accept.metta" \
  '(Err untracked-cic-rewrite-obligation)' \
  'True'
expect_reject "cic-stage3-untracked-rewrite-obligation-accept" "$work/cic_stage3_untracked_rewrite_accept.metta"

if [ "$failures" -eq 0 ]; then
  echo "  [mutation] all Dedukti-guest mutations caught"
  exit 0
else
  echo "  [mutation] missed=$failures"
  exit 1
fi
