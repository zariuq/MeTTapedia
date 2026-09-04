#!/usr/bin/env bash

set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 /path/to/mork /path/to/metamath-test" >&2
  exit 2
fi

mork_bin=$1
metamath_test_root=$2

if [[ ! -x "$mork_bin" ]]; then
  echo "error: MORK executable is not executable: $mork_bin" >&2
  exit 2
fi

valid_source="$metamath_test_root/tests/unit/test_stack_simple.mm"
invalid_source="$metamath_test_root/tests/unit/test26_wrong_conclusion_in_proof.mm"
typecode_invalid_source="$metamath_test_root/tests/unit/test22_typecode_mismatch_in_substitution.mm"
essential_source="$metamath_test_root/tests/unit/test_stack_fhyps.mm"
dv_source="$metamath_test_root/tests/unit/test_dv_yz_required.mm"
dv_invalid_source="$metamath_test_root/tests/unit/test27_disjoint_variable_constraint_violation.mm"
undefined_label_source="$metamath_test_root/tests/unit/test24_undefined_label_in_proof.mm"
malformed_source="$metamath_test_root/tests/unit/test14_variable_without_f_hypothesis.mm"

for source_path in "$valid_source" "$invalid_source" \
    "$typecode_invalid_source" \
    "$essential_source" "$dv_source" "$dv_invalid_source" \
    "$undefined_label_source" \
    "$malformed_source"; do
  if [[ ! -f "$source_path" ]]; then
    echo "error: missing metamath-test unit fixture: $source_path" >&2
    exit 2
  fi
done

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
project_root=$(cd -- "$script_dir/.." && pwd)
output_dir="$project_root/.lake/build/conformance/metamath_mm2_raw_unit"
checked_dir="$project_root/artifacts/conformance/metamath_mm2_raw_unit"

mkdir -p "$output_dir"
cd "$project_root"

valid_program="$output_dir/test_stack_simple.mm2"
valid_result="$output_dir/test_stack_simple.result.mm2"
invalid_program="$output_dir/test26_wrong_conclusion_in_proof.mm2"
invalid_result="$output_dir/test26_wrong_conclusion_in_proof.result.mm2"
typecode_invalid_program="$output_dir/test22_typecode_mismatch_in_substitution.mm2"
typecode_invalid_result="$output_dir/test22_typecode_mismatch_in_substitution.result.mm2"
essential_program="$output_dir/test_stack_fhyps.mm2"
essential_result="$output_dir/test_stack_fhyps.result.mm2"
dv_program="$output_dir/test_dv_yz_required.mm2"
dv_result="$output_dir/test_dv_yz_required.result.mm2"
dv_invalid_program="$output_dir/test27_disjoint_variable_constraint_violation.mm2"
dv_invalid_result="$output_dir/test27_disjoint_variable_constraint_violation.result.mm2"
undefined_label_program="$output_dir/test24_undefined_label_in_proof.mm2"
undefined_label_result="$output_dir/test24_undefined_label_in_proof.result.mm2"
valid_verifier_program="$output_dir/test_stack_simple.verifier.mm2"
valid_source_data_program="$output_dir/test_stack_simple.source-data.mm2"
valid_split_program="$output_dir/test_stack_simple.split.mm2"
invalid_verifier_program="$output_dir/test26_wrong_conclusion_in_proof.verifier.mm2"
invalid_source_data_program="$output_dir/test26_wrong_conclusion_in_proof.source-data.mm2"
invalid_split_program="$output_dir/test26_wrong_conclusion_in_proof.split.mm2"
authored_duplicate_program="$output_dir/authored_duplicate_constant.mm2"
authored_duplicate_result="$output_dir/authored_duplicate_constant.result.mm2"
authored_occupied_program="$output_dir/authored_occupied_constant.mm2"
authored_occupied_result="$output_dir/authored_occupied_constant.result.mm2"
authored_duplicate_variable_program="$output_dir/authored_duplicate_variable.mm2"
authored_duplicate_variable_result="$output_dir/authored_duplicate_variable.result.mm2"
authored_active_variable_program="$output_dir/authored_active_variable.mm2"
authored_active_variable_result="$output_dir/authored_active_variable.result.mm2"
authored_floating_fresh_program="$output_dir/authored_floating_fresh.mm2"
authored_floating_fresh_result="$output_dir/authored_floating_fresh.result.mm2"
authored_floating_conflict_program="$output_dir/authored_floating_conflict.mm2"
authored_floating_conflict_result="$output_dir/authored_floating_conflict.result.mm2"
authored_nested_constant_program="$output_dir/authored_nested_constant.mm2"
authored_nested_constant_result="$output_dir/authored_nested_constant.result.mm2"
authored_scope_underflow_program="$output_dir/authored_scope_underflow.mm2"
authored_scope_underflow_result="$output_dir/authored_scope_underflow.result.mm2"
authored_essential_fresh_program="$output_dir/authored_essential_fresh.mm2"
authored_essential_fresh_result="$output_dir/authored_essential_fresh.result.mm2"
authored_essential_wrong_formula_program="$output_dir/authored_essential_wrong_formula.mm2"
authored_essential_wrong_formula_result="$output_dir/authored_essential_wrong_formula.result.mm2"
authored_essential_occupied_program="$output_dir/authored_essential_occupied.mm2"
authored_essential_occupied_result="$output_dir/authored_essential_occupied.result.mm2"

export_unit() {
  local source_path=$1
  local output_path=$2
  printf '%s\n' \
    'import Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit' \
    '#eval exportMetamathMM2RawUnitFromEnvironment' |
    env METTAPEDIA_MM2_RAW_SOURCE="$source_path" \
      METTAPEDIA_MM2_RAW_OUTPUT="$output_path" \
      lake env lean --stdin
}

export_unit_split() {
  local source_path=$1
  local verifier_output_path=$2
  local source_data_output_path=$3
  printf '%s\n' \
    'import Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit' \
    '#eval exportMetamathMM2RawUnitFromEnvironment' |
    env -u METTAPEDIA_MM2_RAW_OUTPUT \
      METTAPEDIA_MM2_RAW_SOURCE="$source_path" \
      METTAPEDIA_MM2_VERIFIER_OUTPUT="$verifier_output_path" \
      METTAPEDIA_MM2_SOURCE_DATA_OUTPUT="$source_data_output_path" \
      lake env lean --stdin
}

export_authored_declaration_control() {
  local mode=$1
  local output_path=$2
  printf '%s\n' \
    'import Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit' \
    '#eval exportAuthoredDeclarationControlFromEnvironment' |
    env METTAPEDIA_MM2_AUTHORED_DECLARATION_MODE="$mode" \
      METTAPEDIA_MM2_AUTHORED_DECLARATION_OUTPUT="$output_path" \
      lake env lean --stdin
}

assert_source_rejected() {
  local source_path=$1
  local status
  status=$(printf '%s\n' \
    'import Mettapedia.OSLF.Tools.ExportMetamathMM2RawUnit' \
    '#eval exportMetamathMM2RawUnitFromEnvironment' |
    env METTAPEDIA_MM2_RAW_SOURCE="$source_path" \
      METTAPEDIA_MM2_RAW_OUTPUT=/dev/null \
      lake env lean --stdin | tail -n 1)
  if [[ "$status" != 1 ]]; then
    echo "error: structurally malformed Metamath source was not rejected: $source_path" >&2
    exit 1
  fi
}

export_unit "$valid_source" "$valid_program"
export_unit "$invalid_source" "$invalid_program"
export_unit "$typecode_invalid_source" "$typecode_invalid_program"
export_unit "$essential_source" "$essential_program"
export_unit "$dv_source" "$dv_program"
export_unit "$dv_invalid_source" "$dv_invalid_program"
export_unit "$undefined_label_source" "$undefined_label_program"
export_unit_split "$valid_source" \
  "$valid_verifier_program" "$valid_source_data_program"
export_unit_split "$invalid_source" \
  "$invalid_verifier_program" "$invalid_source_data_program"
export_authored_declaration_control \
  constant-duplicate "$authored_duplicate_program"
export_authored_declaration_control \
  constant-occupied "$authored_occupied_program"
export_authored_declaration_control \
  variable-duplicate "$authored_duplicate_variable_program"
export_authored_declaration_control \
  variable-active "$authored_active_variable_program"
export_authored_declaration_control \
  floating-fresh "$authored_floating_fresh_program"
export_authored_declaration_control \
  floating-conflict "$authored_floating_conflict_program"
export_authored_declaration_control \
  constant-nested "$authored_nested_constant_program"
export_authored_declaration_control \
  scope-underflow "$authored_scope_underflow_program"
export_authored_declaration_control \
  essential-fresh "$authored_essential_fresh_program"
export_authored_declaration_control \
  essential-wrong-formula "$authored_essential_wrong_formula_program"
export_authored_declaration_control \
  essential-occupied "$authored_essential_occupied_program"
assert_source_rejected "$malformed_source"

cat "$valid_verifier_program" "$valid_source_data_program" > \
  "$valid_split_program"
cat "$invalid_verifier_program" "$invalid_source_data_program" > \
  "$invalid_split_program"
cmp "$valid_split_program" "$valid_program"
cmp "$invalid_split_program" "$invalid_program"
cmp "$valid_verifier_program" "$invalid_verifier_program"

cmp "$valid_program" "$checked_dir/test_stack_simple.mm2"
cmp "$invalid_program" \
  "$checked_dir/test26_wrong_conclusion_in_proof.mm2"
cmp "$typecode_invalid_program" \
  "$checked_dir/test22_typecode_mismatch_in_substitution.mm2"
cmp "$essential_program" "$checked_dir/test_stack_fhyps.mm2"
cmp "$dv_program" "$checked_dir/test_dv_yz_required.mm2"
cmp "$dv_invalid_program" \
  "$checked_dir/test27_disjoint_variable_constraint_violation.mm2"
cmp "$undefined_label_program" \
  "$checked_dir/test24_undefined_label_in_proof.mm2"

"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$valid_program" "$valid_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$invalid_program" "$invalid_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$typecode_invalid_program" "$typecode_invalid_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$essential_program" "$essential_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$dv_program" "$dv_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$dv_invalid_program" "$dv_invalid_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$undefined_label_program" "$undefined_label_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_duplicate_program" "$authored_duplicate_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_occupied_program" "$authored_occupied_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_duplicate_variable_program" "$authored_duplicate_variable_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_active_variable_program" "$authored_active_variable_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_floating_fresh_program" "$authored_floating_fresh_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_floating_conflict_program" "$authored_floating_conflict_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_nested_constant_program" "$authored_nested_constant_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_scope_underflow_program" "$authored_scope_underflow_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_essential_fresh_program" "$authored_essential_fresh_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_essential_wrong_formula_program" \
  "$authored_essential_wrong_formula_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$authored_essential_occupied_program" "$authored_essential_occupied_result"

count_tag() {
  local tag=$1
  local result_path=$2
  local count
  count=$(grep -c "^($tag " "$result_path" || true)
  echo "${count:-0}"
}

assert_count() {
  local expected=$1
  local tag=$2
  local result_path=$3
  local actual
  actual=$(count_tag "$tag" "$result_path")
  if [[ "$actual" != "$expected" ]]; then
    echo "error: expected $expected $tag rows in $result_path, found $actual" >&2
    exit 1
  fi
}

assert_pattern_count() {
  local expected=$1
  local pattern=$2
  local result_path=$3
  local actual
  actual=$(grep -Ec "$pattern" "$result_path" || true)
  if [[ "$actual" != "$expected" ]]; then
    echo "error: expected $expected rows matching $pattern in $result_path, found $actual" >&2
    exit 1
  fi
}

assert_no_formula_transaction_residue() {
  local result_path=$1
  for tag in \
      mm-source-essential-candidate \
      mm-internal-source-essential-request \
      mm-internal-source-essential-control \
      mm-source-keyed-object-lookup \
      mm-internal-source-formula-validation-request \
      mm-internal-source-formula-typecode-control \
      mm-internal-source-formula-typecode-validated \
      mm-internal-source-formula-body-control \
      mm-internal-source-formula-symbol-validated \
      mm-internal-source-formula-validation-complete \
      mm-internal-source-formula-validation-fault; do
    assert_count 0 "$tag" "$result_path"
  done
}

assert_no_assertion_transaction_residue() {
  local result_path=$1
  for tag in \
      mm-internal-source-assertion-frame-running \
      mm-internal-source-assertion-hypothesis-snapshot \
      mm-internal-source-assertion-distinct-snapshot \
      mm-internal-source-assertion-frame-snapshot \
      mm-internal-source-assertion-certificate-formula \
      mm-internal-source-assertion-certificate-hypotheses \
      mm-internal-source-assertion-certificate-essential \
      mm-internal-source-assertion-certificate-required \
      mm-internal-source-assertion-certificate-required-ticket \
      mm-internal-source-assertion-certificate-entries \
      mm-internal-source-assertion-certificate-coverage-ticket \
      mm-internal-source-assertion-certificate-duplicate-ticket \
      mm-internal-source-assertion-certificate-fault \
      mm-internal-source-assertion-certificate-valid \
      mm-internal-source-assertion-frame-select-hypotheses \
      mm-internal-source-assertion-frame-floating-ticket \
      mm-internal-source-assertion-frame-select-distinct \
      mm-internal-source-assertion-frame-distinct-left-ticket \
      mm-internal-source-assertion-frame-distinct-right-ticket \
      mm-internal-source-assertion-frame-valid \
      mm-internal-source-assertion-publication-running \
      mm-list-membership-request \
      mm-list-membership-found \
      mm-list-membership-missing \
      mm-internal-list-membership-return \
      mm-reload-list-membership \
      mm-reload-source-assertion-certificate \
      mm-reload-source-assertion-frame-selection \
      mm-reload-source-assertion-publication; do
    assert_count 0 "$tag" "$result_path"
  done
  if grep -Eq '^\((mm-assertion-(header|result|hypothesis|hypothesis-successor|dv-header|child)|mm-hypothesis-lookup) .*[$][A-Za-z]' \
      "$result_path"; then
    echo "error: unresolved variable escaped into assertion runtime data: $result_path" >&2
    exit 1
  fi
}

assert_successful_unit() {
  local result_path=$1
  local source_end=$2
  local ordinary_statements=$3
  local object_occurrences=$4
  local active_occurrences=$5
  assert_count 1 mm-source-theorem-admitted "$result_path"
  assert_count 0 mm-source-theorem-rejected "$result_path"
  assert_count 0 mm-accepted "$result_path"
  assert_count 0 mm-rejected "$result_path"
  assert_count 0 mm-proof-fault "$result_path"
  assert_count 0 mm-normal-control "$result_path"
  assert_count 0 mm-normal-label-lookup "$result_path"
  assert_count 0 mm-reload-normal-label-lookup "$result_path"
  assert_count 0 mm-source-current "$result_path"
  assert_count 0 mm-source-object-lookup "$result_path"
  assert_count 0 mm-source-object-missing "$result_path"
  assert_count 0 mm-source-object-found "$result_path"
  assert_count 0 mm-reload-source-object-lookup "$result_path"
  assert_no_formula_transaction_residue "$result_path"
  assert_no_assertion_transaction_residue "$result_path"
  assert_count 0 mm-source-variable-commit "$result_path"
  assert_count 0 mm-source-variable-stage-kind "$result_path"
  assert_count 0 mm-source-constant-commit "$result_path"
  assert_count 0 mm-source-constant-abort "$result_path"
  assert_pattern_count 0 '^\(mm-source-object-(link|frontier) \(mm-source-constant-transaction ' "$result_path"
  assert_count 0 mm-source-action-running "$result_path"
  assert_count 0 mm-source-action-plan "$result_path"
  assert_count 0 mm-source-statement-rejected "$result_path"
  assert_count 2 mm-assertion-header "$result_path"
  assert_count "$object_occurrences" mm-source-object-link "$result_path"
  assert_pattern_count "$active_occurrences" '^\(mm-source-object-link \(mm-source-active-variable-ledger ' "$result_path"
  assert_pattern_count "$active_occurrences" '^\(mm-source-object-link \(mm-source-variable-typecode-ledger ' "$result_path"
  assert_count "$active_occurrences" mm-source-variable-typecode-binding "$result_path"
  assert_count "$active_occurrences" mm-source-active-hypothesis-link "$result_path"
  assert_count 3 mm-source-object-frontier "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-frontier \(mm-source-active-variable-ledger ' "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-frontier \(mm-source-variable-typecode-ledger ' "$result_path"
  assert_count 0 mm-source-floating-request "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-found "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-missing "$result_path"
  assert_count 1 mm-source-end "$result_path"
  assert_count 1 mm-source-control "$result_path"
  assert_count "$ordinary_statements" mm-source-statement-applied "$result_path"
  assert_nat_tail mm-source-end "$source_end" "$result_path"
  assert_nat_tail mm-source-control "$source_end" "$result_path"
}

assert_nat_tail() {
  local tag=$1
  local expected=$2
  local result_path=$3
  if ! grep -Eq "^\\($tag .*\\(mm-nat $expected\\)\\)$" "$result_path"; then
    echo "error: expected $tag to end at position $expected in $result_path" >&2
    exit 1
  fi
}

assert_rejected_unit() {
  local result_path=$1
  local source_end=$2
  local ordinary_statements=$3
  local reason=$4
  local object_occurrences=$5
  local active_occurrences=$6
  assert_count 0 mm-source-theorem-admitted "$result_path"
  assert_count 1 mm-source-theorem-rejected "$result_path"
  assert_count 0 mm-accepted "$result_path"
  assert_count 0 mm-rejected "$result_path"
  assert_count 0 mm-proof-fault "$result_path"
  assert_count 0 mm-normal-control "$result_path"
  assert_count 0 mm-normal-label-lookup "$result_path"
  assert_count 0 mm-reload-normal-label-lookup "$result_path"
  assert_count 0 mm-source-current "$result_path"
  assert_count 0 mm-source-object-lookup "$result_path"
  assert_count 0 mm-source-object-missing "$result_path"
  assert_count 0 mm-source-object-found "$result_path"
  assert_count 0 mm-reload-source-object-lookup "$result_path"
  assert_no_formula_transaction_residue "$result_path"
  assert_no_assertion_transaction_residue "$result_path"
  assert_count 0 mm-source-variable-commit "$result_path"
  assert_count 0 mm-source-variable-stage-kind "$result_path"
  assert_count 0 mm-source-constant-commit "$result_path"
  assert_count 0 mm-source-constant-abort "$result_path"
  assert_pattern_count 0 '^\(mm-source-object-(link|frontier) \(mm-source-constant-transaction ' "$result_path"
  assert_count 0 mm-source-action-running "$result_path"
  assert_count 0 mm-source-action-plan "$result_path"
  assert_count 0 mm-source-statement-rejected "$result_path"
  assert_count 1 mm-assertion-header "$result_path"
  assert_count "$object_occurrences" mm-source-object-link "$result_path"
  assert_pattern_count "$active_occurrences" '^\(mm-source-object-link \(mm-source-active-variable-ledger ' "$result_path"
  assert_pattern_count "$active_occurrences" '^\(mm-source-object-link \(mm-source-variable-typecode-ledger ' "$result_path"
  assert_count "$active_occurrences" mm-source-variable-typecode-binding "$result_path"
  assert_count "$active_occurrences" mm-source-active-hypothesis-link "$result_path"
  assert_count 3 mm-source-object-frontier "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-frontier \(mm-source-active-variable-ledger ' "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-frontier \(mm-source-variable-typecode-ledger ' "$result_path"
  assert_count 0 mm-source-floating-request "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-found "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-missing "$result_path"
  assert_count 0 mm-source-theorem-pending "$result_path"
  assert_count 0 mm-source-theorem-proof-context "$result_path"
  assert_count 1 mm-source-end "$result_path"
  assert_count 0 mm-source-control "$result_path"
  assert_count "$ordinary_statements" mm-source-statement-applied "$result_path"
  assert_nat_tail mm-source-end "$source_end" "$result_path"
  if ! grep -Eq "^\\(mm-source-theorem-rejected .* $reason " "$result_path"; then
    echo "error: expected rejection reason $reason in $result_path" >&2
    exit 1
  fi
}

assert_authored_declaration_rejection() {
  local result_path=$1
  local reason=$2
  local permanent_links=$3
  local active_links=$4
  assert_count 1 mm-source-statement-rejected "$result_path"
  assert_count 0 mm-source-current "$result_path"
  assert_count 0 mm-source-object-lookup "$result_path"
  assert_count 0 mm-source-object-missing "$result_path"
  assert_count 0 mm-source-object-found "$result_path"
  assert_count 0 mm-reload-source-object-lookup "$result_path"
  assert_count 0 mm-source-constant-commit "$result_path"
  assert_count 0 mm-source-constant-abort "$result_path"
  assert_count 0 mm-source-variable-commit "$result_path"
  assert_count 0 mm-source-variable-abort "$result_path"
  assert_count 0 mm-source-variable-stage-kind "$result_path"
  assert_pattern_count 0 '^\(mm-source-object-(link|frontier) \(mm-source-constant-transaction ' "$result_path"
  assert_pattern_count 0 '^\(mm-source-object-(link|frontier) \(mm-source-variable-transaction ' "$result_path"
  assert_count "$permanent_links" mm-source-object-link "$result_path"
  assert_pattern_count "$active_links" '^\(mm-source-object-link \(mm-source-active-variable-ledger ' "$result_path"
  assert_pattern_count 0 '^\(mm-source-object-link \(mm-source-variable-typecode-ledger ' "$result_path"
  assert_count 0 mm-source-variable-typecode-binding "$result_path"
  assert_count 0 mm-source-active-hypothesis-link "$result_path"
  assert_count 3 mm-source-object-frontier "$result_path"
  assert_count 0 mm-source-floating-request "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-found "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-missing "$result_path"
  assert_count 0 mm-source-statement-applied "$result_path"
  if ! grep -Eq "^\\(mm-source-statement-rejected .* $reason " "$result_path"; then
    echo "error: expected authored declaration rejection reason $reason in $result_path" >&2
    exit 1
  fi
}

assert_authored_floating_fresh() {
  local result_path=$1
  assert_count 0 mm-source-current "$result_path"
  assert_count 1 mm-source-control "$result_path"
  assert_count 1 mm-source-statement-applied "$result_path"
  assert_count 0 mm-source-statement-rejected "$result_path"
  assert_count 5 mm-source-object-link "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-link \(mm-source-active-variable-ledger ' "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-link \(mm-source-variable-typecode-ledger ' "$result_path"
  assert_count 3 mm-source-object-frontier "$result_path"
  assert_count 1 mm-source-variable-typecode-binding "$result_path"
  assert_count 1 mm-hypothesis-lookup "$result_path"
  assert_count 1 mm-source-active-hypothesis-link "$result_path"
  assert_count 0 mm-source-floating-request "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-found "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-missing "$result_path"
}

assert_authored_floating_conflict() {
  local result_path=$1
  assert_count 0 mm-source-current "$result_path"
  assert_count 0 mm-source-control "$result_path"
  assert_count 0 mm-source-statement-applied "$result_path"
  assert_count 1 mm-source-statement-rejected "$result_path"
  assert_count 5 mm-source-object-link "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-link \(mm-source-active-variable-ledger ' "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-link \(mm-source-variable-typecode-ledger ' "$result_path"
  assert_count 3 mm-source-object-frontier "$result_path"
  assert_count 1 mm-source-variable-typecode-binding "$result_path"
  assert_count 0 mm-hypothesis-lookup "$result_path"
  assert_count 0 mm-source-active-hypothesis-link "$result_path"
  assert_count 0 mm-source-floating-request "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-found "$result_path"
  assert_count 0 mm-internal-source-variable-typecode-missing "$result_path"
  if ! grep -Eq '^\(mm-source-statement-rejected .* incompatible-floating-typecode ' "$result_path"; then
    echo "error: expected incompatible-floating-typecode in $result_path" >&2
    exit 1
  fi
}

assert_authored_essential_success() {
  local result_path=$1
  assert_count 0 mm-source-current "$result_path"
  assert_count 1 mm-source-control "$result_path"
  assert_count 1 mm-source-statement-applied "$result_path"
  assert_count 0 mm-source-statement-rejected "$result_path"
  assert_count 4 mm-source-object-link "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-link \(mm-source-active-variable-ledger ' "$result_path"
  assert_count 3 mm-source-object-frontier "$result_path"
  assert_count 1 mm-hypothesis-lookup "$result_path"
  assert_count 1 mm-source-active-hypothesis-link "$result_path"
  assert_no_formula_transaction_residue "$result_path"
}

assert_authored_essential_rejection() {
  local result_path=$1
  local reason=$2
  local object_links=$3
  assert_count 0 mm-source-current "$result_path"
  assert_count 0 mm-source-control "$result_path"
  assert_count 0 mm-source-statement-applied "$result_path"
  assert_count 1 mm-source-statement-rejected "$result_path"
  assert_count "$object_links" mm-source-object-link "$result_path"
  assert_pattern_count 1 '^\(mm-source-object-link \(mm-source-active-variable-ledger ' "$result_path"
  assert_count 3 mm-source-object-frontier "$result_path"
  assert_count 0 mm-hypothesis-lookup "$result_path"
  assert_count 0 mm-source-active-hypothesis-link "$result_path"
  assert_no_formula_transaction_residue "$result_path"
  if ! grep -Eq "^\\(mm-source-statement-rejected .* $reason " "$result_path"; then
    echo "error: expected authored essential rejection reason $reason in $result_path" >&2
    exit 1
  fi
}

assert_scoped_dv_unit() {
  local result_path=$1
  assert_count 0 mm-source-dv-occurrence-link "$result_path"
  assert_count 1 mm-source-dv-occurrence-frontier "$result_path"
  assert_count 0 mm-source-active-distinct-link "$result_path"
  assert_count 0 mm-caller-dv "$result_path"
  assert_pattern_count 1 '^\(mm-source-dv-occurrence-frontier .*\(mm-nat 0\)\)$' "$result_path"
  for tag in \
      mm-internal-source-dv-name-validation-request \
      mm-internal-source-dv-name-validation \
      mm-internal-source-dv-name-validated \
      mm-internal-source-dv-name-validation-complete \
      mm-internal-source-dv-name-validation-fault \
      mm-internal-source-dv-pair-validation-request \
      mm-internal-source-dv-pair-validation \
      mm-internal-source-dv-pair-derived \
      mm-internal-source-dv-pair-validated \
      mm-internal-source-dv-pair-validation-complete \
      mm-internal-source-dv-pair-validation-fault \
      mm-internal-source-dv-endpoint-request \
      mm-internal-source-dv-endpoint-status \
      mm-internal-source-dv-classification \
      mm-internal-source-dv-classification-complete \
      mm-internal-source-dv-cleanup \
      mm-internal-source-dv-commit-ready \
      mm-internal-source-dv-commit \
      mm-internal-source-dv-pair-authorized \
      mm-internal-source-dv-pair-committed \
      mm-source-dv-occurrence-lookup \
      mm-source-dv-occurrence-found \
      mm-source-dv-occurrence-missing \
      mm-reload-source-dv-declaration \
      mm-reload-source-dv-occurrence-lookup \
      mm-reload-source-dv-pair-commit; do
    assert_count 0 "$tag" "$result_path"
  done
}

assert_successful_unit "$valid_result" 8 8 10 2
assert_successful_unit "$essential_result" 15 15 20 3
assert_successful_unit "$dv_result" 15 15 16 3
assert_scoped_dv_unit "$dv_result"

assert_rejected_unit "$invalid_result" 6 5 wrong-conclusion 10 2
assert_rejected_unit "$typecode_invalid_result" 6 5 typecode-mismatch 11 2
assert_rejected_unit "$dv_invalid_result" 8 7 dv-same-variable 17 3
assert_rejected_unit "$undefined_label_result" 5 4 undefined-label 6 1

assert_authored_declaration_rejection \
  "$authored_duplicate_result" duplicate-constant-name 0 0
assert_authored_declaration_rejection \
  "$authored_occupied_result" occupied-object-name 1 0
assert_authored_declaration_rejection \
  "$authored_duplicate_variable_result" duplicate-variable-name 0 0
assert_authored_declaration_rejection \
  "$authored_active_variable_result" active-variable-name 2 1
assert_authored_floating_fresh "$authored_floating_fresh_result"
assert_authored_floating_conflict "$authored_floating_conflict_result"
assert_authored_declaration_rejection \
  "$authored_nested_constant_result" constant-not-top-level 0 0
assert_authored_declaration_rejection \
  "$authored_scope_underflow_result" scope-underflow 0 0
assert_authored_essential_success "$authored_essential_fresh_result"
assert_authored_essential_rejection \
  "$authored_essential_wrong_formula_result" invalid-essential-formula 3
assert_authored_essential_rejection \
  "$authored_essential_occupied_result" occupied-essential-label 4

python3 - "$metamath_test_root" "$valid_program" "$invalid_program" \
  "$typecode_invalid_program" \
  "$essential_program" "$dv_program" "$dv_invalid_program" \
  "$undefined_label_program" <<'PY'
import re
import sys
from pathlib import Path

host_path = sys.argv[1]
for artifact_name in sys.argv[2:]:
    text = Path(artifact_name).read_text(encoding="utf-8")
    cursor = 0
    while True:
        start = text.find("(mm-string ", cursor)
        if start < 0:
            break
        depth = 0
        end = start
        for end in range(start, len(text)):
            char = text[end]
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    end += 1
                    break
        encoded = text[start:end]
        values = [int(value) for value in re.findall(r"\(mm-nat ([0-9]+)\)", encoded)]
        decoded = bytes(value for value in values if value <= 255).decode(
            "utf-8", errors="replace")
        if host_path in decoded:
            raise SystemExit(
                f"error: host fixture path leaked into MM2 artifact: {artifact_name}")
        cursor = end
PY

echo "PASS: raw Metamath units and directly authored controls cover declarations, scopes, hypotheses, DV, malformed source, and proof rejection"
