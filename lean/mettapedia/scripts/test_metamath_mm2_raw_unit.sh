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
assert_source_rejected "$malformed_source"

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

"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$valid_program" "$valid_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$invalid_program" "$invalid_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$typecode_invalid_program" "$typecode_invalid_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$essential_program" "$essential_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$dv_program" "$dv_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$dv_invalid_program" "$dv_invalid_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$undefined_label_program" "$undefined_label_result"

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

assert_successful_unit() {
  local result_path=$1
  local source_end=$2
  local ordinary_statements=$3
  assert_count 1 mm-source-theorem-admitted "$result_path"
  assert_count 0 mm-source-theorem-rejected "$result_path"
  assert_count 0 mm-accepted "$result_path"
  assert_count 0 mm-rejected "$result_path"
  assert_count 0 mm-proof-fault "$result_path"
  assert_count 0 mm-normal-control "$result_path"
  assert_count 0 mm-normal-label-lookup "$result_path"
  assert_count 0 mm-reload-normal-label-lookup "$result_path"
  assert_count 0 mm-source-current "$result_path"
  assert_count 0 mm-source-action-running "$result_path"
  assert_count 0 mm-source-action-plan "$result_path"
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
  assert_count 0 mm-source-theorem-admitted "$result_path"
  assert_count 1 mm-source-theorem-rejected "$result_path"
  assert_count 0 mm-accepted "$result_path"
  assert_count 0 mm-rejected "$result_path"
  assert_count 0 mm-proof-fault "$result_path"
  assert_count 0 mm-normal-control "$result_path"
  assert_count 0 mm-normal-label-lookup "$result_path"
  assert_count 0 mm-reload-normal-label-lookup "$result_path"
  assert_count 0 mm-source-current "$result_path"
  assert_count 0 mm-source-action-running "$result_path"
  assert_count 0 mm-source-action-plan "$result_path"
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

assert_successful_unit "$valid_result" 8 8
assert_successful_unit "$essential_result" 15 15
assert_successful_unit "$dv_result" 15 15

assert_rejected_unit "$invalid_result" 6 5 wrong-conclusion
assert_rejected_unit "$typecode_invalid_result" 6 5 typecode-mismatch
assert_rejected_unit "$dv_invalid_result" 8 7 dv-same-variable
assert_rejected_unit "$undefined_label_result" 5 4 undefined-label

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

echo "PASS: raw Metamath units cover hypotheses, DV success, malformed source, and four proof-rejection classes"
