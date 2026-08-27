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

for source_path in "$valid_source" "$invalid_source"; do
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

export_unit "$valid_source" "$valid_program"
export_unit "$invalid_source" "$invalid_program"

cmp "$valid_program" "$checked_dir/test_stack_simple.mm2"
cmp "$invalid_program" \
  "$checked_dir/test26_wrong_conclusion_in_proof.mm2"

"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$valid_program" "$valid_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$invalid_program" "$invalid_result"

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

assert_count 1 mm-source-theorem-admitted "$valid_result"
assert_count 0 mm-source-theorem-rejected "$valid_result"
assert_count 0 mm-accepted "$valid_result"
assert_count 0 mm-rejected "$valid_result"
assert_count 0 mm-normal-control "$valid_result"
assert_count 0 mm-source-current "$valid_result"
assert_count 0 mm-source-action-running "$valid_result"

assert_count 0 mm-source-theorem-admitted "$invalid_result"
assert_count 1 mm-source-theorem-rejected "$invalid_result"
assert_count 0 mm-accepted "$invalid_result"
assert_count 0 mm-rejected "$invalid_result"
assert_count 0 mm-normal-control "$invalid_result"
assert_count 0 mm-source-current "$invalid_result"
assert_count 0 mm-source-action-running "$invalid_result"

if grep -Fq "$metamath_test_root" "$valid_program" "$invalid_program"; then
  echo "error: a host fixture path leaked into the MM2 artifact" >&2
  exit 1
fi

echo "PASS: raw Metamath unit fixtures distinguish admission from rejection in MORK"
