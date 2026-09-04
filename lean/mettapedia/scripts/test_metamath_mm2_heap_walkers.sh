#!/usr/bin/env bash

set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 /path/to/mork" >&2
  exit 2
fi

mork_bin=$1
if [[ ! -x "$mork_bin" ]]; then
  echo "error: MORK executable is not executable: $mork_bin" >&2
  exit 2
fi

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
project_root=$(cd -- "$script_dir/.." && pwd)
fixture_dir="$project_root/artifacts/conformance/metamath_mm2_heap_walkers"
output_dir="$project_root/.lake/build/conformance/metamath_mm2_heap_walkers"
mkdir -p "$output_dir"

run_fixture() {
  local name=$1
  local input_path="$fixture_dir/$name.mm2"
  local result_path="$output_dir/$name.result.mm2"
  "$mork_bin" run --steps 32 --instrumentation 0 "$input_path" "$result_path"
}

assert_exact_line() {
  local expected=$1
  local result_path=$2
  if ! grep -Fxq -- "$expected" "$result_path"; then
    echo "error: expected row not found in $result_path: $expected" >&2
    exit 1
  fi
}

assert_absent_root() {
  local root=$1
  local result_path=$2
  if grep -Eq "^\\($root([ )])" "$result_path"; then
    echo "error: unexpected $root row in $result_path" >&2
    exit 1
  fi
}

for fixture in \
  direct_index_found \
  direct_index_wrong_owner \
  cursor_reserved_frontier_fault \
  fused_link_found \
  fused_link_wrong_owner \
  hybrid_direct_fallback \
  structural_fold_found \
  structural_fold_missing; do
  run_fixture "$fixture"
done

assert_exact_line \
  '(heap-result direct found heap-A 1 assertion ax-1)' \
  "$output_dir/direct_index_found.result.mm2"
assert_absent_root heap-result \
  "$output_dir/direct_index_wrong_owner.result.mm2"
assert_exact_line \
  '(direct-request heap-A 1)' \
  "$output_dir/direct_index_wrong_owner.result.mm2"

assert_exact_line \
  '(heap-result cursor missing heap-A 1 1)' \
  "$output_dir/cursor_reserved_frontier_fault.result.mm2"
assert_absent_root cursor-walk \
  "$output_dir/cursor_reserved_frontier_fault.result.mm2"

assert_exact_line \
  '(heap-result fused found heap-A 1 assertion ax-1)' \
  "$output_dir/fused_link_found.result.mm2"
assert_absent_root heap-result \
  "$output_dir/fused_link_wrong_owner.result.mm2"
assert_exact_line \
  '(fused-walk heap-A 1 0)' \
  "$output_dir/fused_link_wrong_owner.result.mm2"

assert_exact_line \
  '(heap-result hybrid found heap-A 1 assertion ax-1)' \
  "$output_dir/hybrid_direct_fallback.result.mm2"
assert_exact_line \
  '(heap-result hybrid missing heap-B 3 1)' \
  "$output_dir/hybrid_direct_fallback.result.mm2"
assert_absent_root hybrid-request \
  "$output_dir/hybrid_direct_fallback.result.mm2"
assert_absent_root hybrid-frontier-walk \
  "$output_dir/hybrid_direct_fallback.result.mm2"

assert_exact_line \
  '(heap-result fold found heap-A Z assertion ax-1)' \
  "$output_dir/structural_fold_found.result.mm2"
assert_exact_line \
  '(heap-result fold missing heap-A (S Z) E)' \
  "$output_dir/structural_fold_missing.result.mm2"
assert_absent_root fold-lookup \
  "$output_dir/structural_fold_found.result.mm2"
assert_absent_root fold-lookup \
  "$output_dir/structural_fold_missing.result.mm2"

echo "metamath MM2 heap-walker calibration: 8 fixtures green"
