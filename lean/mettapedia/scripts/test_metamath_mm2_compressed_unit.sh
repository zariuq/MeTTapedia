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

valid_source="$metamath_test_root/tests/unit/test38_whitespace_in_valid_compressed.mm"
saved_heap_source="$metamath_test_root/tests/unit/test57_compressed_z_minimal.mm"
save_interrupt_source="$metamath_test_root/tests/unit/test98_compressed_save_interrupts_index_bad.mm"
repeated_save_source="$metamath_test_root/tests/unit/test99_compressed_repeated_save_alias_bad.mm"
underflow_source="$metamath_test_root/tests/unit/test33_compressed_proof_stack_underflow.mm"
duplicate_header_source="$metamath_test_root/tests/unit/test100_compressed_header_explicit_mandatory_hyp_bad.mm"
assertion_fhyp_source="$metamath_test_root/tests/unit/test65_compressed_assertion_fhyp_order.mm"
mandatory_order_source="$metamath_test_root/tests/unit/test66_compressed_mand_hyp_order.mm"
mixed_ehyp_z_source="$metamath_test_root/tests/unit/test58_compressed_ehyp_z.mm"
multibyte_index_source="$metamath_test_root/tests/unit/test101_compressed_multibyte_index.mm"
incomplete_index_source="$metamath_test_root/tests/unit/test102_compressed_incomplete_index.mm"
out_of_range_index_source="$metamath_test_root/tests/unit/test103_compressed_multibyte_index_out_of_range.mm"
nested_prefix_fault_source="$metamath_test_root/tests/unit/test104_compressed_three_byte_index.mm"

for source_path in "$valid_source" "$saved_heap_source" "$save_interrupt_source" "$repeated_save_source" "$underflow_source" "$duplicate_header_source" "$assertion_fhyp_source" "$mandatory_order_source" "$mixed_ehyp_z_source" "$multibyte_index_source" "$incomplete_index_source" "$out_of_range_index_source" "$nested_prefix_fault_source"; do
  if [[ ! -f "$source_path" ]]; then
    echo "error: missing metamath-test unit fixture: $source_path" >&2
    exit 2
  fi
done

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
project_root=$(cd -- "$script_dir/.." && pwd)
output_dir="$project_root/.lake/build/conformance/metamath_mm2_compressed_unit"
mkdir -p "$output_dir"
cd "$project_root"

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

count_root() {
  local tag=$1
  local result_path=$2
  awk -v prefix="($tag " 'index($0, prefix) == 1 { count += 1 }
    END { print count + 0 }' "$result_path"
}

assert_count() {
  local expected=$1
  local tag=$2
  local result_path=$3
  local actual
  actual=$(count_root "$tag" "$result_path")
  if [[ "$actual" != "$expected" ]]; then
    echo "error: expected $expected $tag roots in $result_path, found $actual" >&2
    exit 1
  fi
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

valid_program="$output_dir/test38_whitespace_in_valid_compressed.mm2"
valid_result="$output_dir/test38_whitespace_in_valid_compressed.result.mm2"
saved_heap_program="$output_dir/test57_compressed_z_minimal.mm2"
saved_heap_result="$output_dir/test57_compressed_z_minimal.result.mm2"
save_interrupt_program="$output_dir/test98_compressed_save_interrupts_index_bad.mm2"
save_interrupt_result="$output_dir/test98_compressed_save_interrupts_index_bad.result.mm2"
repeated_save_program="$output_dir/test99_compressed_repeated_save_alias_bad.mm2"
repeated_save_result="$output_dir/test99_compressed_repeated_save_alias_bad.result.mm2"
underflow_program="$output_dir/test33_compressed_proof_stack_underflow.mm2"
underflow_result="$output_dir/test33_compressed_proof_stack_underflow.result.mm2"
duplicate_header_program="$output_dir/test100_compressed_header_explicit_mandatory_hyp_bad.mm2"
duplicate_header_result="$output_dir/test100_compressed_header_explicit_mandatory_hyp_bad.result.mm2"
assertion_fhyp_program="$output_dir/test65_compressed_assertion_fhyp_order.mm2"
assertion_fhyp_result="$output_dir/test65_compressed_assertion_fhyp_order.result.mm2"
mandatory_order_program="$output_dir/test66_compressed_mand_hyp_order.mm2"
mandatory_order_result="$output_dir/test66_compressed_mand_hyp_order.result.mm2"
mixed_ehyp_z_program="$output_dir/test58_compressed_ehyp_z.mm2"
mixed_ehyp_z_result="$output_dir/test58_compressed_ehyp_z.result.mm2"
multibyte_index_program="$output_dir/test101_compressed_multibyte_index.mm2"
multibyte_index_result="$output_dir/test101_compressed_multibyte_index.result.mm2"
incomplete_index_program="$output_dir/test102_compressed_incomplete_index.mm2"
incomplete_index_result="$output_dir/test102_compressed_incomplete_index.result.mm2"
out_of_range_index_program="$output_dir/test103_compressed_multibyte_index_out_of_range.mm2"
out_of_range_index_result="$output_dir/test103_compressed_multibyte_index_out_of_range.result.mm2"
nested_prefix_fault_program="$output_dir/test104_compressed_three_byte_index.mm2"
nested_prefix_fault_result="$output_dir/test104_compressed_three_byte_index.result.mm2"

export_unit "$valid_source" "$valid_program"
export_unit "$saved_heap_source" "$saved_heap_program"
export_unit "$save_interrupt_source" "$save_interrupt_program"
export_unit "$repeated_save_source" "$repeated_save_program"
export_unit "$underflow_source" "$underflow_program"
export_unit "$duplicate_header_source" "$duplicate_header_program"
export_unit "$assertion_fhyp_source" "$assertion_fhyp_program"
export_unit "$mandatory_order_source" "$mandatory_order_program"
export_unit "$mixed_ehyp_z_source" "$mixed_ehyp_z_program"
export_unit "$multibyte_index_source" "$multibyte_index_program"
export_unit "$incomplete_index_source" "$incomplete_index_program"
export_unit "$out_of_range_index_source" "$out_of_range_index_program"
export_unit "$nested_prefix_fault_source" "$nested_prefix_fault_program"

"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$valid_program" "$valid_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$saved_heap_program" "$saved_heap_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$save_interrupt_program" "$save_interrupt_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$repeated_save_program" "$repeated_save_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$underflow_program" "$underflow_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$duplicate_header_program" "$duplicate_header_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$assertion_fhyp_program" "$assertion_fhyp_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$mandatory_order_program" "$mandatory_order_result"
"$mork_bin" run --steps 20000 --instrumentation 0 \
  "$mixed_ehyp_z_program" "$mixed_ehyp_z_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$multibyte_index_program" "$multibyte_index_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$incomplete_index_program" "$incomplete_index_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$out_of_range_index_program" "$out_of_range_index_result"
"$mork_bin" run --steps 10000 --instrumentation 0 \
  "$nested_prefix_fault_program" "$nested_prefix_fault_result"

# Completed compact proof: the raw MM2 observation is consumed by the
# owner-bound continuation and leaves only the authoritative source outcome.
assert_count 1 mm-source-theorem-admitted "$valid_result"
assert_count 0 mm-source-theorem-rejected "$valid_result"
assert_count 0 mm-proof-fault "$valid_result"
assert_count 0 mm-accepted "$valid_result"
assert_count 0 mm-rejected "$valid_result"
assert_count 0 mm-source-theorem-pending "$valid_result"
assert_count 0 mm-source-theorem-proof-context "$valid_result"
assert_count 0 mm-source-action-running "$valid_result"
assert_count 0 mm-source-action-plan "$valid_result"
assert_count 1 mm-source-control "$valid_result"
assert_count 1 mm-source-end "$valid_result"
assert_count 5 mm-source-statement-applied "$valid_result"
assert_nat_tail mm-source-control 5 "$valid_result"
assert_nat_tail mm-source-end 5 "$valid_result"

# The compact `Z` marker saves the current proof occurrence, and the following
# compact index recalls it.  Both operations happen in the emitted verifier:
# no translator-time expansion is permitted, and the consumed heap cell leaves
# no residual compact control or heap entry at the source outcome boundary.
assert_count 1 mm-source-theorem-admitted "$saved_heap_result"
assert_count 0 mm-source-theorem-rejected "$saved_heap_result"
assert_count 0 mm-proof-fault "$saved_heap_result"
assert_count 0 mm-accepted "$saved_heap_result"
assert_count 0 mm-rejected "$saved_heap_result"
assert_count 0 mm-source-theorem-pending "$saved_heap_result"
assert_count 0 mm-source-theorem-proof-context "$saved_heap_result"
assert_count 0 mm-source-action-running "$saved_heap_result"
assert_count 0 mm-source-action-plan "$saved_heap_result"
assert_count 0 mm-normal-control "$saved_heap_result"
assert_count 0 mm-compressed-control "$saved_heap_result"
assert_count 0 mm-compressed-heap-cell "$saved_heap_result"
assert_count 1 mm-source-control "$saved_heap_result"
assert_count 1 mm-source-end "$saved_heap_result"
assert_count 6 mm-source-statement-applied "$saved_heap_result"
assert_nat_tail mm-source-control 6 "$saved_heap_result"
assert_nat_tail mm-source-end 6 "$saved_heap_result"

# A save marker cannot interrupt an unfinished compact index, and a second
# save cannot alias the existing saved occurrence.  The distinct phase markers
# below ensure these are two verifier-side heap-state decisions, not one
# generic malformed-token branch.
for result_path in "$save_interrupt_result" "$repeated_save_result"; do
  assert_count 0 mm-source-theorem-admitted "$result_path"
  assert_count 1 mm-source-theorem-rejected "$result_path"
  assert_count 0 mm-proof-fault "$result_path"
  assert_count 0 mm-accepted "$result_path"
  assert_count 0 mm-rejected "$result_path"
  assert_count 0 mm-source-theorem-pending "$result_path"
  assert_count 0 mm-source-theorem-proof-context "$result_path"
  assert_count 0 mm-source-action-running "$result_path"
  assert_count 0 mm-source-action-plan "$result_path"
  assert_count 0 mm-source-control "$result_path"
  assert_count 1 mm-source-end "$result_path"
  assert_count 7 mm-source-statement-applied "$result_path"
  assert_nat_tail mm-source-end 8 "$result_path"
done
if ! awk 'index($0, "(mm-source-theorem-rejected ") == 1 &&
    index($0, " compressed-save-placement ") > 0 &&
    index($0, " mm-compressed-open-index ") > 0 { found = 1 }
  END { exit !found }' "$save_interrupt_result"; then
  echo "error: save-interrupt rejection lost its compact index phase" >&2
  exit 1
fi
if ! awk 'index($0, "(mm-source-theorem-rejected ") == 1 &&
    index($0, " compressed-save-placement ") > 0 &&
    index($0, " mm-compressed-between-steps ") > 0 { found = 1 }
  END { exit !found }' "$repeated_save_result"; then
  echo "error: repeated-save rejection lost its heap phase" >&2
  exit 1
fi

# Heap underflow: the compact verifier emits a real fault, then the captured
# source continuation consumes it and rejects exactly the pending theorem.
assert_count 0 mm-source-theorem-admitted "$underflow_result"
assert_count 1 mm-source-theorem-rejected "$underflow_result"
assert_count 0 mm-proof-fault "$underflow_result"
assert_count 0 mm-accepted "$underflow_result"
assert_count 0 mm-rejected "$underflow_result"
assert_count 0 mm-source-theorem-pending "$underflow_result"
assert_count 0 mm-source-theorem-proof-context "$underflow_result"
assert_count 0 mm-source-action-running "$underflow_result"
# Rejection consumes the exact deferred after-proof plan together with the
# owner-bound theorem context, so no latent authorization row remains.
assert_count 0 mm-source-action-plan "$underflow_result"
assert_count 0 mm-source-control "$underflow_result"
assert_count 1 mm-source-end "$underflow_result"
assert_count 4 mm-source-statement-applied "$underflow_result"
assert_nat_tail mm-source-end 5 "$underflow_result"
if ! awk 'index($0, "(mm-source-theorem-rejected ") == 1 &&
    index($0, " compressed-missing-heap-reference ") > 0 { found = 1 }
  END { exit !found }' "$underflow_result"; then
  echo "error: heap-underflow source rejection lost its compact fault reason" >&2
  exit 1
fi

# The parenthesized compact header must not repeat an implicit mandatory
# hypothesis.  The header fault is consumed by the owner-bound source
# continuation, so no raw proof fault remains observable at the boundary.
assert_count 0 mm-source-theorem-admitted "$duplicate_header_result"
assert_count 1 mm-source-theorem-rejected "$duplicate_header_result"
assert_count 0 mm-proof-fault "$duplicate_header_result"
assert_count 0 mm-accepted "$duplicate_header_result"
assert_count 0 mm-rejected "$duplicate_header_result"
assert_count 0 mm-source-theorem-pending "$duplicate_header_result"
assert_count 0 mm-source-theorem-proof-context "$duplicate_header_result"
assert_count 0 mm-source-action-running "$duplicate_header_result"
assert_count 0 mm-source-action-plan "$duplicate_header_result"
assert_count 0 mm-source-control "$duplicate_header_result"
assert_count 1 mm-source-end "$duplicate_header_result"
assert_count 4 mm-source-statement-applied "$duplicate_header_result"
assert_nat_tail mm-source-end 5 "$duplicate_header_result"
if ! awk 'index($0, "(mm-source-theorem-rejected ") == 1 &&
    index($0, " compressed-duplicate-mandatory-label ") > 0 { found = 1 }
  END { exit !found }' "$duplicate_header_result"; then
  echo "error: duplicate compact-header rejection lost its fault reason" >&2
  exit 1
fi

# The 13-statement assertion fixture crosses the compact-to-normal handoff,
# applies three floating and two essential hypotheses, then closes its source
# scope.  It therefore detects a one-shot source reloader left behind after a
# long proof run rather than merely a compact-header failure.
assert_count 1 mm-source-theorem-admitted "$assertion_fhyp_result"
assert_count 0 mm-source-theorem-rejected "$assertion_fhyp_result"
assert_count 0 mm-proof-fault "$assertion_fhyp_result"
assert_count 0 mm-accepted "$assertion_fhyp_result"
assert_count 0 mm-rejected "$assertion_fhyp_result"
assert_count 0 mm-source-theorem-pending "$assertion_fhyp_result"
assert_count 0 mm-source-theorem-proof-context "$assertion_fhyp_result"
assert_count 0 mm-source-action-running "$assertion_fhyp_result"
assert_count 0 mm-source-action-plan "$assertion_fhyp_result"
assert_count 0 mm-normal-control "$assertion_fhyp_result"
assert_count 0 mm-compressed-control "$assertion_fhyp_result"
assert_count 1 mm-source-control "$assertion_fhyp_result"
assert_count 1 mm-source-end "$assertion_fhyp_result"
assert_count 13 mm-source-statement-applied "$assertion_fhyp_result"
assert_nat_tail mm-source-control 13 "$assertion_fhyp_result"
assert_nat_tail mm-source-end 13 "$assertion_fhyp_result"

# This second normal-handoff fixture changes the mandatory-hypothesis layout:
# two floating hypotheses followed by two essential hypotheses.  It prevents a
# stack order accident in the richer three-floating fixture from masquerading
# as general compressed assertion support.
assert_count 1 mm-source-theorem-admitted "$mandatory_order_result"
assert_count 0 mm-source-theorem-rejected "$mandatory_order_result"
assert_count 0 mm-proof-fault "$mandatory_order_result"
assert_count 0 mm-accepted "$mandatory_order_result"
assert_count 0 mm-rejected "$mandatory_order_result"
assert_count 0 mm-source-theorem-pending "$mandatory_order_result"
assert_count 0 mm-source-theorem-proof-context "$mandatory_order_result"
assert_count 0 mm-source-action-running "$mandatory_order_result"
assert_count 0 mm-source-action-plan "$mandatory_order_result"
assert_count 0 mm-normal-control "$mandatory_order_result"
assert_count 0 mm-compressed-control "$mandatory_order_result"
assert_count 1 mm-source-control "$mandatory_order_result"
assert_count 1 mm-source-end "$mandatory_order_result"
assert_count 14 mm-source-statement-applied "$mandatory_order_result"
assert_nat_tail mm-source-control 14 "$mandatory_order_result"
assert_nat_tail mm-source-end 14 "$mandatory_order_result"

# This mixed 20-statement unit admits a normal theorem before a compact proof
# with essential hypotheses and a verifier-side `Z` save/recall.  It ensures
# the single source-independent verifier keeps the ordinary source loop live
# across both proof modes rather than only across an all-compact input.  Each
# mode-specific reload request must also be completely consumed.
assert_count 2 mm-source-theorem-admitted "$mixed_ehyp_z_result"
assert_count 0 mm-source-theorem-rejected "$mixed_ehyp_z_result"
assert_count 0 mm-proof-fault "$mixed_ehyp_z_result"
assert_count 0 mm-accepted "$mixed_ehyp_z_result"
assert_count 0 mm-rejected "$mixed_ehyp_z_result"
assert_count 0 mm-source-theorem-pending "$mixed_ehyp_z_result"
assert_count 0 mm-source-theorem-proof-context "$mixed_ehyp_z_result"
assert_count 0 mm-source-theorem-admission-pending "$mixed_ehyp_z_result"
assert_count 0 mm-source-action-running "$mixed_ehyp_z_result"
assert_count 0 mm-source-action-plan "$mixed_ehyp_z_result"
assert_count 0 mm-normal-control "$mixed_ehyp_z_result"
assert_count 0 mm-compressed-control "$mixed_ehyp_z_result"
assert_count 0 mm-compressed-heap-cell "$mixed_ehyp_z_result"
assert_count 0 mm-reload-normal-dispatch "$mixed_ehyp_z_result"
assert_count 0 mm-reload-compressed-normal-rearm "$mixed_ehyp_z_result"
assert_count 0 mm-compressed-normal-handoff-loading "$mixed_ehyp_z_result"
assert_count 1 mm-source-control "$mixed_ehyp_z_result"
assert_count 1 mm-source-end "$mixed_ehyp_z_result"
assert_count 20 mm-source-statement-applied "$mixed_ehyp_z_result"
assert_nat_tail mm-source-control 20 "$mixed_ehyp_z_result"
assert_nat_tail mm-source-end 20 "$mixed_ehyp_z_result"

# The compact scanner must retain a U--Y prefix in verifier state and combine
# it with the following terminal byte.  `UA` denotes index twenty here, so
# this unit detects any translator-side expansion or one-byte-only scanner.
assert_count 1 mm-source-theorem-admitted "$multibyte_index_result"
assert_count 0 mm-source-theorem-rejected "$multibyte_index_result"
assert_count 0 mm-proof-fault "$multibyte_index_result"
assert_count 0 mm-accepted "$multibyte_index_result"
assert_count 0 mm-rejected "$multibyte_index_result"
assert_count 0 mm-source-theorem-pending "$multibyte_index_result"
assert_count 0 mm-source-theorem-proof-context "$multibyte_index_result"
assert_count 0 mm-source-action-running "$multibyte_index_result"
assert_count 0 mm-source-action-plan "$multibyte_index_result"
assert_count 0 mm-normal-control "$multibyte_index_result"
assert_count 0 mm-compressed-control "$multibyte_index_result"
assert_count 0 mm-compressed-heap-cell "$multibyte_index_result"
assert_count 1 mm-source-control "$multibyte_index_result"
assert_count 1 mm-source-end "$multibyte_index_result"
assert_count 23 mm-source-statement-applied "$multibyte_index_result"
assert_nat_tail mm-source-control 23 "$multibyte_index_result"
assert_nat_tail mm-source-end 23 "$multibyte_index_result"

# The raw source keeps a legal prefix byte as compact proof data.  The MM2
# verifier detects end-of-input while the compact index is open and reports
# the exact source-bound incomplete-index rejection.
assert_count 0 mm-source-theorem-admitted "$incomplete_index_result"
assert_count 1 mm-source-theorem-rejected "$incomplete_index_result"
assert_count 0 mm-proof-fault "$incomplete_index_result"
assert_count 0 mm-accepted "$incomplete_index_result"
assert_count 0 mm-rejected "$incomplete_index_result"
assert_count 0 mm-source-theorem-pending "$incomplete_index_result"
assert_count 0 mm-source-theorem-proof-context "$incomplete_index_result"
assert_count 0 mm-source-action-running "$incomplete_index_result"
assert_count 0 mm-source-action-plan "$incomplete_index_result"
assert_count 0 mm-normal-control "$incomplete_index_result"
assert_count 0 mm-compressed-control "$incomplete_index_result"
assert_count 0 mm-compressed-heap-cell "$incomplete_index_result"
assert_count 0 mm-source-control "$incomplete_index_result"
assert_count 1 mm-source-end "$incomplete_index_result"
assert_count 4 mm-source-statement-applied "$incomplete_index_result"
assert_nat_tail mm-source-end 5 "$incomplete_index_result"
if ! awk 'index($0, "(mm-source-theorem-rejected ") == 1 &&
    index($0, " compressed-incomplete-index ") > 0 { found = 1 }
  END { exit !found }' "$incomplete_index_result"; then
  echo "error: incomplete compact index lost its verifier-side rejection reason" >&2
  exit 1
fi

# `UB` computes index twenty-one while the explicit header ends at index
# twenty. The verifier must reach the exact heap frontier and reject, rather
# than accepting a nearby header occurrence or silently stalling.
assert_count 0 mm-source-theorem-admitted "$out_of_range_index_result"
assert_count 1 mm-source-theorem-rejected "$out_of_range_index_result"
assert_count 0 mm-proof-fault "$out_of_range_index_result"
assert_count 0 mm-accepted "$out_of_range_index_result"
assert_count 0 mm-rejected "$out_of_range_index_result"
assert_count 0 mm-source-theorem-pending "$out_of_range_index_result"
assert_count 0 mm-source-theorem-proof-context "$out_of_range_index_result"
assert_count 0 mm-source-action-running "$out_of_range_index_result"
assert_count 0 mm-source-action-plan "$out_of_range_index_result"
assert_count 0 mm-normal-control "$out_of_range_index_result"
assert_count 0 mm-compressed-control "$out_of_range_index_result"
assert_count 0 mm-compressed-heap-cell "$out_of_range_index_result"
assert_count 0 mm-source-control "$out_of_range_index_result"
assert_count 1 mm-source-end "$out_of_range_index_result"
assert_count 22 mm-source-statement-applied "$out_of_range_index_result"
assert_nat_tail mm-source-end 23 "$out_of_range_index_result"
if ! awk 'index($0, "(mm-source-theorem-rejected ") == 1 &&
    index($0, " compressed-missing-heap-reference ") > 0 { found = 1 }
  END { exit !found }' "$out_of_range_index_result"; then
  echo "error: out-of-range compact index lost its verifier-side rejection reason" >&2
  exit 1
fi

# The nested `UU` prefix remains open through its second byte. A following
# `?` therefore faults inside the open compact index rather than taking the
# ordinary unknown-step branch.
assert_count 0 mm-source-theorem-admitted "$nested_prefix_fault_result"
assert_count 1 mm-source-theorem-rejected "$nested_prefix_fault_result"
assert_count 0 mm-proof-fault "$nested_prefix_fault_result"
assert_count 0 mm-accepted "$nested_prefix_fault_result"
assert_count 0 mm-rejected "$nested_prefix_fault_result"
assert_count 0 mm-source-theorem-pending "$nested_prefix_fault_result"
assert_count 0 mm-source-theorem-proof-context "$nested_prefix_fault_result"
assert_count 0 mm-source-action-running "$nested_prefix_fault_result"
assert_count 0 mm-source-action-plan "$nested_prefix_fault_result"
assert_count 0 mm-normal-control "$nested_prefix_fault_result"
assert_count 0 mm-compressed-control "$nested_prefix_fault_result"
assert_count 0 mm-compressed-heap-cell "$nested_prefix_fault_result"
assert_count 0 mm-source-control "$nested_prefix_fault_result"
assert_count 1 mm-source-end "$nested_prefix_fault_result"
assert_count 4 mm-source-statement-applied "$nested_prefix_fault_result"
assert_nat_tail mm-source-end 5 "$nested_prefix_fault_result"
if ! awk 'index($0, "(mm-source-theorem-rejected ") == 1 &&
    index($0, " compressed-question-in-open-index ") > 0 { found = 1 }
  END { exit !found }' "$nested_prefix_fault_result"; then
  echo "error: nested compact prefix lost its verifier-side question fault" >&2
  exit 1
fi

echo "PASS: raw compressed Metamath units admit compact, multi-byte, heap-save, mixed normal/compact, and normal-handoff proofs, and reject heap, save, header, incomplete-index, out-of-range-index, and nested-prefix faults"
