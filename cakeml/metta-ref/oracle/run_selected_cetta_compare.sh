#!/usr/bin/env bash
set -euo pipefail

POLY=${POLY:-/home/zar/claude/CakeML/polyml-local/bin/poly}
CETTA=${CETTA:-/home/zar/claude/hyperon/CeTTa/cetta}
CETTA_TEST_DIR=${CETTA_TEST_DIR:-/home/zar/claude/hyperon/CeTTa/tests}
LOCAL_TEST_DIR=${LOCAL_TEST_DIR:-tests/cetta_selected}
CML_RUNNER=${CML_RUNNER:-./cml/metta_m1_runner.cake}
NORMALIZER=${NORMALIZER:-oracle/normalize_metta_output.py}

if [[ ! -x "$CETTA" ]]; then
  echo "missing executable: $CETTA" >&2
  exit 1
fi

if [[ ! -x "$CML_RUNNER" ]]; then
  echo "missing executable: $CML_RUNNER" >&2
  exit 1
fi

if [[ ! -f "$NORMALIZER" ]]; then
  echo "missing normalizer: $NORMALIZER" >&2
  exit 1
fi

exact_tests=(
  io_he_simple_rewrite.metta
  io_he_pattern_variable_substitution.metta
  io_he_unknown_expr_preserved.metta
  io_he_nested_rewrite.metta
  io_he_ext_if_true.metta
  io_he_ext_if_false.metta
  io_he_ext_collapse_superpose_duplicates.metta
  test_basic_eval.metta
)

normalized_bag_tests=(
  io_he_duplicate_multiplicity_preserved.metta
  io_he_nondet_choose_bag.metta
  nondet_match_bag.metta
  nondet_chain_bag.metta
  nondet_cross_product_bag.metta
  nondet_superpose_eval_bag.metta
  nondet_eval_arg_add_bag.metta
  nondet_if_condition_bag.metta
  nondet_let_value_bag.metta
  nondet_match_eval_template_bag.metta
  nondet_collapse_bag.metta
  nondet_superpose_three_bag.metta
)

failures=0

resolve_test_file() {
  local name=$1

  if [[ "$name" = /* && -f "$name" ]]; then
    printf '%s\n' "$name"
    return 0
  fi
  if [[ -f "$CETTA_TEST_DIR/$name" ]]; then
    printf '%s\n' "$CETTA_TEST_DIR/$name"
    return 0
  fi
  if [[ -f "$LOCAL_TEST_DIR/$name" ]]; then
    printf '%s\n' "$LOCAL_TEST_DIR/$name"
    return 0
  fi

  return 1
}

compare_to_cetta() {
  local label=$1
  local test_file=$2
  shift 2

  if diff -u <("$CETTA" --lang he "$test_file") <("$@") >/dev/null; then
    echo "PASS $label $(basename "$test_file")"
  else
    echo "FAIL $label $(basename "$test_file")" >&2
    diff -u <("$CETTA" --lang he "$test_file") <("$@") || true
    failures=$((failures + 1))
  fi
}

compare_to_cetta_normalized_bag() {
  local label=$1
  local test_file=$2
  shift 2

  if diff -u \
      <("$CETTA" --lang he "$test_file" | "$NORMALIZER" --bag) \
      <("$@" | "$NORMALIZER" --bag) >/dev/null; then
    echo "PASS $label $(basename "$test_file")"
  else
    echo "FAIL $label $(basename "$test_file")" >&2
    diff -u \
      <("$CETTA" --lang he "$test_file" | "$NORMALIZER" --bag) \
      <("$@" | "$NORMALIZER" --bag) || true
    failures=$((failures + 1))
  fi
}

for name in "${exact_tests[@]}"; do
  if ! test_file=$(resolve_test_file "$name"); then
    echo "FAIL $name: missing CeTTa test file" >&2
    failures=$((failures + 1))
    continue
  fi

  compare_to_cetta "sml-vs-cetta" "$test_file" \
    env METTA_FILE="$test_file" "$POLY" --script tests/run_metta_file.sml
  compare_to_cetta "cml-vs-cetta" "$test_file" \
    "$CML_RUNNER" "$test_file"
done

for name in "${normalized_bag_tests[@]}"; do
  if ! test_file=$(resolve_test_file "$name"); then
    echo "FAIL $name: missing CeTTa test file" >&2
    failures=$((failures + 1))
    continue
  fi

  compare_to_cetta_normalized_bag "sml-vs-cetta-normalized-bag" "$test_file" \
    env METTA_FILE="$test_file" "$POLY" --script tests/run_metta_file.sml
  compare_to_cetta_normalized_bag "cml-vs-cetta-normalized-bag" "$test_file" \
    "$CML_RUNNER" "$test_file"
done

if [[ $failures -eq 0 ]]; then
  echo "Selected CeTTa comparisons passed: $((${#exact_tests[@]} + ${#normalized_bag_tests[@]}))"
else
  echo "Selected CeTTa comparisons failed: $failures comparisons" >&2
  exit 1
fi
