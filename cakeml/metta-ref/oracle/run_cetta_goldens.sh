#!/usr/bin/env bash
set -euo pipefail

CETTA=${CETTA:-/home/zar/claude/hyperon/CeTTa/cetta}
CETTA_TEST_DIR=${CETTA_TEST_DIR:-/home/zar/claude/hyperon/CeTTa/tests}

if [[ ! -x "$CETTA" ]]; then
  echo "missing executable: $CETTA" >&2
  exit 1
fi

shopt -s nullglob
tests=("$CETTA_TEST_DIR"/he_*.metta)
shopt -u nullglob

if [[ ${#tests[@]} -eq 0 ]]; then
  echo "no HE golden tests found in $CETTA_TEST_DIR" >&2
  exit 1
fi

failures=0

for test_file in "${tests[@]}"; do
  expected_file=${test_file%.metta}.expected
  name=$(basename "$test_file")

  if [[ ! -f "$expected_file" ]]; then
    echo "FAIL $name: missing expected file $expected_file" >&2
    failures=$((failures + 1))
    continue
  fi

  if diff -u "$expected_file" <("$CETTA" --lang he "$test_file") >/dev/null; then
    echo "PASS $name"
  else
    echo "FAIL $name" >&2
    diff -u "$expected_file" <("$CETTA" --lang he "$test_file") || true
    failures=$((failures + 1))
  fi
done

if [[ $failures -eq 0 ]]; then
  echo "CeTTa HE golden tests passed: ${#tests[@]}"
else
  echo "CeTTa HE golden tests failed: $failures of ${#tests[@]}" >&2
  exit 1
fi
