#!/bin/bash
# Verify all ramsey36 Egal mode proofs

echo "Verifying ramsey36 proofs in Egal mode..."
echo "=========================================="

files=(
  "ramsey36/vertex_degree_bound.mg"
  "ramsey36/lower_bound_proof.mg"
  "ramsey36/remaining_theorems.mg"
  "ramsey36/good_graph_proof.mg"
  "ramsey36/adj17_with_sym.mg"
)

passed=0
failed=0

for file in "${files[@]}"; do
  echo -n "Testing $file ... "
  if ./bin/megalodon -I Megalodon/examples/egal/PfgEAug2022Preamble.mgs \
                     ramsey36/ramsey36_egal_preamble.mgs \
                     "$file" > /dev/null 2>&1; then
    echo "✅ PASS"
    ((passed++))
  else
    echo "❌ FAIL"
    ((failed++))
  fi
done

echo "=========================================="
echo "Results: $passed passed, $failed failed"
