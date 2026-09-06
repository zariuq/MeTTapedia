#!/usr/bin/env bash
set -euo pipefail

echo "Checking version pins..."

# Ensure lakefile.toml has the pinned mathlib rev
if ! grep -q 'rev = "0df444a360eaa60ab8c11dca51a86af692955474"' lakefile.toml; then
  echo "❌ mathlib not pinned to approved rev 0df444a360eaa60ab8c11dca51a86af692955474"
  echo "   Current lakefile.toml mathlib config:"
  grep -A 2 'name = "mathlib"' lakefile.toml || echo "   (mathlib section not found)"
  exit 1
fi

# Ensure lean-toolchain is 4.33.1
if ! grep -q 'leanprover/lean4:v4.33.1' lean-toolchain; then
  echo "❌ lean-toolchain not pinned to v4.33.1"
  echo "   Current lean-toolchain:"
  cat lean-toolchain
  exit 1
fi

echo "✅ Version pins verified:"
echo "   - Lean: v4.33.1"
echo "   - mathlib: 0df444a360eaa60ab8c11dca51a86af692955474"
