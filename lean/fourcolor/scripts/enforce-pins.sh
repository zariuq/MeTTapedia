#!/usr/bin/env bash
set -euo pipefail

echo "Checking version pins..."

# Ensure lakefile.toml has the pinned mathlib rev
if ! grep -q 'rev = "06d95e5f5311594940c0c3dff5381fabe4fcabe7"' lakefile.toml; then
  echo "❌ mathlib not pinned to approved rev 06d95e5f5311594940c0c3dff5381fabe4fcabe7"
  echo "   Current lakefile.toml mathlib config:"
  grep -A 2 'name = "mathlib"' lakefile.toml || echo "   (mathlib section not found)"
  exit 1
fi

# Ensure lean-toolchain is 4.24.0-rc1
if ! grep -q 'leanprover/lean4:v4.24.0-rc1' lean-toolchain; then
  echo "❌ lean-toolchain not pinned to v4.24.0-rc1"
  echo "   Current lean-toolchain:"
  cat lean-toolchain
  exit 1
fi

echo "✅ Version pins verified:"
echo "   - Lean: v4.24.0-rc1"
echo "   - mathlib: 06d95e5f5311594940c0c3dff5381fabe4fcabe7"
