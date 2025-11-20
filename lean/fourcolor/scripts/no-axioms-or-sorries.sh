#!/usr/bin/env bash
set -euo pipefail

# Whitelist of files allowed to have axioms/sorries (edit as needed):
WHITELIST_FILES=(
  "FourColor/Geometry/RotationSystem.lean"  # allowed: 5 foundation axioms (documented in AXIOMS.md)
  "FourColor/Geometry/Disk.lean"            # allowed: 4 axioms + 2 sorries (documented in AXIOMS.md)
  "FourColor/Triangulation.lean"            # allowed: existing sorries
  "FourColor/Tait.lean"                     # allowed: existing sorries (Tait equivalence construction)
  "FourColor/KempeExistence.lean"           # allowed: existing sorries (Kempe chain integration)
  "FourColor/KempeAPI.lean"                 # allowed: existing sorries (API wiring)
  "FourColor/FourColorTheorem.lean"         # allowed: existing sorries (top-level theorem)
  "FourColor/GraphTheory/SpanningForest.lean"  # allowed: existing sorries
  "FourColor/Examples/Tetrahedron.lean"     # allowed: existing sorries (example proof)
)

# Build a grep -v pattern for the whitelist
WHITELIST_PATTERN="$(printf '|%s' "${WHITELIST_FILES[@]}")"
WHITELIST_PATTERN="${WHITELIST_PATTERN:1}"

# Get changed files (for pre-commit hook usage)
if [ "${1:-}" = "--all" ]; then
  # Check all .lean files
  CHANGED="$(find FourColor -name '*.lean' 2>/dev/null || true)"
else
  # Check only staged files (pre-commit mode)
  CHANGED="$(git diff --cached --name-only --diff-filter=ACM 2>/dev/null | grep -E '\.lean$' || true)"
fi

# Nothing to check
[ -z "$CHANGED" ] && exit 0

FAIL=0

# Flag any 'axiom', 'admit', or 'sorry' outside whitelist
if echo "$CHANGED" | grep -Ev "$WHITELIST_PATTERN" | xargs -r grep -nE '\b(axiom|admit|sorry)\b' 2>/dev/null; then
  echo
  echo "❌ Found forbidden 'axiom'/'admit'/'sorry' outside whitelist."
  echo "   Whitelist: ${WHITELIST_FILES[*]}"
  echo "   All axioms/sorries must be documented in AXIOMS.md and added to whitelist."
  FAIL=1
fi

# For whitelisted files, just warn about changes (don't block)
# All existing axioms/sorries are documented in AXIOMS.md
if echo "$CHANGED" | grep -E "$WHITELIST_PATTERN" | xargs -r grep -nE '\b(axiom|sorry)\b' 2>/dev/null; then
  echo
  echo "⚠️  Modified whitelisted file with axioms/sorries."
  echo "   Please verify changes against AXIOMS.md documentation."
  echo "   If adding new axioms/sorries, update AXIOMS.md first."
fi

if [ $FAIL -eq 0 ]; then
  echo "✅ Axiom/sorry hygiene check passed"
fi

exit $FAIL
