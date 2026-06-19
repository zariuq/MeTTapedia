#!/bin/sh
# ============================================================================
# Reproducibility harness for the PLN confidence degrees-of-freedom pack.
#
# HONEST CONTRACT: the Lean theorems (see DOF-INDEX.md) are the correctness
# ORACLE. These .metta runs reproduce the paper's displayed numbers so a knob
# can be SEEN to matter. Runtime failures are real failures of the example pack;
# matching output is still illustration/reproducibility, NOT proof.
# (See docs/EXPECTED.md for the numbers.)
#
# Usage:  sh run_all.sh
# Override engine locations with CETTA=... PETTA=...
# ============================================================================
set -eu
PKG=$(cd "$(dirname "$0")" && pwd)
CETTA_DIR=${CETTA:-$PKG/../../../hyperon/CeTTa}
PETTA_DIR=${PETTA:-$PKG/../../../hyperon/PeTTa}

echo "### Building CeTTa (BUILD=core; fast no-op if current) ..."
( cd "$CETTA_DIR" && make BUILD=core >/dev/null 2>&1 && echo "    cetta: OK" ) \
  || { echo "    cetta build FAILED"; exit 1; }

echo
echo "### Running examples on CeTTa (HE mode)"
failures=0
for f in "$PKG"/metta/dof*.metta; do
  echo "----- $(basename "$f") -----"
  if ! "$CETTA_DIR/cetta" "$f"; then
    echo "    [FAILED]"
    failures=$((failures + 1))
  fi
done

echo
if command -v swipl >/dev/null 2>&1 && [ -f "$PETTA_DIR/run.sh" ]; then
  echo "### Running examples on PeTTa"
  for f in "$PKG"/metta/dof*.metta; do
    echo "----- $(basename "$f") -----"
    if ! ( cd "$PETTA_DIR" && sh run.sh "$f" 2>&1 \
        | sed 's/\x1b\[[0-9;]*m//g' \
        | grep -E '^\[|^[0-9-]|^\(evidence|^\(stv|^true$|^false$' ); then
      echo "    [FAILED]"
      failures=$((failures + 1))
    fi
  done
else
  echo "### PeTTa skipped (set PETTA=... and install SWI-Prolog to enable)"
fi

echo
echo "### Done. Compare numbers against docs/EXPECTED.md (eyeball, not a gate)."
if [ "$failures" -ne 0 ]; then
  echo "### Runtime failures: $failures"
  exit 1
fi
