#!/usr/bin/env bash
# ============================================================================
# Generated-kernel-signature freshness gate.
#
# The files kernel_signature_metta_{add,rev}_generated_v0.metta are DERIVED:
# their entire contents are rendered by Lean from the LanguageDef-derived
# signatures (Mettapedia.GSLT.LanguageDef.MIEvalHostingGeneratedFiles).
# This gate re-renders them from the current Lean value and diffs against the
# checked-in files.  Any divergence (hand edit of the .metta, or a Lean-side
# change not re-emitted) fails RED.  Engine-level equality with the kernel
# fixture is separately asserted inside the generated files themselves when
# the parity gate runs them; this gate covers the Lean->file freshness leg.
#
# Usage: bash check_generated_kernel_sigs.sh
#   KERNEL_DIR override supported (for testing the gate itself).
# ============================================================================
set -u
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
KERNEL_DIR="${KERNEL_DIR:-$SCRIPT_DIR}"
LEAN_PKG="$(cd "$SCRIPT_DIR/../../lean/mettapedia" && pwd)"
LAKE="$(command -v lake || echo "$HOME/.elan/bin/lake")"

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

cat > "$tmpdir/EmitGeneratedSigs.lean" <<'EOF'
import Mettapedia.GSLT.LanguageDef.MIEvalHostingGeneratedFiles

def main (args : List String) : IO Unit := do
  match args with
  | [addOut, revOut] =>
      IO.FS.writeFile addOut mettaAddGeneratedKernelSignatureFile
      IO.FS.writeFile revOut mettaRevGeneratedKernelSignatureFile
  | _ => throw (IO.userError "usage: EmitGeneratedSigs <addOut> <revOut>")
EOF

if ! ( cd "$LEAN_PKG" && LEAN_NUM_THREADS=1 LAKE_JOBS=1 nice -n 19 \
       "$LAKE" build Mettapedia.GSLT.LanguageDef.MIEvalHostingGeneratedFiles ) \
     > "$tmpdir/build.log" 2>&1; then
  echo "  [generated-sig] FAIL: Lean prerequisite build failed"
  tail -8 "$tmpdir/build.log" | sed 's/^/        /'
  exit 1
fi

if ! ( cd "$LEAN_PKG" && LEAN_NUM_THREADS=1 LAKE_JOBS=1 nice -n 19 \
       "$LAKE" env lean --run "$tmpdir/EmitGeneratedSigs.lean" \
       "$tmpdir/add_generated.metta" "$tmpdir/rev_generated.metta" ) \
     > "$tmpdir/emit.log" 2>&1; then
  echo "  [generated-sig] FAIL: Lean emission failed"
  tail -8 "$tmpdir/emit.log" | sed 's/^/        /'
  exit 1
fi

fail=0
for pair in \
  "add_generated.metta:kernel_signature_metta_add_generated_v0.metta" \
  "rev_generated.metta:kernel_signature_metta_rev_generated_v0.metta"; do
  fresh="$tmpdir/${pair%%:*}"
  intree="$KERNEL_DIR/${pair##*:}"
  if [ ! -f "$intree" ]; then
    echo "  [generated-sig] FAIL: missing in-tree file ${pair##*:}"
    fail=1
    continue
  fi
  if diff -u "$intree" "$fresh" > "$tmpdir/diff.out" 2>&1; then
    echo "  [generated-sig] ${pair##*:}  FRESH (matches Lean-rendered signature)"
  else
    echo "  [generated-sig] ${pair##*:}  STALE/DIVERGED  X"
    echo "        The in-tree file no longer matches what the Lean LanguageDef value renders."
    echo "        Either a hand edit crept into the derived .metta, or the Lean-side signature"
    echo "        changed without re-emitting.  Re-emit from Lean; never hand-edit derived files."
    head -12 "$tmpdir/diff.out" | sed 's/^/        /'
    fail=1
  fi
done

exit "$fail"
