#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KERNEL="$(cd "$ROOT/.." && pwd)"
METTAPEDIA="$(cd "$ROOT/../../.." && pwd)"
AIHUB="${AIHUB:-$(cd "$METTAPEDIA/.." && pwd)}"

CETTA_PRIME="${CETTA_PRIME:-cetta}"
CETTA_GSLT="${CETTA_GSLT:?set CETTA_GSLT to a GSLT-enabled CeTTa executable}"
GSLT_GRAMMAR="${GSLT_GRAMMAR:?set GSLT_GRAMMAR to the generated Metamath grammar}"
SETMM_REVISION="${SETMM_REVISION:-47e6e06b87581cd630d210dc41cf83b02eea78ea}"
SETMM_SHA256="${SETMM_SHA256:-3aecffcfcab6f6e114cce1d873a8300d7f41f24928648c04164aaa305b1f491a}"
SETMM="${SETMM:?set SETMM to set.mm at revision $SETMM_REVISION}"
MMLEAN_ROOT="${MMLEAN_ROOT:-$AIHUB/Mettapedia/lean/standalone/mm-lean4}"
LEAN_ROOT="${LEAN_ROOT:-$METTAPEDIA/lean/mettapedia}"
LOGDIR="${LOGDIR:-$ROOT/parity_logs/setmm_prime_quantified_ax5d_v0}"

SOURCE="$ROOT/setmm_ax5d_source_v0.mm"
REFERENCE="$ROOT/setmm_ax5d_semantic_reference_v0.metta"
REPLAY="$ROOT/setmm_prime_quantified_ax5d_v0.metta"
SEARCH="$ROOT/setmm_prime_quantified_ax5d_search_v0.metta"
TOOLS="$ROOT/setmm_quantified_ax5d_tools.py"
REPLAY_LIBRARY="$KERNEL/metamath_assertion_replay_v1.metta"
SEMANTIC_EXPORTER="Mettapedia/Languages/Metamath/SourceGSLTSemanticMeTTaExport.lean"
SOURCE_DIGEST="94b6e5c31ab5d0c8416d136a1daaec75cc9b89690c0c62c5a24d947feccd9819"
SOURCE_IDENTITY="set.mm-47e6e06b-ax5d"

mkdir -p "$LOGDIR"

fail() {
  echo "SET.MM PRIME QUANTIFIED AX5D V0 GATE: FAIL ($*)" >&2
  exit 1
}

actual_setmm_sha256="$(sha256sum "$SETMM" | awk '{print $1}')"
[[ "$actual_setmm_sha256" == "$SETMM_SHA256" ]] ||
  fail "set.mm SHA-256 mismatch"

FRESH_PREFIX="$LOGDIR/setmm-through-ax5d.fresh.mm"
FRESH_SOURCE="$LOGDIR/setmm_ax5d_source_v0.fresh.mm"
FRESH_MANIFEST="$LOGDIR/setmm_ax5d_source_v0.manifest.json"

python3 "$TOOLS" \
  --setmm "$SETMM" \
  --output-prefix "$FRESH_PREFIX" \
  --output-slice "$FRESH_SOURCE" \
  --manifest "$FRESH_MANIFEST" \
  >"$LOGDIR/source-generation.log" 2>&1 ||
  fail "source reconstruction"

python3 "$TOOLS" \
  --setmm "$SETMM" \
  --output-prefix "$FRESH_PREFIX" \
  --output-slice "$FRESH_SOURCE" \
  --manifest "$FRESH_MANIFEST" \
  --check \
  >"$LOGDIR/source-determinism.log" 2>&1 ||
  fail "source reconstruction determinism"

cmp -s "$SOURCE" "$FRESH_SOURCE" ||
  fail "checked compact source differs from pinned reconstruction"

if ! (
  cd "$MMLEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake exe mm-lean4 "$SOURCE"
) >"$LOGDIR/mm-lean4.log" 2>&1; then
  fail "mm-lean4 source verification"
fi
[[ "$(grep -Fxc 'verified, 25 objects' "$LOGDIR/mm-lean4.log")" -eq 1 ]] ||
  fail "mm-lean4 verification summary absent or changed"

if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake build \
    Mettapedia.Languages.Metamath.SourceGSLTSemanticMeTTaExport
) >"$LOGDIR/semantic-exporter-build.log" 2>&1; then
  fail "semantic exporter build"
fi

FRESH_REFERENCE="$LOGDIR/setmm_ax5d_semantic_reference_v0.fresh.metta"
if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 lake env lean --run "$SEMANTIC_EXPORTER" \
    "$FRESH_REFERENCE" \
    "$SOURCE_IDENTITY" "$SOURCE_DIGEST" "$SOURCE"
) >"$LOGDIR/semantic-export.log" 2>&1; then
  fail "mm-lean4 semantic export"
fi
cmp -s "$REFERENCE" "$FRESH_REFERENCE" ||
  fail "semantic reference differs from mm-lean4 export"

SUMMARY_EXPRESSION="!(metamath-ledger:summary (metamath-ledger:parse-file \"$GSLT_GRAMMAR\" (MMSourceIdentityV0 \"$SOURCE_IDENTITY\" \"$SOURCE_DIGEST\") \"$SOURCE\"))"
if ! (
  cd "$KERNEL"
  "$CETTA_GSLT" --lang he --profile he-prime --import-mode ancestor-walk \
    -e '!(import! &self metamath_statement_ledger_v0)' \
    -e "$SUMMARY_EXPRESSION"
) >"$LOGDIR/gslt-summary.log" 2>&1; then
  fail "GSLT source ledger"
fi
EXPECTED_SUMMARY="[(MMCheckedLedgerSummary (MMSourceIdentityV0 \"$SOURCE_IDENTITY\" \"$SOURCE_DIGEST\") 154 280 (MMLedgerCounts 26 1 1 2 4 3 5 2 0 2 4 4 0))]"
[[ "$(grep -Fxc "$EXPECTED_SUMMARY" "$LOGDIR/gslt-summary.log")" -eq 1 ]] ||
  fail "GSLT ledger summary absent or changed"

AGREEMENT_EXPRESSION="!(mm-semantic:agrees (metamath-ledger:parse-file \"$GSLT_GRAMMAR\" (MMSourceIdentityV0 \"$SOURCE_IDENTITY\" \"$SOURCE_DIGEST\") \"$SOURCE\") (mm-semantic-reference-v0 \"$SOURCE_DIGEST\"))"
if ! (
  cd "$KERNEL"
  "$CETTA_GSLT" --lang he --profile he-prime --import-mode ancestor-walk \
    -e '!(import! &self pcxp_trace_certification/setmm_ax5d_semantic_reference_v0)' \
    -e "$AGREEMENT_EXPRESSION"
) >"$LOGDIR/gslt-semantic-agreement.log" 2>&1; then
  fail "GSLT/mm-lean4 semantic agreement"
fi
[[ "$(grep -Fxc '[True]' "$LOGDIR/gslt-semantic-agreement.log")" -eq 1 ]] ||
  fail "GSLT/mm-lean4 semantic agreement absent or changed"

if ! (
  cd "$KERNEL"
  "$CETTA_PRIME" --lang prime --import-mode ancestor-walk \
    pcxp_trace_certification/setmm_prime_quantified_ax5d_v0.metta
) >"$LOGDIR/prime-replay.log" 2>&1; then
  fail "Prime source replay"
fi
if grep -Eq '\(FAIL |\(Error ' "$LOGDIR/prime-replay.log"; then
  fail "Prime source replay emitted a failure"
fi
[[ "$(grep -Ec '^\[\(PASS ' "$LOGDIR/prime-replay.log")" -eq 10 ]] ||
  fail "Prime source replay verdict count changed"
grep -Fq '(SetMMPrimeQuantifiedAx5dSummary replay 1 rejected-mutations 9)' \
  "$LOGDIR/prime-replay.log" ||
  fail "Prime source replay summary absent"

if ! (
  cd "$KERNEL"
  "$CETTA_PRIME" --lang prime --import-mode ancestor-walk \
    pcxp_trace_certification/setmm_prime_quantified_ax5d_search_v0.metta
) >"$LOGDIR/prime-search.log" 2>&1; then
  fail "Prime quantified search"
fi
if grep -Eq '\(FAIL |\(Error ' "$LOGDIR/prime-search.log"; then
  fail "Prime quantified search emitted a failure"
fi
[[ "$(grep -Ec '^\[\(PASS ' "$LOGDIR/prime-search.log")" -eq 3 ]] ||
  fail "Prime quantified search verdict count changed"
grep -Fq '(SetMMPrimeQuantifiedAx5dSearchSummary discovered 1 replayed 1 rejected 1)' \
  "$LOGDIR/prime-search.log" ||
  fail "Prime quantified search summary absent"

if rg -n '\bsorry\b|\badmit\b|theorem_wanted|native_decide' \
    "$REPLAY_LIBRARY" "$REPLAY" "$SEARCH" "$TOOLS" \
    "$LEAN_ROOT/$SEMANTIC_EXPORTER" >"$LOGDIR/placeholder-scan.log"; then
  fail "placeholder or prohibited proof shortcut found"
fi

echo 'SET.MM PRIME QUANTIFIED AX5D V0 GATE: PASS (pinned source reconstruction; compressed proof decoded; mm-lean4 and GSLT agree; 1 authentic replay; 9 replay mutations rejected; DV-erased search discovered and replayed 1 proof; 1 searched-term mutation rejected)'
