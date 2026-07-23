#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AIHUB="${AIHUB:-$(cd "$ROOT/../../.." && pwd)}"
CETTA_ROOT="${CETTA_ROOT:-$AIHUB/hyperon/CeTTa}"
CETTA="${CETTA:-$CETTA_ROOT/cetta}"
MM_TEST="$AIHUB/hyperon/metamath/metamath-test"
LEAN_ROOT="$AIHUB/Mettapedia/lean/mettapedia"
EXPORTER="Mettapedia/Languages/Metamath/SourceGSLTMeTTaExport.lean"
PARSER_EXPORTER="Mettapedia/Languages/Metamath/SourceGSLTParserExport.lean"
SEMANTIC_ORACLE="Mettapedia/Languages/Metamath/SourceGSLTSemanticOracle.lean"
SEMANTIC_EXPORTER="Mettapedia/Languages/Metamath/SourceGSLTSemanticMeTTaExport.lean"
GRAMMAR="$CETTA_ROOT/lib/lib_parse_metamath_grammar_generated_v0.metta"
PARSER_PRESENTATION="$CETTA_ROOT/experiments/gslt2parse_foundation/presentations/languages/metamath_appendix_e_v1.metta"
LEXER="$CETTA_ROOT/lib/lib_parse_metamath.metta"
SEMANTICS="$ROOT/metamath_statement_semantics_v0.metta"
SEMANTIC_REFERENCE="$ROOT/metamath_statement_semantic_reference_v0.metta"
LOGDIR="$ROOT/parity_logs/metamath_statement_ledger_v0"

mkdir -p "$LOGDIR"

fail() {
  echo "METAMATH STATEMENT LEDGER V0 GATE: FAIL ($*)"
  exit 1
}

LEAN_BUILD_LOG="$LOGDIR/source-gslt-build.log"
if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 \
    lake build \
      Mettapedia.GSLT.CheckedLanguage \
      Mettapedia.Languages.Megalodon.CheckedLanguageSkeleton \
      Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler \
      Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence \
      Mettapedia.Languages.Metamath.SourceGSLT \
      Mettapedia.Languages.Metamath.SourceGSLTParserExport \
      Mettapedia.Languages.Metamath.VerifiedCheckerSemantics \
      Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment \
      Mettapedia.Languages.Metamath.SourceGSLTCheckedLanguage \
      Mettapedia.Languages.Metamath.SourceGSLTSemanticOracle \
      Mettapedia.Languages.Metamath.SourceGSLTSemanticMeTTaExport
) >"$LEAN_BUILD_LOG" 2>&1; then
  fail "source GSLT Lean build; log: $LEAN_BUILD_LOG"
fi

FRESH_GRAMMAR="$LOGDIR/lib_parse_metamath_grammar_generated_v0.fresh.metta"
EXPORT_LOG="$LOGDIR/source-gslt-export.log"
if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 \
    lake env lean --run "$EXPORTER" "$FRESH_GRAMMAR"
) >"$EXPORT_LOG" 2>&1; then
  fail "source GSLT export; log: $EXPORT_LOG"
fi
cmp -s "$GRAMMAR" "$FRESH_GRAMMAR" ||
  fail "generated grammar differs from its Lean GSLT root: $FRESH_GRAMMAR"

FRESH_PARSER_PRESENTATION="$LOGDIR/metamath_appendix_e_v1.fresh.metta"
PARSER_EXPORT_LOG="$LOGDIR/source-gslt-parser-export.log"
if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 \
    lake env lean --run "$PARSER_EXPORTER" "$FRESH_PARSER_PRESENTATION"
) >"$PARSER_EXPORT_LOG" 2>&1; then
  fail "source GSLT parser-presentation export; log: $PARSER_EXPORT_LOG"
fi
cmp -s "$PARSER_PRESENTATION" "$FRESH_PARSER_PRESENTATION" ||
  fail "generated parser presentation differs from its Lean GSLT root: $FRESH_PARSER_PRESENTATION"

SOURCE_CERTIFICATE_LOG="$LOGDIR/source-certificate-projector.log"
if ! make -C "$CETTA_ROOT" test-gslt2parse-source-certificate-v1 \
    >"$SOURCE_CERTIFICATE_LOG" 2>&1; then
  fail "generic source-certificate projector; log: $SOURCE_CERTIFICATE_LOG"
fi

check_source() {
  local label="$1"
  local source="$2"
  local expected_hash="$3"
  local expected_bytes="$4"
  local actual_hash
  local actual_bytes
  actual_hash="$(sha256sum "$source" | awk '{print $1}')"
  actual_bytes="$(wc -c < "$source")"
  [[ "$actual_hash" == "$expected_hash" ]] ||
    fail "$label source hash changed: $actual_hash"
  [[ "$actual_bytes" -eq "$expected_bytes" ]] ||
    fail "$label source byte count changed: $actual_bytes"
}

run_summary() {
  local label="$1"
  local source="$2"
  local revision="$3"
  local digest="$4"
  local expected="$5"
  local log="$LOGDIR/$label.summary.log"
  local expression
  expression="!(metamath-ledger:summary (metamath-ledger:parse-file \"$GRAMMAR\" (MMSourceIdentityV0 \"$revision\" \"$digest\") \"$source\"))"
  if ! (
    cd "$ROOT"
    "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
      -e '!(import! &self metamath_statement_ledger_v0)' \
      -e "$expression"
  ) >"$log" 2>&1; then
    fail "$label process; log: $log"
  fi
  if grep -q 'Error\|❌' "$log"; then
    fail "$label emitted an error; log: $log"
  fi
  [[ "$(grep -Fxc "$expected" "$log")" -eq 1 ]] ||
    fail "$label exact summary absent or duplicated; log: $log"
}

run_overview() {
  local label="$1"
  local source="$2"
  local revision="$3"
  local digest="$4"
  local expected="$5"
  local log="$LOGDIR/$label.overview.log"
  local expression
  expression="!(metamath-ledger:overview (metamath-ledger:parse-file \"$GRAMMAR\" (MMSourceIdentityV0 \"$revision\" \"$digest\") \"$source\"))"
  if ! (
    cd "$ROOT"
    "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
      -e '!(import! &self metamath_statement_ledger_v0)' \
      -e "$expression"
  ) >"$log" 2>&1; then
    fail "$label process; log: $log"
  fi
  if grep -q 'Error\|❌' "$log"; then
    fail "$label emitted an error; log: $log"
  fi
  [[ "$(grep -Fxc "$expected" "$log")" -eq 1 ]] ||
    fail "$label exact overview absent or duplicated; log: $log"
}

run_claims() {
  local label="$1"
  local source="$2"
  local revision="$3"
  local digest="$4"
  local log="$LOGDIR/$label.claims.log"
  local expression
  expression="!(metamath-ledger:theorem-claims (metamath-ledger:parse-file \"$GRAMMAR\" (MMSourceIdentityV0 \"$revision\" \"$digest\") \"$source\"))"
  if ! (
    cd "$ROOT"
    "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
      -e '!(import! &self metamath_statement_ledger_v0)' \
      -e "$expression"
  ) >"$log" 2>&1; then
    fail "$label theorem claims; log: $log"
  fi
  grep -F 'MMTheoremClaim' "$log" ||
    fail "$label theorem claim absent; log: $log"
}

run_rejection() {
  local label="$1"
  local source="$2"
  local digest="$3"
  local expected="$4"
  local log="$LOGDIR/$label.rejection.log"
  local expression
  expression="!(metamath-ledger:parse-file \"$GRAMMAR\" (MMSourceIdentityV0 \"negative/$label\" \"$digest\") \"$source\")"
  if ! (
    cd "$ROOT"
    "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
      -e '!(import! &self metamath_statement_ledger_v0)' \
      -e "$expression"
  ) >"$log" 2>&1; then
    fail "$label process; log: $log"
  fi
  [[ "$(grep -Fxc "$expected" "$log")" -eq 1 ]] ||
    fail "$label rejection absent or changed; log: $log"
}

run_checker_rejection_syntax_acceptance() {
  local label="$1"
  local source="$2"
  local digest="$3"
  local log="$LOGDIR/$label.syntax-acceptance.log"
  local expression
  expression="!(metamath-ledger:summary (metamath-ledger:parse-file \"$GRAMMAR\" (MMSourceIdentityV0 \"negative/$label\" \"$digest\") \"$source\"))"
  if ! (
    cd "$ROOT"
    "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
      -e '!(import! &self metamath_statement_ledger_v0)' \
      -e "$expression"
  ) >"$log" 2>&1; then
    fail "$label syntax-acceptance process; log: $log"
  fi
  if grep -q 'Error\|Rejected\|MMStatementLedgerError\|❌' "$log"; then
    fail "$label failed before semantic checking; log: $log"
  fi
  [[ "$(grep -Ec '^\[\(MMCheckedLedgerSummary ' "$log")" -eq 1 ]] ||
    fail "$label did not produce one checked syntax ledger; log: $log"
}

run_semantic_agreement() {
  local label="$1"
  local source="$2"
  local revision="$3"
  local digest="$4"
  local reference_module="${5:-metamath_statement_semantic_reference_v0}"
  local expected="${6:-[True]}"
  local log="$LOGDIR/$label.semantic-agreement.log"
  local expression
  expression="!(mm-semantic:agrees (metamath-ledger:parse-file \"$GRAMMAR\" (MMSourceIdentityV0 \"$revision\" \"$digest\") \"$source\") (mm-semantic-reference-v0 \"$digest\"))"
  if ! (
    cd "$ROOT"
    "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
      -e "!(import! &self $reference_module)" \
      -e "$expression"
  ) >"$log" 2>&1; then
    fail "$label semantic agreement process; log: $log"
  fi
  if grep -q 'Error\|❌' "$log"; then
    fail "$label semantic agreement emitted an error; log: $log"
  fi
  [[ "$(grep -Ec '^\[(True|False)\]$' "$log")" -eq 1 ]] ||
    fail "$label semantic comparison was not single-result; log: $log"
  [[ "$(grep -Fxc "$expected" "$log")" -eq 1 ]] ||
    fail "$label semantic agreement absent or changed; log: $log"
}

run_tree_substitution_rejection() {
  local source="$1"
  local digest="$2"
  local log="$LOGDIR/tree-substitution.rejection.log"
  local expression
  expression="!(case (fs:read-text \"$source\") ((\$text (case (lib_parse:mm-lex-string \$text) (((Ok \$tokens) (case (lib_parse:mm-parse-database-shared \"$GRAMMAR\" \$tokens) (((Unique \$tree) (case (lib_parse:dag-presentation-candidate (lib_parse:mm-database-grammar) \"$digest\" \$tokens) (((LPInferencePresentation (GPresentation \$constructors \$judgments \$rules)) (case (gparse:inference-dag-proof (lib_parse:mm-database-grammar) \"$digest\" outer_database \$tokens \$tree) (((LPInferenceDagBlocks \$goal \$root \$blocks \$node-count) (case (gic-build-pathmap-index-parts \$constructors \$judgments \$rules) (((GICIndexOK \$space) (metamath-ledger:checked-dag-ledger \$space \"negative/tree-substitution\" \"$digest\" \$tokens (EpsC) \$goal \$root \$blocks \$node-count)) (\$error \$error)))) (\$error \$error)))) (\$error \$error)))) (\$error \$error)))) (\$error \$error)))) (\$error \$error)))"
  if ! (
    cd "$ROOT"
    "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
      -e '!(import! &self metamath_statement_ledger_v0)' \
      -e "$expression"
  ) >"$log" 2>&1; then
    fail "tree-substitution process; log: $log"
  fi
  [[ "$(grep -Fxc '[(MMStatementLedgerError checked-tree-disagrees-with-parser)]' "$log")" -eq 1 ]] ||
    fail "tree substitution was not rejected; log: $log"
}

DEMO0="$MM_TEST/demo0.mm"
MIU="$MM_TEST/miu.mm"
PEANO="$MM_TEST/peano-fixed.mm"
DV="$ROOT/metamath_dv_fixture_v0.mm"
NORMAL="$MM_TEST/tests/unit/test_compressed_simple.mm"
COMPRESSED="$MM_TEST/tests/unit/test_compressed_syl.mm"
SETMM_PROPOSITIONAL="$ROOT/setmm_propositional_idalt_slice_v0.mm"
NESTED_COMMENT="$MM_TEST/tests/unit/test03_nested_comment_delimiters.mm"
UNBALANCED_SCOPE="$MM_TEST/tests/unit/test04_unbalanced_block_delimiters.mm"
ILLEGAL_LABEL="$MM_TEST/demo0-illegal-label-bad1.mm"
MISSING_COMMAND="$AIHUB/repos/metamath-exe/tests/missing-dollar-p.mm"
INCLUDE_INNER_SCOPE="$MM_TEST/tests/unit/test17_include_scope_violation.mm"
UNDEFINED_PROOF_LABEL="$MM_TEST/tests/unit/test24_undefined_label_in_proof.mm"
DV_VIOLATION="$MM_TEST/tests/unit/test27_disjoint_variable_constraint_violation.mm"
CORRUPTED_COMPRESSED="$MM_TEST/tests/unit/test29_compressed_proof_header_mismatch.mm"
FORWARD_REFERENCE="$MM_TEST/tests/unit/test32_forward_reference_in_proof.mm"

DEMO0_HASH=b68d7488bdbf2d55d1a955f3a6a3efac68ca9e3009d24f867e1a75aacb7b03d3
MIU_HASH=43ead5a0b37e968462cd66331dec324d42959c8f54460eab35cfb869b423d3f2
PEANO_HASH=c5314f062315415f5ad730df00cf74a000c881a11e707cda5dd932e11523e163
DV_HASH=46bfd4628307e20b9541682265fa7e815404cb362f12311330d43879579879da
NORMAL_HASH=c80051de58b21dd7007d6e7650c3de5ac789ac6a9de13c756db8b02cfdb63772
COMPRESSED_HASH=d25a0000ee11255db8b17e6b3ae2a1ea958be70097fc879d100910808649b2ac
SETMM_PROPOSITIONAL_HASH=2ea64ae8d82e5929cdc5094846ebc62ca72f7779eb15b558df89b7be7b1f5134
INCLUDE_INNER_SCOPE_HASH=fae6594d2913723aca0de61ca91cc1b51d33e1b5f427e14a6d1a8e8286d72b79
UNDEFINED_PROOF_LABEL_HASH=70f57154048101616be5c7154f6768a1fa4758e18335f7ddb03e184a5aeefca5
DV_VIOLATION_HASH=80bd764753be2ff2de19019171500f3af39cf3fd901e40db422bac9b030786f5
CORRUPTED_COMPRESSED_HASH=4f9877c39e31f77e2d7529d14c6aed50b4d0823528d52471cd3d2704c4d11dfd
FORWARD_REFERENCE_HASH=064a3c7cf19850af891791566124d62a60d48ad8a0ee36fd59b600693113c751

check_source demo0 "$DEMO0" "$DEMO0_HASH" 1353
check_source miu "$MIU" "$MIU_HASH" 4649
check_source peano "$PEANO" "$PEANO_HASH" 27843
check_source dv "$DV" "$DV_HASH" 532
check_source normal "$NORMAL" "$NORMAL_HASH" 343
check_source compressed "$COMPRESSED" "$COMPRESSED_HASH" 430
check_source setmm-propositional "$SETMM_PROPOSITIONAL" \
  "$SETMM_PROPOSITIONAL_HASH" 533
check_source nested-comment "$NESTED_COMMENT" \
  524ea329b3e455f63ce33faf6c2937a3d60f8533e81926039e2f9e53fc272390 155
check_source unbalanced-scope "$UNBALANCED_SCOPE" \
  2363f91e5d64d4a2bf80bdcfeb4f7dc2dbcf4a3a14191ee5761a85d6cf44e2a6 148
check_source illegal-label "$ILLEGAL_LABEL" \
  433f8b7255b62b66f3029b89886235837eeff57bbfdc2c44e41d9ab0807dc48a 1399
check_source missing-command "$MISSING_COMMAND" \
  b1765569ee8982948624ae41d06853f2664486e5bec2de0de8c6f8df870bbfd8 15
check_source include-inner-scope "$INCLUDE_INNER_SCOPE" \
  "$INCLUDE_INNER_SCOPE_HASH" 404
check_source undefined-proof-label "$UNDEFINED_PROOF_LABEL" \
  "$UNDEFINED_PROOF_LABEL_HASH" 152
check_source dv-violation "$DV_VIOLATION" "$DV_VIOLATION_HASH" 402
check_source corrupted-compressed "$CORRUPTED_COMPRESSED" \
  "$CORRUPTED_COMPRESSED_HASH" 217
check_source forward-reference "$FORWARD_REFERENCE" \
  "$FORWARD_REFERENCE_HASH" 156

SEMANTIC_ORACLE_LOG="$LOGDIR/mm-lean4-semantic-oracle.log"
if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 \
    lake env lean --run "$SEMANTIC_ORACLE" \
      "$DEMO0" "$MIU" "$PEANO" "$DV" "$NORMAL" "$COMPRESSED" \
      "$SETMM_PROPOSITIONAL"
) >"$SEMANTIC_ORACLE_LOG" 2>&1; then
  fail "mm-lean4 semantic oracle; log: $SEMANTIC_ORACLE_LOG"
fi
[[ "$(grep -Fxc 'MMSourceSemanticOracleSummary 7 [29, 24, 111, 12, 15, 15, 20] True' \
      "$SEMANTIC_ORACLE_LOG")" -eq 1 ]] ||
  fail "mm-lean4 semantic summary absent or changed; log: $SEMANTIC_ORACLE_LOG"

SEMANTIC_REJECTION_LOG="$LOGDIR/mm-lean4-semantic-rejections.log"
if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 \
    lake env lean --run "$SEMANTIC_ORACLE" --reject \
      "$UNDEFINED_PROOF_LABEL" "$DV_VIOLATION" \
      "$CORRUPTED_COMPRESSED" "$FORWARD_REFERENCE"
) >"$SEMANTIC_REJECTION_LOG" 2>&1; then
  fail "mm-lean4 semantic rejection oracle; log: $SEMANTIC_REJECTION_LOG"
fi
for expected in \
    'MMSourceSemanticRejection some (Metamath.Verify.ParseErrorCode.statementNotFound)' \
    'MMSourceSemanticRejection some (Metamath.Verify.ParseErrorCode.disjointVariableViolation)' \
    'MMSourceSemanticRejection some (Metamath.Verify.ParseErrorCode.stackUnderflow)'; do
  [[ "$(grep -Fxc "$expected" "$SEMANTIC_REJECTION_LOG")" -ge 1 ]] ||
    fail "semantic rejection code absent: $expected; log: $SEMANTIC_REJECTION_LOG"
done
[[ "$(grep -Fxc 'MMSourceSemanticRejection some (Metamath.Verify.ParseErrorCode.statementNotFound)' \
      "$SEMANTIC_REJECTION_LOG")" -eq 2 ]] ||
  fail "wrong-label and forward-reference errors were not independently caught"
[[ "$(grep -Fxc 'MMSourceSemanticRejectionSummary 4 True' \
      "$SEMANTIC_REJECTION_LOG")" -eq 1 ]] ||
  fail "semantic rejection summary absent or changed; log: $SEMANTIC_REJECTION_LOG"

FRESH_SEMANTIC_REFERENCE="$LOGDIR/metamath_statement_semantic_reference_v0.fresh.metta"
SEMANTIC_EXPORT_LOG="$LOGDIR/mm-lean4-semantic-export.log"
if ! (
  cd "$LEAN_ROOT"
  LEAN_NUM_THREADS=1 LAKE_JOBS=1 \
    lake env lean --run "$SEMANTIC_EXPORTER" \
      "$FRESH_SEMANTIC_REFERENCE" \
      metamath-test/demo0.mm "$DEMO0_HASH" "$DEMO0" \
      metamath-test/miu.mm "$MIU_HASH" "$MIU" \
      metamath-test/peano-fixed.mm "$PEANO_HASH" "$PEANO" \
      mettakernel/metamath_dv_fixture_v0.mm "$DV_HASH" "$DV" \
      metamath-test/test_compressed_simple.mm "$NORMAL_HASH" "$NORMAL" \
      metamath-test/test_compressed_syl.mm "$COMPRESSED_HASH" "$COMPRESSED" \
      set.mm/propositional-idALT-slice "$SETMM_PROPOSITIONAL_HASH" \
        "$SETMM_PROPOSITIONAL"
) >"$SEMANTIC_EXPORT_LOG" 2>&1; then
  fail "mm-lean4 semantic export; log: $SEMANTIC_EXPORT_LOG"
fi
cmp -s "$SEMANTIC_REFERENCE" "$FRESH_SEMANTIC_REFERENCE" ||
  fail "semantic reference differs from mm-lean4 output: $FRESH_SEMANTIC_REFERENCE"

run_semantic_agreement demo0 "$DEMO0" metamath-test/demo0.mm "$DEMO0_HASH"
run_semantic_agreement miu "$MIU" metamath-test/miu.mm "$MIU_HASH"
run_semantic_agreement peano "$PEANO" metamath-test/peano-fixed.mm "$PEANO_HASH"
run_semantic_agreement dv "$DV" \
  mettakernel/metamath_dv_fixture_v0.mm "$DV_HASH"
run_semantic_agreement normal "$NORMAL" \
  metamath-test/test_compressed_simple.mm "$NORMAL_HASH"
run_semantic_agreement compressed "$COMPRESSED" \
  metamath-test/test_compressed_syl.mm "$COMPRESSED_HASH"
run_semantic_agreement setmm-propositional "$SETMM_PROPOSITIONAL" \
  set.mm/propositional-idALT-slice "$SETMM_PROPOSITIONAL_HASH"

run_summary demo0 "$DEMO0" metamath-test/demo0.mm "$DEMO0_HASH" \
  "[(MMCheckedLedgerSummary (MMSourceIdentityV0 \"metamath-test/demo0.mm\" \"$DEMO0_HASH\") 166 324 (MMLedgerCounts 19 1 1 0 5 2 7 1 1 0 1 1 0))]"
run_summary miu "$MIU" metamath-test/miu.mm "$MIU_HASH" \
  "[(MMCheckedLedgerSummary (MMSourceIdentityV0 \"metamath-test/miu.mm\" \"$MIU_HASH\") 162 326 (MMLedgerCounts 27 1 1 0 2 4 10 1 1 0 4 4 0))]"
run_summary peano "$PEANO" metamath-test/peano-fixed.mm "$PEANO_HASH" \
  "[(MMCheckedLedgerSummary (MMSourceIdentityV0 \"metamath-test/peano-fixed.mm\" \"$PEANO_HASH\") 789 1549 (MMLedgerCounts 116 9 7 12 18 6 48 0 0 0 8 8 0))]"
run_summary dv "$DV" mettakernel/metamath_dv_fixture_v0.mm "$DV_HASH" \
  "[(MMCheckedLedgerSummary (MMSourceIdentityV0 \"mettakernel/metamath_dv_fixture_v0.mm\" \"$DV_HASH\") 62 120 (MMLedgerCounts 15 1 1 2 3 2 1 1 1 0 2 2 0))]"

CLAIM='(Cons (MMTheoremClaim "th" (Cons "|-" (Cons "R" (Cons "|=" (Cons "T" Nil))))) Nil)'
run_overview normal "$NORMAL" metamath-test/test_compressed_simple.mm "$NORMAL_HASH" \
  "[(MMCheckedLedgerOverview (MMSourceIdentityV0 \"metamath-test/test_compressed_simple.mm\" \"$NORMAL_HASH\") 78 152 (MMLedgerCounts 15 1 1 0 3 4 1 1 1 0 2 2 0) $CLAIM)]"
run_overview compressed "$COMPRESSED" metamath-test/test_compressed_syl.mm "$COMPRESSED_HASH" \
  "[(MMCheckedLedgerOverview (MMSourceIdentityV0 \"metamath-test/test_compressed_syl.mm\" \"$COMPRESSED_HASH\") 76 148 (MMLedgerCounts 15 1 1 0 3 4 1 1 0 1 2 2 0) $CLAIM)]"

SETMM_CLAIM='(Cons (MMTheoremClaim "idALT" (Cons "|-" (Cons "(" (Cons "ph" (Cons "->" (Cons "ph" (Cons ")" Nil))))))) Nil)'
run_overview setmm-propositional "$SETMM_PROPOSITIONAL" \
  set.mm/propositional-idALT-slice "$SETMM_PROPOSITIONAL_HASH" \
  "[(MMCheckedLedgerOverview (MMSourceIdentityV0 \"set.mm/propositional-idALT-slice\" \"$SETMM_PROPOSITIONAL_HASH\") 137 272 (MMLedgerCounts 22 6 3 0 3 2 5 1 0 1 1 1 0) $SETMM_CLAIM)]"

normal_claims="$(run_claims normal "$NORMAL" metamath-test/test_compressed_simple.mm "$NORMAL_HASH")"
compressed_claims="$(run_claims compressed "$COMPRESSED" metamath-test/test_compressed_syl.mm "$COMPRESSED_HASH")"
[[ "$normal_claims" == "$compressed_claims" ]] ||
  fail "normal/compressed theorem claims differ"

run_rejection nested-comment "$NESTED_COMMENT" \
  524ea329b3e455f63ce33faf6c2937a3d60f8533e81926039e2f9e53fc272390 \
  '[(Rejected (mm-lex bad-label-continuation "$)"))]'
run_rejection unbalanced-scope "$UNBALANCED_SCOPE" \
  2363f91e5d64d4a2bf80bdcfeb4f7dc2dbcf4a3a14191ee5761a85d6cf44e2a6 \
  '[(MMStatementLedgerError source-does-not-derive)]'
run_rejection illegal-label "$ILLEGAL_LABEL" \
  433f8b7255b62b66f3029b89886235837eeff57bbfdc2c44e41d9ab0807dc48a \
  '[(Rejected (mm-lex invalid-label "t\\t"))]'
run_rejection missing-command "$MISSING_COMMAND" \
  b1765569ee8982948624ae41d06853f2664486e5bec2de0de8c6f8df870bbfd8 \
  '[(Rejected (mm-lex bad-label-continuation "$}"))]'
run_rejection include-inner-scope "$INCLUDE_INNER_SCOPE" \
  "$INCLUDE_INNER_SCOPE_HASH" \
  '[(MMStatementLedgerError source-does-not-derive)]'

run_checker_rejection_syntax_acceptance undefined-proof-label \
  "$UNDEFINED_PROOF_LABEL" "$UNDEFINED_PROOF_LABEL_HASH"
run_checker_rejection_syntax_acceptance dv-violation \
  "$DV_VIOLATION" "$DV_VIOLATION_HASH"
run_checker_rejection_syntax_acceptance corrupted-compressed \
  "$CORRUPTED_COMPRESSED" "$CORRUPTED_COMPRESSED_HASH"
run_checker_rejection_syntax_acceptance forward-reference \
  "$FORWARD_REFERENCE" "$FORWARD_REFERENCE_HASH"

run_tree_substitution_rejection "$NORMAL" "$NORMAL_HASH"

MUTATED="$LOGDIR/lib_parse_metamath.metta"
perl -0pe \
  's/ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_\./ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_.\(/; END { print "\n!(lib_parse:mm-lex-string \"bad(label \$a |- x \$. \" )\n" }' \
  "$LEXER" >"$MUTATED"
MUTATION_LOG="$LOGDIR/label-rule-mutation.log"
if ! (
  "$CETTA" --lang he --profile he-prime --import-mode ancestor-walk \
    "$MUTATED"
) >"$MUTATION_LOG" 2>&1; then
  fail "label-rule mutation process; log: $MUTATION_LOG"
fi
grep -Fq '[(Ok ' "$MUTATION_LOG" ||
  fail "label-rule mutation was not activated; log: $MUTATION_LOG"
if grep -Fq 'invalid-label' "$MUTATION_LOG"; then
  fail "illegal-label negative did not distinguish the mutation"
fi

MUTATED_SEMANTIC_REFERENCE="$LOGDIR/metamath_statement_semantic_reference_v0.mutated.metta"
perl -0pe \
  's/\Q(MMSemanticConstant "(")\E/(MMSemanticConstant "mutated-open-paren")/' \
  "$SEMANTIC_REFERENCE" >"$MUTATED_SEMANTIC_REFERENCE"
[[ "$(grep -Fo '(MMSemanticConstant "mutated-open-paren")' \
      "$MUTATED_SEMANTIC_REFERENCE" | wc -l)" -eq 1 ]] ||
  fail "semantic-reference mutation was not activated exactly once"
run_semantic_agreement semantic-reference-mutation "$DEMO0" \
  metamath-test/demo0.mm "$DEMO0_HASH" \
  parity_logs/metamath_statement_ledger_v0/metamath_statement_semantic_reference_v0.mutated \
  '[False]'

if rg -n '^\s*\(=\s+\([^()[:space:]]+\?' \
    "$GRAMMAR" "$LEXER" "$ROOT/metamath_statement_ledger_v0.metta" \
    "$SEMANTICS" "$SEMANTIC_REFERENCE"; then
  fail "MeTTa definition uses a question-mark suffix"
fi

if rg -n '^import (Metamath|Mettapedia\.Languages\.Metamath)' \
    "$LEAN_ROOT/Mettapedia/GSLT/CheckedLanguage.lean" \
    "$LEAN_ROOT/Mettapedia/GSLT/Parsing/LanguageDefSyntaxCompiler.lean" \
    "$LEAN_ROOT/Mettapedia/GSLT/Parsing/LanguageDefSyntaxCorrespondence.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/SourceGSLT.lean"; then
  fail "syntax root or generic compiler imports Metamath semantics"
fi

if ! git -C "$CETTA_ROOT" diff --check -- \
    Makefile \
    experiments/gslt2parse_foundation/presentations/languages/metamath_appendix_e_v1.metta \
    lib/lib_parse_metamath.metta \
    lib/lib_parse_metamath_grammar_generated_v0.metta \
    tools/gslt2parse_source_certificate_v1.py \
    tools/test_gslt2parse_source_certificate_v1.py; then
  fail "Metamath grammar source has whitespace errors"
fi
if ! git -C "$AIHUB/Mettapedia" diff --check -- \
    MettaKernel/kernel/metamath_statement_ledger_v0.metta \
    MettaKernel/kernel/metamath_statement_semantics_v0.metta \
    MettaKernel/kernel/metamath_statement_semantic_reference_v0.metta \
    MettaKernel/kernel/setmm_propositional_idalt_slice_v0.mm \
    MettaKernel/kernel/run_metamath_statement_ledger_v0_gate.sh \
    lean/mettapedia/Mettapedia/Languages/Metamath/SourceGSLT.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/SourceGSLTMeTTaExport.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/SourceGSLTParserExport.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/VerifiedCheckerSemantics.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/SourceGSLTCheckerAlignment.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/SourceGSLTCheckedLanguage.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/MMLean4SemanticView.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/SourceGSLTSemanticOracle.lean \
    lean/mettapedia/Mettapedia/Languages/Metamath/SourceGSLTSemanticMeTTaExport.lean \
    lean/mettapedia/Mettapedia/GSLT/CheckedLanguage.lean \
    lean/mettapedia/Mettapedia/Languages/Megalodon/CheckedLanguageSkeleton.lean \
    lean/mettapedia/Mettapedia/GSLT/Parsing/LanguageDefSyntaxCompiler.lean \
    lean/mettapedia/Mettapedia/GSLT/Parsing/LanguageDefSyntaxCorrespondence.lean \
    lean/mettapedia/Mettapedia/OSLF/MeTTaIL/Syntax.lean; then
  fail "ledger source has whitespace errors"
fi

if rg -n '\bsorry\b|\badmit\b|_wanted\b|\bnative_decide\b|^\s*axiom\b' \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/SourceGSLT.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/SourceGSLTMeTTaExport.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/SourceGSLTParserExport.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/VerifiedCheckerSemantics.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/SourceGSLTCheckerAlignment.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/SourceGSLTCheckedLanguage.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/MMLean4SemanticView.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/SourceGSLTSemanticOracle.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Metamath/SourceGSLTSemanticMeTTaExport.lean" \
    "$LEAN_ROOT/Mettapedia/GSLT/CheckedLanguage.lean" \
    "$LEAN_ROOT/Mettapedia/Languages/Megalodon/CheckedLanguageSkeleton.lean" \
    "$LEAN_ROOT/Mettapedia/GSLT/Parsing/LanguageDefSyntaxCompiler.lean" \
    "$LEAN_ROOT/Mettapedia/GSLT/Parsing/LanguageDefSyntaxCorrespondence.lean"; then
  fail "source GSLT Lean files contain an unproved or disallowed shortcut"
fi

echo "METAMATH STATEMENT LEDGER V0 GATE: PASS (one generated GSLT grammar; 7 checked ordered ledgers; 7/7 exact object-level agreement with mm-lean4; authentic set.mm compressed theorem; exact normal/compressed claim and semantic agreement; 5 malformed sources rejected; wrong-label, DV, compressed-proof, declaration-order, tree, lexer, and semantic-reference mutations caught)"
