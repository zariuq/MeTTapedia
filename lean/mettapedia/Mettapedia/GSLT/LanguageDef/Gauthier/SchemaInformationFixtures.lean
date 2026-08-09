import Mettapedia.GSLT.LanguageDef.Gauthier.SchemaValueGate

/-!
# Cross-runtime fixtures for schema information and action evidence

This executable emits a small, deterministic JSONL contract for Lean, Python,
PeTTa, and CeTTa.  The rows exercise canonical role-indexed schema identity,
causal-root support, credal admission, three-channel action evidence, calibrated
information value, and the work-normalized four-cell gate.  Exact quantities
are encoded as signed numerator/positive-denominator pairs; consumers therefore
need no floating-point convention.

Every expected field below is backed by a theorem over the production
definitions.  The negative rows are deliberate boundaries, not malformed
inputs to be ignored.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierSchemaInformationFixtures

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open Mettapedia.GSLT.LanguageDef.GauthierPatternSupport
open Mettapedia.GSLT.LanguageDef.GauthierSchemaCredalBank
open Mettapedia.GSLT.LanguageDef.GauthierSchemaActionEvidence
open Mettapedia.GSLT.LanguageDef.GauthierActionEvidencePCBridge
open Mettapedia.InformationTheory.FiniteBrierInformation
open Mettapedia.GSLT.LanguageDef.GauthierSchemaValueGate

private def jsonEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | character => character.toString

private def jsonString (value : String) : String :=
  "\"" ++ String.join (value.toList.map jsonEscapeChar) ++ "\""

private def jsonBool (value : Bool) : String :=
  if value then "true" else "false"

private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def renderNatArray (values : List Nat) : String :=
  jsonArray (values.map toString)

private def roleName : HoleRole → String
  | .root => "root"
  | .code => "code"
  | .value => "value"

mutual

private def renderPattern : Pattern → String
  | .hole key =>
      "{" ++
        "\"kind\":\"hole\"," ++
        "\"role\":" ++ jsonString (roleName key.role) ++ "," ++
        "\"left\":" ++ renderNatArray (rpnTokens key.left) ++ "," ++
        "\"right\":" ++ renderNatArray (rpnTokens key.right) ++
      "}"
  | .node operation children =>
      "{" ++
        "\"kind\":\"node\"," ++
        "\"op_id\":" ++ toString operation ++ "," ++
        "\"children\":" ++ renderPatterns children ++
      "}"

private def renderPatterns (patterns : List Pattern) : String :=
  jsonArray (patterns.map renderPattern)

end

mutual

private def renderSchemaPattern : SchemaPattern → String
  | .hole role index =>
      "{" ++
        "\"kind\":\"hole\"," ++
        "\"role\":" ++ jsonString (roleName role) ++ "," ++
        "\"first_occurrence\":" ++ toString index ++
      "}"
  | .node operation children =>
      "{" ++
        "\"kind\":\"node\"," ++
        "\"op_id\":" ++ toString operation ++ "," ++
        "\"children\":" ++ renderSchemaPatterns children ++
      "}"

private def renderSchemaPatterns (patterns : List SchemaPattern) : String :=
  jsonArray (patterns.map renderSchemaPattern)

end


private def renderRatio (numerator : Int) (denominator : Nat) : String :=
  "{" ++
    "\"numerator\":" ++ toString numerator ++ "," ++
    "\"denominator\":" ++ toString denominator ++
  "}"

/-! ## Executable identity boundary -/

def rawSwapEqual : Bool :=
  decide (swappedRawLeft = swappedRawRight)

def canonicalSwapEqual : Bool :=
  decide (canonicalSchema swappedRawLeft = canonicalSchema swappedRawRight)

def typedRolesEqual : Bool :=
  decide (SchemaPattern.hole .code 0 = SchemaPattern.hole .value 0)

def erasedRolesEqual : Bool :=
  decide (eraseRoles (.hole .code 0) = eraseRoles (.hole .value 0))

/-- The executable identity row has both positive invariance and negative
boundaries: raw orientation is unstable and erasing roles is unsound. -/
theorem identityFixture_sound :
    rawSwapEqual = false ∧
      canonicalSwapEqual = true ∧
      typedRolesEqual = false ∧
      erasedRolesEqual = true := by
  simp [rawSwapEqual, canonicalSwapEqual, typedRolesEqual, erasedRolesEqual,
    swapped_lgg_raw_ne, swapped_lgg_canonical_eq,
    role_erasure_identifies_distinct_schemas]

/-! ## Executable causal-support boundary -/

def independentOneRootMatch : SourceMatch rootHolePattern where
  observation := ⟨one, 11, [1], 8⟩
  matching := oneRootMatch.matching

def rawSameRootRows : Nat :=
  rawMatchCount [zeroRootMatch, oneRootMatch]

def causalSameRootSupport : Nat :=
  (supportRoots [zeroRootMatch, oneRootMatch]).card

def independentRootSupport : Nat :=
  (supportRoots [zeroRootMatch, independentOneRootMatch]).card

/-- Two matching rows from one root count once; changing only the second
causal root makes the support exactly two. -/
theorem supportFixture_sound :
    rawSameRootRows = 2 ∧
      causalSameRootSupport = 1 ∧
      independentRootSupport = 2 := by
  constructor
  · exact raw_match_count_inflates_same_root.1
  constructor
  · exact raw_match_count_inflates_same_root.2
  · simp [independentRootSupport, supportRoots, zeroRootMatch,
      independentOneRootMatch]

/-! ## Credal bank and action-channel boundary -/

namespace BankControl

open Mettapedia.GSLT.LanguageDef.GauthierSchemaCredalBank.Control

/-- The three canonical control schemas exercise all bank outcomes. -/
theorem fixture_sound :
    SchemaPattern.hole .root 0 ∈
        robustSchemaBank controlFamily controlMeaning ∧
      SchemaPattern.hole .root 1 ∈
        provisionalSchemaBank controlFamily controlMeaning ∧
      SchemaPattern.hole .code 0 ∈
        rejectedSchemaBank controlFamily controlMeaning :=
  ⟨root_zero_is_robust, root_one_is_provisional, code_zero_is_rejected⟩

end BankControl

namespace ActionControl

open Mettapedia.GSLT.LanguageDef.GauthierSchemaActionEvidence.Control

def partialAction :=
  { positiveAction with verdict := .provablyPartial }

def undeterminedAction :=
  { positiveAction with verdict := .undeterminedAtBudget }

def positiveCount : Nat :=
  (correctedSchemaActionEvidence [positiveAction]).positive.counts actionZero

def partialPositiveCount : Nat :=
  (correctedSchemaActionEvidence [partialAction]).positive.counts actionZero

def partialNegativeCount : Nat :=
  (correctedSchemaActionEvidence [partialAction]).negative.counts actionZero

def undeterminedPositiveCount : Nat :=
  (correctedSchemaActionEvidence [undeterminedAction]).positive.counts actionZero

def undeterminedNegativeCount : Nat :=
  (correctedSchemaActionEvidence [undeterminedAction]).negative.counts actionZero

def undeterminedCount : Nat :=
  (correctedSchemaActionEvidence [undeterminedAction]).undetermined.counts actionZero

def duplicatePositiveCount : Nat :=
  (correctedSchemaActionEvidence [positiveAction, positiveAction]).positive.counts
    actionZero

/-- Compilation preserves positive, negative, and undetermined channels;
duplicating one causal observation cannot inflate the positive count. -/
theorem fixture_sound :
    positiveCount = 1 ∧
      partialPositiveCount = 0 ∧ partialNegativeCount = 1 ∧
      undeterminedPositiveCount = 0 ∧ undeterminedNegativeCount = 0 ∧
      undeterminedCount = 1 ∧ duplicatePositiveCount = 1 := by
  have positive := positiveAction_compiles_positive
  have partialProof := promoted_partial_is_negative partialAction rfl
  have undeterminedProof := promoted_undetermined_stays_undetermined
    undeterminedAction rfl
  have duplicate := correctedSchemaActionEvidence_duplicate positiveAction []
  constructor
  · exact positive
  constructor
  · exact partialProof.1
  constructor
  · exact partialProof.2
  constructor
  · exact undeterminedProof.1
  constructor
  · exact undeterminedProof.2.1
  constructor
  · exact undeterminedProof.2.2
  · unfold duplicatePositiveCount
    rw [duplicate]
    exact positive

end ActionControl

/-! ## Exact proper-score and value-gate rows -/

/-- Exact rational expectations used by every runtime: informative schemas
gain one half, irrelevant schemas gain zero, and an uncalibrated confident
forecast doubles fair Brier risk from one half to one. -/
theorem informationFixture_sound :
    brierInformationValue twoModeModel = 1 / 2 ∧
      brierInformationValue irrelevantSchemaModel = 0 ∧
      expectedBrier fairTruth fairTruth = 1 / 2 ∧
      expectedBrier fairTruth misleadingForecast = 1 := by
  exact ⟨twoMode_brierInformationValue_eq_half,
    irrelevantSchema_has_zero_brierInformationValue,
    misleading_uncalibrated_schema_increases_brierRisk.1,
    misleading_uncalibrated_schema_increases_brierRisk.2.1⟩

/-- Exact work-normalized values, interaction controls, and two incompatible
completions of the same three observed cells. -/
theorem valueFixture_sound :
    workNormalizedNetSchemaValue 2 3 2 2 1 5 = 1 / 5 ∧
      workNormalizedNetSchemaValue 2 3 2 4 1 5 = -(1 / 5) ∧
      schemaRuleInteraction 10 11 10 13 = 2 ∧
      schemaRuleInteraction 10 11 12 13 = 0 ∧
      schemaRuleInteraction 10 11 10 0 = -11 ∧
      schemaRuleInteraction 10 11 10 1 = -10 := by
  norm_num [workNormalizedNetSchemaValue, netSchemaValue,
    schemaRuleInteraction]

/-! ## Deterministic JSONL rendering -/

private def renderIdentityFixture : String :=
  "{" ++
    "\"kind\":\"schema_identity\"," ++
    "\"case\":\"input_swap_and_role_boundary\"," ++
    "\"raw_left\":" ++ renderPattern swappedRawLeft ++ "," ++
    "\"raw_right\":" ++ renderPattern swappedRawRight ++ "," ++
    "\"canonical_left\":" ++ renderSchemaPattern (canonicalSchema swappedRawLeft) ++ "," ++
    "\"canonical_right\":" ++ renderSchemaPattern (canonicalSchema swappedRawRight) ++ "," ++
    "\"raw_equal\":" ++ jsonBool rawSwapEqual ++ "," ++
    "\"canonical_equal\":" ++ jsonBool canonicalSwapEqual ++ "," ++
    "\"typed_code_value_equal\":" ++ jsonBool typedRolesEqual ++ "," ++
    "\"role_erased_code_value_equal\":" ++ jsonBool erasedRolesEqual ++
  "}"

private def renderSupportFixture : String :=
  "{" ++
    "\"kind\":\"causal_support\"," ++
    "\"case\":\"raw_rows_vs_source_roots\"," ++
    "\"same_root_rows\":[" ++
      "{\"program\":" ++ renderNatArray (rpnTokens zero) ++ ",\"root\":7}," ++
      "{\"program\":" ++ renderNatArray (rpnTokens one) ++ ",\"root\":7}]," ++
    "\"raw_match_count\":" ++ toString rawSameRootRows ++ "," ++
    "\"causal_root_count\":" ++ toString causalSameRootSupport ++ "," ++
    "\"independent_root_count\":" ++ toString independentRootSupport ++
  "}"

private def renderBankFixture : String :=
  "{" ++
    "\"kind\":\"credal_schema_bank\"," ++
    "\"cases\":[" ++
      "{\"schema\":{" ++
        "\"kind\":\"hole\",\"role\":\"root\",\"first_occurrence\":0}," ++
        "\"expected\":\"robust\"}," ++
      "{\"schema\":{" ++
        "\"kind\":\"hole\",\"role\":\"root\",\"first_occurrence\":1}," ++
        "\"expected\":\"provisional\"}," ++
      "{\"schema\":{" ++
        "\"kind\":\"hole\",\"role\":\"code\",\"first_occurrence\":0}," ++
        "\"expected\":\"rejected\"}]" ++
  "}"

private def renderActionFixture : String :=
  "{" ++
    "\"kind\":\"action_evidence\"," ++
    "\"action\":" ++ toString actionZero.val ++ "," ++
    "\"positive\":{" ++
      "\"positive\":" ++ toString ActionControl.positiveCount ++
      ",\"negative\":0,\"undetermined\":0}," ++
    "\"refutation\":{" ++
      "\"positive\":" ++ toString ActionControl.partialPositiveCount ++ "," ++
      "\"negative\":" ++ toString ActionControl.partialNegativeCount ++
      ",\"undetermined\":0}," ++
    "\"resource_boundary\":{" ++
      "\"positive\":" ++ toString ActionControl.undeterminedPositiveCount ++ "," ++
      "\"negative\":" ++ toString ActionControl.undeterminedNegativeCount ++ "," ++
      "\"undetermined\":" ++ toString ActionControl.undeterminedCount ++ "}," ++
    "\"duplicate_positive_count\":" ++
      toString ActionControl.duplicatePositiveCount ++ "," ++
    "\"rejected_schema_promotable\":false" ++
  "}"

private def renderInformationFixture : String :=
  "{" ++
    "\"kind\":\"proper_score_information\"," ++
    "\"informative_two_mode_value\":" ++ renderRatio 1 2 ++ "," ++
    "\"irrelevant_schema_value\":" ++ renderRatio 0 1 ++ "," ++
    "\"fair_bayes_risk\":" ++ renderRatio 1 2 ++ "," ++
    "\"misleading_uncalibrated_risk\":" ++ renderRatio 1 1 ++
  "}"

private def renderValueFixture : String :=
  "{" ++
    "\"kind\":\"schema_value_gate\"," ++
    "\"accepted_net_value\":" ++ renderRatio 1 5 ++ "," ++
    "\"excess_work_net_value\":" ++ renderRatio (-1) 5 ++ "," ++
    "\"positive_interaction\":2," ++
    "\"additive_static_interaction\":0," ++
    "\"same_three_cells\":{" ++
      "\"bp_off\":10,\"bp_on\":11,\"pc_off\":10}," ++
    "\"completion_interactions\":[" ++
      "{\"pc_on\":0,\"interaction\":-11}," ++
      "{\"pc_on\":1,\"interaction\":-10}]" ++
  "}"

private def metaFixture : String :=
  "{" ++
    "\"kind\":\"meta\"," ++
    "\"schema\":\"gslt.schema_information.v1\"," ++
    "\"runtimes\":[\"lean\",\"python\",\"petta\",\"cetta\"]," ++
    "\"exact_number_encoding\":\"signed_numerator_positive_denominator\"," ++
    "\"fixture_count\":6" ++
  "}"

def renderFixtures : String :=
  String.intercalate "\n"
    [metaFixture, renderIdentityFixture, renderSupportFixture,
      renderBankFixture, renderActionFixture, renderInformationFixture,
      renderValueFixture] ++ "\n"

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["write", outputPath] =>
      let output := renderFixtures
      IO.FS.writeFile outputPath output
      IO.println s!"wrote {output.toUTF8.size} bytes to {outputPath}"
      pure 0
  | ["check", fixturePath] =>
      let actual ← IO.FS.readFile fixturePath
      if actual = renderFixtures then
        IO.println s!"fixture parity OK: {fixturePath}"
        pure 0
      else
        IO.eprintln s!"fixture drift: regenerate {fixturePath} from SchemaInformationFixtures.lean"
        pure 1
  | _ =>
      IO.eprintln "usage: SchemaInformationFixtures (write|check) <fixture.jsonl>"
      pure 1

#print axioms identityFixture_sound
#print axioms supportFixture_sound
#print axioms BankControl.fixture_sound
#print axioms ActionControl.fixture_sound
#print axioms informationFixture_sound
#print axioms valueFixture_sound

end Mettapedia.GSLT.LanguageDef.GauthierSchemaInformationFixtures

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.GauthierSchemaInformationFixtures.main arguments
