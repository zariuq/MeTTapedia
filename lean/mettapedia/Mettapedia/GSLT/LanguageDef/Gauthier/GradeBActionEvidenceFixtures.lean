/-
# Deterministic conformance fixtures for Grade-B action evidence

The executable below serializes the full trusted path from ranked Gauthier
programs through structural sharing, role-aware anti-unification, partial
decoder alignment, provenance-correct evidence, and the checker-masked exact
action distribution.  `write` creates the byte-pinned JSONL artifact and
`check` rejects any drift.
-/

import Mettapedia.GSLT.LanguageDef.Gauthier.GradeBActionEvidence

namespace Mettapedia.GSLT.LanguageDef.GauthierGradeBActionEvidenceFixtures

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierSkeletonMask
open Mettapedia.GSLT.LanguageDef.GauthierProgramDAG
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
open Mettapedia.GSLT.LanguageDef.GauthierPartialPostfixAlignment
open Mettapedia.GSLT.LanguageDef.GauthierAlignmentEvidence
open Mettapedia.GSLT.LanguageDef.GauthierActionEvidencePCBridge
open Mettapedia.GSLT.LanguageDef.GauthierGradeBActionEvidence
open Mettapedia.GSLT.LanguageDef.GauthierProbeRigidity
open Mettapedia.PLN.Bridges.PredictiveCoding
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet

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

private def renderIntArray (values : List Int) : String :=
  jsonArray (values.map toString)

private def roleName : HoleRole → String
  | .root => "root"
  | .code => "code"
  | .value => "value"

private def verdictName : TotalityVerdict → String
  | .provablyTotal => "positive"
  | .provablyPartial => "negative"
  | .undeterminedAtBudget => "undetermined"

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

  private def renderPatterns : List Pattern → String
    | [] => "[]"
    | patterns => jsonArray (patterns.map renderPattern)

end

mutual

  private def patternHoleKeys : Pattern → List HoleKey
    | .hole key => [key]
    | .node _ children => patternListHoleKeys children

  private def patternListHoleKeys : List Pattern → List HoleKey
    | [] => []
    | pattern :: rest => patternHoleKeys pattern ++ patternListHoleKeys rest

end

private def renderSubstitutionRow (key : HoleKey) : String :=
  "{" ++
    "\"role\":" ++ jsonString (roleName key.role) ++ "," ++
    "\"key_left\":" ++ renderNatArray (rpnTokens key.left) ++ "," ++
    "\"key_right\":" ++ renderNatArray (rpnTokens key.right) ++ "," ++
    "\"left_image\":" ++ renderNatArray (rpnTokens (leftSubstitution key)) ++ "," ++
    "\"right_image\":" ++ renderNatArray (rpnTokens (rightSubstitution key)) ++
  "}"

private def renderSubstitutions (pattern : Pattern) : String :=
  jsonArray ((patternHoleKeys pattern).eraseDups.map renderSubstitutionRow)

private def renderSharedNode (node : SharedNode) : String :=
  "{" ++
    "\"structural_id\":" ++ renderNatArray node.structuralId ++ "," ++
    "\"op_id\":" ++ toString node.opId ++ "," ++
    "\"child_ids\":" ++ jsonArray (node.childIds.map renderNatArray) ++
  "}"

private def renderSharedDAG (program : Prog) : String :=
  let dag := compress program
  "{" ++
    "\"root_id\":" ++ renderNatArray dag.rootId ++ "," ++
    "\"nodes\":" ++
      jsonArray ((occurrenceNodes program).eraseDups.map renderSharedNode) ++
  "}"

private def renderCoordinate (coordinate : AlignmentCoordinate) : String :=
  "{" ++
    "\"forest_index\":" ++ toString coordinate.forestIndex ++ "," ++
    "\"path\":" ++ renderNatArray coordinate.path ++ "," ++
    "\"role\":" ++ jsonString (roleName coordinate.role) ++ "," ++
    "\"exact\":" ++ jsonBool coordinate.exact ++
  "}"

private def renderAlignment (left right : Prog) : String :=
  match alignForests orgMemoSignature [left] [right] with
  | none => "null"
  | some alignment =>
      "{" ++
        "\"score\":" ++ toString alignment.score ++ "," ++
        "\"patterns\":" ++ renderPatterns alignment.patterns ++ "," ++
        "\"coordinates\":" ++
          jsonArray (alignment.coordinates.map renderCoordinate) ++
      "}"

private def renderMask (maxLen : Nat) (decoderPrefix : List Nat) : String :=
  match run orgMemoSignature (decoderPrefix.map Int.ofNat) (initial maxLen) with
  | none =>
      "{" ++
        "\"accepted\":false," ++
        "\"prefix\":" ++ renderNatArray decoderPrefix ++
      "}"
  | some state =>
      "{" ++
        "\"accepted\":true," ++
        "\"prefix\":" ++ renderNatArray decoderPrefix ++ "," ++
        "\"depth\":" ++ toString state.depth ++ "," ++
        "\"tokens_emitted\":" ++ toString state.tokensEmitted ++ "," ++
        "\"max_len\":" ++ toString state.maxLen ++ "," ++
        "\"legal_tokens\":" ++ renderIntArray (legalTokens orgMemoSignature state) ++
      "}"

abbrev ObservationSpec := Nat × TotalityVerdict × Nat × Nat

structure FixtureCase where
  name : String
  left : Prog
  right : Prog
  decoderPrefix : List Nat
  observations : List ObservationSpec
  illegalTransferCanary : Bool := false
  boundedClassCanary : Bool := false

private def observationCoordinate (left right : Prog) : Option AlignmentCoordinate := do
  let alignment ← alignForests orgMemoSignature [left] [right]
  alignment.coordinates.head?

private def observationFromSpec (fixture : FixtureCase) (query : ActionQuery) :
    ObservationSpec → Option ActionObservation
  | (action, verdict, sourceLineage, sourceRoot) => do
      let coordinate ← observationCoordinate fixture.left fixture.right
      if haction : action < operatorCount then
        pure
          { query
            alignmentCoordinate := coordinate
            structuralSource := rpnTokens fixture.right
            action := ⟨action, haction⟩
            verdict
            sourceLineage
            sourceRoot }
      else none

private def fixtureObservations (fixture : FixtureCase) : List ActionObservation :=
  let query : ActionQuery := ⟨0, fixture.decoderPrefix⟩
  fixture.observations.filterMap (observationFromSpec fixture query)

private def evidenceCounts (evidence : GradedActionEvidence operatorCount)
    (select : GradedActionEvidence operatorCount → MultiEvidence operatorCount) :
    List Nat :=
  (List.finRange operatorCount).map fun action => (select evidence).counts action

/-- Evidence counts in the exact integer scale used by the categorical
register.  Dividing these counts by `oppositionScale` recovers the data-only
evidence mass: positive observations contribute one unit to their action,
while one refutation contributes one unit in total across all alternatives. -/
private def scaledEvidenceCounts
    (evidence : GradedActionEvidence operatorCount) : List Nat :=
  (List.finRange operatorCount).map fun action =>
    oppositionScale * evidence.positive.counts action +
      (evidence.negative.total - evidence.negative.counts action)

private def scaledConcentrations
    (evidence : GradedActionEvidence operatorCount) : List Nat :=
  (List.finRange operatorCount).map (scaledActionConcentration evidence)

private def renderObservation (observation : ActionObservation) : String :=
  "{" ++
    "\"action\":" ++ toString observation.action.val ++ "," ++
    "\"verdict\":" ++ jsonString (verdictName observation.verdict) ++ "," ++
    "\"source_lineage\":" ++ toString observation.sourceLineage ++ "," ++
    "\"source_root\":" ++ toString observation.sourceRoot ++ "," ++
    "\"coordinate\":" ++ renderCoordinate observation.alignmentCoordinate ++
  "}"

private def renderExactProbability (probability : ExactActionProbability) : String :=
  "{" ++
    "\"action\":" ++ toString probability.action ++ "," ++
    "\"legal\":" ++ jsonBool probability.legal ++ "," ++
    "\"numerator\":" ++ toString probability.numerator ++ "," ++
    "\"denominator\":" ++ toString probability.denominator ++
  "}"

private def illegalTransferRejected : Bool :=
  (candidateForEvent orgMemoSignature [] (initial 8) illegalEvent).isNone

private def boundedContinuationsDiffer : Bool :=
  (rpnTokens probeId).drop 1 != (rpnTokens probeZeroAfterZero).drop 1

private def renderFixture (fixture : FixtureCase) : String :=
  let pattern := lgg orgMemoSignature .root fixture.left fixture.right
  let observations := fixtureObservations fixture
  let query : ActionQuery := ⟨0, fixture.decoderPrefix⟩
  let evidence := alignedRepresentativeEvidence observations query
  let distribution :=
    match run orgMemoSignature (fixture.decoderPrefix.map Int.ofNat) (initial 8) with
    | none => []
    | some state => exactMaskedActionDistribution evidence state
  "{" ++
    "\"kind\":\"case\"," ++
    "\"name\":" ++ jsonString fixture.name ++ "," ++
    "\"original_programs\":{" ++
      "\"left\":" ++ renderNatArray (rpnTokens fixture.left) ++ "," ++
      "\"right\":" ++ renderNatArray (rpnTokens fixture.right) ++ "}," ++
    "\"shared_dags\":{" ++
      "\"left\":" ++ renderSharedDAG fixture.left ++ "," ++
      "\"right\":" ++ renderSharedDAG fixture.right ++ "}," ++
    "\"lgg\":" ++ renderPattern pattern ++ "," ++
    "\"substitutions\":" ++ renderSubstitutions pattern ++ "," ++
    "\"alignment\":" ++ renderAlignment fixture.left fixture.right ++ "," ++
    "\"parser_prefix\":" ++ renderMask 8 fixture.decoderPrefix ++ "," ++
    "\"transported_observations\":" ++
      jsonArray (observations.map renderObservation) ++ "," ++
    "\"transported_positive_counts\":" ++
      renderNatArray (evidenceCounts evidence (fun value => value.positive)) ++ "," ++
    "\"transported_negative_counts\":" ++
      renderNatArray (evidenceCounts evidence (fun value => value.negative)) ++ "," ++
    "\"transported_undetermined_counts\":" ++
      renderNatArray (evidenceCounts evidence (fun value => value.undetermined)) ++ "," ++
    "\"overlap_corrected_categorical_evidence\":" ++
      "{" ++
        "\"scale_denominator\":" ++ toString oppositionScale ++ "," ++
        "\"scaled_counts\":" ++ renderNatArray (scaledEvidenceCounts evidence) ++ "," ++
        "\"scaled_concentrations\":" ++
          renderNatArray (scaledConcentrations evidence) ++
      "}," ++
    "\"final_masked_action_distribution\":" ++
      jsonArray (distribution.map renderExactProbability) ++ "," ++
    "\"illegal_transfer_rejected\":" ++
      jsonBool (fixture.illegalTransferCanary && illegalTransferRejected) ++ "," ++
    "\"bounded_class_continuations\":{" ++
      "\"enabled\":" ++ jsonBool fixture.boundedClassCanary ++ "," ++
      "\"left\":" ++ renderNatArray ((rpnTokens fixture.left).drop 1) ++ "," ++
      "\"right\":" ++ renderNatArray ((rpnTokens fixture.right).drop 1) ++ "," ++
      "\"different\":" ++
        jsonBool (fixture.boundedClassCanary && boundedContinuationsDiffer) ++ "}" ++
  "}"

private def addZeroZero : Prog := .node 3 [zero, zero]
private def addZeroOneProgram : Prog := .node 3 [zero, one]
private def roleLeft : Prog := .node 9 [zero, zero, zero]
private def roleRight : Prog := .node 9 [one, one, one]

def fixtureCases : List FixtureCase :=
  [ { name := "exact_identity"
      left := addZeroOneProgram, right := addZeroOneProgram, decoderPrefix := [0]
      observations := [(0, .provablyTotal, 10, 10)] }
  , { name := "one_mismatch"
      left := addZeroZero, right := addZeroOneProgram, decoderPrefix := [0]
      observations := [(1, .provablyTotal, 11, 11)] }
  , { name := "repeated_mismatch"
      left := repeatedLeft, right := repeatedRight, decoderPrefix := [0]
      observations := [(1, .provablyTotal, 12, 12)] }
  , { name := "role_conflict"
      left := roleLeft, right := roleRight, decoderPrefix := [0]
      observations := [] }
  , { name := "shared_subtree"
      left := addZeroZero, right := addZeroZero, decoderPrefix := [0]
      observations := [(0, .provablyTotal, 13, 13)] }
  , { name := "illegal_transferred_token"
      left := zero, right := one, decoderPrefix := []
      observations := [], illegalTransferCanary := true }
  , { name := "duplicated_source"
      left := addZeroZero, right := addZeroOneProgram, decoderPrefix := [0]
      observations :=
        [(0, .provablyTotal, 20, 7), (0, .provablyTotal, 21, 7)] }
  , { name := "refutation"
      left := addZeroZero, right := addZeroOneProgram, decoderPrefix := [0]
      observations := [(0, .provablyPartial, 30, 30)] }
  , { name := "undetermined_result"
      left := addZeroZero, right := addZeroOneProgram, decoderPrefix := [0]
      observations := [(0, .undeterminedAtBudget, 40, 40)] }
  , { name := "bounded_equivalent_different_actions"
      left := probeId, right := probeZeroAfterZero, decoderPrefix := [10]
      observations :=
        [(0, .provablyTotal, 50, 50), (10, .provablyTotal, 51, 51)]
      boundedClassCanary := true }
  ]

private def renderPipelineCanary : String :=
  match sharedPositiveStep with
  | none =>
      "{\"kind\":\"pipeline_canary\",\"accepted\":false}"
  | some result =>
      "{" ++
        "\"kind\":\"pipeline_canary\"," ++
        "\"accepted\":true," ++
        "\"decoder_prefix\":" ++ renderNatArray result.query.decoderPrefix ++ "," ++
        "\"legal_tokens\":" ++ renderIntArray result.legalTokens ++ "," ++
        "\"observations\":" ++
          jsonArray (result.observations.map renderObservation) ++ "," ++
        "\"positive_counts\":" ++
          renderNatArray (evidenceCounts result.evidence (fun value => value.positive)) ++ "," ++
        "\"negative_counts\":" ++
          renderNatArray (evidenceCounts result.evidence (fun value => value.negative)) ++ "," ++
        "\"final_masked_action_distribution\":" ++
          jsonArray (result.actionDistribution.map renderExactProbability) ++
      "}"

private def metaFixture : String :=
  "{" ++
    "\"kind\":\"meta\"," ++
    "\"schema\":\"gslt.grade_b_action_evidence.v1\"," ++
    "\"signature\":\"orgMemoSignature\"," ++
    "\"operator_count\":" ++ toString operatorCount ++ "," ++
    "\"case_count\":" ++ toString fixtureCases.length ++
  "}"

def renderFixtures : String :=
  String.intercalate "\n"
    (metaFixture :: fixtureCases.map renderFixture ++ [renderPipelineCanary]) ++ "\n"

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
        IO.eprintln s!"fixture drift: regenerate {fixturePath} from GradeBActionEvidenceFixtures.lean"
        pure 1
  | _ =>
      IO.eprintln "usage: GradeBActionEvidenceFixtures (write|check) <fixture.jsonl>"
      pure 1

end Mettapedia.GSLT.LanguageDef.GauthierGradeBActionEvidenceFixtures

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.GauthierGradeBActionEvidenceFixtures.main arguments
