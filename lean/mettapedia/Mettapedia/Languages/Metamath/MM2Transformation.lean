import Mettapedia.GSLT.LanguageDef.LanguageDefTransformation
import Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
import Mettapedia.Languages.Metamath.MM2DataEncoding
import Mettapedia.Languages.Metamath.MM2NormalDataRows
import Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
import Mettapedia.Languages.Metamath.MM2Target
import Mettapedia.Languages.Metamath.SourceStateNativeTypes
import Mettapedia.Languages.ProcessCalculi.MORK.AuthoredContextBridge
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternFactorOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.InvertibleHead
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes

/-!
# Authored Metamath to MM2 transformation

This module starts the executable compiler at its proper boundary.  Its source
input is an admitted authored Metamath scope, including its generated inference
language.  Its target input is the existing reflective MM2 GSLT together
with the ordinary MM2 surface renderer.  Neither input is replaced by a file
name, digest, or implementation callback.

The first machine slice handles native active-hypothesis proof steps.  The
database remains indexed target data.  One generic MM2 rule reads that data and
dynamic linked proof-token rows, advances explicit control, and retains the
source proof occurrence in the produced stack cell.  Assertion application and
compressed-proof actions extend this same machine; this file does not identify
the current slice with a complete Metamath verifier.
-/

namespace Mettapedia.Languages.Metamath.MM2Transformation

open Mettapedia.GSLT.ProofRelevant
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.Metamath.SourceStateGSLT
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-! ## Supplied Metamath verifier GSLT -/

/-- A compiler input that exposes the authored Metamath state calculus
through an operational GSLT and an exact proof-relevant translation.  The
translation prevents an endpoint-correct encoding from erasing distinct
source transition occurrences.  The finite operation spine is inspectable
compiler input; it must cover every authored state action and cannot contain
duplicate operation occurrences. -/
structure MetamathVerifierGSLT where
  operational : ProofRelevantGSLT
  exact : ExactTranslation SourceStateGSLT.system operational
  operations : List SourceOperation
  operations_nodup : operations.Nodup
  action_operation_mem : ∀ action : StateAction,
    action.operation ∈ operations

namespace MetamathVerifierGSLT

def embedState (source : MetamathVerifierGSLT) :
    SourceState → source.operational.theory.Term :=
  source.exact.toTranslation.mapTerm

/-- Exact evidence fibres imply exact extensional steps at every pair of
embedded source states. -/
theorem step_iff (sourceGSLT : MetamathVerifierGSLT)
    (source target : SourceState) :
    sourceGSLT.operational.theory.Step
        (sourceGSLT.embedState source) (sourceGSLT.embedState target) ↔
      SourceStateGSLT.theory.Step source target := by
  constructor
  · intro targetStep
    obtain ⟨targetEvidence⟩ :=
      sourceGSLT.operational.steps.witness targetStep
    exact SourceStateGSLT.system.steps.erase
      ((sourceGSLT.exact.evidenceEquiv source target).symm targetEvidence)
  · intro sourceStep
    obtain ⟨sourceEvidence⟩ := SourceStateGSLT.system.steps.witness sourceStep
    exact sourceGSLT.operational.steps.erase
      (sourceGSLT.exact.toTranslation.mapEvidence sourceEvidence)

/-- Every compiler input exposes the exact authored occurrence fibre at fixed
source endpoints; endpoint agreement alone is not an admissible substitute. -/
def evidenceFibreEquiv (sourceGSLT : MetamathVerifierGSLT)
    (source target : SourceState) :
    SourceStateGSLT.TransitionEvidence source target ≃
      sourceGSLT.operational.steps.Evidence
        (sourceGSLT.embedState source) (sourceGSLT.embedState target) :=
  sourceGSLT.exact.evidenceEquiv source target

/-- Every admissible verifier GSLT covers the normal-proof operation.
This is forced by the authored action family, rather than assumed by the
normal-slice transformer. -/
theorem normal_operation_mem (sourceGSLT : MetamathVerifierGSLT)
    (label : String)
    (formula : Mettapedia.Languages.Metamath.InferenceEncoding.ConstantHeadedFormula)
    (proofLabels : List String) :
    SourceOperation.checkTheoremNormal ∈ sourceGSLT.operations := by
  simpa [StateAction.operation] using
    sourceGSLT.action_operation_mem
      (.theoremNormal label formula proofLabels)

/-- A purported verifier input whose operation spine omits normal proofs is
rejected by the source-language contract. -/
theorem no_input_without_normal_operation
    (sourceGSLT : MetamathVerifierGSLT)
    (missing : SourceOperation.checkTheoremNormal ∉ sourceGSLT.operations) :
    False := by
  exact missing
    (sourceGSLT.normal_operation_mem "" ⟨"", []⟩ [])

end MetamathVerifierGSLT

/-- The repository's authored source-state GSLT as a verifier
compiler input. -/
def authoredMetamathVerifierGSLT : MetamathVerifierGSLT where
  operational := SourceStateGSLT.system
  exact := ExactTranslation.id SourceStateGSLT.system
  operations := SourceStateGSLT.stateOperations
  operations_nodup := by decide
  action_operation_mem := SourceStateGSLT.action_operation_mem_stateOperations

/-- OSLF is applied to the actual supplied verifier GSLT.  Its exact-target
native type agrees precisely with the authored Metamath state transition on
the embedded source image. -/
theorem MetamathVerifierGSLT.native_type_iff_source_step
    (sourceGSLT : MetamathVerifierGSLT) (source target : SourceState) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      sourceGSLT.operational.theory).satisfies
        (sourceGSLT.embedState source)
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
          sourceGSLT.operational.theory
          (sourceGSLT.embedState target)).pred ↔
      SourceStateGSLT.theory.Step source target := by
  exact
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.satisfies_exactTargetNativeType_iff_step
      sourceGSLT.operational.theory (sourceGSLT.embedState source)
      (sourceGSLT.embedState target)).trans
      (sourceGSLT.step_iff source target)

/-! ## Database rows read by the generic machine -/

@[simp] theorem hypothesisLookupRows_length
    (scopeOwner : Atom) (state : SourceState) :
    (hypothesisLookupRows scopeOwner state).length =
      state.activeHypotheses.length := by
  simp [hypothesisLookupRows]

/-! ## Source-derived assertion execution indexes -/

/-- Directly supplied MM2 caller-DV rows denote exactly the symmetric
relation generated by the supplied ordered source pair list.  Later verifier
traces use this theorem in both directions, so a forged row cannot become a
trusted disjointness witness. -/
theorem callerDVRow_mem_callerDVRowsOfPairs_iff (scopeOwner : Atom)
    (pairs : List (String × String)) (left right : String) :
    callerDVRow scopeOwner left right ∈ callerDVRowsOfPairs scopeOwner pairs ↔
      DVRelation pairs left right := by
  simp only [callerDVRowsOfPairs, List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨rows, ⟨pair, pair_mem, rfl⟩, row_mem⟩
    rcases pair with ⟨pairLeft, pairRight⟩
    simp only [callerDVRowsForPair, List.mem_cons] at row_mem
    rcases row_mem with forward | reverse
    · have encodedNames :
          stringAtom left = stringAtom pairLeft ∧
            stringAtom right = stringAtom pairRight := by
        simpa [callerDVRow] using forward
      have leftName := stringAtom_injective encodedNames.1
      have rightName := stringAtom_injective encodedNames.2
      subst pairLeft
      subst pairRight
      exact Or.inl pair_mem
    · have encodedNames :
          stringAtom left = stringAtom pairRight ∧
            stringAtom right = stringAtom pairLeft := by
        simpa [callerDVRow] using reverse
      have leftName := stringAtom_injective encodedNames.1
      have rightName := stringAtom_injective encodedNames.2
      subst pairRight
      subst pairLeft
      exact Or.inr pair_mem
  · intro relation
    rcases relation with forward | reverse
    · refine ⟨callerDVRowsForPair scopeOwner (left, right), ?_, ?_⟩
      · exact ⟨(left, right), forward, rfl⟩
      · simp [callerDVRowsForPair]
    · refine ⟨callerDVRowsForPair scopeOwner (right, left), ?_, ?_⟩
      · exact ⟨(right, left), reverse, rfl⟩
      · simp [callerDVRowsForPair]

/-- The target lookup table represents exactly the source proof-facing
symmetric DV relation.  In particular, emitting both orientations does not
invent any caller obligation that the admitted source state did not license. -/
theorem callerDVRow_mem_callerDVRows_iff (scopeOwner : Atom)
    (state : SourceState) (left right : String) :
    callerDVRow scopeOwner left right ∈ callerDVRows scopeOwner state ↔
      DVRelation state.proofDistinctVariables left right := by
  exact callerDVRow_mem_callerDVRowsOfPairs_iff scopeOwner
    state.proofDistinctVariables left right

/-- Source-indexed classification of every derived row for one assertion.
This predicate is stated directly over the authored assertion fields rather
than by referring back to `assertionExecutionRowsFor`; it is the reflection
boundary used by later operational proofs. -/
def AssertionExecutionRowFor (scopeOwner : Atom) (assertionPosition : Nat)
    (assertion : SourceAssertion) (row : Atom) : Prop :=
  assertionHeaderRow scopeOwner assertionPosition assertion = row ∨
  (∃ (position : Nat) (inBounds : position < assertion.hypotheses.length),
    assertionHypothesisRow scopeOwner assertion position
      assertion.hypotheses[position] = row) ∨
  (∃ (position : Nat) (_inBounds : position < assertion.hypotheses.length),
    assertionHypothesisSuccessorRow scopeOwner assertion position = row) ∨
  assertionDVHeaderRow scopeOwner assertion = row ∨
  (∃ (position : Nat)
      (inBounds : position < assertion.frame.distinctVariables.length),
    assertionDVPairRow scopeOwner assertion position
      assertion.frame.distinctVariables[position] = row) ∨
  (∃ (position : Nat)
      (_inBounds : position < assertion.frame.distinctVariables.length),
    (.expression
      [.symbol "mm-assertion-dv-successor", scopeOwner,
        stringAtom assertion.label, natAtom position,
        natAtom (position + 1)] : Atom) = row) ∨
  assertionResultRow scopeOwner assertion = row

/-- One derived assertion row is licensed by an exact occurrence of an
assertion in the admitted ordered source database. -/
def AssertionExecutionRowFrom (scopeOwner : Atom) (state : SourceState)
    (row : Atom) : Prop :=
  ∃ (assertionPosition : Nat)
      (inBounds : assertionPosition < state.assertions.length),
    AssertionExecutionRowFor scopeOwner assertionPosition
      state.assertions[assertionPosition] row

/-- A source-licensed caller-DV lookup row, stated independently of the
concrete list construction. -/
def CallerDVRowFrom (scopeOwner : Atom) (state : SourceState)
    (row : Atom) : Prop :=
  ∃ left right,
    DVRelation state.proofDistinctVariables left right ∧
      callerDVRow scopeOwner left right = row

/-- Exact source classification of every datum read by the normal assertion
machine. -/
def NormalExecutionRowFrom (scopeOwner : Atom) (state : SourceState)
    (row : Atom) : Prop :=
  CallerDVRowFrom scopeOwner state row ∨
    AssertionExecutionRowFrom scopeOwner state row

theorem mem_assertionExecutionRowsFor_iff (scopeOwner : Atom)
    (assertionPosition : Nat) (assertion : SourceAssertion) (row : Atom) :
    row ∈ assertionExecutionRowsFor scopeOwner assertionPosition assertion ↔
      AssertionExecutionRowFor scopeOwner assertionPosition assertion row := by
  simp [assertionExecutionRowsFor, AssertionExecutionRowFor,
    assertionHypothesisRows, assertionHypothesisSuccessorRows,
    assertionDVPairRows, assertionDVSuccessorRows, List.mem_mapIdx, eq_comm]

theorem mem_assertionExecutionRows_iff (scopeOwner : Atom)
    (state : SourceState) (row : Atom) :
    row ∈ assertionExecutionRows scopeOwner state ↔
      AssertionExecutionRowFrom scopeOwner state row := by
  simp only [assertionExecutionRows, List.mem_flatten, List.mem_mapIdx,
    AssertionExecutionRowFrom]
  constructor
  · rintro ⟨rows, ⟨position, inBounds, rfl⟩, row_mem⟩
    exact ⟨position, inBounds,
      (mem_assertionExecutionRowsFor_iff scopeOwner position
        state.assertions[position] row).mp row_mem⟩
  · rintro ⟨position, inBounds, licensed⟩
    exact
      ⟨assertionExecutionRowsFor scopeOwner position
          state.assertions[position],
        ⟨position, inBounds, rfl⟩,
        (mem_assertionExecutionRowsFor_iff scopeOwner position
          state.assertions[position] row).mpr licensed⟩

theorem mem_callerDVRows_iff (scopeOwner : Atom) (state : SourceState)
    (row : Atom) :
    row ∈ callerDVRows scopeOwner state ↔
    CallerDVRowFrom scopeOwner state row := by
  simp only [callerDVRows, callerDVRowsOfPairs, List.mem_flatten, List.mem_map,
    CallerDVRowFrom]
  constructor
  · rintro ⟨rows, ⟨pair, pair_mem, rfl⟩, row_mem⟩
    rcases pair with ⟨left, right⟩
    simp only [callerDVRowsForPair, List.mem_cons, List.not_mem_nil,
      or_false] at row_mem
    rcases row_mem with forward | reverse
    · exact ⟨left, right, Or.inl pair_mem, forward.symm⟩
    · exact ⟨right, left, Or.inr pair_mem, reverse.symm⟩
  · rintro ⟨left, right, relation, rfl⟩
    rcases relation with forward | reverse
    · exact
        ⟨callerDVRowsForPair scopeOwner (left, right),
          ⟨(left, right), forward, rfl⟩,
          by simp [callerDVRowsForPair]⟩
    · exact
        ⟨callerDVRowsForPair scopeOwner (right, left),
          ⟨(right, left), reverse, rfl⟩,
          by simp [callerDVRowsForPair]⟩

/-- The compiler's complete derived assertion data is neither missing nor
invented: list membership is exactly the source-indexed classification. -/
theorem mem_normalExecutionRows_iff (scopeOwner : Atom)
    (state : SourceState) (row : Atom) :
    row ∈ normalExecutionRows scopeOwner state ↔
      NormalExecutionRowFrom scopeOwner state row := by
  simp [normalExecutionRows, NormalExecutionRowFrom,
    mem_callerDVRows_iff, mem_assertionExecutionRows_iff]

/-- Every header consumed by the assertion-entry rule comes from an actual
ordered assertion occurrence in the supplied source state. -/
theorem assertionHeaderRow_mem_normalExecutionRows (scopeOwner : Atom)
    (state : SourceState) (assertionPosition : Nat)
    (inBounds : assertionPosition < state.assertions.length) :
    assertionHeaderRow scopeOwner assertionPosition
        state.assertions[assertionPosition] ∈
      normalExecutionRows scopeOwner state := by
  apply (mem_normalExecutionRows_iff scopeOwner state _).2
  exact Or.inr ⟨assertionPosition, inBounds, Or.inl rfl⟩

/-- Every cursor edge used by the pop loop is likewise derived from the exact
ordered hypothesis list of one admitted source assertion. -/
theorem assertionHypothesisSuccessorRow_mem_normalExecutionRows
    (scopeOwner : Atom) (state : SourceState) (assertionPosition : Nat)
    (assertionInBounds : assertionPosition < state.assertions.length)
    (hypothesisPosition : Nat)
    (hypothesisInBounds :
      hypothesisPosition <
        state.assertions[assertionPosition].hypotheses.length) :
    assertionHypothesisSuccessorRow scopeOwner
        state.assertions[assertionPosition] hypothesisPosition ∈
      normalExecutionRows scopeOwner state := by
  apply (mem_normalExecutionRows_iff scopeOwner state _).2
  exact Or.inr ⟨assertionPosition, assertionInBounds,
    Or.inr (Or.inr (Or.inl
      ⟨hypothesisPosition, hypothesisInBounds, rfl⟩))⟩

/-- Every hypothesis datum consumed by either assertion-hypothesis rule is
the exact indexed occurrence in an admitted source assertion. -/
theorem assertionHypothesisRow_mem_normalExecutionRows
    (scopeOwner : Atom) (state : SourceState) (assertionPosition : Nat)
    (assertionInBounds : assertionPosition < state.assertions.length)
    (hypothesisPosition : Nat)
    (hypothesisInBounds :
      hypothesisPosition <
        state.assertions[assertionPosition].hypotheses.length) :
    assertionHypothesisRow scopeOwner state.assertions[assertionPosition]
        hypothesisPosition
        state.assertions[assertionPosition].hypotheses[hypothesisPosition] ∈
      normalExecutionRows scopeOwner state := by
  apply (mem_normalExecutionRows_iff scopeOwner state _).2
  exact Or.inr ⟨assertionPosition, assertionInBounds,
    Or.inr (Or.inl
      ⟨hypothesisPosition, hypothesisInBounds, rfl⟩)⟩

@[simp] theorem assertionHypothesisRows_length (scopeOwner : Atom)
    (assertion : SourceAssertion) :
    (assertionHypothesisRows scopeOwner assertion).length =
      assertion.hypotheses.length := by
  simp [assertionHypothesisRows]

@[simp] theorem assertionHypothesisSuccessorRows_length (scopeOwner : Atom)
    (assertion : SourceAssertion) :
    (assertionHypothesisSuccessorRows scopeOwner assertion).length =
      assertion.hypotheses.length := by
  simp [assertionHypothesisSuccessorRows]

@[simp] theorem assertionDVPairRows_length (scopeOwner : Atom)
    (assertion : SourceAssertion) :
    (assertionDVPairRows scopeOwner assertion).length =
      assertion.frame.distinctVariables.length := by
  simp [assertionDVPairRows]

@[simp] theorem assertionDVSuccessorRows_length (scopeOwner : Atom)
    (assertion : SourceAssertion) :
    (assertionDVSuccessorRows scopeOwner assertion).length =
      assertion.frame.distinctVariables.length := by
  simp [assertionDVSuccessorRows]

/-! ## Generic normal-proof rules -/

private def normalStepLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-normal-hypothesis-step"]

private def normalAcceptLocation : Atom :=
  .expression [.symbol "33", .symbol "mm-normal-accept"]

private def normalStepPatternAtoms : List Atom :=
  [.expression
        [.symbol "exec", normalStepLocation,
          .var "self-input", .var "self-output"],
   .expression
        [.symbol "mm-normal-control", .var "scope", .var "proof",
          .var "pc", .var "top"],
   .expression
        [.symbol "mm-linked-row", stringAtom "normal-proof-label",
          .var "proof", .var "pc", .var "next-pc", .var "label"],
   .expression
        [.symbol "mm-hypothesis-lookup", .var "scope",
          .var "label", .var "formula"],
   .expression
        [.symbol "mm-index-successor", .var "proof",
          .var "top", .var "next-top"]]

private def normalStepInput : Atom :=
  .expression (.symbol "," :: normalStepPatternAtoms)

private def normalStepSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalStepLocation,
      .var "self-input", .var "self-output"]

private def normalStepControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope", .var "proof",
      .var "pc", .var "top"]

private def normalStepNextControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope", .var "proof",
      .var "next-pc", .var "next-top"]

private def normalStepStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof", .var "top",
      .var "formula", .var "pc"]

private def normalStepSinks : List Sink :=
  [.add normalStepSelfTemplate, .remove normalStepControlTemplate,
   .add normalStepNextControlTemplate, .add normalStepStackTemplate]

private def normalStepOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "+", normalStepSelfTemplate],
      .expression
        [.symbol "-", normalStepControlTemplate],
      .expression
        [.symbol "+", normalStepNextControlTemplate],
      .expression
        [.symbol "+", normalStepStackTemplate]]

/-- One generic persistent MM2 rule implements every active-hypothesis proof
step.  It reads the source-derived hypothesis table; no database label is
compiled into the rule. -/
def normalHypothesisStepRule : Atom :=
  .expression
    [.symbol "exec", normalStepLocation,
      normalStepInput, normalStepOutput]

/-- The supported ordinary-MM2 directive represented by the emitted
active-hypothesis step rule.  This public boundary lets the correctness proof
reason about the parsed target rule rather than duplicating its semantics. -/
def normalHypothesisDirective : SourceExecFact where
  atom := normalHypothesisStepRule
  loc := normalStepLocation
  rule :=
    { priority := 0
      name := "mm-normal-hypothesis-step"
      input := .compat (mkPattern normalStepPatternAtoms)
      guards := []
      tmpl := mkTemplate normalStepSinks }

/-- Parsing the emitted hypothesis-step atom recovers its exact target
directive. -/
theorem extract_normalHypothesisStepRule_exact :
    extractSupportedSourceExecFact normalHypothesisStepRule =
      some normalHypothesisDirective := by
  rfl

/-! ## Floating-hypothesis assertion slice -/

private def normalAssertionStartLocation : Atom :=
  .expression [.symbol "01", .symbol "mm-normal-assertion-start"]

private def normalAssertionPopLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-normal-assertion-pop"]

private def normalAssertionBeginLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-normal-assertion-begin"]

private def normalAssertionFloatingLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-normal-assertion-floating"]

private def normalAssertionFinishLocation : Atom :=
  .expression [.symbol "13", .symbol "mm-normal-assertion-finish"]

private def normalAssertionEssentialLocation : Atom :=
  .expression [.symbol "05", .symbol "mm-normal-assertion-essential"]

private def normalDispatchReloadLocation : Atom :=
  .expression [.symbol "32", .symbol "mm-normal-dispatch-reload"]

private def normalBodyMatchConstLocation : Atom :=
  .expression [.symbol "06", .symbol "mm-normal-body-match-const"]

private def normalBodyMatchVariableLocation : Atom :=
  .expression [.symbol "07", .symbol "mm-normal-body-match-variable"]

private def normalBodyPrefixNilLocation : Atom :=
  .expression [.symbol "08", .symbol "mm-normal-body-prefix-nil"]

private def normalBodyPrefixConsLocation : Atom :=
  .expression [.symbol "09", .symbol "mm-normal-body-prefix-cons"]

private def normalBodyMatchNilLocation : Atom :=
  .expression [.symbol "10", .symbol "mm-normal-body-match-nil"]

private def normalBodyReloadLocation : Atom :=
  .expression [.symbol "11", .symbol "mm-normal-body-reload"]

private def normalAssertionEssentialCompleteLocation : Atom :=
  .expression [.symbol "12", .symbol "mm-normal-essential-complete"]

private def normalBodyBuildConstLocation : Atom :=
  .expression [.symbol "23", .symbol "mm-normal-body-build-const"]

private def normalBodyBuildVariableLocation : Atom :=
  .expression [.symbol "24", .symbol "mm-normal-body-build-variable"]

private def normalBodyBuildPrefixNilLocation : Atom :=
  .expression [.symbol "25", .symbol "mm-normal-body-build-prefix-nil"]

private def normalBodyBuildPrefixConsLocation : Atom :=
  .expression [.symbol "26", .symbol "mm-normal-body-build-prefix-cons"]

private def normalBodyBuildNilLocation : Atom :=
  .expression [.symbol "27", .symbol "mm-normal-body-build-nil"]

private def normalBodyReverseConsLocation : Atom :=
  .expression [.symbol "28", .symbol "mm-normal-body-reverse-cons"]

private def normalBodyReverseNilLocation : Atom :=
  .expression [.symbol "29", .symbol "mm-normal-body-reverse-nil"]

private def normalBodyBuildReloadLocation : Atom :=
  .expression [.symbol "30", .symbol "mm-normal-body-build-reload"]

private def normalAssertionResultCompleteLocation : Atom :=
  .expression [.symbol "31", .symbol "mm-normal-result-complete"]

private def normalDVPairBeginLocation : Atom :=
  .expression [.symbol "14", .symbol "mm-normal-dv-pair-begin"]

private def normalDVLeftConstLocation : Atom :=
  .expression [.symbol "15", .symbol "mm-normal-dv-left-const"]

private def normalDVLeftVariableLocation : Atom :=
  .expression [.symbol "16", .symbol "mm-normal-dv-left-variable"]

private def normalDVRightConstLocation : Atom :=
  .expression [.symbol "17", .symbol "mm-normal-dv-right-const"]

private def normalDVRightVariableLocation : Atom :=
  .expression [.symbol "18", .symbol "mm-normal-dv-right-variable"]

private def normalDVRightNilLocation : Atom :=
  .expression [.symbol "19", .symbol "mm-normal-dv-right-nil"]

private def normalDVLeftNilLocation : Atom :=
  .expression [.symbol "20", .symbol "mm-normal-dv-left-nil"]

private def normalDVCompleteLocation : Atom :=
  .expression [.symbol "21", .symbol "mm-normal-dv-complete"]

private def normalDVReloadLocation : Atom :=
  .expression [.symbol "22", .symbol "mm-normal-dv-reload"]

private def normalAssertionStartPatternAtoms : List Atom :=
  [.expression
        [.symbol "mm-normal-control", .var "scope", .var "proof",
          .var "pc", .var "top"],
   .expression
        [.symbol "mm-linked-row", stringAtom "normal-proof-label",
          .var "proof", .var "pc", .var "next-pc", .var "label"],
   .expression
        [.symbol "mm-assertion-header", .var "scope",
          .var "assertion-position", .var "label", .var "hyp-end"]]

private def normalAssertionStartInput : Atom :=
  .expression (.symbol "," :: normalAssertionStartPatternAtoms)

private def normalAssertionStartControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope", .var "proof",
      .var "pc", .var "top"]

private def normalAssertionStartPopTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-pop", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "hyp-end", .var "top"]

private def normalAssertionStartSinks : List Sink :=
  [.remove normalAssertionStartControlTemplate,
   .add normalAssertionStartPopTemplate]

private def normalAssertionStartOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-", normalAssertionStartControlTemplate],
      .expression
        [.symbol "+", normalAssertionStartPopTemplate]]

/-- Enter assertion execution from an assertion label found in the source
index.  No assertion-specific rule is emitted. -/
def normalAssertionStartRule : Atom :=
  .expression
    [.symbol "exec", normalAssertionStartLocation,
      normalAssertionStartInput, normalAssertionStartOutput]

def normalAssertionStartDirective : SourceExecFact where
  atom := normalAssertionStartRule
  loc := normalAssertionStartLocation
  rule :=
    { priority := 1
      name := "mm-normal-assertion-start"
      input := .compat (mkPattern normalAssertionStartPatternAtoms)
      guards := []
      tmpl := mkTemplate normalAssertionStartSinks }

theorem extract_normalAssertionStartRule_exact :
    extractSupportedSourceExecFact normalAssertionStartRule =
      some normalAssertionStartDirective := by
  rfl

private def normalAssertionPopPatternAtoms : List Atom :=
  [.expression
        [.symbol "exec", normalAssertionPopLocation,
          .var "self-input", .var "self-output"],
   .expression
        [.symbol "mm-assertion-pop", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label",
          .var "hyp-cursor", .var "stack-cursor"],
   .expression
        [.symbol "mm-assertion-hypothesis-successor", .var "scope",
          .var "label", .var "previous-hyp", .var "hyp-cursor"],
   .expression
        [.symbol "mm-index-successor", .var "proof",
          .var "previous-stack", .var "stack-cursor"]]

private def normalAssertionPopInput : Atom :=
  .expression (.symbol "," :: normalAssertionPopPatternAtoms)

private def normalAssertionPopSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalAssertionPopLocation,
      .var "self-input", .var "self-output"]

private def normalAssertionPopCurrentTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-pop", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "hyp-cursor", .var "stack-cursor"]

private def normalAssertionPopPreviousTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-pop", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "previous-hyp", .var "previous-stack"]

private def normalAssertionPopSinks : List Sink :=
  [.add normalAssertionPopSelfTemplate,
   .remove normalAssertionPopCurrentTemplate,
   .add normalAssertionPopPreviousTemplate]

private def normalAssertionPopOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "+", normalAssertionPopSelfTemplate],
      .expression
        [.symbol "-", normalAssertionPopCurrentTemplate],
      .expression
        [.symbol "+", normalAssertionPopPreviousTemplate]]

/-- Walk the explicit assertion and stack successor relations backward to
find the base of the ordered mandatory-hypothesis segment. -/
def normalAssertionPopRule : Atom :=
  .expression
    [.symbol "exec", normalAssertionPopLocation,
      normalAssertionPopInput, normalAssertionPopOutput]

def normalAssertionPopDirective : SourceExecFact where
  atom := normalAssertionPopRule
  loc := normalAssertionPopLocation
  rule :=
    { priority := 2
      name := "mm-normal-assertion-pop"
      input := .compat (mkPattern normalAssertionPopPatternAtoms)
      guards := []
      tmpl := mkTemplate normalAssertionPopSinks }

theorem extract_normalAssertionPopRule_exact :
    extractSupportedSourceExecFact normalAssertionPopRule =
      some normalAssertionPopDirective := by
  rfl

private def normalAssertionBeginPatternAtoms : List Atom :=
  [.expression
        [.symbol "mm-assertion-pop", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label", natAtom 0,
          .var "stack-base"],
   .expression
        [.symbol "mm-assertion-header", .var "scope",
          .var "assertion-position", .var "label", .var "hyp-end"]]

private def normalAssertionBeginInput : Atom :=
  .expression (.symbol "," :: normalAssertionBeginPatternAtoms)

private def normalAssertionBeginPopTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-pop", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label", natAtom 0,
      .var "stack-base"]

private def normalAssertionBeginBindTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label", natAtom 0,
      .var "hyp-end", .var "stack-base", .var "stack-base"]

private def normalAssertionBeginSinks : List Sink :=
  [.remove normalAssertionBeginPopTemplate,
   .add normalAssertionBeginBindTemplate]

private def normalAssertionBeginOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-", normalAssertionBeginPopTemplate],
      .expression
        [.symbol "+", normalAssertionBeginBindTemplate]]

def normalAssertionBeginRule : Atom :=
  .expression
    [.symbol "exec", normalAssertionBeginLocation,
      normalAssertionBeginInput, normalAssertionBeginOutput]

def normalAssertionBeginDirective : SourceExecFact where
  atom := normalAssertionBeginRule
  loc := normalAssertionBeginLocation
  rule :=
    { priority := 3
      name := "mm-normal-assertion-begin"
      input := .compat (mkPattern normalAssertionBeginPatternAtoms)
      guards := []
      tmpl := mkTemplate normalAssertionBeginSinks }

theorem extract_normalAssertionBeginRule_exact :
    extractSupportedSourceExecFact normalAssertionBeginRule =
      some normalAssertionBeginDirective := by
  rfl

private def normalAssertionFloatingPatternAtoms : List Atom :=
  [.expression
        [.symbol "exec", normalAssertionFloatingLocation,
          .var "self-input", .var "self-output"],
   .expression
        [.symbol "mm-assertion-bind", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label", .var "hyp-position",
          .var "hyp-end", .var "stack-position", .var "stack-base"],
   .expression
        [.symbol "mm-assertion-hypothesis", .var "scope", .var "label",
          .var "hyp-position",
          .expression
            [.symbol "mm-floating", .var "hyp-label", .var "typecode",
              .var "variable-name"]],
   .expression
        [.symbol "mm-assertion-hypothesis-successor", .var "scope",
          .var "label", .var "hyp-position", .var "next-hyp-position"],
   .expression
        [.symbol "mm-index-successor", .var "proof",
          .var "stack-position", .var "next-stack-position"],
   .expression
        [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
          .expression
            [.symbol "mm-formula", .var "typecode", .var "body"],
          .var "child-occurrence"]]

private def normalAssertionFloatingInput : Atom :=
  .expression (.symbol "," :: normalAssertionFloatingPatternAtoms)

private def normalAssertionFloatingSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalAssertionFloatingLocation,
      .var "self-input", .var "self-output"]

private def normalAssertionFloatingBindTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "hyp-position", .var "hyp-end",
      .var "stack-position", .var "stack-base"]

private def normalAssertionFloatingStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
      .expression
        [.symbol "mm-formula", .var "typecode", .var "body"],
      .var "child-occurrence"]

private def normalAssertionFloatingNextBindTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "next-hyp-position", .var "hyp-end",
      .var "next-stack-position", .var "stack-base"]

private def normalAssertionFloatingSubstitutionTemplate : Atom :=
  .expression
    [.symbol "mm-substitution", .var "proof", .var "pc",
      .var "variable-name", .var "body"]

private def normalAssertionFloatingChildTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-child", .var "proof", .var "pc",
      .var "hyp-position", .var "child-occurrence"]

private def normalAssertionFloatingSinks : List Sink :=
  [.add normalAssertionFloatingSelfTemplate,
   .remove normalAssertionFloatingBindTemplate,
   .remove normalAssertionFloatingStackTemplate,
   .add normalAssertionFloatingNextBindTemplate,
   .add normalAssertionFloatingSubstitutionTemplate,
   .add normalAssertionFloatingChildTemplate]

private def normalAssertionFloatingOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "+", normalAssertionFloatingSelfTemplate],
      .expression
        [.symbol "-", normalAssertionFloatingBindTemplate],
      .expression
        [.symbol "-", normalAssertionFloatingStackTemplate],
      .expression
        [.symbol "+", normalAssertionFloatingNextBindTemplate],
      .expression
        [.symbol "+", normalAssertionFloatingSubstitutionTemplate],
      .expression
        [.symbol "+", normalAssertionFloatingChildTemplate]]

/-- Bind one source floating hypothesis to the body of its ordered actual
stack formula.  The consumed child occurrence remains as indexed assertion
evidence. -/
def normalAssertionFloatingRule : Atom :=
  .expression
    [.symbol "exec", normalAssertionFloatingLocation,
      normalAssertionFloatingInput, normalAssertionFloatingOutput]

/-- Parsed ordinary-MM2 directive for the generic floating-hypothesis phase. -/
def normalAssertionFloatingDirective : SourceExecFact where
  atom := normalAssertionFloatingRule
  loc := normalAssertionFloatingLocation
  rule :=
    { priority := 4
      name := "mm-normal-assertion-floating"
      input := .compat (mkPattern normalAssertionFloatingPatternAtoms)
      guards := []
      tmpl := mkTemplate normalAssertionFloatingSinks }

theorem extract_normalAssertionFloatingRule_exact :
    extractSupportedSourceExecFact normalAssertionFloatingRule =
      some normalAssertionFloatingDirective := by
  rfl

private def normalAssertionEssentialPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-assertion-bind", .var "scope", .var "proof",
        .var "pc", .var "next-pc", .var "label", .var "hyp-position",
        .var "hyp-end", .var "stack-position", .var "stack-base"],
   .expression
      [.symbol "mm-assertion-hypothesis", .var "scope", .var "label",
        .var "hyp-position",
        .expression
          [.symbol "mm-essential", .var "hyp-label",
            .expression
              [.symbol "mm-formula", .var "typecode",
                .var "source-body"]]],
   .expression
      [.symbol "mm-assertion-hypothesis-successor", .var "scope",
        .var "label", .var "hyp-position", .var "next-hyp-position"],
   .expression
      [.symbol "mm-index-successor", .var "proof",
        .var "stack-position", .var "next-stack-position"],
   .expression
      [.symbol "mm-stack-cell", .var "proof", .var "stack-position",
        .expression
          [.symbol "mm-formula", .var "typecode", .var "actual-body"],
        .var "child-occurrence"]]

private def normalAssertionEssentialInput : Atom :=
  .expression (.symbol "," :: normalAssertionEssentialPatternAtoms)

private def normalAssertionEssentialCompleteTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-essential-complete",
      .var "scope", .var "proof", .var "pc", .var "next-pc",
      .var "label", .var "next-hyp-position", .var "hyp-end",
      .var "next-stack-position", .var "stack-base",
      .var "hyp-position", .var "child-occurrence"]

private def normalAssertionEssentialBindTemplate : Atom :=
  normalAssertionEssentialPatternAtoms[0]'(by decide)

private def normalAssertionEssentialStackTemplate : Atom :=
  normalAssertionEssentialPatternAtoms[4]'(by decide)

private def normalAssertionEssentialMatchTemplate : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .var "source-body", .var "actual-body",
      normalAssertionEssentialCompleteTemplate]

private def normalAssertionEssentialSinks : List Sink :=
  [.remove normalAssertionEssentialBindTemplate,
   .remove normalAssertionEssentialStackTemplate,
   .add normalAssertionEssentialMatchTemplate]

private def normalAssertionEssentialOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalAssertionEssentialBindTemplate],
      .expression [.symbol "-", normalAssertionEssentialStackTemplate],
      .expression [.symbol "+", normalAssertionEssentialMatchTemplate]]

/-- Start an exact substitution match for one essential hypothesis.  Source
and actual bodies remain ordinary bounded-arity MM2 list data; the fixed body
machine below consumes them without compiling a formula-specific rule. -/
def normalAssertionEssentialRule : Atom :=
  .expression
    [.symbol "exec", normalAssertionEssentialLocation,
      normalAssertionEssentialInput, normalAssertionEssentialOutput]

/-- Parsed ordinary-MM2 directive for the generic essential-hypothesis
phase.  The rule starts a body-substitution match and carries the source
hypothesis position and child occurrence in its continuation. -/
def normalAssertionEssentialDirective : SourceExecFact where
  atom := normalAssertionEssentialRule
  loc := normalAssertionEssentialLocation
  rule :=
    { priority := 5
      name := "mm-normal-assertion-essential"
      input := .compat (mkPattern normalAssertionEssentialPatternAtoms)
      guards := []
      tmpl := mkTemplate normalAssertionEssentialSinks }

theorem extract_normalAssertionEssentialRule_exact :
    extractSupportedSourceExecFact normalAssertionEssentialRule =
      some normalAssertionEssentialDirective := by
  rfl

private def normalBodyMatchConstPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-match", .var "proof", .var "pc",
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-const", .var "constant-name"],
            .var "source-tail"],
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-const", .var "constant-name"],
            .var "actual-tail"],
        .var "continuation"]]

private def normalBodyMatchConstInput : Atom :=
  .expression (.symbol "," :: normalBodyMatchConstPatternAtoms)

private def normalBodyMatchConstCurrentTemplate : Atom :=
  normalBodyMatchConstPatternAtoms[0]'(by decide)

private def normalBodyMatchConstTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .var "source-tail", .var "actual-tail", .var "continuation"]

private def normalBodyMatchReloadTemplate : Atom :=
  .expression
    [.symbol "mm-reload-body-match", .var "proof", .var "pc"]

private def normalBodyMatchConstSinks : List Sink :=
  [.remove normalBodyMatchConstCurrentTemplate,
   .add normalBodyMatchConstTailTemplate,
   .add normalBodyMatchReloadTemplate]

private def normalBodyMatchConstOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalBodyMatchConstCurrentTemplate],
      .expression [.symbol "+", normalBodyMatchConstTailTemplate],
      .expression [.symbol "+", normalBodyMatchReloadTemplate]]

def normalBodyMatchConstRule : Atom :=
  .expression
    [.symbol "exec", normalBodyMatchConstLocation,
      normalBodyMatchConstInput, normalBodyMatchConstOutput]

def normalBodyMatchConstDirective : SourceExecFact where
  atom := normalBodyMatchConstRule
  loc := normalBodyMatchConstLocation
  rule :=
    { priority := 6
      name := "mm-normal-body-match-const"
      input := .compat (mkPattern normalBodyMatchConstPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyMatchConstSinks }

theorem extract_normalBodyMatchConstRule_exact :
    extractSupportedSourceExecFact normalBodyMatchConstRule =
      some normalBodyMatchConstDirective := by
  rfl

private def normalBodyMatchVariablePatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-match", .var "proof", .var "pc",
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-variable", .var "variable-name"],
            .var "source-tail"],
        .var "actual-body", .var "continuation"],
   .expression
      [.symbol "mm-substitution", .var "proof", .var "pc",
        .var "variable-name", .var "replacement-body"]]

private def normalBodyMatchVariableInput : Atom :=
  .expression (.symbol "," :: normalBodyMatchVariablePatternAtoms)

private def normalBodyMatchVariableCurrentTemplate : Atom :=
  normalBodyMatchVariablePatternAtoms[0]'(by decide)

private def normalBodyMatchVariableSubstitutionTemplate : Atom :=
  normalBodyMatchVariablePatternAtoms[1]'(by decide)

private def normalBodyMatchVariablePrefixTemplate : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .var "replacement-body", .var "actual-body",
      .var "source-tail", .var "continuation"]

private def normalBodyMatchVariableReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-body-match", .var "proof", .var "pc"]

private def normalBodyMatchVariableSinks : List Sink :=
  [.remove normalBodyMatchVariableCurrentTemplate,
   .add normalBodyMatchVariablePrefixTemplate,
   .add normalBodyMatchVariableReloadTemplate]

private def normalBodyMatchVariableOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalBodyMatchVariableCurrentTemplate],
      .expression [.symbol "+", normalBodyMatchVariablePrefixTemplate],
      .expression [.symbol "+", normalBodyMatchVariableReloadTemplate]]

def normalBodyMatchVariableRule : Atom :=
  .expression
    [.symbol "exec", normalBodyMatchVariableLocation,
      normalBodyMatchVariableInput, normalBodyMatchVariableOutput]

def normalBodyMatchVariableDirective : SourceExecFact where
  atom := normalBodyMatchVariableRule
  loc := normalBodyMatchVariableLocation
  rule :=
    { priority := 7
      name := "mm-normal-body-match-variable"
      input := .compat (mkPattern normalBodyMatchVariablePatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyMatchVariableSinks }

theorem extract_normalBodyMatchVariableRule_exact :
    extractSupportedSourceExecFact normalBodyMatchVariableRule =
      some normalBodyMatchVariableDirective := by
  rfl

private def normalBodyPrefixNilPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-prefix", .var "proof", .var "pc",
        .expression [.symbol "mm-nil"], .var "actual-body",
        .var "source-tail", .var "continuation"]]

private def normalBodyPrefixNilInput : Atom :=
  .expression (.symbol "," :: normalBodyPrefixNilPatternAtoms)

private def normalBodyPrefixNilCurrentTemplate : Atom :=
  normalBodyPrefixNilPatternAtoms[0]'(by decide)

private def normalBodyPrefixNilTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-match", .var "proof", .var "pc",
      .var "source-tail", .var "actual-body", .var "continuation"]

private def normalBodyPrefixNilReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-body-match", .var "proof", .var "pc"]

private def normalBodyPrefixNilSinks : List Sink :=
  [.remove normalBodyPrefixNilCurrentTemplate,
   .add normalBodyPrefixNilTailTemplate,
   .add normalBodyPrefixNilReloadTemplate]

private def normalBodyPrefixNilOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalBodyPrefixNilCurrentTemplate],
      .expression [.symbol "+", normalBodyPrefixNilTailTemplate],
      .expression [.symbol "+", normalBodyPrefixNilReloadTemplate]]

def normalBodyPrefixNilRule : Atom :=
  .expression
    [.symbol "exec", normalBodyPrefixNilLocation,
      normalBodyPrefixNilInput, normalBodyPrefixNilOutput]

def normalBodyPrefixNilDirective : SourceExecFact where
  atom := normalBodyPrefixNilRule
  loc := normalBodyPrefixNilLocation
  rule :=
    { priority := 8
      name := "mm-normal-body-prefix-nil"
      input := .compat (mkPattern normalBodyPrefixNilPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyPrefixNilSinks }

theorem extract_normalBodyPrefixNilRule_exact :
    extractSupportedSourceExecFact normalBodyPrefixNilRule =
      some normalBodyPrefixNilDirective := by
  rfl

private def normalBodyPrefixConsPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-prefix", .var "proof", .var "pc",
        .expression
          [.symbol "mm-cons", .var "replacement-symbol",
            .var "replacement-tail"],
        .expression
          [.symbol "mm-cons", .var "replacement-symbol",
            .var "actual-tail"],
        .var "source-tail", .var "continuation"]]

private def normalBodyPrefixConsInput : Atom :=
  .expression (.symbol "," :: normalBodyPrefixConsPatternAtoms)

private def normalBodyPrefixConsCurrentTemplate : Atom :=
  normalBodyPrefixConsPatternAtoms[0]'(by decide)

private def normalBodyPrefixConsTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-prefix", .var "proof", .var "pc",
      .var "replacement-tail", .var "actual-tail",
      .var "source-tail", .var "continuation"]

private def normalBodyPrefixConsReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-body-match", .var "proof", .var "pc"]

private def normalBodyPrefixConsSinks : List Sink :=
  [.remove normalBodyPrefixConsCurrentTemplate,
   .add normalBodyPrefixConsTailTemplate,
   .add normalBodyPrefixConsReloadTemplate]

private def normalBodyPrefixConsOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalBodyPrefixConsCurrentTemplate],
      .expression [.symbol "+", normalBodyPrefixConsTailTemplate],
      .expression [.symbol "+", normalBodyPrefixConsReloadTemplate]]

def normalBodyPrefixConsRule : Atom :=
  .expression
    [.symbol "exec", normalBodyPrefixConsLocation,
      normalBodyPrefixConsInput, normalBodyPrefixConsOutput]

def normalBodyPrefixConsDirective : SourceExecFact where
  atom := normalBodyPrefixConsRule
  loc := normalBodyPrefixConsLocation
  rule :=
    { priority := 9
      name := "mm-normal-body-prefix-cons"
      input := .compat (mkPattern normalBodyPrefixConsPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyPrefixConsSinks }

theorem extract_normalBodyPrefixConsRule_exact :
    extractSupportedSourceExecFact normalBodyPrefixConsRule =
      some normalBodyPrefixConsDirective := by
  rfl

private def normalBodyMatchNilPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-match", .var "proof", .var "pc",
        .expression [.symbol "mm-nil"], .expression [.symbol "mm-nil"],
        .var "continuation"]]

private def normalBodyMatchNilInput : Atom :=
  .expression (.symbol "," :: normalBodyMatchNilPatternAtoms)

private def normalBodyMatchNilCurrentTemplate : Atom :=
  normalBodyMatchNilPatternAtoms[0]'(by decide)

private def normalBodyMatchNilContinuationTemplate : Atom :=
  .var "continuation"

private def normalBodyMatchNilReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-body-match", .var "proof", .var "pc"]

private def normalBodyMatchNilSinks : List Sink :=
  [.remove normalBodyMatchNilCurrentTemplate,
   .add normalBodyMatchNilContinuationTemplate,
   .add normalBodyMatchNilReloadTemplate]

private def normalBodyMatchNilOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalBodyMatchNilCurrentTemplate],
      .expression [.symbol "+", normalBodyMatchNilContinuationTemplate],
      .expression [.symbol "+", normalBodyMatchNilReloadTemplate]]

def normalBodyMatchNilRule : Atom :=
  .expression
    [.symbol "exec", normalBodyMatchNilLocation,
      normalBodyMatchNilInput, normalBodyMatchNilOutput]

def normalBodyMatchNilDirective : SourceExecFact where
  atom := normalBodyMatchNilRule
  loc := normalBodyMatchNilLocation
  rule :=
    { priority := 10
      name := "mm-normal-body-match-nil"
      input := .compat (mkPattern normalBodyMatchNilPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyMatchNilSinks }

theorem extract_normalBodyMatchNilRule_exact :
    extractSupportedSourceExecFact normalBodyMatchNilRule =
      some normalBodyMatchNilDirective := by
  rfl

private def normalBodyReloadInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "exec", normalBodyReloadLocation,
          .var "body-reload-self-input", .var "body-reload-self-output"],
      .expression
        [.symbol "mm-reload-body-match", .var "body-reload-proof",
          .var "body-reload-pc"],
      .expression
        [.symbol "mm-internal-body-match-rules",
          .var "body-rule-const", .var "body-rule-variable",
          .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
          .var "body-rule-nil"]]

private def normalBodyReloadOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "+",
          .expression
            [.symbol "exec", normalBodyReloadLocation,
              .var "body-reload-self-input",
              .var "body-reload-self-output"]],
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-reload-body-match", .var "body-reload-proof",
              .var "body-reload-pc"]],
      .expression [.symbol "+", .var "body-rule-const"],
      .expression [.symbol "+", .var "body-rule-variable"],
      .expression [.symbol "+", .var "body-rule-prefix-nil"],
      .expression [.symbol "+", .var "body-rule-prefix-cons"],
      .expression [.symbol "+", .var "body-rule-nil"]]

def normalBodyReloadRule : Atom :=
  .expression
    [.symbol "exec", normalBodyReloadLocation,
      normalBodyReloadInput, normalBodyReloadOutput]

/-- Verifier-owned body-matcher code captured opaquely by the reload rule. -/
def normalBodyMatchRuleBundle : Atom :=
  .expression
    [.symbol "mm-internal-body-match-rules",
      normalBodyMatchConstRule, normalBodyMatchVariableRule,
      normalBodyPrefixNilRule, normalBodyPrefixConsRule,
      normalBodyMatchNilRule]

private def normalBodyReloadSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalBodyReloadLocation,
      .var "body-reload-self-input", .var "body-reload-self-output"]

private def normalBodyReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-body-match", .var "body-reload-proof",
      .var "body-reload-pc"]

private def normalBodyReloadBundleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-body-match-rules",
      .var "body-rule-const", .var "body-rule-variable",
      .var "body-rule-prefix-nil", .var "body-rule-prefix-cons",
      .var "body-rule-nil"]

private def normalBodyReloadPatternAtoms : List Atom :=
  [normalBodyReloadSelfTemplate, normalBodyReloadTriggerTemplate,
   normalBodyReloadBundleTemplate]

private def normalBodyReloadSinks : List Sink :=
  [.add normalBodyReloadSelfTemplate,
   .remove normalBodyReloadTriggerTemplate,
   .add (.var "body-rule-const"),
   .add (.var "body-rule-variable"),
   .add (.var "body-rule-prefix-nil"),
   .add (.var "body-rule-prefix-cons"),
   .add (.var "body-rule-nil")]

def normalBodyReloadDirective : SourceExecFact where
  atom := normalBodyReloadRule
  loc := normalBodyReloadLocation
  rule :=
    { priority := 11
      name := "mm-normal-body-reload"
      input := .compat (mkPattern normalBodyReloadPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyReloadSinks }

theorem extract_normalBodyReloadRule_exact :
    extractSupportedSourceExecFact normalBodyReloadRule =
      some normalBodyReloadDirective := by
  rfl

def normalBodyReloadPhaseSpace (proofOwner : Atom)
    (proofPosition : Nat) : Space :=
  [normalBodyReloadRule,
   .expression
     [.symbol "mm-reload-body-match", proofOwner, natAtom proofPosition],
   normalBodyMatchRuleBundle].toFinset

theorem normalBodyReloadPhase_selects_directive
    (proofOwner : Atom) (proofPosition : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyReloadPhaseSpace proofOwner proofPosition)) =
      some normalBodyReloadDirective := by
  let atoms :=
    [normalBodyReloadRule,
     .expression
       [.symbol "mm-reload-body-match", proofOwner, natAtom proofPosition],
     normalBodyMatchRuleBundle]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyReloadDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyReloadDirective
    (by simp [atoms, normalBodyReloadRule, normalBodyMatchRuleBundle])
    (by rfl)

private def normalBodyReloadSubstitution (proofOwner : Atom)
    (proofPosition : Nat) : Subst :=
  [("body-rule-nil", normalBodyMatchNilRule),
   ("body-rule-prefix-cons", normalBodyPrefixConsRule),
   ("body-rule-prefix-nil", normalBodyPrefixNilRule),
   ("body-rule-variable", normalBodyMatchVariableRule),
   ("body-rule-const", normalBodyMatchConstRule),
   ("body-reload-pc", natAtom proofPosition),
   ("body-reload-proof", proofOwner),
   ("body-reload-self-output", normalBodyReloadOutput),
   ("body-reload-self-input", normalBodyReloadInput)]

private theorem normalBodyReloadMatchRow_mem
    (proofOwner : Atom) (proofPosition : Nat) :
    normalBodyReloadSubstitution proofOwner proofPosition ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyReloadPhaseSpace proofOwner proofPosition)
          normalBodyReloadRule)
        normalBodyReloadDirective.rule.input).map Prod.fst := by
  let request : Atom :=
    .expression
      [.symbol "mm-reload-body-match", proofOwner, natAtom proofPosition]
  let read := readCopyAtom
    (normalBodyReloadPhaseSpace proofOwner proofPosition)
    normalBodyReloadRule
  let afterSelf : Subst :=
    [("body-reload-self-output", normalBodyReloadOutput),
     ("body-reload-self-input", normalBodyReloadInput)]
  let afterRequest : Subst :=
    [("body-reload-pc", natAtom proofPosition),
     ("body-reload-proof", proofOwner),
     ("body-reload-self-output", normalBodyReloadOutput),
     ("body-reload-self-input", normalBodyReloadInput)]
  let substitution := normalBodyReloadSubstitution proofOwner proofPosition
  have selfMem : normalBodyReloadRule ∈ read := by
    simp [read, readCopyAtom, normalBodyReloadPhaseSpace]
  have requestMem : request ∈ read := by
    simp [read, readCopyAtom, consumeAtom, request,
      normalBodyReloadPhaseSpace, normalBodyReloadRule]
  have bundleMem : normalBodyMatchRuleBundle ∈ read := by
    simp [read, readCopyAtom, consumeAtom,
      normalBodyReloadPhaseSpace, normalBodyReloadRule,
      normalBodyMatchRuleBundle]
  have matchSelf :
      matchAtom [] normalBodyReloadSelfTemplate normalBodyReloadRule =
        some afterSelf := by
    simp [normalBodyReloadSelfTemplate, normalBodyReloadRule,
      normalBodyReloadLocation, normalBodyReloadInput,
      normalBodyReloadOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchRequest :
      matchAtom afterSelf normalBodyReloadTriggerTemplate request =
        some afterRequest := by
    simp [normalBodyReloadTriggerTemplate, request, afterSelf,
      afterRequest, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchBundle :
      matchAtom afterRequest normalBodyReloadBundleTemplate
          normalBodyMatchRuleBundle = some substitution := by
    simp [normalBodyReloadBundleTemplate, normalBodyMatchRuleBundle,
      afterRequest, substitution, normalBodyReloadSubstitution, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution,
    {normalBodyReloadRule, request, normalBodyMatchRuleBundle}), ?_, rfl⟩
  simp only [normalBodyReloadDirective, matchInputSpec,
    normalBodyReloadPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterSelf, normalBodyReloadRule),
    matchOneInSpace_mem [] _ read normalBodyReloadRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterRequest, request),
    matchOneInSpace_mem afterSelf _ read request requestMem afterRequest
      matchRequest, ?_⟩
  refine ⟨(substitution, normalBodyMatchRuleBundle),
    matchOneInSpace_mem afterRequest _ read normalBodyMatchRuleBundle
      bundleMem substitution matchBundle, ?_⟩
  simp [substitution, request]

theorem normalBodyReloadPhase_inhabits_target_native_type
    (proofOwner : Atom) (proofPosition : Nat) :
    let source := normalBodyReloadPhaseSpace proofOwner proofPosition
    let target := fireReflectiveSourceExecFact source
      normalBodyReloadDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred := by
  dsimp only
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected
      (normalBodyReloadPhase_selects_directive proofOwner proofPosition))

def normalBodyMatchMachineRules : List Atom :=
  [normalBodyMatchConstRule, normalBodyMatchVariableRule,
   normalBodyPrefixNilRule, normalBodyPrefixConsRule,
   normalBodyMatchNilRule, normalBodyReloadRule]

private def normalAssertionEssentialCompletePatternAtoms : List Atom :=
  [normalAssertionEssentialCompleteTemplate]

private def normalAssertionEssentialCompleteInput : Atom :=
  .expression (.symbol "," :: normalAssertionEssentialCompletePatternAtoms)

private def normalAssertionEssentialCompleteNextBindTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label",
      .var "next-hyp-position", .var "hyp-end",
      .var "next-stack-position", .var "stack-base"]

private def normalAssertionEssentialCompleteChildTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-child", .var "proof", .var "pc",
      .var "hyp-position", .var "child-occurrence"]

private def normalAssertionEssentialCompleteReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-normal-dispatch", .var "proof"]

private def normalAssertionEssentialCompleteSinks : List Sink :=
  [.remove normalAssertionEssentialCompleteTemplate,
   .add normalAssertionEssentialCompleteNextBindTemplate,
   .add normalAssertionEssentialCompleteChildTemplate,
   .add normalAssertionEssentialCompleteReloadTemplate]

private def normalAssertionEssentialCompleteOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalAssertionEssentialCompleteTemplate],
      .expression
        [.symbol "+", normalAssertionEssentialCompleteNextBindTemplate],
      .expression
        [.symbol "+", normalAssertionEssentialCompleteChildTemplate],
      .expression
        [.symbol "+", normalAssertionEssentialCompleteReloadTemplate]]

def normalAssertionEssentialCompleteRule : Atom :=
  .expression
    [.symbol "exec", normalAssertionEssentialCompleteLocation,
      normalAssertionEssentialCompleteInput,
      normalAssertionEssentialCompleteOutput]

/-- Parsed completion directive reached only after the generic body matcher
has discharged one essential-hypothesis equality. -/
def normalAssertionEssentialCompleteDirective : SourceExecFact where
  atom := normalAssertionEssentialCompleteRule
  loc := normalAssertionEssentialCompleteLocation
  rule :=
    { priority := 12
      name := "mm-normal-essential-complete"
      input := .compat
        (mkPattern normalAssertionEssentialCompletePatternAtoms)
      guards := []
      tmpl := mkTemplate normalAssertionEssentialCompleteSinks }

theorem extract_normalAssertionEssentialCompleteRule_exact :
    extractSupportedSourceExecFact normalAssertionEssentialCompleteRule =
      some normalAssertionEssentialCompleteDirective := by
  rfl

private def normalAssertionFinishInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-assertion-bind", .var "scope", .var "proof",
          .var "pc", .var "next-pc", .var "label", .var "hyp-end",
          .var "hyp-end", .var "stack-end", .var "stack-base"],
      .expression
        [.symbol "mm-assertion-result", .var "scope",
          .var "label", .var "result-typecode", .var "source-body"],
      .expression
        [.symbol "mm-assertion-dv-header", .var "scope",
          .var "label", .var "assertion-position"],
      .expression
        [.symbol "mm-index-successor", .var "proof",
          .var "stack-base", .var "next-top"]]

private def normalAssertionFinishOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-assertion-bind", .var "scope", .var "proof",
              .var "pc", .var "next-pc", .var "label", .var "hyp-end",
              .var "hyp-end", .var "stack-end", .var "stack-base"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
              .var "pc", .var "label", natAtom 0, .var "assertion-position",
              .var "source-body",
              .expression
                [.symbol "mm-assertion-result-context", .var "scope",
                  .var "next-pc", .var "label", .var "result-typecode",
                  .var "stack-base", .var "next-top"]]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-dv", .var "proof", .var "pc"]]]

def normalAssertionFinishRule : Atom :=
  .expression
    [.symbol "exec", normalAssertionFinishLocation,
      normalAssertionFinishInput, normalAssertionFinishOutput]

/-! ## Disjoint-variable cross-product machine -/

private def normalDVPairBeginInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
          .var "pc", .var "label", .var "hyp-position",
          .var "hyp-end", .var "source-body", .var "context"],
      .expression
        [.symbol "mm-assertion-dv-pair", .var "scope", .var "label",
          .var "hyp-position", .var "variable-name", .var "hyp-label"],
      .expression
        [.symbol "mm-assertion-dv-successor", .var "scope", .var "label",
          .var "hyp-position", .var "next-hyp-position"],
      .expression
        [.symbol "mm-substitution", .var "proof", .var "pc",
          .var "variable-name", .var "actual-body"],
      .expression
        [.symbol "mm-substitution", .var "proof", .var "pc",
          .var "hyp-label", .var "body"]]

private def normalDVPairBeginOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
              .var "pc", .var "label", .var "hyp-position",
              .var "hyp-end", .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "actual-body", .var "body",
              .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-dv", .var "proof", .var "pc"]]]

def normalDVPairBeginRule : Atom :=
  .expression
    [.symbol "exec", normalDVPairBeginLocation,
      normalDVPairBeginInput, normalDVPairBeginOutput]

private def normalDVLeftConstInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
          .var "pc", .var "label", .var "next-hyp-position",
          .var "hyp-end",
          .expression
            [.symbol "mm-cons",
              .expression [.symbol "mm-const", .var "constant-name"],
              .var "source-tail"],
          .var "body", .var "source-body", .var "context"]]

private def normalDVLeftConstOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end",
              .expression
                [.symbol "mm-cons",
                  .expression [.symbol "mm-const", .var "constant-name"],
                  .var "source-tail"],
              .var "body", .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "source-tail", .var "body",
              .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-dv", .var "proof", .var "pc"]]]

def normalDVLeftConstRule : Atom :=
  .expression
    [.symbol "exec", normalDVLeftConstLocation,
      normalDVLeftConstInput, normalDVLeftConstOutput]

private def normalDVLeftVariableInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
          .var "pc", .var "label", .var "next-hyp-position",
          .var "hyp-end",
          .expression
            [.symbol "mm-cons",
              .expression [.symbol "mm-variable", .var "variable-name"],
              .var "source-tail"],
          .var "body", .var "source-body", .var "context"]]

private def normalDVLeftVariableOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end",
              .expression
                [.symbol "mm-cons",
                  .expression
                    [.symbol "mm-variable", .var "variable-name"],
                  .var "source-tail"],
              .var "body", .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "variable-name", .var "source-tail",
              .var "body", .var "body", .var "source-body",
              .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-dv", .var "proof", .var "pc"]]]

def normalDVLeftVariableRule : Atom :=
  .expression
    [.symbol "exec", normalDVLeftVariableLocation,
      normalDVLeftVariableInput, normalDVLeftVariableOutput]

private def normalDVRightConstInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
          .var "pc", .var "label", .var "next-hyp-position",
          .var "hyp-end", .var "variable-name", .var "source-tail",
          .expression
            [.symbol "mm-cons",
              .expression [.symbol "mm-const", .var "constant-name"],
              .var "actual-tail"],
          .var "body", .var "source-body", .var "context"]]

private def normalDVRightConstOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "variable-name", .var "source-tail",
              .expression
                [.symbol "mm-cons",
                  .expression [.symbol "mm-const", .var "constant-name"],
                  .var "actual-tail"],
              .var "body", .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "variable-name", .var "source-tail",
              .var "actual-tail", .var "body", .var "source-body",
              .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-dv", .var "proof", .var "pc"]]]

def normalDVRightConstRule : Atom :=
  .expression
    [.symbol "exec", normalDVRightConstLocation,
      normalDVRightConstInput, normalDVRightConstOutput]

private def normalDVRightVariableInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
          .var "pc", .var "label", .var "next-hyp-position",
          .var "hyp-end", .var "variable-name", .var "source-tail",
          .expression
            [.symbol "mm-cons",
              .expression [.symbol "mm-variable", .var "hyp-label"],
              .var "actual-tail"],
          .var "body", .var "source-body", .var "context"],
      .expression
        [.symbol "mm-caller-dv", .var "scope",
          .var "variable-name", .var "hyp-label"]]

private def normalDVRightVariableOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "variable-name", .var "source-tail",
              .expression
                [.symbol "mm-cons",
                  .expression
                    [.symbol "mm-variable", .var "hyp-label"],
                  .var "actual-tail"],
              .var "body", .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "variable-name", .var "source-tail",
              .var "actual-tail", .var "body", .var "source-body",
              .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-dv", .var "proof", .var "pc"]]]

def normalDVRightVariableRule : Atom :=
  .expression
    [.symbol "exec", normalDVRightVariableLocation,
      normalDVRightVariableInput, normalDVRightVariableOutput]

private def normalDVRightNilInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
          .var "pc", .var "label", .var "next-hyp-position",
          .var "hyp-end", .var "variable-name", .var "source-tail",
          .expression [.symbol "mm-nil"], .var "body",
          .var "source-body", .var "context"]]

private def normalDVRightNilOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "variable-name", .var "source-tail",
              .expression [.symbol "mm-nil"], .var "body",
              .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "source-tail", .var "body",
              .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-dv", .var "proof", .var "pc"]]]

def normalDVRightNilRule : Atom :=
  .expression
    [.symbol "exec", normalDVRightNilLocation,
      normalDVRightNilInput, normalDVRightNilOutput]

private def normalDVLeftNilInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
          .var "pc", .var "label", .var "next-hyp-position",
          .var "hyp-end", .expression [.symbol "mm-nil"],
          .var "body", .var "source-body", .var "context"]]

private def normalDVLeftNilOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .expression [.symbol "mm-nil"],
              .var "body", .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
              .var "pc", .var "label", .var "next-hyp-position",
              .var "hyp-end", .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-dv", .var "proof", .var "pc"]]]

def normalDVLeftNilRule : Atom :=
  .expression
    [.symbol "exec", normalDVLeftNilLocation,
      normalDVLeftNilInput, normalDVLeftNilOutput]

private def normalDVCompleteInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
          .var "pc", .var "label", .var "hyp-end", .var "hyp-end",
          .var "source-body", .var "context"]]

private def normalDVCompleteOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
              .var "pc", .var "label", .var "hyp-end", .var "hyp-end",
              .var "source-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-body-build", .var "proof", .var "pc",
              .var "source-body", .expression [.symbol "mm-nil"],
              .var "context"]]]

def normalDVCompleteRule : Atom :=
  .expression
    [.symbol "exec", normalDVCompleteLocation,
      normalDVCompleteInput, normalDVCompleteOutput]

private def normalDVReloadInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "exec", normalDVReloadLocation,
          .var "dv-reload-self-input", .var "dv-reload-self-output"],
      .expression
        [.symbol "mm-reload-dv", .var "dv-reload-proof",
          .var "dv-reload-pc"],
      .expression
        [.symbol "mm-internal-dv-rules",
          .var "dv-rule-pair-begin", .var "dv-rule-left-const",
          .var "dv-rule-left-variable", .var "dv-rule-right-const",
          .var "dv-rule-right-variable", .var "dv-rule-right-nil",
          .var "dv-rule-left-nil", .var "dv-rule-complete"]]

private def normalDVReloadOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "+",
          .expression
            [.symbol "exec", normalDVReloadLocation,
              .var "dv-reload-self-input", .var "dv-reload-self-output"]],
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-reload-dv", .var "dv-reload-proof",
              .var "dv-reload-pc"]],
      .expression [.symbol "+", .var "dv-rule-pair-begin"],
      .expression [.symbol "+", .var "dv-rule-left-const"],
      .expression [.symbol "+", .var "dv-rule-left-variable"],
      .expression [.symbol "+", .var "dv-rule-right-const"],
      .expression [.symbol "+", .var "dv-rule-right-variable"],
      .expression [.symbol "+", .var "dv-rule-right-nil"],
      .expression [.symbol "+", .var "dv-rule-left-nil"],
      .expression [.symbol "+", .var "dv-rule-complete"]]

def normalDVReloadRule : Atom :=
  .expression
    [.symbol "exec", normalDVReloadLocation,
      normalDVReloadInput, normalDVReloadOutput]

def normalDVMachineRules : List Atom :=
  [normalDVPairBeginRule, normalDVLeftConstRule,
   normalDVLeftVariableRule, normalDVRightConstRule,
   normalDVRightVariableRule, normalDVRightNilRule,
   normalDVLeftNilRule, normalDVCompleteRule, normalDVReloadRule]

/-- Verifier-owned DV-machine code captured opaquely by the reload rule.
The carrier is inert data; only the exact generic verifier artifact supplies
it to the executable matcher. -/
def normalDVRuleBundle : Atom :=
  .expression
    [.symbol "mm-internal-dv-rules",
      normalDVPairBeginRule, normalDVLeftConstRule,
      normalDVLeftVariableRule, normalDVRightConstRule,
      normalDVRightVariableRule, normalDVRightNilRule,
      normalDVLeftNilRule, normalDVCompleteRule]

private def normalBodyBuildConstInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-body-build", .var "proof", .var "pc",
          .expression
            [.symbol "mm-cons",
              .expression [.symbol "mm-const", .var "constant-name"],
              .var "source-tail"],
          .var "reversed-body", .var "context"]]

private def normalBodyBuildConstOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-body-build", .var "proof", .var "pc",
              .expression
                [.symbol "mm-cons",
                  .expression [.symbol "mm-const", .var "constant-name"],
                  .var "source-tail"],
              .var "reversed-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-body-build", .var "proof", .var "pc",
              .var "source-tail",
              .expression
                [.symbol "mm-cons",
                  .expression [.symbol "mm-const", .var "constant-name"],
                  .var "reversed-body"],
              .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-body-build", .var "proof", .var "pc"]]]

def normalBodyBuildConstRule : Atom :=
  .expression
    [.symbol "exec", normalBodyBuildConstLocation,
      normalBodyBuildConstInput, normalBodyBuildConstOutput]

private def normalBodyBuildVariableInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-body-build", .var "proof", .var "pc",
          .expression
            [.symbol "mm-cons",
              .expression [.symbol "mm-variable", .var "variable-name"],
              .var "source-tail"],
          .var "reversed-body", .var "context"],
      .expression
        [.symbol "mm-substitution", .var "proof", .var "pc",
          .var "variable-name", .var "replacement-body"]]

private def normalBodyBuildVariableOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-body-build", .var "proof", .var "pc",
              .expression
                [.symbol "mm-cons",
                  .expression [.symbol "mm-variable", .var "variable-name"],
                  .var "source-tail"],
              .var "reversed-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
              .var "replacement-body", .var "source-tail",
              .var "reversed-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-body-build", .var "proof", .var "pc"]]]

def normalBodyBuildVariableRule : Atom :=
  .expression
    [.symbol "exec", normalBodyBuildVariableLocation,
      normalBodyBuildVariableInput, normalBodyBuildVariableOutput]

private def normalBodyBuildPrefixNilInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
          .expression [.symbol "mm-nil"], .var "source-tail",
          .var "reversed-body", .var "context"]]

private def normalBodyBuildPrefixNilOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
              .expression [.symbol "mm-nil"], .var "source-tail",
              .var "reversed-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-body-build", .var "proof", .var "pc",
              .var "source-tail", .var "reversed-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-body-build", .var "proof", .var "pc"]]]

def normalBodyBuildPrefixNilRule : Atom :=
  .expression
    [.symbol "exec", normalBodyBuildPrefixNilLocation,
      normalBodyBuildPrefixNilInput, normalBodyBuildPrefixNilOutput]

private def normalBodyBuildPrefixConsInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
          .expression
            [.symbol "mm-cons", .var "replacement-symbol",
              .var "replacement-tail"],
          .var "source-tail", .var "reversed-body", .var "context"]]

private def normalBodyBuildPrefixConsOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
              .expression
                [.symbol "mm-cons", .var "replacement-symbol",
                  .var "replacement-tail"],
              .var "source-tail", .var "reversed-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
              .var "replacement-tail", .var "source-tail",
              .expression
                [.symbol "mm-cons", .var "replacement-symbol",
                  .var "reversed-body"],
              .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-body-build", .var "proof", .var "pc"]]]

def normalBodyBuildPrefixConsRule : Atom :=
  .expression
    [.symbol "exec", normalBodyBuildPrefixConsLocation,
      normalBodyBuildPrefixConsInput, normalBodyBuildPrefixConsOutput]

private def normalBodyBuildNilInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-body-build", .var "proof", .var "pc",
          .expression [.symbol "mm-nil"], .var "reversed-body",
          .var "context"]]

private def normalBodyBuildNilOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-body-build", .var "proof", .var "pc",
              .expression [.symbol "mm-nil"], .var "reversed-body",
              .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-body-reverse", .var "proof", .var "pc",
              .var "reversed-body", .expression [.symbol "mm-nil"],
              .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-body-build", .var "proof", .var "pc"]]]

def normalBodyBuildNilRule : Atom :=
  .expression
    [.symbol "exec", normalBodyBuildNilLocation,
      normalBodyBuildNilInput, normalBodyBuildNilOutput]

private def normalBodyReverseConsInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-body-reverse", .var "proof", .var "pc",
          .expression
            [.symbol "mm-cons", .var "head", .var "reversed-tail"],
          .var "result-body", .var "context"]]

private def normalBodyReverseConsOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-body-reverse", .var "proof", .var "pc",
              .expression
                [.symbol "mm-cons", .var "head", .var "reversed-tail"],
              .var "result-body", .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-body-reverse", .var "proof", .var "pc",
              .var "reversed-tail",
              .expression
                [.symbol "mm-cons", .var "head", .var "result-body"],
              .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-reload-body-build", .var "proof", .var "pc"]]]

def normalBodyReverseConsRule : Atom :=
  .expression
    [.symbol "exec", normalBodyReverseConsLocation,
      normalBodyReverseConsInput, normalBodyReverseConsOutput]

private def normalBodyReverseNilInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-body-reverse", .var "proof", .var "pc",
          .expression [.symbol "mm-nil"], .var "result-body",
          .var "context"]]

private def normalBodyReverseNilOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-body-reverse", .var "proof", .var "pc",
              .expression [.symbol "mm-nil"], .var "result-body",
              .var "context"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-body-built", .var "proof", .var "pc",
              .var "context", .var "result-body"]]]

def normalBodyReverseNilRule : Atom :=
  .expression
    [.symbol "exec", normalBodyReverseNilLocation,
      normalBodyReverseNilInput, normalBodyReverseNilOutput]

private def normalBodyBuildReloadInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "exec", normalBodyBuildReloadLocation,
          .var "build-reload-self-input", .var "build-reload-self-output"],
      .expression
        [.symbol "mm-reload-body-build", .var "build-reload-proof",
          .var "build-reload-pc"],
      .expression
        [.symbol "mm-internal-body-build-rules",
          .var "build-rule-const", .var "build-rule-variable",
          .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
          .var "build-rule-nil", .var "build-rule-reverse-cons",
          .var "build-rule-reverse-nil"]]

private def normalBodyBuildReloadOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "+",
          .expression
            [.symbol "exec", normalBodyBuildReloadLocation,
              .var "build-reload-self-input",
              .var "build-reload-self-output"]],
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-reload-body-build", .var "build-reload-proof",
              .var "build-reload-pc"]],
      .expression [.symbol "+", .var "build-rule-const"],
      .expression [.symbol "+", .var "build-rule-variable"],
      .expression [.symbol "+", .var "build-rule-prefix-nil"],
      .expression [.symbol "+", .var "build-rule-prefix-cons"],
      .expression [.symbol "+", .var "build-rule-nil"],
      .expression [.symbol "+", .var "build-rule-reverse-cons"],
      .expression [.symbol "+", .var "build-rule-reverse-nil"]]

def normalBodyBuildReloadRule : Atom :=
  .expression
    [.symbol "exec", normalBodyBuildReloadLocation,
      normalBodyBuildReloadInput, normalBodyBuildReloadOutput]

/-- Verifier-owned code bytes captured by the body-builder reload rule.  The
inner variables belong to the reloaded `exec` expressions; binding each whole
rule atom keeps them opaque at the outer reload level. -/
def normalBodyBuildRuleBundle : Atom :=
  .expression
    [.symbol "mm-internal-body-build-rules",
      normalBodyBuildConstRule, normalBodyBuildVariableRule,
      normalBodyBuildPrefixNilRule, normalBodyBuildPrefixConsRule,
      normalBodyBuildNilRule, normalBodyReverseConsRule,
      normalBodyReverseNilRule]

def normalBodyBuildMachineRules : List Atom :=
  [normalBodyBuildConstRule, normalBodyBuildVariableRule,
   normalBodyBuildPrefixNilRule, normalBodyBuildPrefixConsRule,
   normalBodyBuildNilRule, normalBodyReverseConsRule,
   normalBodyReverseNilRule, normalBodyBuildReloadRule]

private def normalAssertionResultCompleteInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "mm-body-built", .var "proof", .var "pc",
          .expression
            [.symbol "mm-assertion-result-context", .var "scope",
              .var "next-pc", .var "label", .var "result-typecode",
              .var "stack-base", .var "next-top"],
          .var "result-body"]]

private def normalAssertionResultCompleteOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-body-built", .var "proof", .var "pc",
              .expression
                [.symbol "mm-assertion-result-context", .var "scope",
                  .var "next-pc", .var "label", .var "result-typecode",
                  .var "stack-base", .var "next-top"],
              .var "result-body"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-normal-control", .var "scope", .var "proof",
              .var "next-pc", .var "next-top"]],
      .expression
        [.symbol "+",
          .expression
            [.symbol "mm-stack-cell", .var "proof", .var "stack-base",
              .expression
                [.symbol "mm-formula", .var "result-typecode",
                  .var "result-body"],
              .expression
                [.symbol "mm-assertion-occurrence", .var "pc",
                  .var "label"]]],
      .expression
        [.symbol "+",
          .expression [.symbol "mm-reload-normal-dispatch", .var "proof"]]]

def normalAssertionResultCompleteRule : Atom :=
  .expression
    [.symbol "exec", normalAssertionResultCompleteLocation,
      normalAssertionResultCompleteInput,
      normalAssertionResultCompleteOutput]

private def normalAcceptPatternAtoms : List Atom :=
  [.expression
        [.symbol "mm-normal-control", .var "scope", .var "proof",
          .var "end", .var "top"],
   .expression
        [.symbol "mm-proof-end", .var "proof", .var "end"],
   .expression
        [.symbol "mm-proof", .var "scope", .var "proof",
          .symbol "normal", .var "theorem-label", .var "expected"],
   .expression
        [.symbol "mm-index-successor", .var "proof",
          natAtom 0, .var "top"],
   .expression
        [.symbol "mm-stack-cell", .var "proof", natAtom 0,
          .var "expected", .var "occurrence"]]

private def normalAcceptInput : Atom :=
  .expression (.symbol "," :: normalAcceptPatternAtoms)

/-- Public terminal observation produced by the ordinary MM2 normal-proof
machine.  It retains source scope, dynamic proof identity, theorem claim,
formula, and the exact final proof occurrence. -/
def normalAcceptedAtom (scopeOwner proofOwner theoremLabel expected
    occurrence : Atom) : Atom :=
  .expression
    [.symbol "mm-accepted", scopeOwner, proofOwner, theoremLabel, expected,
      occurrence]

/-- The ordered-event continuation consumes the normal machine's actual
terminal wire observation when the proof owner is source-position indexed. -/
@[simp] theorem sourceTheoremNormalAcceptedAtom_eq_normalAcceptedAtom
    (owner : Atom) (position : Nat)
    (theoremLabel expected proofOccurrence : Atom) :
    sourceTheoremNormalAcceptedAtom owner position theoremLabel expected
        proofOccurrence =
      normalAcceptedAtom owner (sourceTheoremProofOwnerAtom owner position)
        theoremLabel expected proofOccurrence := by
  rfl

private def normalAcceptedTemplate : Atom :=
  normalAcceptedAtom (.var "scope") (.var "proof")
    (.var "theorem-label") (.var "expected") (.var "occurrence")

private def normalAcceptControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope", .var "proof",
      .var "end", .var "top"]

private def normalAcceptSinks : List Sink :=
  [.remove normalAcceptControlTemplate, .add normalAcceptedTemplate]

private def normalAcceptOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "-", normalAcceptControlTemplate],
      .expression
        [.symbol "+",
          normalAcceptedTemplate]]

/-- Terminal acceptance for an exhausted normal proof with exactly one
represented stack cell carrying the claimed formula. -/
def normalAcceptRule : Atom :=
  .expression
    [.symbol "exec", normalAcceptLocation,
      normalAcceptInput, normalAcceptOutput]

/-- The actual ordinary-MM2 parser sees the acceptance directive with exactly
one control removal and one terminal-observation addition. -/
theorem normalAcceptRule_sinks_exact :
    (extractSupportedSourceExecFact normalAcceptRule).map
        (fun directive => directive.rule.tmpl.sinks) =
      some
        normalAcceptSinks := by
  rfl

private def normalAcceptSubstitution (scopeOwner proofOwner endPosition
    topPosition theoremLabel expected occurrence : Atom) : Subst :=
  [("occurrence", occurrence), ("expected", expected),
   ("theorem-label", theoremLabel), ("top", topPosition),
   ("end", endPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

/-- Once the acceptance input has bound its seven fields, reflective MM2
instantiation produces exactly the declared terminal observation.  Captured
code and surface rendering play no role in this boundary. -/
theorem normalAcceptedTemplate_instantiates
    (scopeOwner proofOwner endPosition topPosition theoremLabel expected
      occurrence : Atom) :
    instantiateTemplateAtom?
        (normalAcceptSubstitution scopeOwner proofOwner endPosition
          topPosition theoremLabel expected occurrence)
        normalAcceptedTemplate =
      some
        (normalAcceptedAtom scopeOwner proofOwner theoremLabel expected
          occurrence) := by
  rfl

/-- The supported ordinary-MM2 directive represented by the emitted
acceptance rule itself. -/
def normalAcceptDirective : SourceExecFact where
  atom := normalAcceptRule
  loc := normalAcceptLocation
  rule :=
    { priority := 33
      name := "mm-normal-accept"
      input := .compat (mkPattern normalAcceptPatternAtoms)
      guards := []
      tmpl := mkTemplate normalAcceptSinks }

/-- Parsing the actual emitted atom recovers the exact directive used by the
semantic firing theorem. -/
theorem extract_normalAcceptRule_exact :
    extractSupportedSourceExecFact normalAcceptRule =
      some normalAcceptDirective := by
  rfl

/-- Canonical target boundary immediately before terminal acceptance.  This
contains only the emitted rule and the five data facts demanded by its input;
the arbitrary-proof theorem reaches this boundary after processing the label
stream. -/
def normalAcceptPhaseSpace (scopeOwner proofOwner theoremLabel expected
    occurrence : Atom) (endPosition : Nat) : Space :=
  [normalAcceptRule,
   .expression
    [.symbol "mm-normal-control", scopeOwner, proofOwner,
      natAtom endPosition, natAtom 1],
   .expression
    [.symbol "mm-proof-end", proofOwner, natAtom endPosition],
   .expression
    [.symbol "mm-proof", scopeOwner, proofOwner, .symbol "normal",
      theoremLabel, expected],
   .expression
    [.symbol "mm-index-successor", proofOwner, natAtom 0, natAtom 1],
   .expression
    [.symbol "mm-stack-cell", proofOwner, natAtom 0, expected,
      occurrence]].toFinset

/-- The ordinary scheduler selects terminal acceptance when the dynamic proof
has ended with exactly one stack cell equal to the expected theorem formula. -/
theorem normalAcceptPhase_selects_directive
    (scopeOwner proofOwner theoremLabel expected occurrence : Atom)
    (endPosition : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAcceptPhaseSpace scopeOwner proofOwner theoremLabel expected
            occurrence endPosition)) =
      some normalAcceptDirective := by
  let atoms :=
    [normalAcceptRule,
     .expression
      [.symbol "mm-normal-control", scopeOwner, proofOwner,
        natAtom endPosition, natAtom 1],
     .expression
      [.symbol "mm-proof-end", proofOwner, natAtom endPosition],
     .expression
      [.symbol "mm-proof", scopeOwner, proofOwner, .symbol "normal",
        theoremLabel, expected],
     .expression
      [.symbol "mm-index-successor", proofOwner, natAtom 0, natAtom 1],
     .expression
      [.symbol "mm-stack-cell", proofOwner, natAtom 0, expected,
        occurrence]]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAcceptDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAcceptDirective
    (by simp [atoms, normalAcceptRule, normalAcceptLocation,
      normalAcceptInput, normalAcceptOutput, normalAcceptPatternAtoms])
    (by rfl)

private theorem reflectiveStage_add_contains_of_row
    (rows : List Subst) (substitution : Subst) (template candidate : Atom)
    (rowMember : substitution ∈ rows)
    (instantiates : instantiateTemplateAtom? substitution template =
      some candidate) :
    candidate ∈ rows.foldl
      (stageReflectiveSupportSink (.add template)) [] := by
  have stagePreserves : ∀ (remaining : List Subst) (staged : List Atom),
      candidate ∈ staged →
      candidate ∈ remaining.foldl
        (stageReflectiveSupportSink (.add template)) staged := by
    intro remaining
    induction remaining with
    | nil =>
        intro staged member
        exact member
    | cons head tail induction =>
        intro staged member
        apply induction
        simp only [stageReflectiveSupportSink, Sink.atom]
        split
        · exact member
        · simp only [insertSupport]
          split
          · exact member
          · exact List.mem_append_left _ member
  suffices containsOfRow : ∀ (remaining : List Subst) (staged : List Atom),
      substitution ∈ remaining →
      candidate ∈ remaining.foldl
        (stageReflectiveSupportSink (.add template)) staged by
    exact containsOfRow rows [] rowMember
  intro remaining
  induction remaining with
  | nil =>
      intro staged rowMember
      simp at rowMember
  | cons head tail induction =>
      intro staged rowMember
      simp only [List.mem_cons] at rowMember
      simp only [List.foldl_cons]
      rcases rowMember with rfl | rowMember
      · apply stagePreserves tail
          (stageReflectiveSupportSink (.add template) staged substitution)
        simp only [stageReflectiveSupportSink, Sink.atom]
        rw [instantiates]
        by_cases present : candidate ∈ staged
        · simp [insertSupport, present]
        · simp [insertSupport, present]
      · exact induction
          (stageReflectiveSupportSink (.add template) staged head) rowMember

/-- The body reloader reinstalls the exact captured case-rule atoms.  This is
the semantic property that syntactic surface acceptance alone cannot show. -/
theorem normalBodyReloadDirective_fires_boundary_rules
    (proofOwner : Atom) (proofPosition : Nat) :
    let result := fireReflectiveSourceExecFact
      (normalBodyReloadPhaseSpace proofOwner proofPosition)
      normalBodyReloadDirective
    normalBodyMatchConstRule ∈ result ∧
      normalBodyMatchNilRule ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyReloadPhaseSpace proofOwner proofPosition)
      normalBodyReloadDirective.atom)
    normalBodyReloadDirective.rule.input).map Prod.fst
  let substitution := normalBodyReloadSubstitution proofOwner proofPosition
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyReloadDirective] using
      normalBodyReloadMatchRow_mem proofOwner proofPosition
  have constInstantiates :
      instantiateTemplateAtom? substitution (.var "body-rule-const") =
        some normalBodyMatchConstRule := by
    rfl
  have nilInstantiates :
      instantiateTemplateAtom? substitution (.var "body-rule-nil") =
        some normalBodyMatchNilRule := by
    rfl
  have constStaged := reflectiveStage_add_contains_of_row rows substitution
    (.var "body-rule-const") normalBodyMatchConstRule rowMember
    constInstantiates
  have nilStaged := reflectiveStage_add_contains_of_row rows substitution
    (.var "body-rule-nil") normalBodyMatchNilRule rowMember nilInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyReloadDirective, normalBodyReloadSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_union_left _
            (Finset.mem_union_right _
              (List.mem_toFinset.mpr constStaged)))))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyReloadDirective, normalBodyReloadSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr nilStaged)

/-! ### Active-hypothesis transition boundary -/

/-- Exact proof occurrence produced by the target active-hypothesis step. -/
def normalHypothesisStackAtom (proofOwner : Atom) (stackPosition : Nat)
    (hypothesis : HypothesisView) (proofPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-stack-cell", proofOwner, natAtom stackPosition,
      formulaAtom hypothesis.formula, natAtom proofPosition]

/-- The finite atom state of the canonical active-hypothesis phase.
Keeping this list explicit lets the computable scheduler and finite-support
semantics be related without choosing an enumeration of a `Finset`. -/
def normalHypothesisPhaseAtoms (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) : List Atom :=
  [normalHypothesisStepRule,
   .expression
    [.symbol "mm-normal-control", scopeOwner, proofOwner,
      natAtom proofPosition, natAtom stackPosition],
   linkedRow "normal-proof-label" proofOwner proofPosition nextProofPosition
     (stringAtom hypothesis.label),
   hypothesisLookupRow scopeOwner hypothesis,
   .expression
    [.symbol "mm-index-successor", proofOwner, natAtom stackPosition,
      natAtom nextStackPosition]]

/-- Canonical MM2 boundary for one source-indexed active-hypothesis step. -/
def normalHypothesisPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) : Space :=
  (normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition stackPosition nextStackPosition hypothesis).toFinset

private theorem normalHypothesisPhaseAtoms_nodup
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) :
    (normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition stackPosition nextStackPosition hypothesis).Nodup := by
  cases hypothesis <;>
    simp [normalHypothesisPhaseAtoms, normalHypothesisStepRule,
      hypothesisLookupRow, linkedRow]

private theorem normalHypothesisPhaseAtoms_supported
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) :
    cSupportedSourceExecFacts
        (normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
          nextProofPosition stackPosition nextStackPosition hypothesis) =
      [normalHypothesisDirective] := by
  cases hypothesis <;>
    rfl

private theorem normalHypothesisPhaseAtoms_raw
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) :
    cRawExecFacts
        (normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
          nextProofPosition stackPosition nextStackPosition hypothesis) =
      [⟨normalHypothesisStepRule, normalStepLocation,
        normalStepInput, normalStepOutput⟩] := by
  cases hypothesis <;>
    rfl

private theorem normalHypothesisDirective_support_set_template :
    ReflectiveSupportSetTemplate normalHypothesisDirective.rule.tmpl := by
  simp [ReflectiveSupportSetTemplate, normalHypothesisDirective,
    normalStepSinks, ReflectiveSupportSetSink, mkTemplate]

/-- The generic active-hypothesis phase satisfies the complete executable-
to-authored realization invariant, not only the support-level singleton
scheduler condition. -/
theorem normalHypothesisPhase_reflective_invariant
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) :
    ReflectiveWorkQueueInvariant
      (normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
        nextProofPosition stackPosition nextStackPosition hypothesis) := by
  let atoms := normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition stackPosition nextStackPosition hypothesis
  constructor
  · exact normalHypothesisPhaseAtoms_nodup scopeOwner proofOwner
      proofPosition nextProofPosition stackPosition nextStackPosition
      hypothesis
  · rw [show cSupportedSourceExecFacts atoms =
        [normalHypothesisDirective] from
      normalHypothesisPhaseAtoms_supported scopeOwner proofOwner
        proofPosition nextProofPosition stackPosition nextStackPosition
        hypothesis]
    simp [KeyInjective]
  · rw [show cRawExecFacts atoms =
        [⟨normalHypothesisStepRule, normalStepLocation,
          normalStepInput, normalStepOutput⟩] from
      normalHypothesisPhaseAtoms_raw scopeOwner proofOwner proofPosition
        nextProofPosition stackPosition nextStackPosition hypothesis]
    simp [KeyInjective]
  · intro directive selected
    have equal : directive = normalHypothesisDirective := by
      rw [show cSupportedSourceExecFacts atoms =
          [normalHypothesisDirective] from
        normalHypothesisPhaseAtoms_supported scopeOwner proofOwner
          proofPosition nextProofPosition stackPosition nextStackPosition
          hypothesis] at selected
      simpa [selectNextScheduled] using selected.symm
    subst directive
    have nodup := normalHypothesisPhaseAtoms_nodup scopeOwner proofOwner
      proofPosition nextProofPosition stackPosition nextStackPosition
      hypothesis
    exact reflectiveSourceFiringAgreement_of_supportAlignment atoms
      normalHypothesisDirective nodup
      normalHypothesisDirective_support_set_template
      (reflectiveSourceRowSupportAlignment_of_nodup atoms
        normalHypothesisDirective nodup)
  · intro raw directive selected decoded
    have rawEqual : raw =
        ⟨normalHypothesisStepRule, normalStepLocation,
          normalStepInput, normalStepOutput⟩ := by
      rw [show cRawExecFacts atoms =
          [⟨normalHypothesisStepRule, normalStepLocation,
            normalStepInput, normalStepOutput⟩] from
        normalHypothesisPhaseAtoms_raw scopeOwner proofOwner proofPosition
          nextProofPosition stackPosition nextStackPosition hypothesis] at selected
      simpa [selectNextScheduled] using selected.symm
    subst raw
    have directiveEqual : directive = normalHypothesisDirective := by
      change some normalHypothesisDirective = some directive at decoded
      exact (Option.some.inj decoded).symm
    subst directive
    have nodup := normalHypothesisPhaseAtoms_nodup scopeOwner proofOwner
      proofPosition nextProofPosition stackPosition nextStackPosition
      hypothesis
    exact reflectiveSourceFiringAgreement_of_supportAlignment atoms
      normalHypothesisDirective nodup
      normalHypothesisDirective_support_set_template
      (reflectiveSourceRowSupportAlignment_of_nodup atoms
        normalHypothesisDirective nodup)

/-- The real reflective scheduler selects the emitted hypothesis directive in
its canonical phase space.  This closes the gap between direct rule firing
lemmas and an actual target GSLT step. -/
theorem normalHypothesisPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalHypothesisPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition stackPosition nextStackPosition hypothesis)) =
      some normalHypothesisDirective := by
  let atoms := normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition stackPosition nextStackPosition hypothesis
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalHypothesisDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalHypothesisDirective
    (normalHypothesisPhaseAtoms_nodup scopeOwner proofOwner proofPosition
      nextProofPosition stackPosition nextStackPosition hypothesis)
    (normalHypothesisPhaseAtoms_supported scopeOwner proofOwner proofPosition
      nextProofPosition stackPosition nextStackPosition hypothesis)

/-- The computable MM2 scheduler takes the actual hypothesis directive from
the canonical phase list and returns its concrete fired successor. -/
theorem normalHypothesisPhase_cstep
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) :
    let atoms := normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition stackPosition nextStackPosition hypothesis
    cReflectiveSourceWorkQueueStep .leaveInert atoms =
      some (cFireReflectiveSourceExecFact atoms normalHypothesisDirective) := by
  let atoms := normalHypothesisPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition stackPosition nextStackPosition hypothesis
  have invariant := normalHypothesisPhase_reflective_invariant scopeOwner
    proofOwner proofPosition nextProofPosition stackPosition nextStackPosition
    hypothesis
  have supportSelected :
      selectNextScheduled
          (supportedSourceExecFactsOfSpace atoms.toFinset) =
        some normalHypothesisDirective := by
    change selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalHypothesisPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition stackPosition nextStackPosition hypothesis)) =
      some normalHypothesisDirective
    exact normalHypothesisPhase_selects_directive scopeOwner proofOwner
      proofPosition nextProofPosition stackPosition nextStackPosition
      hypothesis
  have concreteSelected :
      selectNextScheduled (cSupportedSourceExecFacts atoms) =
        some normalHypothesisDirective := by
    rw [cSourceWorkQueueStep_selectSupported_eq atoms invariant.nodup
      invariant.supportedKeyInj]
    exact supportSelected
  change (match selectNextScheduled (cSupportedSourceExecFacts atoms) with
    | none => none
    | some directive =>
        some (cFireReflectiveSourceExecFact atoms directive)) =
      some (cFireReflectiveSourceExecFact atoms normalHypothesisDirective)
  rw [concreteSelected]

private def normalHypothesisSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) : Subst :=
  [("next-top", natAtom nextStackPosition),
   ("formula", formulaAtom hypothesis.formula),
   ("label", stringAtom hypothesis.label),
   ("next-pc", natAtom nextProofPosition),
   ("top", natAtom stackPosition),
   ("pc", natAtom proofPosition),
   ("proof", proofOwner), ("scope", scopeOwner),
   ("self-output", normalStepOutput), ("self-input", normalStepInput)]

private theorem normalHypothesisMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) :
    normalHypothesisSubstitution scopeOwner proofOwner proofPosition
        nextProofPosition stackPosition nextStackPosition hypothesis ∈
      (matchInputSpec []
        (readCopyAtom
          (normalHypothesisPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition stackPosition nextStackPosition hypothesis)
          normalHypothesisStepRule)
        normalHypothesisDirective.rule.input).map Prod.fst := by
  let control : Atom :=
    .expression
      [.symbol "mm-normal-control", scopeOwner, proofOwner,
        natAtom proofPosition, natAtom stackPosition]
  let proofRow : Atom :=
    linkedRow "normal-proof-label" proofOwner proofPosition
      nextProofPosition (stringAtom hypothesis.label)
  let lookupRow : Atom := hypothesisLookupRow scopeOwner hypothesis
  let successor : Atom :=
    .expression
      [.symbol "mm-index-successor", proofOwner, natAtom stackPosition,
        natAtom nextStackPosition]
  let read : Space := readCopyAtom
    (normalHypothesisPhaseSpace scopeOwner proofOwner proofPosition
      nextProofPosition stackPosition nextStackPosition hypothesis)
    normalHypothesisStepRule
  let afterSelf : Subst :=
    [("self-output", normalStepOutput), ("self-input", normalStepInput)]
  let afterControl : Subst :=
    [("top", natAtom stackPosition), ("pc", natAtom proofPosition),
     ("proof", proofOwner), ("scope", scopeOwner),
     ("self-output", normalStepOutput), ("self-input", normalStepInput)]
  let afterProofRow : Subst :=
    [("label", stringAtom hypothesis.label),
     ("next-pc", natAtom nextProofPosition),
     ("top", natAtom stackPosition), ("pc", natAtom proofPosition),
     ("proof", proofOwner), ("scope", scopeOwner),
     ("self-output", normalStepOutput), ("self-input", normalStepInput)]
  let afterLookup : Subst :=
    [("formula", formulaAtom hypothesis.formula),
     ("label", stringAtom hypothesis.label),
     ("next-pc", natAtom nextProofPosition),
     ("top", natAtom stackPosition), ("pc", natAtom proofPosition),
     ("proof", proofOwner), ("scope", scopeOwner),
     ("self-output", normalStepOutput), ("self-input", normalStepInput)]
  let finalRow : Subst :=
    normalHypothesisSubstitution scopeOwner proofOwner proofPosition
      nextProofPosition stackPosition nextStackPosition hypothesis
  have readMember (atom : Atom)
      (member : atom ∈
        normalHypothesisPhaseSpace scopeOwner proofOwner proofPosition
          nextProofPosition stackPosition nextStackPosition hypothesis) :
      atom ∈ read := by
    by_cases equal : atom = normalHypothesisStepRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : normalHypothesisStepRule ∈ read := by
    apply readMember
    simp [normalHypothesisPhaseSpace, normalHypothesisPhaseAtoms]
  have controlMem : control ∈ read := by
    apply readMember
    simp [control, normalHypothesisPhaseSpace, normalHypothesisPhaseAtoms]
  have proofRowMem : proofRow ∈ read := by
    apply readMember
    simp [proofRow, normalHypothesisPhaseSpace, normalHypothesisPhaseAtoms]
  have lookupRowMem : lookupRow ∈ read := by
    apply readMember
    simp [lookupRow, normalHypothesisPhaseSpace, normalHypothesisPhaseAtoms]
  have successorMem : successor ∈ read := by
    apply readMember
    simp [successor, normalHypothesisPhaseSpace, normalHypothesisPhaseAtoms]
  have matchLocation :
      matchAtom [] normalStepLocation normalStepLocation = some [] := by
    simp [normalStepLocation, matchAtom, matchAtom.matchAtomList]
  have matchSelf :
      matchAtom []
          (.expression
            [.symbol "exec", normalStepLocation,
              .var "self-input", .var "self-output"])
          normalHypothesisStepRule = some afterSelf := by
    simp [normalHypothesisStepRule, normalStepInput, normalStepOutput,
      afterSelf, matchAtom, matchAtom.matchAtomList, Subst.lookup,
      matchLocation]
  have matchControl :
      matchAtom afterSelf
          (.expression
            [.symbol "mm-normal-control", .var "scope", .var "proof",
              .var "pc", .var "top"])
          control = some afterControl := by
    simp [afterSelf, afterControl, control, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchProofLabelTag :
      matchAtom afterControl (stringAtom "normal-proof-label")
          (stringAtom "normal-proof-label") = some afterControl := by
    exact groundAtom_matchAtom_self afterControl
      (stringAtom "normal-proof-label") (by simp)
  have matchProofRow :
      matchAtom afterControl
          (.expression
            [.symbol "mm-linked-row", stringAtom "normal-proof-label",
              .var "proof", .var "pc", .var "next-pc", .var "label"])
          proofRow = some afterProofRow := by
    simp [afterControl, afterProofRow, proofRow, linkedRow, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, matchProofLabelTag]
  have matchLookup :
      matchAtom afterProofRow
          (.expression
            [.symbol "mm-hypothesis-lookup", .var "scope",
              .var "label", .var "formula"])
          lookupRow = some afterLookup := by
    cases hypothesis <;>
      simp [afterProofRow, afterLookup, lookupRow, hypothesisLookupRow,
        HypothesisView.label, HypothesisView.formula, matchAtom,
        matchAtom.matchAtomList, Subst.lookup]
  have matchSuccessor :
      matchAtom afterLookup
          (.expression
            [.symbol "mm-index-successor", .var "proof", .var "top",
              .var "next-top"])
          successor = some finalRow := by
    simp [afterLookup, finalRow, normalHypothesisSubstitution, successor,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow,
    {normalHypothesisStepRule, control, proofRow, lookupRow, successor}), ?_, rfl⟩
  simp only [normalHypothesisDirective, matchInputSpec,
    normalStepPatternAtoms, mkPattern, matchPattern, matchPattern.go,
    List.mem_flatMap]
  refine ⟨(afterSelf, normalHypothesisStepRule),
    matchOneInSpace_mem [] _ read normalHypothesisStepRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterControl, control),
    matchOneInSpace_mem afterSelf _ read control controlMem afterControl
      matchControl, ?_⟩
  refine ⟨(afterProofRow, proofRow),
    matchOneInSpace_mem afterControl _ read proofRow proofRowMem afterProofRow
      matchProofRow, ?_⟩
  refine ⟨(afterLookup, lookupRow),
    matchOneInSpace_mem afterProofRow _ read lookupRow lookupRowMem afterLookup
      matchLookup, ?_⟩
  refine ⟨(finalRow, successor),
    matchOneInSpace_mem afterLookup _ read successor successorMem finalRow
      matchSuccessor, ?_⟩
  simp [finalRow, control, proofRow, lookupRow, successor]

/-- Firing the actual emitted active-hypothesis directive produces the exact
source formula and proof occurrence as an MM2 stack cell. -/
theorem normalHypothesisDirective_fires_stack
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) :
    normalHypothesisStackAtom proofOwner stackPosition hypothesis
        proofPosition ∈
      fireReflectiveSourceExecFact
        (normalHypothesisPhaseSpace scopeOwner proofOwner proofPosition
          nextProofPosition stackPosition nextStackPosition hypothesis)
        normalHypothesisDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalHypothesisPhaseSpace scopeOwner proofOwner proofPosition
        nextProofPosition stackPosition nextStackPosition hypothesis)
      normalHypothesisDirective.atom)
    normalHypothesisDirective.rule.input).map Prod.fst
  have rowMember :
      normalHypothesisSubstitution scopeOwner proofOwner proofPosition
          nextProofPosition stackPosition nextStackPosition hypothesis ∈ rows := by
    simpa [rows, normalHypothesisDirective] using
      normalHypothesisMatchRow_mem scopeOwner proofOwner proofPosition
        nextProofPosition stackPosition nextStackPosition hypothesis
  have stackInstantiates :
      instantiateTemplateAtom?
          (normalHypothesisSubstitution scopeOwner proofOwner proofPosition
            nextProofPosition stackPosition nextStackPosition hypothesis)
          normalStepStackTemplate =
        some (normalHypothesisStackAtom proofOwner stackPosition hypothesis
          proofPosition) := by
    cases hypothesis <;>
      rfl
  have stagedMember :
      normalHypothesisStackAtom proofOwner stackPosition hypothesis
          proofPosition ∈
        rows.foldl
          (stageReflectiveSupportSink (.add normalStepStackTemplate)) [] :=
    reflectiveStage_add_contains_of_row rows
      (normalHypothesisSubstitution scopeOwner proofOwner proofPosition
        nextProofPosition stackPosition nextStackPosition hypothesis)
      normalStepStackTemplate
      (normalHypothesisStackAtom proofOwner stackPosition hypothesis
        proofPosition)
      rowMember stackInstantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalHypothesisDirective, normalStepSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr stagedMember)

/-- The canonical active-hypothesis boundary is an actual scheduled step of
the supplied reflective MM2 GSLT, hence an inhabitant of its OSLF-generated
native target type; the same step contains the exact source formula and proof
occurrence. -/
theorem normalHypothesisPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackPosition nextStackPosition : Nat)
    (hypothesis : HypothesisView) :
    let source := normalHypothesisPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition stackPosition nextStackPosition
      hypothesis
    let target := fireReflectiveSourceExecFact source
      normalHypothesisDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalHypothesisStackAtom proofOwner stackPosition hypothesis
        proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalHypothesisPhase_selects_directive scopeOwner proofOwner
          proofPosition nextProofPosition stackPosition nextStackPosition
          hypothesis))
  · exact normalHypothesisDirective_fires_stack scopeOwner proofOwner
      proofPosition nextProofPosition stackPosition nextStackPosition
      hypothesis

/-! ### Assertion-entry transition boundary -/

/-- One cursor state of the administrative backward walk that locates an
assertion's ordered stack suffix. -/
def normalAssertionPopCursorAtom (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisCursor stackCursor : Nat) : Atom :=
  .expression
    [.symbol "mm-assertion-pop", scopeOwner, proofOwner,
      natAtom proofPosition, natAtom nextProofPosition,
      stringAtom assertionLabel, natAtom hypothesisCursor,
      natAtom stackCursor]

/-- Exact assertion-pop state created after a dynamic proof label selects one
source-indexed assertion header. -/
def normalAssertionPopAtom (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertion : SourceAssertion)
    (stackTop : Nat) : Atom :=
  normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
    nextProofPosition assertion.label assertion.hypotheses.length stackTop

/-- The finite atom state of the canonical assertion-entry phase. -/
def normalAssertionStartPhaseAtoms (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) : List Atom :=
  [normalAssertionStartRule,
   .expression
    [.symbol "mm-normal-control", scopeOwner, proofOwner,
      natAtom proofPosition, natAtom stackTop],
   linkedRow "normal-proof-label" proofOwner proofPosition nextProofPosition
     (stringAtom assertion.label),
   assertionHeaderRow scopeOwner assertionPosition assertion]

/-- Canonical entry boundary for one actual assertion occurrence in the
source-owned database. -/
def normalAssertionStartPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) : Space :=
  (normalAssertionStartPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition stackTop assertionPosition assertion).toFinset

private theorem normalAssertionStartPhaseAtoms_nodup
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) :
    (normalAssertionStartPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition stackTop assertionPosition assertion).Nodup := by
  cases assertion
  all_goals
    simp [normalAssertionStartPhaseAtoms, normalAssertionStartRule,
      linkedRow, assertionHeaderRow]

private theorem normalAssertionStartPhaseAtoms_supported
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) :
    cSupportedSourceExecFacts
        (normalAssertionStartPhaseAtoms scopeOwner proofOwner proofPosition
          nextProofPosition stackTop assertionPosition assertion) =
      [normalAssertionStartDirective] := by
  cases assertion
  all_goals rfl

/-- The real reflective scheduler selects the emitted assertion-entry
directive in its canonical phase space. -/
theorem normalAssertionStartPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionStartPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition stackTop assertionPosition assertion)) =
      some normalAssertionStartDirective := by
  let atoms := normalAssertionStartPhaseAtoms scopeOwner proofOwner
    proofPosition nextProofPosition stackTop assertionPosition assertion
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionStartDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionStartDirective
    (normalAssertionStartPhaseAtoms_nodup scopeOwner proofOwner proofPosition
      nextProofPosition stackTop assertionPosition assertion)
    (normalAssertionStartPhaseAtoms_supported scopeOwner proofOwner
      proofPosition nextProofPosition stackTop assertionPosition assertion)

private def normalAssertionStartSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) : Subst :=
  [("hyp-end", natAtom assertion.hypotheses.length),
   ("assertion-position", natAtom assertionPosition),
   ("label", stringAtom assertion.label),
   ("next-pc", natAtom nextProofPosition),
   ("top", natAtom stackTop), ("pc", natAtom proofPosition),
   ("proof", proofOwner), ("scope", scopeOwner)]

private theorem normalAssertionStartMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) :
    normalAssertionStartSubstitution scopeOwner proofOwner proofPosition
        nextProofPosition stackTop assertionPosition assertion ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionStartPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition stackTop assertionPosition assertion)
          normalAssertionStartRule)
        normalAssertionStartDirective.rule.input).map Prod.fst := by
  let control : Atom :=
    .expression
      [.symbol "mm-normal-control", scopeOwner, proofOwner,
        natAtom proofPosition, natAtom stackTop]
  let proofRow : Atom := linkedRow "normal-proof-label" proofOwner
    proofPosition nextProofPosition (stringAtom assertion.label)
  let header : Atom := assertionHeaderRow scopeOwner assertionPosition assertion
  let read : Space := readCopyAtom
    (normalAssertionStartPhaseSpace scopeOwner proofOwner proofPosition
      nextProofPosition stackTop assertionPosition assertion)
    normalAssertionStartRule
  let afterControl : Subst :=
    [("top", natAtom stackTop), ("pc", natAtom proofPosition),
     ("proof", proofOwner), ("scope", scopeOwner)]
  let afterProof : Subst :=
    [("label", stringAtom assertion.label),
     ("next-pc", natAtom nextProofPosition),
     ("top", natAtom stackTop), ("pc", natAtom proofPosition),
     ("proof", proofOwner), ("scope", scopeOwner)]
  let finalRow := normalAssertionStartSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition stackTop assertionPosition assertion
  have readMember (atom : Atom)
      (member : atom ∈ normalAssertionStartPhaseSpace scopeOwner proofOwner
        proofPosition nextProofPosition stackTop assertionPosition assertion) :
      atom ∈ read := by
    by_cases equal : atom = normalAssertionStartRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have controlMem : control ∈ read := by
    apply readMember
    simp [control, normalAssertionStartPhaseSpace,
      normalAssertionStartPhaseAtoms]
  have proofRowMem : proofRow ∈ read := by
    apply readMember
    simp [proofRow, normalAssertionStartPhaseSpace,
      normalAssertionStartPhaseAtoms]
  have headerMem : header ∈ read := by
    apply readMember
    simp [header, normalAssertionStartPhaseSpace,
      normalAssertionStartPhaseAtoms]
  have matchControl :
      matchAtom [] (normalAssertionStartPatternAtoms[0]'(by decide)) control =
        some afterControl := by
    simp [normalAssertionStartPatternAtoms, control, afterControl, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchProof :
      matchAtom afterControl
          (normalAssertionStartPatternAtoms[1]'(by decide)) proofRow =
        some afterProof := by
    have matchTag :
        matchAtom afterControl (stringAtom "normal-proof-label")
            (stringAtom "normal-proof-label") = some afterControl := by
      exact groundAtom_matchAtom_self afterControl
        (stringAtom "normal-proof-label") (by simp)
    simp [normalAssertionStartPatternAtoms, afterControl, afterProof,
      proofRow, linkedRow, matchAtom, matchAtom.matchAtomList, Subst.lookup,
      matchTag]
  have matchHeader :
      matchAtom afterProof
          (normalAssertionStartPatternAtoms[2]'(by decide)) header =
        some finalRow := by
    cases assertion
    simp [normalAssertionStartPatternAtoms, afterProof, finalRow,
      normalAssertionStartSubstitution, header, assertionHeaderRow, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {control, proofRow, header}), ?_, rfl⟩
  simp only [normalAssertionStartDirective, matchInputSpec,
    normalAssertionStartPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterControl, control),
    matchOneInSpace_mem [] _ read control controlMem afterControl
      matchControl, ?_⟩
  refine ⟨(afterProof, proofRow),
    matchOneInSpace_mem afterControl _ read proofRow proofRowMem afterProof
      matchProof, ?_⟩
  refine ⟨(finalRow, header),
    matchOneInSpace_mem afterProof _ read header headerMem finalRow
      matchHeader, ?_⟩
  simp [finalRow, control, proofRow, header]

/-- Firing the actual emitted assertion-entry directive enters the exact
source assertion and preserves its ordered mandatory-hypothesis count. -/
theorem normalAssertionStartDirective_fires_pop
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) :
    normalAssertionPopAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertion stackTop ∈
      fireReflectiveSourceExecFact
        (normalAssertionStartPhaseSpace scopeOwner proofOwner proofPosition
          nextProofPosition stackTop assertionPosition assertion)
        normalAssertionStartDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalAssertionStartPhaseSpace scopeOwner proofOwner proofPosition
        nextProofPosition stackTop assertionPosition assertion)
      normalAssertionStartDirective.atom)
    normalAssertionStartDirective.rule.input).map Prod.fst
  let substitution := normalAssertionStartSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition stackTop assertionPosition assertion
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalAssertionStartDirective] using
      normalAssertionStartMatchRow_mem scopeOwner proofOwner proofPosition
        nextProofPosition stackTop assertionPosition assertion
  have instantiates :
      instantiateTemplateAtom? substitution normalAssertionStartPopTemplate =
        some (normalAssertionPopAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion stackTop) := by
    cases assertion
    rfl
  have stagedMember :
      normalAssertionPopAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion stackTop ∈
        rows.foldl
          (stageReflectiveSupportSink (.add normalAssertionStartPopTemplate))
          [] :=
    reflectiveStage_add_contains_of_row rows substitution
      normalAssertionStartPopTemplate
      (normalAssertionPopAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertion stackTop) rowMember instantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalAssertionStartDirective, normalAssertionStartSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr stagedMember)

/-- Assertion entry is an actual scheduled step of the reflective MM2 GSLT,
hence inhabits the exact target type generated by OSLF; the target retains the
source assertion's ordered mandatory-hypothesis cursor. -/
theorem normalAssertionStartPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackTop assertionPosition : Nat)
    (assertion : SourceAssertion) :
    let source := normalAssertionStartPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition stackTop assertionPosition assertion
    let target := fireReflectiveSourceExecFact source
      normalAssertionStartDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionPopAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertion stackTop ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionStartPhase_selects_directive scopeOwner proofOwner
          proofPosition nextProofPosition stackTop assertionPosition
          assertion))
  · exact normalAssertionStartDirective_fires_pop scopeOwner proofOwner
      proofPosition nextProofPosition stackTop assertionPosition assertion

/-- Finite atom state for one administrative backward cursor step. -/
def normalAssertionPopPhaseAtoms (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    List Atom :=
  [normalAssertionPopRule,
   normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
     nextProofPosition assertionLabel hypothesisCursor stackCursor,
   .expression
    [.symbol "mm-assertion-hypothesis-successor", scopeOwner,
      stringAtom assertionLabel, natAtom previousHypothesis,
      natAtom hypothesisCursor],
   .expression
    [.symbol "mm-index-successor", proofOwner, natAtom previousStack,
      natAtom stackCursor]]

/-- Canonical boundary for one administrative backward cursor step. -/
def normalAssertionPopPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    Space :=
  (normalAssertionPopPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition assertionLabel previousHypothesis hypothesisCursor
    previousStack stackCursor).toFinset

private theorem normalAssertionPopPhaseAtoms_nodup
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    (normalAssertionPopPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel previousHypothesis hypothesisCursor
      previousStack stackCursor).Nodup := by
  simp [normalAssertionPopPhaseAtoms, normalAssertionPopRule,
    normalAssertionPopCursorAtom]

private theorem normalAssertionPopPhaseAtoms_supported
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    cSupportedSourceExecFacts
        (normalAssertionPopPhaseAtoms scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel previousHypothesis hypothesisCursor
          previousStack stackCursor) =
      [normalAssertionPopDirective] := by
  rfl

/-- The real reflective scheduler selects the emitted assertion-pop directive
at this exact cursor boundary. -/
theorem normalAssertionPopPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionPopPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel previousHypothesis
            hypothesisCursor previousStack stackCursor)) =
      some normalAssertionPopDirective := by
  let atoms := normalAssertionPopPhaseAtoms scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel previousHypothesis
    hypothesisCursor previousStack stackCursor
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionPopDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionPopDirective
    (normalAssertionPopPhaseAtoms_nodup scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel previousHypothesis hypothesisCursor
      previousStack stackCursor)
    (normalAssertionPopPhaseAtoms_supported scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel previousHypothesis hypothesisCursor
      previousStack stackCursor)

private def normalAssertionPopSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    Subst :=
  [("previous-stack", natAtom previousStack),
   ("previous-hyp", natAtom previousHypothesis),
   ("stack-cursor", natAtom stackCursor),
   ("hyp-cursor", natAtom hypothesisCursor),
   ("label", stringAtom assertionLabel),
   ("next-pc", natAtom nextProofPosition),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner), ("self-output", normalAssertionPopOutput),
   ("self-input", normalAssertionPopInput)]

private theorem normalAssertionPopMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    normalAssertionPopSubstitution scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel previousHypothesis hypothesisCursor
        previousStack stackCursor ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionPopPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel previousHypothesis
            hypothesisCursor previousStack stackCursor)
          normalAssertionPopRule)
        normalAssertionPopDirective.rule.input).map Prod.fst := by
  let current := normalAssertionPopCursorAtom scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisCursor stackCursor
  let hypothesisSuccessor : Atom :=
    .expression
      [.symbol "mm-assertion-hypothesis-successor", scopeOwner,
        stringAtom assertionLabel, natAtom previousHypothesis,
        natAtom hypothesisCursor]
  let stackSuccessor : Atom :=
    .expression
      [.symbol "mm-index-successor", proofOwner, natAtom previousStack,
        natAtom stackCursor]
  let read := readCopyAtom
    (normalAssertionPopPhaseSpace scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel previousHypothesis hypothesisCursor
      previousStack stackCursor) normalAssertionPopRule
  let afterSelf : Subst :=
    [("self-output", normalAssertionPopOutput),
     ("self-input", normalAssertionPopInput)]
  let afterCurrent : Subst :=
    [("stack-cursor", natAtom stackCursor),
     ("hyp-cursor", natAtom hypothesisCursor),
     ("label", stringAtom assertionLabel),
     ("next-pc", natAtom nextProofPosition),
     ("pc", natAtom proofPosition), ("proof", proofOwner),
     ("scope", scopeOwner), ("self-output", normalAssertionPopOutput),
     ("self-input", normalAssertionPopInput)]
  let afterHypothesis : Subst :=
    ("previous-hyp", natAtom previousHypothesis) :: afterCurrent
  let finalRow := normalAssertionPopSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel previousHypothesis
    hypothesisCursor previousStack stackCursor
  have readMember (atom : Atom)
      (member : atom ∈ normalAssertionPopPhaseSpace scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel previousHypothesis
        hypothesisCursor previousStack stackCursor) : atom ∈ read := by
    by_cases equal : atom = normalAssertionPopRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : normalAssertionPopRule ∈ read := by
    apply readMember
    simp [normalAssertionPopPhaseSpace, normalAssertionPopPhaseAtoms]
  have currentMem : current ∈ read := by
    apply readMember
    simp [current, normalAssertionPopPhaseSpace,
      normalAssertionPopPhaseAtoms]
  have hypothesisSuccessorMem : hypothesisSuccessor ∈ read := by
    apply readMember
    simp [hypothesisSuccessor, normalAssertionPopPhaseSpace,
      normalAssertionPopPhaseAtoms]
  have stackSuccessorMem : stackSuccessor ∈ read := by
    apply readMember
    simp [stackSuccessor, normalAssertionPopPhaseSpace,
      normalAssertionPopPhaseAtoms]
  have matchLocation :
      matchAtom [] normalAssertionPopLocation normalAssertionPopLocation =
        some [] := by
    simp [normalAssertionPopLocation, matchAtom, matchAtom.matchAtomList]
  have matchSelf :
      matchAtom [] normalAssertionPopSelfTemplate normalAssertionPopRule =
        some afterSelf := by
    simp [normalAssertionPopSelfTemplate, normalAssertionPopRule,
      normalAssertionPopInput, normalAssertionPopOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, matchLocation]
  have matchCurrent :
      matchAtom afterSelf normalAssertionPopCurrentTemplate current =
        some afterCurrent := by
    simp [normalAssertionPopCurrentTemplate, current,
      normalAssertionPopCursorAtom, afterSelf, afterCurrent, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchHypothesisSuccessor :
      matchAtom afterCurrent
          (normalAssertionPopPatternAtoms[2]'(by decide))
          hypothesisSuccessor = some afterHypothesis := by
    simp [normalAssertionPopPatternAtoms, afterCurrent, afterHypothesis,
      hypothesisSuccessor, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchStackSuccessor :
      matchAtom afterHypothesis
          (normalAssertionPopPatternAtoms[3]'(by decide)) stackSuccessor =
        some finalRow := by
    simp [normalAssertionPopPatternAtoms, afterHypothesis, afterCurrent,
      finalRow, normalAssertionPopSubstitution, stackSuccessor, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow,
    {normalAssertionPopRule, current, hypothesisSuccessor, stackSuccessor}),
    ?_, rfl⟩
  simp only [normalAssertionPopDirective, matchInputSpec,
    normalAssertionPopPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterSelf, normalAssertionPopRule),
    matchOneInSpace_mem [] _ read normalAssertionPopRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterCurrent, current),
    matchOneInSpace_mem afterSelf _ read current currentMem afterCurrent
      matchCurrent, ?_⟩
  refine ⟨(afterHypothesis, hypothesisSuccessor),
    matchOneInSpace_mem afterCurrent _ read hypothesisSuccessor
      hypothesisSuccessorMem afterHypothesis matchHypothesisSuccessor, ?_⟩
  refine ⟨(finalRow, stackSuccessor),
    matchOneInSpace_mem afterHypothesis _ read stackSuccessor
      stackSuccessorMem finalRow matchStackSuccessor, ?_⟩
  simp [finalRow, current, hypothesisSuccessor, stackSuccessor]

/-- One actual pop firing decrements both cursors along the two explicit
successor relations. -/
theorem normalAssertionPopDirective_fires_previous
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel previousHypothesis previousStack ∈
      fireReflectiveSourceExecFact
        (normalAssertionPopPhaseSpace scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel previousHypothesis hypothesisCursor
          previousStack stackCursor)
        normalAssertionPopDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalAssertionPopPhaseSpace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel previousHypothesis hypothesisCursor
        previousStack stackCursor)
      normalAssertionPopDirective.atom)
    normalAssertionPopDirective.rule.input).map Prod.fst
  let substitution := normalAssertionPopSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel previousHypothesis
    hypothesisCursor previousStack stackCursor
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalAssertionPopDirective] using
      normalAssertionPopMatchRow_mem scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel previousHypothesis hypothesisCursor
        previousStack stackCursor
  have instantiates :
      instantiateTemplateAtom? substitution normalAssertionPopPreviousTemplate =
        some (normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel previousHypothesis previousStack) := by
    rfl
  have stagedMember :
      normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel previousHypothesis previousStack ∈
        rows.foldl
          (stageReflectiveSupportSink (.add normalAssertionPopPreviousTemplate))
          [] :=
    reflectiveStage_add_contains_of_row rows substitution
      normalAssertionPopPreviousTemplate
      (normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel previousHypothesis previousStack)
      rowMember instantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalAssertionPopDirective, normalAssertionPopSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr stagedMember)

/-- One cursor decrement is an actual scheduled reflective-MM2 step and
therefore inhabits the exact OSLF-generated target type. -/
theorem normalAssertionPopPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (previousHypothesis hypothesisCursor previousStack stackCursor : Nat) :
    let source := normalAssertionPopPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel previousHypothesis
      hypothesisCursor previousStack stackCursor
    let target := fireReflectiveSourceExecFact source
      normalAssertionPopDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel previousHypothesis previousStack ∈
        target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionPopPhase_selects_directive scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel previousHypothesis
          hypothesisCursor previousStack stackCursor))
  · exact normalAssertionPopDirective_fires_previous scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel previousHypothesis
      hypothesisCursor previousStack stackCursor

/-! ### Floating assertion-hypothesis transition boundary -/

/-- Stable substitution evidence retained by the MM2 assertion machine. -/
def normalAssertionSubstitutionAtom (proofOwner : Atom) (proofPosition : Nat)
    (variableName : String) (body : List Metamath.Verify.Sym) : Atom :=
  .expression
    [.symbol "mm-substitution", proofOwner, natAtom proofPosition,
      stringAtom variableName, listAtom runtimeSymAtom body]

/-- Decoded payload of one target substitution row.  Keeping the proof owner
and proof position in the codec makes row provenance explicit rather than
recovering it from an ambient execution. -/
structure NormalAssertionSubstitutionPayload where
  proofOwner : Atom
  proofPosition : Nat
  variableName : String
  body : List Metamath.Verify.Sym
deriving DecidableEq

def decodeNormalAssertionSubstitutionAtom : Atom →
    Option NormalAssertionSubstitutionPayload
  | .expression
      [.symbol tag, proofOwner, encodedPosition, encodedVariable,
        encodedBody] =>
      if tag = "mm-substitution" then do
        let proofPosition ← decodeNatAtom encodedPosition
        let variableName ← decodeStringAtom encodedVariable
        let body ← decodeListAtom decodeRuntimeSymAtom encodedBody
        pure ⟨proofOwner, proofPosition, variableName, body⟩
      else
        none
  | _ => none

@[simp] theorem decodeNormalAssertionSubstitutionAtom_encode
    (proofOwner : Atom) (proofPosition : Nat) (variableName : String)
    (body : List Metamath.Verify.Sym) :
    decodeNormalAssertionSubstitutionAtom
      (normalAssertionSubstitutionAtom proofOwner proofPosition variableName
        body) = some ⟨proofOwner, proofPosition, variableName, body⟩ := by
  simp [decodeNormalAssertionSubstitutionAtom, normalAssertionSubstitutionAtom]

theorem normalAssertionSubstitutionAtom_injective_payload
    (proofOwner : Atom) (proofPosition : Nat) :
    Function.Injective
      (fun pair : String × List Metamath.Verify.Sym =>
        normalAssertionSubstitutionAtom proofOwner proofPosition pair.1
          pair.2) := by
  intro left right equal
  have decoded := congrArg decodeNormalAssertionSubstitutionAtom equal
  have components : left.1 = right.1 ∧ left.2 = right.2 := by
    simpa using decoded
  exact Prod.ext components.1 components.2

/-- Stable edge from an assertion occurrence to one ordered proof child. -/
def normalAssertionChildAtom (proofOwner : Atom) (proofPosition
    hypothesisPosition childOccurrence : Nat) : Atom :=
  .expression
    [.symbol "mm-assertion-child", proofOwner, natAtom proofPosition,
      natAtom hypothesisPosition, natAtom childOccurrence]

theorem normalAssertionChildAtom_occurrence_injective
    (proofOwner : Atom) (proofPosition hypothesisPosition : Nat) :
    Function.Injective
      (normalAssertionChildAtom proofOwner proofPosition hypothesisPosition) := by
  intro left right equal
  apply natAtom_injective
  simpa [normalAssertionChildAtom] using equal

/-- Stable continuation after consuming one floating hypothesis. -/
def normalAssertionNextBindAtom (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase : Nat) :
    Atom :=
  .expression
    [.symbol "mm-assertion-bind", scopeOwner, proofOwner,
      natAtom proofPosition, natAtom nextProofPosition,
      stringAtom assertionLabel, natAtom nextHypothesisPosition,
      natAtom hypothesisEnd, natAtom nextStackPosition, natAtom stackBase]

/-- Finite atom state at the end of the administrative pop loop. -/
def normalAssertionBeginPhaseAtoms (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) : List Atom :=
  [normalAssertionBeginRule,
   normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
     nextProofPosition assertion.label 0 stackBase,
   assertionHeaderRow scopeOwner assertionPosition assertion]

/-- Canonical boundary at the end of the administrative pop loop. -/
def normalAssertionBeginPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) : Space :=
  (normalAssertionBeginPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition stackBase assertionPosition assertion).toFinset

private theorem normalAssertionBeginPhaseAtoms_nodup
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) :
    (normalAssertionBeginPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition stackBase assertionPosition assertion).Nodup := by
  cases assertion
  all_goals
    simp [normalAssertionBeginPhaseAtoms, normalAssertionBeginRule,
      normalAssertionPopCursorAtom, assertionHeaderRow]

private theorem normalAssertionBeginPhaseAtoms_supported
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) :
    cSupportedSourceExecFacts
        (normalAssertionBeginPhaseAtoms scopeOwner proofOwner proofPosition
          nextProofPosition stackBase assertionPosition assertion) =
      [normalAssertionBeginDirective] := by
  cases assertion
  all_goals rfl

/-- The real reflective scheduler selects the assertion-begin directive once
both ordered cursors have reached their common base. -/
theorem normalAssertionBeginPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionBeginPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition stackBase assertionPosition assertion)) =
      some normalAssertionBeginDirective := by
  let atoms := normalAssertionBeginPhaseAtoms scopeOwner proofOwner
    proofPosition nextProofPosition stackBase assertionPosition assertion
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionBeginDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionBeginDirective
    (normalAssertionBeginPhaseAtoms_nodup scopeOwner proofOwner proofPosition
      nextProofPosition stackBase assertionPosition assertion)
    (normalAssertionBeginPhaseAtoms_supported scopeOwner proofOwner
      proofPosition nextProofPosition stackBase assertionPosition assertion)

private def normalAssertionBeginSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) : Subst :=
  [("hyp-end", natAtom assertion.hypotheses.length),
   ("assertion-position", natAtom assertionPosition),
   ("stack-base", natAtom stackBase),
   ("label", stringAtom assertion.label),
   ("next-pc", natAtom nextProofPosition),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalAssertionBeginMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) :
    normalAssertionBeginSubstitution scopeOwner proofOwner proofPosition
        nextProofPosition stackBase assertionPosition assertion ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionBeginPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition stackBase assertionPosition assertion)
          normalAssertionBeginRule)
        normalAssertionBeginDirective.rule.input).map Prod.fst := by
  let pop := normalAssertionPopCursorAtom scopeOwner proofOwner proofPosition
    nextProofPosition assertion.label 0 stackBase
  let header := assertionHeaderRow scopeOwner assertionPosition assertion
  let read := readCopyAtom
    (normalAssertionBeginPhaseSpace scopeOwner proofOwner proofPosition
      nextProofPosition stackBase assertionPosition assertion)
    normalAssertionBeginRule
  let afterPop : Subst :=
    [("stack-base", natAtom stackBase),
     ("label", stringAtom assertion.label),
     ("next-pc", natAtom nextProofPosition),
     ("pc", natAtom proofPosition), ("proof", proofOwner),
     ("scope", scopeOwner)]
  let finalRow := normalAssertionBeginSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition stackBase assertionPosition assertion
  have readMember (atom : Atom)
      (member : atom ∈ normalAssertionBeginPhaseSpace scopeOwner proofOwner
        proofPosition nextProofPosition stackBase assertionPosition assertion) :
      atom ∈ read := by
    by_cases equal : atom = normalAssertionBeginRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have popMem : pop ∈ read := by
    apply readMember
    simp [pop, normalAssertionBeginPhaseSpace,
      normalAssertionBeginPhaseAtoms]
  have headerMem : header ∈ read := by
    apply readMember
    simp [header, normalAssertionBeginPhaseSpace,
      normalAssertionBeginPhaseAtoms]
  have matchNatZero :
      matchAtom
          [("label", stringAtom assertion.label),
           ("next-pc", natAtom nextProofPosition),
           ("pc", natAtom proofPosition), ("proof", proofOwner),
           ("scope", scopeOwner)]
          (natAtom 0) (natAtom 0) =
        some
          [("label", stringAtom assertion.label),
           ("next-pc", natAtom nextProofPosition),
           ("pc", natAtom proofPosition), ("proof", proofOwner),
           ("scope", scopeOwner)] := by
    exact groundAtom_matchAtom_self _ (natAtom 0)
      (isGroundAtom_natAtom 0)
  have matchPop :
      matchAtom [] (normalAssertionBeginPatternAtoms[0]'(by decide)) pop =
        some afterPop := by
    simp [normalAssertionBeginPatternAtoms, pop,
      normalAssertionPopCursorAtom, afterPop, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, matchNatZero]
  have matchHeader :
      matchAtom afterPop (normalAssertionBeginPatternAtoms[1]'(by decide))
          header = some finalRow := by
    cases assertion
    simp [normalAssertionBeginPatternAtoms, afterPop, finalRow,
      normalAssertionBeginSubstitution, header, assertionHeaderRow, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {pop, header}), ?_, rfl⟩
  simp only [normalAssertionBeginDirective, matchInputSpec,
    normalAssertionBeginPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterPop, pop),
    matchOneInSpace_mem [] _ read pop popMem afterPop matchPop, ?_⟩
  refine ⟨(finalRow, header),
    matchOneInSpace_mem afterPop _ read header headerMem finalRow
      matchHeader, ?_⟩
  simp [finalRow, pop, header]

/-- The actual begin directive turns the zero cursor into the exact first
hypothesis bind state. -/
theorem normalAssertionBeginDirective_fires_bind
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) :
    normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertion.label 0 assertion.hypotheses.length
        stackBase stackBase ∈
      fireReflectiveSourceExecFact
        (normalAssertionBeginPhaseSpace scopeOwner proofOwner proofPosition
          nextProofPosition stackBase assertionPosition assertion)
        normalAssertionBeginDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalAssertionBeginPhaseSpace scopeOwner proofOwner proofPosition
        nextProofPosition stackBase assertionPosition assertion)
      normalAssertionBeginDirective.atom)
    normalAssertionBeginDirective.rule.input).map Prod.fst
  let substitution := normalAssertionBeginSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition stackBase assertionPosition assertion
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalAssertionBeginDirective] using
      normalAssertionBeginMatchRow_mem scopeOwner proofOwner proofPosition
        nextProofPosition stackBase assertionPosition assertion
  have instantiates :
      instantiateTemplateAtom? substitution normalAssertionBeginBindTemplate =
        some (normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion.label 0 assertion.hypotheses.length
          stackBase stackBase) := by
    cases assertion
    rfl
  have stagedMember :
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertion.label 0 assertion.hypotheses.length
          stackBase stackBase ∈
        rows.foldl
          (stageReflectiveSupportSink (.add normalAssertionBeginBindTemplate))
          [] :=
    reflectiveStage_add_contains_of_row rows substitution
      normalAssertionBeginBindTemplate
      (normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertion.label 0 assertion.hypotheses.length
        stackBase stackBase) rowMember instantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalAssertionBeginDirective, normalAssertionBeginSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr stagedMember)

/-- The transition from the zero pop cursor to the first ordered bind state is
an actual scheduled reflective-MM2 step inhabiting its OSLF-generated target
type. -/
theorem normalAssertionBeginPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition stackBase assertionPosition : Nat)
    (assertion : SourceAssertion) :
    let source := normalAssertionBeginPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition stackBase assertionPosition assertion
    let target := fireReflectiveSourceExecFact source
      normalAssertionBeginDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertion.label 0 assertion.hypotheses.length
        stackBase stackBase ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionBeginPhase_selects_directive scopeOwner proofOwner
          proofPosition nextProofPosition stackBase assertionPosition
          assertion))
  · exact normalAssertionBeginDirective_fires_bind scopeOwner proofOwner
      proofPosition nextProofPosition stackBase assertionPosition assertion

/-- Finite atom state for one floating hypothesis in an assertion
application.  It contains the exact source-indexed hypothesis row and the
exact child stack occurrence consumed by the emitted generic rule. -/
def normalAssertionFloatingPhaseAtoms (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) :
    List Atom :=
  [normalAssertionFloatingRule,
   .expression
    [.symbol "mm-assertion-bind", scopeOwner, proofOwner,
      natAtom proofPosition, natAtom nextProofPosition,
      stringAtom assertionLabel, natAtom hypothesisPosition,
      natAtom hypothesisEnd, natAtom stackPosition, natAtom stackBase],
   .expression
    [.symbol "mm-assertion-hypothesis", scopeOwner,
      stringAtom assertionLabel, natAtom hypothesisPosition,
      .expression
        [.symbol "mm-floating", stringAtom hypothesisLabel,
          stringAtom typecode, stringAtom variableName]],
   .expression
    [.symbol "mm-assertion-hypothesis-successor", scopeOwner,
      stringAtom assertionLabel, natAtom hypothesisPosition,
      natAtom nextHypothesisPosition],
   .expression
    [.symbol "mm-index-successor", proofOwner, natAtom stackPosition,
      natAtom nextStackPosition],
   .expression
    [.symbol "mm-stack-cell", proofOwner, natAtom stackPosition,
      formulaAtom ⟨typecode, actualBody⟩, natAtom childOccurrence]]

/-- Canonical MM2 boundary for one floating assertion hypothesis. -/
def normalAssertionFloatingPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) : Space :=
  (normalAssertionFloatingPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition assertionLabel hypothesisPosition
    nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
    stackBase hypothesisLabel typecode variableName actualBody
    childOccurrence).toFinset

private theorem normalAssertionFloatingPhaseAtoms_nodup
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) :
    (normalAssertionFloatingPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actualBody
      childOccurrence).Nodup := by
  simp [normalAssertionFloatingPhaseAtoms, normalAssertionFloatingRule]

private theorem normalAssertionFloatingPhaseAtoms_supported
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) :
    cSupportedSourceExecFacts
        (normalAssertionFloatingPhaseAtoms scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
          stackBase hypothesisLabel typecode variableName actualBody
          childOccurrence) =
      [normalAssertionFloatingDirective] := by
  rfl

/-- The ordinary scheduler selects the floating-hypothesis directive at the
exact source-indexed phase boundary. -/
theorem normalAssertionFloatingPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionFloatingPhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertionLabel hypothesisPosition
            nextHypothesisPosition hypothesisEnd stackPosition
            nextStackPosition stackBase hypothesisLabel typecode variableName
            actualBody childOccurrence)) =
      some normalAssertionFloatingDirective := by
  let atoms := normalAssertionFloatingPhaseAtoms scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisPosition
    nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
    stackBase hypothesisLabel typecode variableName actualBody childOccurrence
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionFloatingDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionFloatingDirective
    (normalAssertionFloatingPhaseAtoms_nodup scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actualBody
      childOccurrence)
    (normalAssertionFloatingPhaseAtoms_supported scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actualBody
      childOccurrence)

private def normalAssertionFloatingSubstitution
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) : Subst :=
  [("child-occurrence", natAtom childOccurrence),
   ("body", listAtom runtimeSymAtom actualBody),
   ("next-stack-position", natAtom nextStackPosition),
   ("next-hyp-position", natAtom nextHypothesisPosition),
   ("variable-name", stringAtom variableName),
   ("typecode", stringAtom typecode),
   ("hyp-label", stringAtom hypothesisLabel),
   ("stack-base", natAtom stackBase),
   ("stack-position", natAtom stackPosition),
   ("hyp-end", natAtom hypothesisEnd),
   ("hyp-position", natAtom hypothesisPosition),
   ("label", stringAtom assertionLabel),
   ("next-pc", natAtom nextProofPosition),
   ("pc", natAtom proofPosition),
   ("proof", proofOwner), ("scope", scopeOwner),
   ("self-output", normalAssertionFloatingOutput),
   ("self-input", normalAssertionFloatingInput)]

private theorem normalAssertionFloatingMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) :
    normalAssertionFloatingSubstitution scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel typecode variableName actualBody
        childOccurrence ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionFloatingPhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertionLabel hypothesisPosition
            nextHypothesisPosition hypothesisEnd stackPosition
            nextStackPosition stackBase hypothesisLabel typecode variableName
            actualBody childOccurrence)
          normalAssertionFloatingRule)
        normalAssertionFloatingDirective.rule.input).map Prod.fst := by
  let bind : Atom :=
    .expression
      [.symbol "mm-assertion-bind", scopeOwner, proofOwner,
        natAtom proofPosition, natAtom nextProofPosition,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        natAtom hypothesisEnd, natAtom stackPosition, natAtom stackBase]
  let hypothesisRow : Atom :=
    .expression
      [.symbol "mm-assertion-hypothesis", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        .expression
          [.symbol "mm-floating", stringAtom hypothesisLabel,
            stringAtom typecode, stringAtom variableName]]
  let hypothesisSuccessor : Atom :=
    .expression
      [.symbol "mm-assertion-hypothesis-successor", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        natAtom nextHypothesisPosition]
  let stackSuccessor : Atom :=
    .expression
      [.symbol "mm-index-successor", proofOwner, natAtom stackPosition,
        natAtom nextStackPosition]
  let stack : Atom :=
    .expression
      [.symbol "mm-stack-cell", proofOwner, natAtom stackPosition,
        formulaAtom ⟨typecode, actualBody⟩, natAtom childOccurrence]
  let read : Space := readCopyAtom
    (normalAssertionFloatingPhaseSpace scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actualBody
      childOccurrence)
    normalAssertionFloatingRule
  let afterSelf : Subst :=
    [("self-output", normalAssertionFloatingOutput),
     ("self-input", normalAssertionFloatingInput)]
  let afterBind : Subst :=
    [("stack-base", natAtom stackBase),
     ("stack-position", natAtom stackPosition),
     ("hyp-end", natAtom hypothesisEnd),
     ("hyp-position", natAtom hypothesisPosition),
     ("label", stringAtom assertionLabel),
     ("next-pc", natAtom nextProofPosition),
     ("pc", natAtom proofPosition),
     ("proof", proofOwner), ("scope", scopeOwner),
     ("self-output", normalAssertionFloatingOutput),
     ("self-input", normalAssertionFloatingInput)]
  let afterHypothesis : Subst :=
    [("variable-name", stringAtom variableName),
     ("typecode", stringAtom typecode),
     ("hyp-label", stringAtom hypothesisLabel),
     ("stack-base", natAtom stackBase),
     ("stack-position", natAtom stackPosition),
     ("hyp-end", natAtom hypothesisEnd),
     ("hyp-position", natAtom hypothesisPosition),
     ("label", stringAtom assertionLabel),
     ("next-pc", natAtom nextProofPosition),
     ("pc", natAtom proofPosition),
     ("proof", proofOwner), ("scope", scopeOwner),
     ("self-output", normalAssertionFloatingOutput),
     ("self-input", normalAssertionFloatingInput)]
  let afterHypothesisSuccessor : Subst :=
    ("next-hyp-position", natAtom nextHypothesisPosition) :: afterHypothesis
  let afterStackSuccessor : Subst :=
    ("next-stack-position", natAtom nextStackPosition) ::
      afterHypothesisSuccessor
  let finalRow : Subst :=
    normalAssertionFloatingSubstitution scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actualBody
      childOccurrence
  have readMember (atom : Atom)
      (member : atom ∈
        normalAssertionFloatingPhaseSpace scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
          stackBase hypothesisLabel typecode variableName actualBody
          childOccurrence) : atom ∈ read := by
    by_cases equal : atom = normalAssertionFloatingRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have selfMem : normalAssertionFloatingRule ∈ read := by
    apply readMember
    simp [normalAssertionFloatingPhaseSpace,
      normalAssertionFloatingPhaseAtoms]
  have bindMem : bind ∈ read := by
    apply readMember
    simp [bind, normalAssertionFloatingPhaseSpace,
      normalAssertionFloatingPhaseAtoms]
  have hypothesisRowMem : hypothesisRow ∈ read := by
    apply readMember
    simp [hypothesisRow, normalAssertionFloatingPhaseSpace,
      normalAssertionFloatingPhaseAtoms]
  have hypothesisSuccessorMem : hypothesisSuccessor ∈ read := by
    apply readMember
    simp [hypothesisSuccessor, normalAssertionFloatingPhaseSpace,
      normalAssertionFloatingPhaseAtoms]
  have stackSuccessorMem : stackSuccessor ∈ read := by
    apply readMember
    simp [stackSuccessor, normalAssertionFloatingPhaseSpace,
      normalAssertionFloatingPhaseAtoms]
  have stackMem : stack ∈ read := by
    apply readMember
    simp [stack, normalAssertionFloatingPhaseSpace,
      normalAssertionFloatingPhaseAtoms]
  have matchLocation :
      matchAtom [] normalAssertionFloatingLocation
          normalAssertionFloatingLocation = some [] := by
    simp [normalAssertionFloatingLocation, matchAtom,
      matchAtom.matchAtomList]
  have matchSelf :
      matchAtom [] normalAssertionFloatingSelfTemplate
          normalAssertionFloatingRule = some afterSelf := by
    simp [normalAssertionFloatingSelfTemplate,
      normalAssertionFloatingRule, normalAssertionFloatingInput,
      normalAssertionFloatingOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, matchLocation]
  have matchBind :
      matchAtom afterSelf normalAssertionFloatingBindTemplate bind =
        some afterBind := by
    simp [normalAssertionFloatingBindTemplate, afterSelf, afterBind, bind,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchHypothesis :
      matchAtom afterBind
          (normalAssertionFloatingPatternAtoms[2]'(by decide))
          hypothesisRow = some afterHypothesis := by
    simp [normalAssertionFloatingPatternAtoms, afterBind, afterHypothesis,
      hypothesisRow, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchHypothesisSuccessor :
      matchAtom afterHypothesis
          (normalAssertionFloatingPatternAtoms[3]'(by decide))
          hypothesisSuccessor = some afterHypothesisSuccessor := by
    simp [normalAssertionFloatingPatternAtoms, afterHypothesis,
      afterHypothesisSuccessor, hypothesisSuccessor, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchStackSuccessor :
      matchAtom afterHypothesisSuccessor
          (normalAssertionFloatingPatternAtoms[4]'(by decide))
          stackSuccessor = some afterStackSuccessor := by
    simp [normalAssertionFloatingPatternAtoms, afterHypothesisSuccessor,
      afterStackSuccessor, afterHypothesis, stackSuccessor, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchStack :
      matchAtom afterStackSuccessor
          (normalAssertionFloatingPatternAtoms[5]'(by decide))
          stack = some finalRow := by
    simp [normalAssertionFloatingPatternAtoms, afterStackSuccessor,
      afterHypothesisSuccessor, afterHypothesis, finalRow,
      normalAssertionFloatingSubstitution, stack, formulaAtom, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow,
    {normalAssertionFloatingRule, bind, hypothesisRow,
      hypothesisSuccessor, stackSuccessor, stack}), ?_, rfl⟩
  simp only [normalAssertionFloatingDirective, matchInputSpec,
    normalAssertionFloatingPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterSelf, normalAssertionFloatingRule),
    matchOneInSpace_mem [] _ read normalAssertionFloatingRule selfMem
      afterSelf matchSelf, ?_⟩
  refine ⟨(afterBind, bind),
    matchOneInSpace_mem afterSelf _ read bind bindMem afterBind matchBind, ?_⟩
  refine ⟨(afterHypothesis, hypothesisRow),
    matchOneInSpace_mem afterBind _ read hypothesisRow hypothesisRowMem
      afterHypothesis matchHypothesis, ?_⟩
  refine ⟨(afterHypothesisSuccessor, hypothesisSuccessor),
    matchOneInSpace_mem afterHypothesis _ read hypothesisSuccessor
      hypothesisSuccessorMem afterHypothesisSuccessor
      matchHypothesisSuccessor, ?_⟩
  refine ⟨(afterStackSuccessor, stackSuccessor),
    matchOneInSpace_mem afterHypothesisSuccessor _ read stackSuccessor
      stackSuccessorMem afterStackSuccessor matchStackSuccessor, ?_⟩
  refine ⟨(finalRow, stack),
    matchOneInSpace_mem afterStackSuccessor _ read stack stackMem finalRow
      matchStack, ?_⟩
  simp [finalRow, bind, hypothesisRow, hypothesisSuccessor, stackSuccessor,
    stack]

/-- Firing the actual emitted floating-hypothesis directive retains both the
finite-substitution binding and the ordered child occurrence. -/
theorem normalAssertionFloatingDirective_fires_evidence
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) :
    let target := fireReflectiveSourceExecFact
      (normalAssertionFloatingPhaseSpace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel typecode variableName actualBody
        childOccurrence)
      normalAssertionFloatingDirective;
    normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel nextHypothesisPosition
          hypothesisEnd nextStackPosition stackBase ∈ target ∧
      normalAssertionSubstitutionAtom proofOwner proofPosition variableName
            actualBody ∈ target ∧
        normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
            childOccurrence ∈ target := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalAssertionFloatingPhaseSpace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel typecode variableName actualBody
        childOccurrence)
      normalAssertionFloatingDirective.atom)
    normalAssertionFloatingDirective.rule.input).map Prod.fst
  let substitution := normalAssertionFloatingSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisPosition
    nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
    stackBase hypothesisLabel typecode variableName actualBody childOccurrence
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalAssertionFloatingDirective] using
      normalAssertionFloatingMatchRow_mem scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel typecode variableName actualBody
        childOccurrence
  have substitutionInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionFloatingSubstitutionTemplate =
        some (normalAssertionSubstitutionAtom proofOwner proofPosition
          variableName actualBody) := by
    rfl
  have nextBindInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionFloatingNextBindTemplate =
        some (normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel nextHypothesisPosition
          hypothesisEnd nextStackPosition stackBase) := by
    rfl
  have childInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionFloatingChildTemplate =
        some (normalAssertionChildAtom proofOwner proofPosition
          hypothesisPosition childOccurrence) := by
    rfl
  have substitutionStaged :
      normalAssertionSubstitutionAtom proofOwner proofPosition variableName
          actualBody ∈
        rows.foldl
          (stageReflectiveSupportSink
            (.add normalAssertionFloatingSubstitutionTemplate)) [] :=
    reflectiveStage_add_contains_of_row rows substitution
      normalAssertionFloatingSubstitutionTemplate
      (normalAssertionSubstitutionAtom proofOwner proofPosition variableName
      actualBody) rowMember substitutionInstantiates
  have nextBindStaged :
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel nextHypothesisPosition
          hypothesisEnd nextStackPosition stackBase ∈
        rows.foldl
          (stageReflectiveSupportSink
            (.add normalAssertionFloatingNextBindTemplate)) [] :=
    reflectiveStage_add_contains_of_row rows substitution
      normalAssertionFloatingNextBindTemplate
      (normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel nextHypothesisPosition hypothesisEnd
        nextStackPosition stackBase) rowMember nextBindInstantiates
  have childStaged :
      normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
          childOccurrence ∈
        rows.foldl
          (stageReflectiveSupportSink
            (.add normalAssertionFloatingChildTemplate)) [] :=
    reflectiveStage_add_contains_of_row rows substitution
      normalAssertionFloatingChildTemplate
      (normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
        childOccurrence) rowMember childInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalAssertionFloatingDirective, normalAssertionFloatingSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_left _
        (Finset.mem_union_right _ (List.mem_toFinset.mpr nextBindStaged)))
  · constructor
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
        normalAssertionFloatingDirective, normalAssertionFloatingSinks,
        reflectiveSupportSinkProvider]
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (List.mem_toFinset.mpr substitutionStaged))
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
        normalAssertionFloatingDirective, normalAssertionFloatingSinks,
        reflectiveSupportSinkProvider]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr childStaged)

/-- The floating-hypothesis transition is an actual scheduled reflective-MM2
step inhabiting its exact OSLF-generated target type; the native observation
retains the continuation, substitution binding, and child occurrence. -/
theorem normalAssertionFloatingPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode variableName : String)
    (actualBody : List Metamath.Verify.Sym) (childOccurrence : Nat) :
    let source := normalAssertionFloatingPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actualBody
      childOccurrence
    let target := fireReflectiveSourceExecFact source
      normalAssertionFloatingDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel nextHypothesisPosition
            hypothesisEnd nextStackPosition stackBase ∈ target ∧
        normalAssertionSubstitutionAtom proofOwner proofPosition variableName
              actualBody ∈ target ∧
          normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
              childOccurrence ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionFloatingPhase_selects_directive scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel typecode variableName
          actualBody childOccurrence))
  · exact normalAssertionFloatingDirective_fires_evidence scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode variableName actualBody
      childOccurrence

/-! ### Essential assertion-hypothesis transition boundary -/

/-- Continuation retained while the generic body machine checks one source
essential formula against its ordered actual child. -/
def normalAssertionEssentialContinuationAtom (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) : Atom :=
  .expression
    [.symbol "mm-assertion-essential-complete", scopeOwner, proofOwner,
      natAtom proofPosition, natAtom nextProofPosition,
      stringAtom assertionLabel, natAtom nextHypothesisPosition,
      natAtom hypothesisEnd, natAtom nextStackPosition, natAtom stackBase,
      natAtom hypothesisPosition, natAtom childOccurrence]

/-- Exact body-match request emitted for one essential hypothesis. -/
def normalAssertionEssentialMatchAtom (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat)
    (sourceBody actualBody : List Metamath.Verify.Sym) : Atom :=
  .expression
    [.symbol "mm-body-match", proofOwner, natAtom proofPosition,
      listAtom runtimeSymAtom sourceBody, listAtom runtimeSymAtom actualBody,
      normalAssertionEssentialContinuationAtom scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel
        nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
        hypothesisPosition childOccurrence]

/-- Finite atom state at one source essential hypothesis. -/
def normalAssertionEssentialPhaseAtoms (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) : List Atom :=
  [normalAssertionEssentialRule,
   normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisPosition hypothesisEnd
      stackPosition stackBase,
   .expression
      [.symbol "mm-assertion-hypothesis", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        .expression
          [.symbol "mm-essential", stringAtom hypothesisLabel,
            formulaAtom ⟨typecode, sourceBody⟩]],
   .expression
      [.symbol "mm-assertion-hypothesis-successor", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        natAtom nextHypothesisPosition],
   .expression
      [.symbol "mm-index-successor", proofOwner, natAtom stackPosition,
        natAtom nextStackPosition],
   .expression
      [.symbol "mm-stack-cell", proofOwner, natAtom stackPosition,
        formulaAtom ⟨typecode, actualBody⟩, natAtom childOccurrence]]

/-- Canonical MM2 boundary at one source essential hypothesis. -/
def normalAssertionEssentialPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) : Space :=
  (normalAssertionEssentialPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition assertionLabel hypothesisPosition
    nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
    stackBase hypothesisLabel typecode sourceBody actualBody
    childOccurrence).toFinset

private theorem normalAssertionEssentialPhaseAtoms_nodup
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) :
    (normalAssertionEssentialPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode sourceBody actualBody
      childOccurrence).Nodup := by
  simp [normalAssertionEssentialPhaseAtoms, normalAssertionEssentialRule,
    normalAssertionNextBindAtom]

private theorem normalAssertionEssentialPhaseAtoms_supported
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) :
    cSupportedSourceExecFacts
        (normalAssertionEssentialPhaseAtoms scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
          stackBase hypothesisLabel typecode sourceBody actualBody
          childOccurrence) =
      [normalAssertionEssentialDirective] := by
  rfl

/-- The ordinary scheduler selects the essential-hypothesis directive at the
exact source-indexed phase boundary. -/
theorem normalAssertionEssentialPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionEssentialPhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertionLabel hypothesisPosition
            nextHypothesisPosition hypothesisEnd stackPosition
            nextStackPosition stackBase hypothesisLabel typecode sourceBody
            actualBody childOccurrence)) =
      some normalAssertionEssentialDirective := by
  let atoms := normalAssertionEssentialPhaseAtoms scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisPosition
    nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
    stackBase hypothesisLabel typecode sourceBody actualBody childOccurrence
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionEssentialDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionEssentialDirective
    (normalAssertionEssentialPhaseAtoms_nodup scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode sourceBody actualBody childOccurrence)
    (normalAssertionEssentialPhaseAtoms_supported scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode sourceBody actualBody childOccurrence)

private def normalAssertionEssentialSubstitution
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) : Subst :=
  [("child-occurrence", natAtom childOccurrence),
   ("actual-body", listAtom runtimeSymAtom actualBody),
   ("next-stack-position", natAtom nextStackPosition),
   ("next-hyp-position", natAtom nextHypothesisPosition),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("typecode", stringAtom typecode),
   ("hyp-label", stringAtom hypothesisLabel),
   ("stack-base", natAtom stackBase),
   ("stack-position", natAtom stackPosition),
   ("hyp-end", natAtom hypothesisEnd),
   ("hyp-position", natAtom hypothesisPosition),
   ("label", stringAtom assertionLabel),
   ("next-pc", natAtom nextProofPosition),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalAssertionEssentialMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) :
    normalAssertionEssentialSubstitution scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel typecode sourceBody actualBody
        childOccurrence ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionEssentialPhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertionLabel hypothesisPosition
            nextHypothesisPosition hypothesisEnd stackPosition
            nextStackPosition stackBase hypothesisLabel typecode sourceBody
            actualBody childOccurrence)
          normalAssertionEssentialRule)
        normalAssertionEssentialDirective.rule.input).map Prod.fst := by
  let bind := normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
    nextProofPosition assertionLabel hypothesisPosition hypothesisEnd
    stackPosition stackBase
  let hypothesisRow : Atom :=
    .expression
      [.symbol "mm-assertion-hypothesis", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        .expression
          [.symbol "mm-essential", stringAtom hypothesisLabel,
            formulaAtom ⟨typecode, sourceBody⟩]]
  let hypothesisSuccessor : Atom :=
    .expression
      [.symbol "mm-assertion-hypothesis-successor", scopeOwner,
        stringAtom assertionLabel, natAtom hypothesisPosition,
        natAtom nextHypothesisPosition]
  let stackSuccessor : Atom :=
    .expression
      [.symbol "mm-index-successor", proofOwner, natAtom stackPosition,
        natAtom nextStackPosition]
  let stack : Atom :=
    .expression
      [.symbol "mm-stack-cell", proofOwner, natAtom stackPosition,
        formulaAtom ⟨typecode, actualBody⟩, natAtom childOccurrence]
  let read := readCopyAtom
    (normalAssertionEssentialPhaseSpace scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode sourceBody actualBody childOccurrence)
    normalAssertionEssentialRule
  let afterBind : Subst :=
    [("stack-base", natAtom stackBase),
     ("stack-position", natAtom stackPosition),
     ("hyp-end", natAtom hypothesisEnd),
     ("hyp-position", natAtom hypothesisPosition),
     ("label", stringAtom assertionLabel),
     ("next-pc", natAtom nextProofPosition),
     ("pc", natAtom proofPosition), ("proof", proofOwner),
     ("scope", scopeOwner)]
  let afterHypothesis : Subst :=
    [("source-body", listAtom runtimeSymAtom sourceBody),
     ("typecode", stringAtom typecode),
     ("hyp-label", stringAtom hypothesisLabel),
     ("stack-base", natAtom stackBase),
     ("stack-position", natAtom stackPosition),
     ("hyp-end", natAtom hypothesisEnd),
     ("hyp-position", natAtom hypothesisPosition),
     ("label", stringAtom assertionLabel),
     ("next-pc", natAtom nextProofPosition),
     ("pc", natAtom proofPosition), ("proof", proofOwner),
     ("scope", scopeOwner)]
  let afterHypothesisSuccessor : Subst :=
    ("next-hyp-position", natAtom nextHypothesisPosition) :: afterHypothesis
  let afterStackSuccessor : Subst :=
    ("next-stack-position", natAtom nextStackPosition) ::
      afterHypothesisSuccessor
  let finalRow := normalAssertionEssentialSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisPosition
    nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
    stackBase hypothesisLabel typecode sourceBody actualBody childOccurrence
  have readMember (atom : Atom)
      (member : atom ∈
        normalAssertionEssentialPhaseSpace scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel typecode sourceBody
          actualBody childOccurrence) : atom ∈ read := by
    by_cases equal : atom = normalAssertionEssentialRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have bindMem : bind ∈ read := by
    apply readMember
    simp [bind, normalAssertionEssentialPhaseSpace,
      normalAssertionEssentialPhaseAtoms]
  have hypothesisRowMem : hypothesisRow ∈ read := by
    apply readMember
    simp [hypothesisRow, normalAssertionEssentialPhaseSpace,
      normalAssertionEssentialPhaseAtoms, formulaAtom]
  have hypothesisSuccessorMem : hypothesisSuccessor ∈ read := by
    apply readMember
    simp [hypothesisSuccessor, normalAssertionEssentialPhaseSpace,
      normalAssertionEssentialPhaseAtoms]
  have stackSuccessorMem : stackSuccessor ∈ read := by
    apply readMember
    simp [stackSuccessor, normalAssertionEssentialPhaseSpace,
      normalAssertionEssentialPhaseAtoms]
  have stackMem : stack ∈ read := by
    apply readMember
    simp [stack, normalAssertionEssentialPhaseSpace,
      normalAssertionEssentialPhaseAtoms]
  have matchBind :
      matchAtom [] (normalAssertionEssentialPatternAtoms[0]'(by decide))
          bind = some afterBind := by
    simp [normalAssertionEssentialPatternAtoms, bind,
      normalAssertionNextBindAtom, afterBind, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchHypothesis :
      matchAtom afterBind
          (normalAssertionEssentialPatternAtoms[1]'(by decide))
          hypothesisRow = some afterHypothesis := by
    simp [normalAssertionEssentialPatternAtoms, afterBind, afterHypothesis,
      hypothesisRow, formulaAtom, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchHypothesisSuccessor :
      matchAtom afterHypothesis
          (normalAssertionEssentialPatternAtoms[2]'(by decide))
          hypothesisSuccessor = some afterHypothesisSuccessor := by
    simp [normalAssertionEssentialPatternAtoms, afterHypothesis,
      afterHypothesisSuccessor, hypothesisSuccessor, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchStackSuccessor :
      matchAtom afterHypothesisSuccessor
          (normalAssertionEssentialPatternAtoms[3]'(by decide))
          stackSuccessor = some afterStackSuccessor := by
    simp [normalAssertionEssentialPatternAtoms, afterHypothesisSuccessor,
      afterStackSuccessor, afterHypothesis, stackSuccessor, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchStack :
      matchAtom afterStackSuccessor
          (normalAssertionEssentialPatternAtoms[4]'(by decide))
          stack = some finalRow := by
    simp [normalAssertionEssentialPatternAtoms, afterStackSuccessor,
      afterHypothesisSuccessor, afterHypothesis, finalRow,
      normalAssertionEssentialSubstitution, stack, formulaAtom, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow,
    {bind, hypothesisRow, hypothesisSuccessor, stackSuccessor, stack}),
    ?_, rfl⟩
  simp only [normalAssertionEssentialDirective, matchInputSpec,
    normalAssertionEssentialPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterBind, bind),
    matchOneInSpace_mem [] _ read bind bindMem afterBind matchBind, ?_⟩
  refine ⟨(afterHypothesis, hypothesisRow),
    matchOneInSpace_mem afterBind _ read hypothesisRow hypothesisRowMem
      afterHypothesis matchHypothesis, ?_⟩
  refine ⟨(afterHypothesisSuccessor, hypothesisSuccessor),
    matchOneInSpace_mem afterHypothesis _ read hypothesisSuccessor
      hypothesisSuccessorMem afterHypothesisSuccessor
      matchHypothesisSuccessor, ?_⟩
  refine ⟨(afterStackSuccessor, stackSuccessor),
    matchOneInSpace_mem afterHypothesisSuccessor _ read stackSuccessor
      stackSuccessorMem afterStackSuccessor matchStackSuccessor, ?_⟩
  refine ⟨(finalRow, stack),
    matchOneInSpace_mem afterStackSuccessor _ read stack stackMem finalRow
      matchStack, ?_⟩
  simp [finalRow, bind, hypothesisRow, hypothesisSuccessor, stackSuccessor,
    stack]

/-- Firing the actual emitted essential directive starts exactly the body
match whose continuation retains the ordered child occurrence. -/
theorem normalAssertionEssentialDirective_fires_match
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) :
    normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel nextHypothesisPosition hypothesisEnd
        nextStackPosition stackBase hypothesisPosition childOccurrence
        sourceBody actualBody ∈
      fireReflectiveSourceExecFact
        (normalAssertionEssentialPhaseSpace scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel typecode sourceBody
          actualBody childOccurrence)
        normalAssertionEssentialDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalAssertionEssentialPhaseSpace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel typecode sourceBody actualBody
        childOccurrence)
      normalAssertionEssentialDirective.atom)
    normalAssertionEssentialDirective.rule.input).map Prod.fst
  let substitution := normalAssertionEssentialSubstitution scopeOwner
    proofOwner proofPosition nextProofPosition assertionLabel
    hypothesisPosition nextHypothesisPosition hypothesisEnd stackPosition
    nextStackPosition stackBase hypothesisLabel typecode sourceBody actualBody
    childOccurrence
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalAssertionEssentialDirective] using
      normalAssertionEssentialMatchRow_mem scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisPosition
        nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
        stackBase hypothesisLabel typecode sourceBody actualBody
        childOccurrence
  have instantiates :
      instantiateTemplateAtom? substitution
          normalAssertionEssentialMatchTemplate =
        some (normalAssertionEssentialMatchAtom scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel
          nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
          hypothesisPosition childOccurrence sourceBody actualBody) := by
    rfl
  have stagedMember :
      normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel nextHypothesisPosition
          hypothesisEnd nextStackPosition stackBase hypothesisPosition
          childOccurrence sourceBody actualBody ∈
        rows.foldl
          (stageReflectiveSupportSink
            (.add normalAssertionEssentialMatchTemplate)) [] :=
    reflectiveStage_add_contains_of_row rows substitution
      normalAssertionEssentialMatchTemplate
      (normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel nextHypothesisPosition hypothesisEnd
        nextStackPosition stackBase hypothesisPosition childOccurrence
        sourceBody actualBody) rowMember instantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalAssertionEssentialDirective, normalAssertionEssentialSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr stagedMember)

/-- The essential-hypothesis transition is an actual scheduled reflective-MM2
step inhabiting its exact OSLF-generated target type.  Its target observation
retains the ordered child occurrence in the body-match continuation. -/
theorem normalAssertionEssentialPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisPosition nextHypothesisPosition hypothesisEnd : Nat)
    (stackPosition nextStackPosition stackBase : Nat)
    (hypothesisLabel typecode : String)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (childOccurrence : Nat) :
    let source := normalAssertionEssentialPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode sourceBody actualBody childOccurrence
    let target := fireReflectiveSourceExecFact source
      normalAssertionEssentialDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionEssentialMatchAtom scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel nextHypothesisPosition hypothesisEnd
        nextStackPosition stackBase hypothesisPosition childOccurrence
        sourceBody actualBody ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionEssentialPhase_selects_directive scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel hypothesisPosition
          nextHypothesisPosition hypothesisEnd stackPosition
          nextStackPosition stackBase hypothesisLabel typecode sourceBody
          actualBody childOccurrence))
  · exact normalAssertionEssentialDirective_fires_match scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisPosition
      nextHypothesisPosition hypothesisEnd stackPosition nextStackPosition
      stackBase hypothesisLabel typecode sourceBody actualBody childOccurrence

/-- Dispatch reload requested after an essential child has been retained. -/
def normalAssertionReloadAtom (proofOwner : Atom) : Atom :=
  .expression [.symbol "mm-reload-normal-dispatch", proofOwner]

/-- Finite atom state reached after the body matcher has validated the
source and actual essential-hypothesis bodies. -/
def normalAssertionEssentialCompletePhaseAtoms
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) : List Atom :=
  [normalAssertionEssentialCompleteRule,
   normalAssertionEssentialContinuationAtom scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel nextHypothesisPosition
      hypothesisEnd nextStackPosition stackBase hypothesisPosition
      childOccurrence]

/-- Boundary reached after the body matcher has validated one essential
hypothesis. -/
def normalAssertionEssentialCompletePhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) : Space :=
  (normalAssertionEssentialCompletePhaseAtoms scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel nextHypothesisPosition
    hypothesisEnd nextStackPosition stackBase hypothesisPosition
    childOccurrence).toFinset

private theorem normalAssertionEssentialCompletePhaseAtoms_nodup
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) :
    (normalAssertionEssentialCompletePhaseAtoms scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel nextHypothesisPosition
      hypothesisEnd nextStackPosition stackBase hypothesisPosition
      childOccurrence).Nodup := by
  simp [normalAssertionEssentialCompletePhaseAtoms,
    normalAssertionEssentialCompleteRule,
    normalAssertionEssentialContinuationAtom]

private theorem normalAssertionEssentialCompletePhaseAtoms_supported
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) :
    cSupportedSourceExecFacts
        (normalAssertionEssentialCompletePhaseAtoms scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel
          nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
          hypothesisPosition childOccurrence) =
      [normalAssertionEssentialCompleteDirective] := by
  rfl

/-- The ordinary scheduler selects the essential-completion directive after
the body matcher has established its continuation. -/
theorem normalAssertionEssentialCompletePhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionEssentialCompletePhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertionLabel
            nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
            hypothesisPosition childOccurrence)) =
      some normalAssertionEssentialCompleteDirective := by
  let atoms := normalAssertionEssentialCompletePhaseAtoms scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel nextHypothesisPosition
    hypothesisEnd nextStackPosition stackBase hypothesisPosition
    childOccurrence
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionEssentialCompleteDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionEssentialCompleteDirective
    (normalAssertionEssentialCompletePhaseAtoms_nodup scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel nextHypothesisPosition
      hypothesisEnd nextStackPosition stackBase hypothesisPosition
      childOccurrence)
    (normalAssertionEssentialCompletePhaseAtoms_supported scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel nextHypothesisPosition
      hypothesisEnd nextStackPosition stackBase hypothesisPosition
      childOccurrence)

private def normalAssertionEssentialCompleteSubstitution
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) : Subst :=
  [("child-occurrence", natAtom childOccurrence),
   ("hyp-position", natAtom hypothesisPosition),
   ("stack-base", natAtom stackBase),
   ("next-stack-position", natAtom nextStackPosition),
   ("hyp-end", natAtom hypothesisEnd),
   ("next-hyp-position", natAtom nextHypothesisPosition),
   ("label", stringAtom assertionLabel),
   ("next-pc", natAtom nextProofPosition),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalAssertionEssentialCompleteMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) :
    normalAssertionEssentialCompleteSubstitution scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel
        nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
        hypothesisPosition childOccurrence ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionEssentialCompletePhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertionLabel
            nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
            hypothesisPosition childOccurrence)
          normalAssertionEssentialCompleteRule)
        normalAssertionEssentialCompleteDirective.rule.input).map Prod.fst := by
  let continuation := normalAssertionEssentialContinuationAtom scopeOwner
    proofOwner proofPosition nextProofPosition assertionLabel
    nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
    hypothesisPosition childOccurrence
  let substitution := normalAssertionEssentialCompleteSubstitution scopeOwner
    proofOwner proofPosition nextProofPosition assertionLabel
    nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
    hypothesisPosition childOccurrence
  let read := readCopyAtom
    (normalAssertionEssentialCompletePhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel nextHypothesisPosition
      hypothesisEnd nextStackPosition stackBase hypothesisPosition
      childOccurrence)
    normalAssertionEssentialCompleteRule
  have continuationMem : continuation ∈ read := by
    simp [read, readCopyAtom, consumeAtom, continuation,
      normalAssertionEssentialContinuationAtom,
      normalAssertionEssentialCompletePhaseSpace,
      normalAssertionEssentialCompletePhaseAtoms,
      normalAssertionEssentialCompleteRule]
  have matchContinuation :
      matchAtom [] normalAssertionEssentialCompleteTemplate continuation =
        some substitution := by
    simp [normalAssertionEssentialCompleteTemplate, continuation,
      normalAssertionEssentialContinuationAtom, substitution,
      normalAssertionEssentialCompleteSubstitution, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {continuation}), ?_, rfl⟩
  simp only [normalAssertionEssentialCompleteDirective, matchInputSpec,
    normalAssertionEssentialCompletePatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, continuation),
    matchOneInSpace_mem [] _ read continuation continuationMem substitution
      matchContinuation, ?_⟩
  simp [substitution, continuation]

/-- Completing the actual essential directive advances the ordered fold,
retains the exact child occurrence, and reloads normal dispatch. -/
theorem normalAssertionEssentialCompleteDirective_fires_evidence
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) :
    let result := fireReflectiveSourceExecFact
      (normalAssertionEssentialCompletePhaseSpace scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel nextHypothesisPosition
        hypothesisEnd nextStackPosition stackBase hypothesisPosition
        childOccurrence)
      normalAssertionEssentialCompleteDirective
    normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel nextHypothesisPosition
          hypothesisEnd nextStackPosition stackBase ∈ result ∧
      normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
            childOccurrence ∈ result ∧
        normalAssertionReloadAtom proofOwner ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalAssertionEssentialCompletePhaseSpace scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel nextHypothesisPosition
        hypothesisEnd nextStackPosition stackBase hypothesisPosition
        childOccurrence)
      normalAssertionEssentialCompleteDirective.atom)
    normalAssertionEssentialCompleteDirective.rule.input).map Prod.fst
  let substitution := normalAssertionEssentialCompleteSubstitution scopeOwner
    proofOwner proofPosition nextProofPosition assertionLabel
    nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
    hypothesisPosition childOccurrence
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalAssertionEssentialCompleteDirective] using
      normalAssertionEssentialCompleteMatchRow_mem scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel
        nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
        hypothesisPosition childOccurrence
  have nextInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionEssentialCompleteNextBindTemplate =
        some (normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
          nextProofPosition assertionLabel nextHypothesisPosition
          hypothesisEnd nextStackPosition stackBase) := by
    rfl
  have childInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionEssentialCompleteChildTemplate =
        some (normalAssertionChildAtom proofOwner proofPosition
          hypothesisPosition childOccurrence) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionEssentialCompleteReloadTemplate =
        some (normalAssertionReloadAtom proofOwner) := by
    rfl
  have nextStaged := reflectiveStage_add_contains_of_row rows substitution
    normalAssertionEssentialCompleteNextBindTemplate
    (normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel nextHypothesisPosition hypothesisEnd
      nextStackPosition stackBase) rowMember nextInstantiates
  have childStaged := reflectiveStage_add_contains_of_row rows substitution
    normalAssertionEssentialCompleteChildTemplate
    (normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
      childOccurrence) rowMember childInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalAssertionEssentialCompleteReloadTemplate
    (normalAssertionReloadAtom proofOwner) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalAssertionEssentialCompleteDirective,
      normalAssertionEssentialCompleteSinks, reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_left _
        (Finset.mem_union_right _ (List.mem_toFinset.mpr nextStaged)))
  · constructor
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
        normalAssertionEssentialCompleteDirective,
        normalAssertionEssentialCompleteSinks, reflectiveSupportSinkProvider]
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (List.mem_toFinset.mpr childStaged))
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
        normalAssertionEssentialCompleteDirective,
        normalAssertionEssentialCompleteSinks, reflectiveSupportSinkProvider]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-- Essential completion is an actual scheduled reflective-MM2 step
inhabiting its exact OSLF-generated target type. -/
theorem normalAssertionEssentialCompletePhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence : Nat) :
    let source := normalAssertionEssentialCompletePhaseSpace scopeOwner
      proofOwner proofPosition nextProofPosition assertionLabel
      nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence
    let target := fireReflectiveSourceExecFact source
      normalAssertionEssentialCompleteDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel nextHypothesisPosition
            hypothesisEnd nextStackPosition stackBase ∈ target ∧
        normalAssertionChildAtom proofOwner proofPosition hypothesisPosition
              childOccurrence ∈ target ∧
          normalAssertionReloadAtom proofOwner ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionEssentialCompletePhase_selects_directive scopeOwner
          proofOwner proofPosition nextProofPosition assertionLabel
          nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
          hypothesisPosition childOccurrence))
  · exact normalAssertionEssentialCompleteDirective_fires_evidence scopeOwner
      proofOwner proofPosition nextProofPosition assertionLabel
      nextHypothesisPosition hypothesisEnd nextStackPosition stackBase
      hypothesisPosition childOccurrence

/-! ### Generic body-matcher transition boundary -/

/-- Stable target state for matching one substituted Metamath formula body. -/
def normalBodyMatchAtom (proofOwner : Atom) (proofPosition : Nat)
    (sourceBody actualBody : List Metamath.Verify.Sym)
    (continuation : Atom) : Atom :=
  .expression
    [.symbol "mm-body-match", proofOwner, natAtom proofPosition,
      listAtom runtimeSymAtom sourceBody, listAtom runtimeSymAtom actualBody,
      continuation]

def normalBodyMatchReloadAtom (proofOwner : Atom)
    (proofPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-reload-body-match", proofOwner, natAtom proofPosition]

/-- Stable administrative state that checks one substituted variable body
against the corresponding prefix of the actual formula body. -/
def normalBodyPrefixAtom (proofOwner : Atom) (proofPosition : Nat)
    (replacementBody actualBody sourceTail : List Metamath.Verify.Sym)
    (continuation : Atom) : Atom :=
  .expression
    [.symbol "mm-body-prefix", proofOwner, natAtom proofPosition,
      listAtom runtimeSymAtom replacementBody,
      listAtom runtimeSymAtom actualBody,
      listAtom runtimeSymAtom sourceTail, continuation]

def normalBodyMatchConstPhaseSpace (proofOwner continuation : Atom)
    (proofPosition : Nat) (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) : Space :=
  [normalBodyMatchConstRule,
   normalBodyMatchAtom proofOwner proofPosition
      (.const constantName :: sourceTail)
      (.const constantName :: actualTail) continuation].toFinset

/-- The ordinary scheduler selects the matching-constant directive on its
focused body-match boundary. -/
theorem normalBodyMatchConstPhase_selects_directive
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyMatchConstPhaseSpace proofOwner continuation proofPosition
            constantName sourceTail actualTail)) =
      some normalBodyMatchConstDirective := by
  let atoms :=
    [normalBodyMatchConstRule,
     normalBodyMatchAtom proofOwner proofPosition
       (.const constantName :: sourceTail)
       (.const constantName :: actualTail) continuation]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyMatchConstDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyMatchConstDirective
    (by simp [atoms, normalBodyMatchConstRule, normalBodyMatchAtom])
    (by rfl)

private def normalBodyMatchConstSubstitution (proofOwner continuation : Atom)
    (proofPosition : Nat) (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) : Subst :=
  [("continuation", continuation),
   ("actual-tail", listAtom runtimeSymAtom actualTail),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("constant-name", stringAtom constantName),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyMatchConstMatchRow_mem
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) :
    normalBodyMatchConstSubstitution proofOwner continuation proofPosition
        constantName sourceTail actualTail ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyMatchConstPhaseSpace proofOwner continuation proofPosition
            constantName sourceTail actualTail)
          normalBodyMatchConstRule)
        normalBodyMatchConstDirective.rule.input).map Prod.fst := by
  let current := normalBodyMatchAtom proofOwner proofPosition
    (.const constantName :: sourceTail)
    (.const constantName :: actualTail) continuation
  let substitution := normalBodyMatchConstSubstitution proofOwner
    continuation proofPosition constantName sourceTail actualTail
  let read := readCopyAtom
    (normalBodyMatchConstPhaseSpace proofOwner continuation proofPosition
      constantName sourceTail actualTail)
    normalBodyMatchConstRule
  have currentMem : current ∈ read := by
    simp [read, readCopyAtom, consumeAtom, current, normalBodyMatchAtom,
      normalBodyMatchConstPhaseSpace, normalBodyMatchConstRule,
      runtimeSymAtom, listAtom]
  have matchCurrent :
      matchAtom [] normalBodyMatchConstCurrentTemplate current =
        some substitution := by
    simp [normalBodyMatchConstCurrentTemplate,
      normalBodyMatchConstPatternAtoms, current, normalBodyMatchAtom,
      substitution, normalBodyMatchConstSubstitution, runtimeSymAtom,
      listAtom, consTag, constTag, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {current}), ?_, rfl⟩
  simp only [normalBodyMatchConstDirective, matchInputSpec,
    normalBodyMatchConstPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, current),
    matchOneInSpace_mem [] _ read current currentMem substitution
      matchCurrent, ?_⟩
  simp [substitution, current]

/-- The actual emitted constant rule preserves one equal leading constant
and continues on the exact source and actual tails. -/
theorem normalBodyMatchConstDirective_fires_tail
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyMatchConstPhaseSpace proofOwner continuation proofPosition
        constantName sourceTail actualTail)
      normalBodyMatchConstDirective
    normalBodyMatchAtom proofOwner proofPosition sourceTail actualTail
          continuation ∈ result ∧
      normalBodyMatchReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyMatchConstPhaseSpace proofOwner continuation proofPosition
        constantName sourceTail actualTail)
      normalBodyMatchConstDirective.atom)
    normalBodyMatchConstDirective.rule.input).map Prod.fst
  let substitution := normalBodyMatchConstSubstitution proofOwner
    continuation proofPosition constantName sourceTail actualTail
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyMatchConstDirective] using
      normalBodyMatchConstMatchRow_mem proofOwner continuation proofPosition
        constantName sourceTail actualTail
  have tailInstantiates :
      instantiateTemplateAtom? substitution normalBodyMatchConstTailTemplate =
        some (normalBodyMatchAtom proofOwner proofPosition sourceTail
          actualTail continuation) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalBodyMatchReloadTemplate =
        some (normalBodyMatchReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyMatchConstTailTemplate
    (normalBodyMatchAtom proofOwner proofPosition sourceTail actualTail
      continuation) rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyMatchReloadTemplate
    (normalBodyMatchReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyMatchConstDirective, normalBodyMatchConstSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyMatchConstDirective, normalBodyMatchConstSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-- Matching one equal leading constant is an actual scheduled
reflective-MM2 step inhabiting its exact OSLF-generated target type. -/
theorem normalBodyMatchConstPhase_inhabits_target_native_type
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (constantName : String)
    (sourceTail actualTail : List Metamath.Verify.Sym) :
    let source := normalBodyMatchConstPhaseSpace proofOwner continuation
      proofPosition constantName sourceTail actualTail
    let target := fireReflectiveSourceExecFact source
      normalBodyMatchConstDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyMatchAtom proofOwner proofPosition sourceTail actualTail
            continuation ∈ target ∧
        normalBodyMatchReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyMatchConstPhase_selects_directive proofOwner continuation
          proofPosition constantName sourceTail actualTail))
  · exact normalBodyMatchConstDirective_fires_tail proofOwner continuation
      proofPosition constantName sourceTail actualTail

/-- The emitted constant matcher cannot cross unequal Metamath constants.
This is the local no-invention control paired with the positive transition
above. -/
theorem normalBodyMatchConstPattern_rejects_mismatched_constant
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (sourceConstant actualConstant : String)
    (sourceTail actualTail : List Metamath.Verify.Sym)
    (different : sourceConstant ≠ actualConstant) :
    matchAtom [] normalBodyMatchConstCurrentTemplate
        (normalBodyMatchAtom proofOwner proofPosition
          (.const sourceConstant :: sourceTail)
          (.const actualConstant :: actualTail) continuation) = none := by
  have encodedDifferent :
      stringAtom actualConstant ≠ stringAtom sourceConstant := by
    intro equal
    exact different (stringAtom_injective equal).symm
  simp [normalBodyMatchConstCurrentTemplate,
    normalBodyMatchConstPatternAtoms, normalBodyMatchAtom, runtimeSymAtom,
    listAtom, consTag, constTag, matchAtom, matchAtom.matchAtomList,
    Subst.lookup, encodedDifferent]

def normalBodyMatchVariablePhaseSpace (proofOwner continuation : Atom)
    (proofPosition : Nat) (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyMatchVariableRule,
   normalBodyMatchAtom proofOwner proofPosition
      (.var variableName :: sourceTail) actualBody continuation,
   normalAssertionSubstitutionAtom proofOwner proofPosition variableName
      replacementBody].toFinset

/-- The ordinary scheduler selects the variable-expansion directive on its
focused body-match boundary. -/
theorem normalBodyMatchVariablePhase_selects_directive
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyMatchVariablePhaseSpace proofOwner continuation
            proofPosition variableName replacementBody sourceTail
            actualBody)) =
      some normalBodyMatchVariableDirective := by
  let atoms :=
    [normalBodyMatchVariableRule,
     normalBodyMatchAtom proofOwner proofPosition
       (.var variableName :: sourceTail) actualBody continuation,
     normalAssertionSubstitutionAtom proofOwner proofPosition variableName
       replacementBody]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyMatchVariableDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyMatchVariableDirective
    (by simp [atoms, normalBodyMatchVariableRule, normalBodyMatchAtom,
      normalAssertionSubstitutionAtom])
    (by rfl)

private def normalBodyMatchVariableAfterCurrent
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (variableName : String) (sourceTail actualBody : List Metamath.Verify.Sym) :
    Subst :=
  [("continuation", continuation),
   ("actual-body", listAtom runtimeSymAtom actualBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("variable-name", stringAtom variableName),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private def normalBodyMatchVariableSubstitution
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) : Subst :=
  [("replacement-body", listAtom runtimeSymAtom replacementBody)] ++
    normalBodyMatchVariableAfterCurrent proofOwner continuation proofPosition
      variableName sourceTail actualBody

private theorem normalBodyMatchVariableMatchRow_mem
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) :
    normalBodyMatchVariableSubstitution proofOwner continuation proofPosition
        variableName replacementBody sourceTail actualBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyMatchVariablePhaseSpace proofOwner continuation
            proofPosition variableName replacementBody sourceTail actualBody)
          normalBodyMatchVariableRule)
        normalBodyMatchVariableDirective.rule.input).map Prod.fst := by
  let current := normalBodyMatchAtom proofOwner proofPosition
    (.var variableName :: sourceTail) actualBody continuation
  let substitutionRow := normalAssertionSubstitutionAtom proofOwner
    proofPosition variableName replacementBody
  let afterCurrent := normalBodyMatchVariableAfterCurrent proofOwner
    continuation proofPosition variableName sourceTail actualBody
  let finalRow := normalBodyMatchVariableSubstitution proofOwner continuation
    proofPosition variableName replacementBody sourceTail actualBody
  let read := readCopyAtom
    (normalBodyMatchVariablePhaseSpace proofOwner continuation proofPosition
      variableName replacementBody sourceTail actualBody)
    normalBodyMatchVariableRule
  have currentMem : current ∈ read := by
    simp [read, readCopyAtom, consumeAtom, current, normalBodyMatchAtom,
      normalBodyMatchVariablePhaseSpace, normalBodyMatchVariableRule,
      runtimeSymAtom, listAtom]
  have substitutionMem : substitutionRow ∈ read := by
    simp [read, readCopyAtom, consumeAtom, substitutionRow,
      normalAssertionSubstitutionAtom, normalBodyMatchVariablePhaseSpace,
      normalBodyMatchVariableRule]
  have matchCurrent :
      matchAtom [] normalBodyMatchVariableCurrentTemplate current =
        some afterCurrent := by
    simp [normalBodyMatchVariableCurrentTemplate,
      normalBodyMatchVariablePatternAtoms, current, normalBodyMatchAtom,
      afterCurrent, normalBodyMatchVariableAfterCurrent, runtimeSymAtom,
      listAtom, consTag, variableTag, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchSubstitution :
      matchAtom afterCurrent normalBodyMatchVariableSubstitutionTemplate
          substitutionRow = some finalRow := by
    simp [normalBodyMatchVariableSubstitutionTemplate,
      normalBodyMatchVariablePatternAtoms, substitutionRow,
      normalAssertionSubstitutionAtom, afterCurrent,
      normalBodyMatchVariableAfterCurrent, finalRow,
      normalBodyMatchVariableSubstitution, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {current, substitutionRow}), ?_, rfl⟩
  simp only [normalBodyMatchVariableDirective, matchInputSpec,
    normalBodyMatchVariablePatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterCurrent, current),
    matchOneInSpace_mem [] _ read current currentMem afterCurrent
      matchCurrent, ?_⟩
  refine ⟨(finalRow, substitutionRow),
    matchOneInSpace_mem afterCurrent _ read substitutionRow substitutionMem
      finalRow matchSubstitution, ?_⟩
  simp [finalRow, current, substitutionRow]

/-- The emitted variable rule consumes an exact source-derived substitution
row and starts comparison with that entire replacement body. -/
theorem normalBodyMatchVariableDirective_fires_prefix
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyMatchVariablePhaseSpace proofOwner continuation proofPosition
        variableName replacementBody sourceTail actualBody)
      normalBodyMatchVariableDirective
    normalBodyPrefixAtom proofOwner proofPosition replacementBody actualBody
          sourceTail continuation ∈ result ∧
      normalBodyMatchReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyMatchVariablePhaseSpace proofOwner continuation proofPosition
        variableName replacementBody sourceTail actualBody)
      normalBodyMatchVariableDirective.atom)
    normalBodyMatchVariableDirective.rule.input).map Prod.fst
  let substitution := normalBodyMatchVariableSubstitution proofOwner
    continuation proofPosition variableName replacementBody sourceTail
    actualBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyMatchVariableDirective] using
      normalBodyMatchVariableMatchRow_mem proofOwner continuation proofPosition
        variableName replacementBody sourceTail actualBody
  have prefixInstantiates :
      instantiateTemplateAtom? substitution normalBodyMatchVariablePrefixTemplate =
        some (normalBodyPrefixAtom proofOwner proofPosition replacementBody
          actualBody sourceTail continuation) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalBodyMatchVariableReloadTemplate =
        some (normalBodyMatchReloadAtom proofOwner proofPosition) := by
    rfl
  have prefixStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyMatchVariablePrefixTemplate
    (normalBodyPrefixAtom proofOwner proofPosition replacementBody actualBody
      sourceTail continuation) rowMember prefixInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyMatchVariableReloadTemplate
    (normalBodyMatchReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyMatchVariableDirective, normalBodyMatchVariableSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr prefixStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyMatchVariableDirective, normalBodyMatchVariableSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-- Expanding one substituted variable is an actual scheduled reflective-MM2
step inhabiting its exact OSLF-generated target type. -/
theorem normalBodyMatchVariablePhase_inhabits_target_native_type
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (variableName : String)
    (replacementBody sourceTail actualBody : List Metamath.Verify.Sym) :
    let source := normalBodyMatchVariablePhaseSpace proofOwner continuation
      proofPosition variableName replacementBody sourceTail actualBody
    let target := fireReflectiveSourceExecFact source
      normalBodyMatchVariableDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyPrefixAtom proofOwner proofPosition replacementBody actualBody
            sourceTail continuation ∈ target ∧
        normalBodyMatchReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyMatchVariablePhase_selects_directive proofOwner
          continuation proofPosition variableName replacementBody sourceTail
          actualBody))
  · exact normalBodyMatchVariableDirective_fires_prefix proofOwner
      continuation proofPosition variableName replacementBody sourceTail
      actualBody

def normalBodyPrefixNilPhaseSpace (proofOwner continuation : Atom)
    (proofPosition : Nat)
    (sourceTail actualBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyPrefixNilRule,
   normalBodyPrefixAtom proofOwner proofPosition [] actualBody sourceTail
      continuation].toFinset

/-- The ordinary scheduler selects the empty-prefix directive on its focused
body-match boundary. -/
theorem normalBodyPrefixNilPhase_selects_directive
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (sourceTail actualBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyPrefixNilPhaseSpace proofOwner continuation proofPosition
            sourceTail actualBody)) =
      some normalBodyPrefixNilDirective := by
  let atoms :=
    [normalBodyPrefixNilRule,
     normalBodyPrefixAtom proofOwner proofPosition [] actualBody sourceTail
       continuation]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyPrefixNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyPrefixNilDirective
    (by simp [atoms, normalBodyPrefixNilRule, normalBodyPrefixAtom])
    (by rfl)

private def normalBodyPrefixNilSubstitution (proofOwner continuation : Atom)
    (proofPosition : Nat)
    (sourceTail actualBody : List Metamath.Verify.Sym) : Subst :=
  [("continuation", continuation),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("actual-body", listAtom runtimeSymAtom actualBody),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyPrefixNilMatchRow_mem
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (sourceTail actualBody : List Metamath.Verify.Sym) :
    normalBodyPrefixNilSubstitution proofOwner continuation proofPosition
        sourceTail actualBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyPrefixNilPhaseSpace proofOwner continuation proofPosition
            sourceTail actualBody)
          normalBodyPrefixNilRule)
        normalBodyPrefixNilDirective.rule.input).map Prod.fst := by
  let current := normalBodyPrefixAtom proofOwner proofPosition [] actualBody
    sourceTail continuation
  let substitution := normalBodyPrefixNilSubstitution proofOwner continuation
    proofPosition sourceTail actualBody
  let read := readCopyAtom
    (normalBodyPrefixNilPhaseSpace proofOwner continuation proofPosition
      sourceTail actualBody)
    normalBodyPrefixNilRule
  have currentMem : current ∈ read := by
    simp [read, readCopyAtom, consumeAtom, current, normalBodyPrefixAtom,
      normalBodyPrefixNilPhaseSpace, normalBodyPrefixNilRule, listAtom]
  have matchCurrent :
      matchAtom [] normalBodyPrefixNilCurrentTemplate current =
        some substitution := by
    simp [normalBodyPrefixNilCurrentTemplate,
      normalBodyPrefixNilPatternAtoms, current, normalBodyPrefixAtom,
      substitution, normalBodyPrefixNilSubstitution, listAtom, nilTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {current}), ?_, rfl⟩
  simp only [normalBodyPrefixNilDirective, matchInputSpec,
    normalBodyPrefixNilPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, current),
    matchOneInSpace_mem [] _ read current currentMem substitution
      matchCurrent, ?_⟩
  simp [substitution, current]

/-- Empty replacement prefixes resume the outer source-body match without
changing either remaining tail. -/
theorem normalBodyPrefixNilDirective_fires_match
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (sourceTail actualBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyPrefixNilPhaseSpace proofOwner continuation proofPosition
        sourceTail actualBody)
      normalBodyPrefixNilDirective
    normalBodyMatchAtom proofOwner proofPosition sourceTail actualBody
          continuation ∈ result ∧
      normalBodyMatchReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyPrefixNilPhaseSpace proofOwner continuation proofPosition
        sourceTail actualBody)
      normalBodyPrefixNilDirective.atom)
    normalBodyPrefixNilDirective.rule.input).map Prod.fst
  let substitution := normalBodyPrefixNilSubstitution proofOwner continuation
    proofPosition sourceTail actualBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyPrefixNilDirective] using
      normalBodyPrefixNilMatchRow_mem proofOwner continuation proofPosition
        sourceTail actualBody
  have tailInstantiates :
      instantiateTemplateAtom? substitution normalBodyPrefixNilTailTemplate =
        some (normalBodyMatchAtom proofOwner proofPosition sourceTail actualBody
          continuation) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalBodyPrefixNilReloadTemplate =
        some (normalBodyMatchReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyPrefixNilTailTemplate
    (normalBodyMatchAtom proofOwner proofPosition sourceTail actualBody
      continuation) rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyPrefixNilReloadTemplate
    (normalBodyMatchReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyPrefixNilDirective, normalBodyPrefixNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyPrefixNilDirective, normalBodyPrefixNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-- Exhausting a replacement prefix is an actual scheduled reflective-MM2
step inhabiting its exact OSLF-generated target type. -/
theorem normalBodyPrefixNilPhase_inhabits_target_native_type
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (sourceTail actualBody : List Metamath.Verify.Sym) :
    let source := normalBodyPrefixNilPhaseSpace proofOwner continuation
      proofPosition sourceTail actualBody
    let target := fireReflectiveSourceExecFact source
      normalBodyPrefixNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyMatchAtom proofOwner proofPosition sourceTail actualBody
            continuation ∈ target ∧
        normalBodyMatchReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyPrefixNilPhase_selects_directive proofOwner continuation
          proofPosition sourceTail actualBody))
  · exact normalBodyPrefixNilDirective_fires_match proofOwner continuation
      proofPosition sourceTail actualBody

def normalBodyPrefixConsPhaseSpace (proofOwner continuation : Atom)
    (proofPosition : Nat) (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) : Space :=
  [normalBodyPrefixConsRule,
   normalBodyPrefixAtom proofOwner proofPosition
      (replacementSymbol :: replacementTail)
      (replacementSymbol :: actualTail) sourceTail continuation].toFinset

/-- The ordinary scheduler selects the equal-prefix directive on its focused
body-match boundary. -/
theorem normalBodyPrefixConsPhase_selects_directive
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyPrefixConsPhaseSpace proofOwner continuation
            proofPosition replacementSymbol replacementTail actualTail
            sourceTail)) =
      some normalBodyPrefixConsDirective := by
  let atoms :=
    [normalBodyPrefixConsRule,
     normalBodyPrefixAtom proofOwner proofPosition
       (replacementSymbol :: replacementTail)
       (replacementSymbol :: actualTail) sourceTail continuation]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyPrefixConsDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyPrefixConsDirective
    (by simp [atoms, normalBodyPrefixConsRule, normalBodyPrefixAtom])
    (by rfl)

private def normalBodyPrefixConsSubstitution (proofOwner continuation : Atom)
    (proofPosition : Nat) (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) : Subst :=
  [("continuation", continuation),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("actual-tail", listAtom runtimeSymAtom actualTail),
   ("replacement-tail", listAtom runtimeSymAtom replacementTail),
   ("replacement-symbol", runtimeSymAtom replacementSymbol),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyPrefixConsMatchRow_mem
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) :
    normalBodyPrefixConsSubstitution proofOwner continuation proofPosition
        replacementSymbol replacementTail actualTail sourceTail ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyPrefixConsPhaseSpace proofOwner continuation proofPosition
            replacementSymbol replacementTail actualTail sourceTail)
          normalBodyPrefixConsRule)
        normalBodyPrefixConsDirective.rule.input).map Prod.fst := by
  let current := normalBodyPrefixAtom proofOwner proofPosition
    (replacementSymbol :: replacementTail)
    (replacementSymbol :: actualTail) sourceTail continuation
  let substitution := normalBodyPrefixConsSubstitution proofOwner continuation
    proofPosition replacementSymbol replacementTail actualTail sourceTail
  let read := readCopyAtom
    (normalBodyPrefixConsPhaseSpace proofOwner continuation proofPosition
      replacementSymbol replacementTail actualTail sourceTail)
    normalBodyPrefixConsRule
  have currentMem : current ∈ read := by
    simp [read, readCopyAtom, consumeAtom, current, normalBodyPrefixAtom,
      normalBodyPrefixConsPhaseSpace, normalBodyPrefixConsRule, listAtom]
  have matchCurrent :
      matchAtom [] normalBodyPrefixConsCurrentTemplate current =
        some substitution := by
    simp [normalBodyPrefixConsCurrentTemplate,
      normalBodyPrefixConsPatternAtoms, current, normalBodyPrefixAtom,
      substitution, normalBodyPrefixConsSubstitution, listAtom, consTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {current}), ?_, rfl⟩
  simp only [normalBodyPrefixConsDirective, matchInputSpec,
    normalBodyPrefixConsPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, current),
    matchOneInSpace_mem [] _ read current currentMem substitution
      matchCurrent, ?_⟩
  simp [substitution, current]

/-- Equal leading symbols in a replacement and actual body are consumed by
the emitted prefix rule, retaining all three exact tails. -/
theorem normalBodyPrefixConsDirective_fires_tail
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyPrefixConsPhaseSpace proofOwner continuation proofPosition
        replacementSymbol replacementTail actualTail sourceTail)
      normalBodyPrefixConsDirective
    normalBodyPrefixAtom proofOwner proofPosition replacementTail actualTail
          sourceTail continuation ∈ result ∧
      normalBodyMatchReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyPrefixConsPhaseSpace proofOwner continuation proofPosition
        replacementSymbol replacementTail actualTail sourceTail)
      normalBodyPrefixConsDirective.atom)
    normalBodyPrefixConsDirective.rule.input).map Prod.fst
  let substitution := normalBodyPrefixConsSubstitution proofOwner continuation
    proofPosition replacementSymbol replacementTail actualTail sourceTail
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyPrefixConsDirective] using
      normalBodyPrefixConsMatchRow_mem proofOwner continuation proofPosition
        replacementSymbol replacementTail actualTail sourceTail
  have tailInstantiates :
      instantiateTemplateAtom? substitution normalBodyPrefixConsTailTemplate =
        some (normalBodyPrefixAtom proofOwner proofPosition replacementTail
          actualTail sourceTail continuation) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalBodyPrefixConsReloadTemplate =
        some (normalBodyMatchReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyPrefixConsTailTemplate
    (normalBodyPrefixAtom proofOwner proofPosition replacementTail actualTail
      sourceTail continuation) rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyPrefixConsReloadTemplate
    (normalBodyMatchReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyPrefixConsDirective, normalBodyPrefixConsSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyPrefixConsDirective, normalBodyPrefixConsSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-- Consuming one equal replacement symbol is an actual scheduled
reflective-MM2 step inhabiting its exact OSLF-generated target type. -/
theorem normalBodyPrefixConsPhase_inhabits_target_native_type
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym) :
    let source := normalBodyPrefixConsPhaseSpace proofOwner continuation
      proofPosition replacementSymbol replacementTail actualTail sourceTail
    let target := fireReflectiveSourceExecFact source
      normalBodyPrefixConsDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyPrefixAtom proofOwner proofPosition replacementTail actualTail
            sourceTail continuation ∈ target ∧
        normalBodyMatchReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyPrefixConsPhase_selects_directive proofOwner continuation
          proofPosition replacementSymbol replacementTail actualTail
          sourceTail))
  · exact normalBodyPrefixConsDirective_fires_tail proofOwner continuation
      proofPosition replacementSymbol replacementTail actualTail sourceTail

/-- Prefix comparison cannot consume unequal encoded Metamath symbols. -/
theorem normalBodyPrefixConsPattern_rejects_mismatched_symbol
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (replacementSymbol actualSymbol : Metamath.Verify.Sym)
    (replacementTail actualTail sourceTail : List Metamath.Verify.Sym)
    (different : replacementSymbol ≠ actualSymbol) :
    matchAtom [] normalBodyPrefixConsCurrentTemplate
        (normalBodyPrefixAtom proofOwner proofPosition
          (replacementSymbol :: replacementTail)
          (actualSymbol :: actualTail) sourceTail continuation) = none := by
  have encodedDifferent :
      runtimeSymAtom actualSymbol ≠ runtimeSymAtom replacementSymbol := by
    intro equal
    exact different (runtimeSymAtom_injective equal).symm
  simp [normalBodyPrefixConsCurrentTemplate,
    normalBodyPrefixConsPatternAtoms, normalBodyPrefixAtom, listAtom, consTag,
    matchAtom, matchAtom.matchAtomList, Subst.lookup, encodedDifferent]

def normalBodyMatchNilPhaseSpace (proofOwner continuation : Atom)
    (proofPosition : Nat) : Space :=
  [normalBodyMatchNilRule,
   normalBodyMatchAtom proofOwner proofPosition [] [] continuation].toFinset

/-- The ordinary scheduler selects the completed-body directive on its focused
body-match boundary. -/
theorem normalBodyMatchNilPhase_selects_directive
    (proofOwner continuation : Atom) (proofPosition : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyMatchNilPhaseSpace proofOwner continuation
            proofPosition)) =
      some normalBodyMatchNilDirective := by
  let atoms :=
    [normalBodyMatchNilRule,
     normalBodyMatchAtom proofOwner proofPosition [] [] continuation]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyMatchNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyMatchNilDirective
    (by simp [atoms, normalBodyMatchNilRule, normalBodyMatchAtom])
    (by rfl)

private def normalBodyMatchNilSubstitution (proofOwner continuation : Atom)
    (proofPosition : Nat) : Subst :=
  [("continuation", continuation),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyMatchNilMatchRow_mem
    (proofOwner continuation : Atom) (proofPosition : Nat) :
    normalBodyMatchNilSubstitution proofOwner continuation proofPosition ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyMatchNilPhaseSpace proofOwner continuation proofPosition)
          normalBodyMatchNilRule)
        normalBodyMatchNilDirective.rule.input).map Prod.fst := by
  let current := normalBodyMatchAtom proofOwner proofPosition [] [] continuation
  let substitution := normalBodyMatchNilSubstitution proofOwner continuation
    proofPosition
  let read := readCopyAtom
    (normalBodyMatchNilPhaseSpace proofOwner continuation proofPosition)
    normalBodyMatchNilRule
  have currentMem : current ∈ read := by
    simp [read, readCopyAtom, consumeAtom, current, normalBodyMatchAtom,
      normalBodyMatchNilPhaseSpace, normalBodyMatchNilRule, listAtom]
  have matchCurrent :
      matchAtom [] normalBodyMatchNilCurrentTemplate current =
        some substitution := by
    simp [normalBodyMatchNilCurrentTemplate,
      normalBodyMatchNilPatternAtoms, current, normalBodyMatchAtom,
      substitution, normalBodyMatchNilSubstitution, listAtom, nilTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {current}), ?_, rfl⟩
  simp only [normalBodyMatchNilDirective, matchInputSpec,
    normalBodyMatchNilPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, current),
    matchOneInSpace_mem [] _ read current currentMem substitution
      matchCurrent, ?_⟩
  simp [substitution, current]

/-- Exhausting both bodies emits the exact authored continuation and keeps
the generic matcher available for the next essential hypothesis. -/
theorem normalBodyMatchNilDirective_fires_continuation
    (proofOwner continuation : Atom) (proofPosition : Nat) :
    let result := fireReflectiveSourceExecFact
      (normalBodyMatchNilPhaseSpace proofOwner continuation proofPosition)
      normalBodyMatchNilDirective
    continuation ∈ result ∧
      normalBodyMatchReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyMatchNilPhaseSpace proofOwner continuation proofPosition)
      normalBodyMatchNilDirective.atom)
    normalBodyMatchNilDirective.rule.input).map Prod.fst
  let substitution := normalBodyMatchNilSubstitution proofOwner continuation
    proofPosition
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyMatchNilDirective] using
      normalBodyMatchNilMatchRow_mem proofOwner continuation proofPosition
  have continuationInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyMatchNilContinuationTemplate = some continuation := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalBodyMatchNilReloadTemplate =
        some (normalBodyMatchReloadAtom proofOwner proofPosition) := by
    rfl
  have continuationStaged := reflectiveStage_add_contains_of_row rows
    substitution normalBodyMatchNilContinuationTemplate continuation rowMember
    continuationInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyMatchNilReloadTemplate
    (normalBodyMatchReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyMatchNilDirective, normalBodyMatchNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr continuationStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyMatchNilDirective, normalBodyMatchNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-- Finishing a complete substituted body is an actual scheduled
reflective-MM2 step inhabiting its exact OSLF-generated target type. -/
theorem normalBodyMatchNilPhase_inhabits_target_native_type
    (proofOwner continuation : Atom) (proofPosition : Nat) :
    let source := normalBodyMatchNilPhaseSpace proofOwner continuation
      proofPosition
    let target := fireReflectiveSourceExecFact source
      normalBodyMatchNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      continuation ∈ target ∧
        normalBodyMatchReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyMatchNilPhase_selects_directive proofOwner continuation
          proofPosition))
  · exact normalBodyMatchNilDirective_fires_continuation proofOwner
      continuation proofPosition

/-- A source body cannot finish while the actual formula retains a symbol. -/
theorem normalBodyMatchNilPattern_rejects_actual_remainder
    (proofOwner continuation : Atom) (proofPosition : Nat)
    (actualHead : Metamath.Verify.Sym)
    (actualTail : List Metamath.Verify.Sym) :
    matchAtom [] normalBodyMatchNilCurrentTemplate
        (normalBodyMatchAtom proofOwner proofPosition []
          (actualHead :: actualTail) continuation) = none := by
  simp [normalBodyMatchNilCurrentTemplate, normalBodyMatchNilPatternAtoms,
    normalBodyMatchAtom, listAtom, nilTag, consTag, matchAtom,
    matchAtom.matchAtomList, Subst.lookup]

private theorem normalAcceptMatchRow_mem
    (scopeOwner proofOwner theoremLabel expected occurrence : Atom)
    (endPosition : Nat) :
    normalAcceptSubstitution scopeOwner proofOwner (natAtom endPosition)
        (natAtom 1) theoremLabel expected occurrence ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAcceptPhaseSpace scopeOwner proofOwner theoremLabel expected
            occurrence endPosition)
          normalAcceptRule)
        normalAcceptDirective.rule.input).map Prod.fst := by
  let control : Atom :=
    .expression
      [.symbol "mm-normal-control", scopeOwner, proofOwner,
        natAtom endPosition, natAtom 1]
  let proofEnd : Atom :=
    .expression
      [.symbol "mm-proof-end", proofOwner, natAtom endPosition]
  let proof : Atom :=
    .expression
      [.symbol "mm-proof", scopeOwner, proofOwner, .symbol "normal",
        theoremLabel, expected]
  let successor : Atom :=
    .expression
      [.symbol "mm-index-successor", proofOwner, natAtom 0, natAtom 1]
  let stack : Atom :=
    .expression
      [.symbol "mm-stack-cell", proofOwner, natAtom 0, expected, occurrence]
  let read : Space := readCopyAtom
    (normalAcceptPhaseSpace scopeOwner proofOwner theoremLabel expected
      occurrence endPosition)
    normalAcceptRule
  let afterControl : Subst :=
    [("top", natAtom 1), ("end", natAtom endPosition),
     ("proof", proofOwner), ("scope", scopeOwner)]
  let afterProof : Subst :=
    [("expected", expected), ("theorem-label", theoremLabel),
     ("top", natAtom 1), ("end", natAtom endPosition),
     ("proof", proofOwner), ("scope", scopeOwner)]
  let finalRow : Subst :=
    normalAcceptSubstitution scopeOwner proofOwner (natAtom endPosition)
      (natAtom 1) theoremLabel expected occurrence
  have controlMem : control ∈ read := by
    simp [read, control, readCopyAtom, consumeAtom, normalAcceptPhaseSpace,
      normalAcceptRule]
  have proofEndMem : proofEnd ∈ read := by
    simp [read, proofEnd, readCopyAtom, consumeAtom, normalAcceptPhaseSpace,
      normalAcceptRule]
  have proofMem : proof ∈ read := by
    simp [read, proof, readCopyAtom, consumeAtom, normalAcceptPhaseSpace,
      normalAcceptRule]
  have successorMem : successor ∈ read := by
    simp [read, successor, readCopyAtom, consumeAtom, normalAcceptPhaseSpace,
      normalAcceptRule]
  have stackMem : stack ∈ read := by
    simp [read, stack, readCopyAtom, consumeAtom, normalAcceptPhaseSpace,
      normalAcceptRule]
  have matchControl :
      matchAtom []
          (.expression
            [.symbol "mm-normal-control", .var "scope", .var "proof",
              .var "end", .var "top"])
          control = some afterControl := by
    simp [control, afterControl, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchProofEnd :
      matchAtom afterControl
          (.expression
            [.symbol "mm-proof-end", .var "proof", .var "end"])
          proofEnd = some afterControl := by
    simp [afterControl, proofEnd, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchProof :
      matchAtom afterControl
          (.expression
            [.symbol "mm-proof", .var "scope", .var "proof",
              .symbol "normal", .var "theorem-label", .var "expected"])
          proof = some afterProof := by
    simp [afterControl, afterProof, proof, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchNatZero :
      matchAtom afterProof (natAtom 0) (natAtom 0) = some afterProof := by
    simp [natAtom, matchAtom, matchAtom.matchAtomList]
  have matchSuccessor :
      matchAtom afterProof
          (.expression
            [.symbol "mm-index-successor", .var "proof",
              natAtom 0, .var "top"])
          successor = some afterProof := by
    simp [afterProof, successor, matchAtom, matchAtom.matchAtomList,
      Subst.lookup, matchNatZero]
  have matchStack :
      matchAtom afterProof
          (.expression
            [.symbol "mm-stack-cell", .var "proof", natAtom 0,
              .var "expected", .var "occurrence"])
          stack = some finalRow := by
    simp [afterProof, finalRow, normalAcceptSubstitution, stack, matchAtom,
      matchAtom.matchAtomList, Subst.lookup, matchNatZero]
  rw [List.mem_map]
  refine ⟨(finalRow, {control, proofEnd, proof, successor, stack}), ?_, rfl⟩
  simp only [normalAcceptDirective, matchInputSpec, normalAcceptPatternAtoms,
    mkPattern, matchPattern, matchPattern.go, List.mem_flatMap]
  refine ⟨(afterControl, control),
    matchOneInSpace_mem [] _ read control controlMem afterControl matchControl, ?_⟩
  refine ⟨(afterControl, proofEnd),
    matchOneInSpace_mem afterControl _ read proofEnd proofEndMem afterControl
      matchProofEnd, ?_⟩
  refine ⟨(afterProof, proof),
    matchOneInSpace_mem afterControl _ read proof proofMem afterProof matchProof, ?_⟩
  refine ⟨(afterProof, successor),
    matchOneInSpace_mem afterProof _ read successor successorMem afterProof
      matchSuccessor, ?_⟩
  refine ⟨(finalRow, stack),
    matchOneInSpace_mem afterProof _ read stack stackMem finalRow matchStack, ?_⟩
  simp [finalRow, control, proofEnd, proof, successor, stack]

/-- The actual reflective-MM2 firing of the emitted acceptance directive adds
the exact terminal observation.  This is an operational statement about the
target evaluator, not merely a template-shape assertion. -/
theorem normalAcceptDirective_fires_terminal
    (scopeOwner proofOwner theoremLabel expected occurrence : Atom)
    (endPosition : Nat) :
    normalAcceptedAtom scopeOwner proofOwner theoremLabel expected occurrence ∈
      fireReflectiveSourceExecFact
        (normalAcceptPhaseSpace scopeOwner proofOwner theoremLabel expected
          occurrence endPosition)
        normalAcceptDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalAcceptPhaseSpace scopeOwner proofOwner theoremLabel expected
        occurrence endPosition)
      normalAcceptDirective.atom)
    normalAcceptDirective.rule.input).map Prod.fst
  have rowMember :
      normalAcceptSubstitution scopeOwner proofOwner (natAtom endPosition)
          (natAtom 1) theoremLabel expected occurrence ∈ rows := by
    simpa [rows, normalAcceptDirective] using
      normalAcceptMatchRow_mem scopeOwner proofOwner theoremLabel expected
        occurrence endPosition
  have stagedMember :
      normalAcceptedAtom scopeOwner proofOwner theoremLabel expected occurrence ∈
        rows.foldl
          (stageReflectiveSupportSink (.add normalAcceptedTemplate)) [] :=
    reflectiveStage_add_contains_of_row rows
      (normalAcceptSubstitution scopeOwner proofOwner (natAtom endPosition)
        (natAtom 1) theoremLabel expected occurrence)
      normalAcceptedTemplate
      (normalAcceptedAtom scopeOwner proofOwner theoremLabel expected occurrence)
      rowMember
      (normalAcceptedTemplate_instantiates scopeOwner proofOwner
        (natAtom endPosition) (natAtom 1) theoremLabel expected occurrence)
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalAcceptDirective, normalAcceptSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr stagedMember)

/-- Terminal acceptance is an actual scheduled reflective-MM2 step inhabiting
its exact OSLF-generated target type and producing the declared observation. -/
theorem normalAcceptPhase_inhabits_target_native_type
    (scopeOwner proofOwner theoremLabel expected occurrence : Atom)
    (endPosition : Nat) :
    let source := normalAcceptPhaseSpace scopeOwner proofOwner theoremLabel
      expected occurrence endPosition
    let target := fireReflectiveSourceExecFact source normalAcceptDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalAcceptedAtom scopeOwner proofOwner theoremLabel expected
        occurrence ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAcceptPhase_selects_directive scopeOwner proofOwner theoremLabel
          expected occurrence endPosition))
  · exact normalAcceptDirective_fires_terminal scopeOwner proofOwner
      theoremLabel expected occurrence endPosition

/-! ### Assertion finish and DV-entry boundary -/

/-- Result data read by the generic assertion-finishing phase. -/
def normalAssertionResultAtom (scopeOwner : Atom) (assertionLabel
    resultTypecode : String) (sourceBody : List Metamath.Verify.Sym) : Atom :=
  .expression
    [.symbol "mm-assertion-result", scopeOwner, stringAtom assertionLabel,
      stringAtom resultTypecode, listAtom runtimeSymAtom sourceBody]

/-- The exact result-construction context carried through DV checking. -/
def normalAssertionResultContextAtom (scopeOwner : Atom)
    (nextProofPosition : Nat) (assertionLabel resultTypecode : String)
    (stackBase nextTop : Nat) : Atom :=
  .expression
    [.symbol "mm-assertion-result-context", scopeOwner,
      natAtom nextProofPosition, stringAtom assertionLabel,
      stringAtom resultTypecode, natAtom stackBase, natAtom nextTop]

/-- Ordered cursor for one source assertion's DV-pair table. -/
def normalDVNextPairAtom (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (pairPosition pairEnd : Nat) (sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", scopeOwner, proofOwner,
      natAtom proofPosition, stringAtom assertionLabel,
      natAtom pairPosition, natAtom pairEnd,
      listAtom runtimeSymAtom sourceBody, context]

/-- Explicit request to reinstall the finite DV micro-machine. -/
def normalDVReloadAtom (proofOwner : Atom) (proofPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-reload-dv", proofOwner, natAtom proofPosition]

/-- Cursor for the left-hand substitution body of one callee DV pair. -/
def normalDVScanLeftAtom (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", scopeOwner, proofOwner,
      natAtom proofPosition, stringAtom assertionLabel,
      natAtom nextPairPosition, natAtom pairEnd,
      listAtom runtimeSymAtom leftBody,
      listAtom runtimeSymAtom rightBody,
      listAtom runtimeSymAtom sourceBody, context]

/-- Cursor for the right-hand substitution body at one selected variable from
the left-hand substitution body. -/
def normalDVScanRightAtom (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightRemainder rightBody sourceBody :
      List Metamath.Verify.Sym) (context : Atom) : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", scopeOwner, proofOwner,
      natAtom proofPosition, stringAtom assertionLabel,
      natAtom nextPairPosition, natAtom pairEnd,
      stringAtom leftVariable, listAtom runtimeSymAtom leftTail,
      listAtom runtimeSymAtom rightRemainder,
      listAtom runtimeSymAtom rightBody,
      listAtom runtimeSymAtom sourceBody, context]

private def normalAssertionFinishPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-assertion-bind", .var "scope", .var "proof",
        .var "pc", .var "next-pc", .var "label", .var "hyp-end",
        .var "hyp-end", .var "stack-end", .var "stack-base"],
   .expression
      [.symbol "mm-assertion-result", .var "scope", .var "label",
        .var "result-typecode", .var "source-body"],
   .expression
      [.symbol "mm-assertion-dv-header", .var "scope", .var "label",
        .var "assertion-position"],
   .expression
      [.symbol "mm-index-successor", .var "proof", .var "stack-base",
        .var "next-top"]]

private def normalAssertionFinishBindTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-bind", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "label", .var "hyp-end",
      .var "hyp-end", .var "stack-end", .var "stack-base"]

private def normalAssertionFinishNextPairTemplate : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
      .var "pc", .var "label", natAtom 0, .var "assertion-position",
      .var "source-body",
      .expression
        [.symbol "mm-assertion-result-context", .var "scope",
          .var "next-pc", .var "label", .var "result-typecode",
          .var "stack-base", .var "next-top"]]

private def normalAssertionFinishReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-dv", .var "proof", .var "pc"]

private def normalAssertionFinishSinks : List Sink :=
  [.remove normalAssertionFinishBindTemplate,
   .add normalAssertionFinishNextPairTemplate,
   .add normalAssertionFinishReloadTemplate]

/-- Supported ordinary-MM2 directive represented by the emitted assertion
finish rule. -/
def normalAssertionFinishDirective : SourceExecFact where
  atom := normalAssertionFinishRule
  loc := normalAssertionFinishLocation
  rule :=
    { priority := 13
      name := "mm-normal-assertion-finish"
      input := .compat (mkPattern normalAssertionFinishPatternAtoms)
      guards := []
      tmpl := mkTemplate normalAssertionFinishSinks }

theorem extract_normalAssertionFinishRule_exact :
    extractSupportedSourceExecFact normalAssertionFinishRule =
      some normalAssertionFinishDirective := by
  rfl

def normalAssertionFinishPhaseAtoms (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackEnd stackBase : Nat) (resultTypecode : String)
    (sourceBody : List Metamath.Verify.Sym) (dvEnd nextTop : Nat) :
    List Atom :=
  [normalAssertionFinishRule,
   normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisEnd hypothesisEnd stackEnd
      stackBase,
   normalAssertionResultAtom scopeOwner assertionLabel resultTypecode
      sourceBody,
   .expression
      [.symbol "mm-assertion-dv-header", scopeOwner,
        stringAtom assertionLabel, natAtom dvEnd],
   .expression
      [.symbol "mm-index-successor", proofOwner, natAtom stackBase,
        natAtom nextTop]]

def normalAssertionFinishPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackEnd stackBase : Nat) (resultTypecode : String)
    (sourceBody : List Metamath.Verify.Sym) (dvEnd nextTop : Nat) : Space :=
  (normalAssertionFinishPhaseAtoms scopeOwner proofOwner proofPosition
    nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
    resultTypecode sourceBody dvEnd nextTop).toFinset

theorem normalAssertionFinishPhaseAtoms_nodup
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackEnd stackBase : Nat) (resultTypecode : String)
    (sourceBody : List Metamath.Verify.Sym) (dvEnd nextTop : Nat) :
    (normalAssertionFinishPhaseAtoms scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
      resultTypecode sourceBody dvEnd nextTop).Nodup := by
  simp [normalAssertionFinishPhaseAtoms, normalAssertionFinishRule,
    normalAssertionFinishLocation, normalAssertionFinishInput,
    normalAssertionFinishOutput, normalAssertionNextBindAtom,
    normalAssertionResultAtom]

theorem normalAssertionFinishPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackEnd stackBase : Nat) (resultTypecode : String)
    (sourceBody : List Metamath.Verify.Sym) (dvEnd nextTop : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionFinishPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
            resultTypecode sourceBody dvEnd nextTop)) =
      some normalAssertionFinishDirective := by
  let atoms := normalAssertionFinishPhaseAtoms scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisEnd stackEnd
    stackBase resultTypecode sourceBody dvEnd nextTop
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionFinishDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionFinishDirective
    (normalAssertionFinishPhaseAtoms_nodup scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
      resultTypecode sourceBody dvEnd nextTop)
    (by rfl)

private def normalAssertionFinishSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackEnd stackBase : Nat) (resultTypecode : String)
    (sourceBody : List Metamath.Verify.Sym) (dvEnd nextTop : Nat) : Subst :=
  [("next-top", natAtom nextTop), ("assertion-position", natAtom dvEnd),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("result-typecode", stringAtom resultTypecode),
   ("stack-base", natAtom stackBase), ("stack-end", natAtom stackEnd),
   ("hyp-end", natAtom hypothesisEnd),
   ("label", stringAtom assertionLabel),
   ("next-pc", natAtom nextProofPosition),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalAssertionFinishMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackEnd stackBase : Nat) (resultTypecode : String)
    (sourceBody : List Metamath.Verify.Sym) (dvEnd nextTop : Nat) :
    normalAssertionFinishSubstitution scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
        resultTypecode sourceBody dvEnd nextTop ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionFinishPhaseSpace scopeOwner proofOwner proofPosition
            nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
            resultTypecode sourceBody dvEnd nextTop)
          normalAssertionFinishRule)
        normalAssertionFinishDirective.rule.input).map Prod.fst := by
  let bind := normalAssertionNextBindAtom scopeOwner proofOwner proofPosition
    nextProofPosition assertionLabel hypothesisEnd hypothesisEnd stackEnd
    stackBase
  let resultRow := normalAssertionResultAtom scopeOwner assertionLabel
    resultTypecode sourceBody
  let dvHeader : Atom :=
    .expression
      [.symbol "mm-assertion-dv-header", scopeOwner,
        stringAtom assertionLabel, natAtom dvEnd]
  let successor : Atom :=
    .expression
      [.symbol "mm-index-successor", proofOwner, natAtom stackBase,
        natAtom nextTop]
  let afterBind : Subst :=
    [("stack-base", natAtom stackBase), ("stack-end", natAtom stackEnd),
     ("hyp-end", natAtom hypothesisEnd),
     ("label", stringAtom assertionLabel),
     ("next-pc", natAtom nextProofPosition),
     ("pc", natAtom proofPosition), ("proof", proofOwner),
     ("scope", scopeOwner)]
  let afterResult : Subst :=
    [("source-body", listAtom runtimeSymAtom sourceBody),
     ("result-typecode", stringAtom resultTypecode)] ++ afterBind
  let afterDV : Subst :=
    [("assertion-position", natAtom dvEnd)] ++ afterResult
  let finalRow := normalAssertionFinishSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisEnd stackEnd
    stackBase resultTypecode sourceBody dvEnd nextTop
  let read := readCopyAtom
    (normalAssertionFinishPhaseSpace scopeOwner proofOwner proofPosition
      nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
      resultTypecode sourceBody dvEnd nextTop)
    normalAssertionFinishRule
  have bindMem : bind ∈ read := by
    simp [read, bind, readCopyAtom, consumeAtom,
      normalAssertionFinishPhaseSpace, normalAssertionFinishPhaseAtoms,
      normalAssertionFinishRule, normalAssertionFinishLocation,
      normalAssertionFinishInput, normalAssertionFinishOutput,
      normalAssertionNextBindAtom]
  have resultMem : resultRow ∈ read := by
    simp [read, resultRow, readCopyAtom, consumeAtom,
      normalAssertionFinishPhaseSpace, normalAssertionFinishPhaseAtoms,
      normalAssertionFinishRule, normalAssertionFinishLocation,
      normalAssertionFinishInput, normalAssertionFinishOutput,
      normalAssertionResultAtom]
  have dvMem : dvHeader ∈ read := by
    simp [read, dvHeader, readCopyAtom, consumeAtom,
      normalAssertionFinishPhaseSpace, normalAssertionFinishPhaseAtoms,
      normalAssertionFinishRule, normalAssertionFinishLocation,
      normalAssertionFinishInput, normalAssertionFinishOutput]
  have successorMem : successor ∈ read := by
    simp [read, successor, readCopyAtom, consumeAtom,
      normalAssertionFinishPhaseSpace, normalAssertionFinishPhaseAtoms,
      normalAssertionFinishRule, normalAssertionFinishLocation,
      normalAssertionFinishInput, normalAssertionFinishOutput]
  have matchBind :
      matchAtom [] normalAssertionFinishBindTemplate bind =
        some afterBind := by
    simp [normalAssertionFinishBindTemplate, bind,
      normalAssertionNextBindAtom, afterBind, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchResult :
      matchAtom afterBind normalAssertionFinishPatternAtoms[1] resultRow =
        some afterResult := by
    simp [normalAssertionFinishPatternAtoms, resultRow,
      normalAssertionResultAtom, afterBind, afterResult, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchDV :
      matchAtom afterResult normalAssertionFinishPatternAtoms[2] dvHeader =
        some afterDV := by
    simp [normalAssertionFinishPatternAtoms, dvHeader, afterResult, afterDV,
      afterBind, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchSuccessor :
      matchAtom afterDV normalAssertionFinishPatternAtoms[3] successor =
        some finalRow := by
    simp [normalAssertionFinishPatternAtoms, successor, afterDV, afterResult,
      afterBind, finalRow, normalAssertionFinishSubstitution, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {bind, resultRow, dvHeader, successor}), ?_, rfl⟩
  simp only [normalAssertionFinishDirective, matchInputSpec,
    normalAssertionFinishPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterBind, bind),
    matchOneInSpace_mem [] _ read bind bindMem afterBind matchBind, ?_⟩
  refine ⟨(afterResult, resultRow),
    matchOneInSpace_mem afterBind _ read resultRow resultMem afterResult
      matchResult, ?_⟩
  refine ⟨(afterDV, dvHeader),
    matchOneInSpace_mem afterResult _ read dvHeader dvMem afterDV matchDV, ?_⟩
  refine ⟨(finalRow, successor),
    matchOneInSpace_mem afterDV _ read successor successorMem finalRow
      matchSuccessor, ?_⟩
  simp [finalRow, bind, resultRow, dvHeader, successor]

theorem normalAssertionFinishDirective_fires_dv_entry
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackEnd stackBase : Nat) (resultTypecode : String)
    (sourceBody : List Metamath.Verify.Sym) (dvEnd nextTop : Nat) :
    let context := normalAssertionResultContextAtom scopeOwner
      nextProofPosition assertionLabel resultTypecode stackBase nextTop
    let result := fireReflectiveSourceExecFact
      (normalAssertionFinishPhaseSpace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
        resultTypecode sourceBody dvEnd nextTop)
      normalAssertionFinishDirective
    normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel 0
          dvEnd sourceBody context ∈ result ∧
      normalDVReloadAtom proofOwner proofPosition ∈ result := by
  dsimp only
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalAssertionFinishPhaseSpace scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
        resultTypecode sourceBody dvEnd nextTop)
      normalAssertionFinishDirective.atom)
    normalAssertionFinishDirective.rule.input).map Prod.fst
  let substitution := normalAssertionFinishSubstitution scopeOwner proofOwner
    proofPosition nextProofPosition assertionLabel hypothesisEnd stackEnd
    stackBase resultTypecode sourceBody dvEnd nextTop
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalAssertionFinishDirective] using
      normalAssertionFinishMatchRow_mem scopeOwner proofOwner proofPosition
        nextProofPosition assertionLabel hypothesisEnd stackEnd stackBase
        resultTypecode sourceBody dvEnd nextTop
  have nextInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionFinishNextPairTemplate =
        some (normalDVNextPairAtom scopeOwner proofOwner proofPosition
          assertionLabel 0 dvEnd sourceBody
          (normalAssertionResultContextAtom scopeOwner nextProofPosition
            assertionLabel resultTypecode stackBase nextTop)) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionFinishReloadTemplate =
        some (normalDVReloadAtom proofOwner proofPosition) := by
    rfl
  have nextStaged := reflectiveStage_add_contains_of_row rows substitution
    normalAssertionFinishNextPairTemplate
    (normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel 0
      dvEnd sourceBody
      (normalAssertionResultContextAtom scopeOwner nextProofPosition
        assertionLabel resultTypecode stackBase nextTop))
    rowMember nextInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalAssertionFinishReloadTemplate
    (normalDVReloadAtom proofOwner proofPosition) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalAssertionFinishDirective, normalAssertionFinishSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr nextStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalAssertionFinishDirective, normalAssertionFinishSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-- Entering the DV machine is an actual scheduled reflective-MM2 step
inhabiting the exact target native type synthesized by OSLF. -/
theorem normalAssertionFinishPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat) (assertionLabel : String)
    (hypothesisEnd stackEnd stackBase : Nat) (resultTypecode : String)
    (sourceBody : List Metamath.Verify.Sym) (dvEnd nextTop : Nat) :
    let context := normalAssertionResultContextAtom scopeOwner
      nextProofPosition assertionLabel resultTypecode stackBase nextTop
    let source := normalAssertionFinishPhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel hypothesisEnd stackEnd
      stackBase resultTypecode sourceBody dvEnd nextTop
    let target := fireReflectiveSourceExecFact source
      normalAssertionFinishDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel 0
            dvEnd sourceBody context ∈ target ∧
        normalDVReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionFinishPhase_selects_directive scopeOwner proofOwner
          proofPosition nextProofPosition assertionLabel hypothesisEnd
          stackEnd stackBase resultTypecode sourceBody dvEnd nextTop))
  · exact normalAssertionFinishDirective_fires_dv_entry scopeOwner
      proofOwner proofPosition nextProofPosition assertionLabel hypothesisEnd
      stackEnd stackBase resultTypecode sourceBody dvEnd nextTop

/-! ### DV-pair entry boundary -/

def normalDVPairBeginPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
        .var "pc", .var "label", .var "hyp-position",
        .var "hyp-end", .var "source-body", .var "context"],
   .expression
      [.symbol "mm-assertion-dv-pair", .var "scope", .var "label",
        .var "hyp-position", .var "variable-name", .var "hyp-label"],
   .expression
      [.symbol "mm-assertion-dv-successor", .var "scope", .var "label",
        .var "hyp-position", .var "next-hyp-position"],
   .expression
      [.symbol "mm-substitution", .var "proof", .var "pc",
        .var "variable-name", .var "actual-body"],
   .expression
      [.symbol "mm-substitution", .var "proof", .var "pc",
        .var "hyp-label", .var "body"]]

private def normalDVPairBeginCursorTemplate : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
      .var "pc", .var "label", .var "hyp-position",
      .var "hyp-end", .var "source-body", .var "context"]

private def normalDVPairBeginScanTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "actual-body", .var "body",
      .var "source-body", .var "context"]

private def normalDVPairBeginReloadTemplate : Atom :=
  .expression
    [.symbol "mm-reload-dv", .var "proof", .var "pc"]

private def normalDVPairBeginSinks : List Sink :=
  [.remove normalDVPairBeginCursorTemplate,
   .add normalDVPairBeginScanTemplate,
   .add normalDVPairBeginReloadTemplate]

def normalDVPairBeginDirective : SourceExecFact where
  atom := normalDVPairBeginRule
  loc := normalDVPairBeginLocation
  rule :=
    { priority := 14
      name := "mm-normal-dv-pair-begin"
      input := .compat (mkPattern normalDVPairBeginPatternAtoms)
      guards := []
      tmpl := mkTemplate normalDVPairBeginSinks }

theorem extract_normalDVPairBeginRule_exact :
    extractSupportedSourceExecFact normalDVPairBeginRule =
      some normalDVPairBeginDirective := by
  rfl

def normalDVPairBeginPhaseAtoms (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : List Atom :=
  [normalDVPairBeginRule,
   normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel
     pairPosition pairEnd sourceBody context,
   .expression
      [.symbol "mm-assertion-dv-pair", scopeOwner,
        stringAtom assertionLabel, natAtom pairPosition,
        stringAtom leftVariable, stringAtom rightVariable],
   .expression
      [.symbol "mm-assertion-dv-successor", scopeOwner,
        stringAtom assertionLabel, natAtom pairPosition,
        natAtom nextPairPosition],
   normalAssertionSubstitutionAtom proofOwner proofPosition leftVariable
     leftBody,
   normalAssertionSubstitutionAtom proofOwner proofPosition rightVariable
     rightBody]

def normalDVPairBeginPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  (normalDVPairBeginPhaseAtoms scopeOwner proofOwner proofPosition
    assertionLabel pairPosition nextPairPosition pairEnd leftVariable
    rightVariable leftBody rightBody sourceBody context).toFinset

private theorem normalDVPairBeginPhaseAtoms_nodup
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (variablesDistinct : leftVariable ≠ rightVariable) :
    (normalDVPairBeginPhaseAtoms scopeOwner proofOwner proofPosition
      assertionLabel pairPosition nextPairPosition pairEnd leftVariable
      rightVariable leftBody rightBody sourceBody context).Nodup := by
  have encodedDistinct :
      stringAtom leftVariable ≠ stringAtom rightVariable := by
    intro equal
    exact variablesDistinct (stringAtom_injective equal)
  simp [normalDVPairBeginPhaseAtoms, normalDVPairBeginRule,
    normalDVPairBeginLocation, normalDVPairBeginInput,
    normalDVPairBeginOutput, normalDVNextPairAtom,
    normalAssertionSubstitutionAtom, encodedDistinct]

theorem normalDVPairBeginPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (variablesDistinct : leftVariable ≠ rightVariable) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVPairBeginPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel pairPosition nextPairPosition pairEnd leftVariable
            rightVariable leftBody rightBody sourceBody context)) =
      some normalDVPairBeginDirective := by
  let atoms := normalDVPairBeginPhaseAtoms scopeOwner proofOwner
    proofPosition assertionLabel pairPosition nextPairPosition pairEnd
    leftVariable rightVariable leftBody rightBody sourceBody context
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVPairBeginDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVPairBeginDirective
    (normalDVPairBeginPhaseAtoms_nodup scopeOwner proofOwner proofPosition
      assertionLabel pairPosition nextPairPosition pairEnd leftVariable
      rightVariable leftBody rightBody sourceBody context variablesDistinct)
    (by rfl)

private def normalDVPairBeginSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("body", listAtom runtimeSymAtom rightBody),
   ("actual-body", listAtom runtimeSymAtom leftBody),
   ("next-hyp-position", natAtom nextPairPosition),
   ("hyp-label", stringAtom rightVariable),
   ("variable-name", stringAtom leftVariable),
   ("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("hyp-end", natAtom pairEnd),
   ("hyp-position", natAtom pairPosition),
   ("label", stringAtom assertionLabel),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalDVPairBeginMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVPairBeginSubstitution scopeOwner proofOwner proofPosition
        assertionLabel pairPosition nextPairPosition pairEnd leftVariable
        rightVariable leftBody rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVPairBeginPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel pairPosition nextPairPosition pairEnd leftVariable
            rightVariable leftBody rightBody sourceBody context)
          normalDVPairBeginRule)
        normalDVPairBeginDirective.rule.input).map Prod.fst := by
  let cursor := normalDVNextPairAtom scopeOwner proofOwner proofPosition
    assertionLabel pairPosition pairEnd sourceBody context
  let pairRow : Atom :=
    .expression
      [.symbol "mm-assertion-dv-pair", scopeOwner,
        stringAtom assertionLabel, natAtom pairPosition,
        stringAtom leftVariable, stringAtom rightVariable]
  let successor : Atom :=
    .expression
      [.symbol "mm-assertion-dv-successor", scopeOwner,
        stringAtom assertionLabel, natAtom pairPosition,
        natAtom nextPairPosition]
  let leftRow := normalAssertionSubstitutionAtom proofOwner proofPosition
    leftVariable leftBody
  let rightRow := normalAssertionSubstitutionAtom proofOwner proofPosition
    rightVariable rightBody
  let read := readCopyAtom
    (normalDVPairBeginPhaseSpace scopeOwner proofOwner proofPosition
      assertionLabel pairPosition nextPairPosition pairEnd leftVariable
      rightVariable leftBody rightBody sourceBody context)
    normalDVPairBeginRule
  let afterCursor : Subst :=
    [("context", context),
     ("source-body", listAtom runtimeSymAtom sourceBody),
     ("hyp-end", natAtom pairEnd),
     ("hyp-position", natAtom pairPosition),
     ("label", stringAtom assertionLabel),
     ("pc", natAtom proofPosition), ("proof", proofOwner),
     ("scope", scopeOwner)]
  let afterPair : Subst :=
    [("hyp-label", stringAtom rightVariable),
     ("variable-name", stringAtom leftVariable)] ++ afterCursor
  let afterSuccessor : Subst :=
    ("next-hyp-position", natAtom nextPairPosition) :: afterPair
  let afterLeft : Subst :=
    ("actual-body", listAtom runtimeSymAtom leftBody) :: afterSuccessor
  let finalRow := normalDVPairBeginSubstitution scopeOwner proofOwner
    proofPosition assertionLabel pairPosition nextPairPosition pairEnd
    leftVariable rightVariable leftBody rightBody sourceBody context
  have readMember (atom : Atom)
      (member : atom ∈
        normalDVPairBeginPhaseSpace scopeOwner proofOwner proofPosition
          assertionLabel pairPosition nextPairPosition pairEnd leftVariable
          rightVariable leftBody rightBody sourceBody context) : atom ∈ read := by
    by_cases equal : atom = normalDVPairBeginRule
    · subst atom
      simp [read, readCopyAtom]
    · exact Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨equal, member⟩)
  have cursorMem : cursor ∈ read := by
    apply readMember
    simp [cursor, normalDVPairBeginPhaseSpace,
      normalDVPairBeginPhaseAtoms]
  have pairMem : pairRow ∈ read := by
    apply readMember
    simp [pairRow, normalDVPairBeginPhaseSpace,
      normalDVPairBeginPhaseAtoms]
  have successorMem : successor ∈ read := by
    apply readMember
    simp [successor, normalDVPairBeginPhaseSpace,
      normalDVPairBeginPhaseAtoms]
  have leftMem : leftRow ∈ read := by
    apply readMember
    simp [leftRow, normalDVPairBeginPhaseSpace,
      normalDVPairBeginPhaseAtoms]
  have rightMem : rightRow ∈ read := by
    apply readMember
    simp [rightRow, normalDVPairBeginPhaseSpace,
      normalDVPairBeginPhaseAtoms]
  have matchCursor :
      matchAtom [] (normalDVPairBeginPatternAtoms[0]'(by decide)) cursor =
        some afterCursor := by
    simp [normalDVPairBeginPatternAtoms, cursor, normalDVNextPairAtom,
      afterCursor, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchPair :
      matchAtom afterCursor
          (normalDVPairBeginPatternAtoms[1]'(by decide)) pairRow =
        some afterPair := by
    simp [normalDVPairBeginPatternAtoms, pairRow, afterCursor, afterPair,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchSuccessor :
      matchAtom afterPair
          (normalDVPairBeginPatternAtoms[2]'(by decide)) successor =
        some afterSuccessor := by
    simp [normalDVPairBeginPatternAtoms, successor, afterPair,
      afterSuccessor, afterCursor, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchLeft :
      matchAtom afterSuccessor
          (normalDVPairBeginPatternAtoms[3]'(by decide)) leftRow =
        some afterLeft := by
    simp [normalDVPairBeginPatternAtoms, leftRow,
      normalAssertionSubstitutionAtom, afterSuccessor, afterPair,
      afterCursor, afterLeft, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  have matchRight :
      matchAtom afterLeft
          (normalDVPairBeginPatternAtoms[4]'(by decide)) rightRow =
        some finalRow := by
    simp [normalDVPairBeginPatternAtoms, rightRow,
      normalAssertionSubstitutionAtom, afterLeft, afterSuccessor,
      afterPair, afterCursor, finalRow, normalDVPairBeginSubstitution,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(finalRow, {cursor, pairRow, successor, leftRow, rightRow}), ?_, rfl⟩
  simp only [normalDVPairBeginDirective, matchInputSpec,
    normalDVPairBeginPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterCursor, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem afterCursor matchCursor, ?_⟩
  refine ⟨(afterPair, pairRow),
    matchOneInSpace_mem afterCursor _ read pairRow pairMem afterPair
      matchPair, ?_⟩
  refine ⟨(afterSuccessor, successor),
    matchOneInSpace_mem afterPair _ read successor successorMem
      afterSuccessor matchSuccessor, ?_⟩
  refine ⟨(afterLeft, leftRow),
    matchOneInSpace_mem afterSuccessor _ read leftRow leftMem afterLeft
      matchLeft, ?_⟩
  refine ⟨(finalRow, rightRow),
    matchOneInSpace_mem afterLeft _ read rightRow rightMem finalRow
      matchRight, ?_⟩
  simp [finalRow, cursor, pairRow, successor, leftRow, rightRow]

theorem normalDVPairBeginDirective_fires_scan
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let result := fireReflectiveSourceExecFact
      (normalDVPairBeginPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel pairPosition nextPairPosition pairEnd leftVariable
        rightVariable leftBody rightBody sourceBody context)
      normalDVPairBeginDirective
    normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftBody rightBody sourceBody context ∈
        result ∧
      normalDVReloadAtom proofOwner proofPosition ∈ result := by
  dsimp only
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVPairBeginPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel pairPosition nextPairPosition pairEnd leftVariable
        rightVariable leftBody rightBody sourceBody context)
      normalDVPairBeginDirective.atom)
    normalDVPairBeginDirective.rule.input).map Prod.fst
  let substitution := normalDVPairBeginSubstitution scopeOwner proofOwner
    proofPosition assertionLabel pairPosition nextPairPosition pairEnd
    leftVariable rightVariable leftBody rightBody sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVPairBeginDirective] using
      normalDVPairBeginMatchRow_mem scopeOwner proofOwner proofPosition
        assertionLabel pairPosition nextPairPosition pairEnd leftVariable
        rightVariable leftBody rightBody sourceBody context
  have scanInstantiates :
      instantiateTemplateAtom? substitution normalDVPairBeginScanTemplate =
        some (normalDVScanLeftAtom scopeOwner proofOwner proofPosition
          assertionLabel nextPairPosition pairEnd leftBody rightBody
          sourceBody context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVPairBeginReloadTemplate =
        some (normalDVReloadAtom proofOwner proofPosition) := by
    rfl
  have scanStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVPairBeginScanTemplate
    (normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
      nextPairPosition pairEnd leftBody rightBody sourceBody context)
    rowMember scanInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVPairBeginReloadTemplate
    (normalDVReloadAtom proofOwner proofPosition) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVPairBeginDirective, normalDVPairBeginSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr scanStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVPairBeginDirective, normalDVPairBeginSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

/-- Selecting a source-owned callee DV pair enters the exact Cartesian-product
scan state and inhabits the target native type synthesized by OSLF. -/
theorem normalDVPairBeginPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (pairPosition nextPairPosition pairEnd : Nat)
    (leftVariable rightVariable : String)
    (leftBody rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) (variablesDistinct : leftVariable ≠ rightVariable) :
    let source := normalDVPairBeginPhaseSpace scopeOwner proofOwner
      proofPosition assertionLabel pairPosition nextPairPosition pairEnd
      leftVariable rightVariable leftBody rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVPairBeginDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
            nextPairPosition pairEnd leftBody rightBody sourceBody context ∈
          target ∧
        normalDVReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVPairBeginPhase_selects_directive scopeOwner proofOwner
          proofPosition assertionLabel pairPosition nextPairPosition pairEnd
          leftVariable rightVariable leftBody rightBody sourceBody context
          variablesDistinct))
  · exact normalDVPairBeginDirective_fires_scan scopeOwner proofOwner
      proofPosition assertionLabel pairPosition nextPairPosition pairEnd
      leftVariable rightVariable leftBody rightBody sourceBody context

/-! ### DV left-body constant transition -/

def normalDVLeftConstPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
        .var "pc", .var "label", .var "next-hyp-position",
        .var "hyp-end",
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-const", .var "constant-name"],
            .var "source-tail"],
        .var "body", .var "source-body", .var "context"]]

private def normalDVLeftConstCursorTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "source-tail"],
      .var "body", .var "source-body", .var "context"]

private def normalDVLeftConstTailTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "source-tail", .var "body",
      .var "source-body", .var "context"]

private def normalDVLeftConstSinks : List Sink :=
  [.remove normalDVLeftConstCursorTemplate,
   .add normalDVLeftConstTailTemplate,
   .add normalDVPairBeginReloadTemplate]

def normalDVLeftConstDirective : SourceExecFact where
  atom := normalDVLeftConstRule
  loc := normalDVLeftConstLocation
  rule :=
    { priority := 15
      name := "mm-normal-dv-left-const"
      input := .compat (mkPattern normalDVLeftConstPatternAtoms)
      guards := []
      tmpl := mkTemplate normalDVLeftConstSinks }

theorem extract_normalDVLeftConstRule_exact :
    extractSupportedSourceExecFact normalDVLeftConstRule =
      some normalDVLeftConstDirective := by
  rfl

def normalDVLeftConstPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVLeftConstRule,
   normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
     nextPairPosition pairEnd (.const constantName :: leftTail) rightBody
     sourceBody context].toFinset

theorem normalDVLeftConstPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVLeftConstPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd constantName leftTail
            rightBody sourceBody context)) =
      some normalDVLeftConstDirective := by
  let atoms :=
    [normalDVLeftConstRule,
     normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
       nextPairPosition pairEnd (.const constantName :: leftTail) rightBody
       sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVLeftConstDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVLeftConstDirective
    (by simp [atoms, normalDVLeftConstRule, normalDVScanLeftAtom])
    (by rfl)

private def normalDVLeftConstSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("constant-name", stringAtom constantName),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalDVLeftConstMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVLeftConstSubstitution scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd constantName leftTail
        rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVLeftConstPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd constantName leftTail
            rightBody sourceBody context)
          normalDVLeftConstRule)
        normalDVLeftConstDirective.rule.input).map Prod.fst := by
  let cursor := normalDVScanLeftAtom scopeOwner proofOwner proofPosition
    assertionLabel nextPairPosition pairEnd (.const constantName :: leftTail)
    rightBody sourceBody context
  let substitution := normalDVLeftConstSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd constantName
    leftTail rightBody sourceBody context
  let read := readCopyAtom
    (normalDVLeftConstPhaseSpace scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd constantName leftTail rightBody
      sourceBody context)
    normalDVLeftConstRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalDVScanLeftAtom,
      normalDVLeftConstPhaseSpace, normalDVLeftConstRule, runtimeSymAtom,
      listAtom]
  have matchCursor :
      matchAtom [] normalDVLeftConstCursorTemplate cursor =
        some substitution := by
    simp [normalDVLeftConstCursorTemplate, cursor, normalDVScanLeftAtom,
      substitution,
      normalDVLeftConstSubstitution, runtimeSymAtom, listAtom, consTag,
      constTag, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalDVLeftConstDirective, matchInputSpec,
    normalDVLeftConstPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalDVLeftConstDirective_fires_tail
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let result := fireReflectiveSourceExecFact
      (normalDVLeftConstPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd constantName leftTail
        rightBody sourceBody context)
      normalDVLeftConstDirective
    normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
        result ∧
      normalDVReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVLeftConstPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd constantName leftTail
        rightBody sourceBody context)
      normalDVLeftConstDirective.atom)
    normalDVLeftConstDirective.rule.input).map Prod.fst
  let substitution := normalDVLeftConstSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd constantName
    leftTail rightBody sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVLeftConstDirective] using
      normalDVLeftConstMatchRow_mem scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd constantName leftTail
        rightBody sourceBody context
  have tailInstantiates :
      instantiateTemplateAtom? substitution normalDVLeftConstTailTemplate =
        some (normalDVScanLeftAtom scopeOwner proofOwner proofPosition
          assertionLabel nextPairPosition pairEnd leftTail rightBody
          sourceBody context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVPairBeginReloadTemplate =
        some (normalDVReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVLeftConstTailTemplate
    (normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
      nextPairPosition pairEnd leftTail rightBody sourceBody context)
    rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVPairBeginReloadTemplate
    (normalDVReloadAtom proofOwner proofPosition) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVLeftConstDirective, normalDVLeftConstSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVLeftConstDirective, normalDVLeftConstSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalDVLeftConstPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (constantName : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVLeftConstPhaseSpace scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd constantName
      leftTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVLeftConstDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
            nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
          target ∧
        normalDVReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVLeftConstPhase_selects_directive scopeOwner proofOwner
          proofPosition assertionLabel nextPairPosition pairEnd constantName
          leftTail rightBody sourceBody context))
  · exact normalDVLeftConstDirective_fires_tail scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd constantName
      leftTail rightBody sourceBody context

/-! ### DV left-body variable transition -/

def normalDVLeftVariablePatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
        .var "pc", .var "label", .var "next-hyp-position",
        .var "hyp-end",
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-variable", .var "variable-name"],
            .var "source-tail"],
        .var "body", .var "source-body", .var "context"]]

private def normalDVLeftVariableCursorTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", .var "variable-name"],
          .var "source-tail"],
      .var "body", .var "source-body", .var "context"]

private def normalDVLeftVariableRightTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .var "body", .var "body", .var "source-body", .var "context"]

private def normalDVLeftVariableSinks : List Sink :=
  [.remove normalDVLeftVariableCursorTemplate,
   .add normalDVLeftVariableRightTemplate,
   .add normalDVPairBeginReloadTemplate]

def normalDVLeftVariableDirective : SourceExecFact where
  atom := normalDVLeftVariableRule
  loc := normalDVLeftVariableLocation
  rule :=
    { priority := 16
      name := "mm-normal-dv-left-variable"
      input := .compat (mkPattern normalDVLeftVariablePatternAtoms)
      guards := []
      tmpl := mkTemplate normalDVLeftVariableSinks }

theorem extract_normalDVLeftVariableRule_exact :
    extractSupportedSourceExecFact normalDVLeftVariableRule =
      some normalDVLeftVariableDirective := by
  rfl

def normalDVLeftVariablePhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVLeftVariableRule,
   normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
     nextPairPosition pairEnd (.var leftVariable :: leftTail) rightBody
     sourceBody context].toFinset

theorem normalDVLeftVariablePhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVLeftVariablePhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd leftVariable leftTail
            rightBody sourceBody context)) =
      some normalDVLeftVariableDirective := by
  let atoms :=
    [normalDVLeftVariableRule,
     normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
       nextPairPosition pairEnd (.var leftVariable :: leftTail) rightBody
       sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVLeftVariableDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVLeftVariableDirective
    (by simp [atoms, normalDVLeftVariableRule, normalDVScanLeftAtom])
    (by rfl)

private def normalDVLeftVariableSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("variable-name", stringAtom leftVariable),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalDVLeftVariableMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVLeftVariableSubstitution scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVLeftVariablePhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd leftVariable leftTail
            rightBody sourceBody context)
          normalDVLeftVariableRule)
        normalDVLeftVariableDirective.rule.input).map Prod.fst := by
  let cursor := normalDVScanLeftAtom scopeOwner proofOwner proofPosition
    assertionLabel nextPairPosition pairEnd (.var leftVariable :: leftTail)
    rightBody sourceBody context
  let substitution := normalDVLeftVariableSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    leftTail rightBody sourceBody context
  let read := readCopyAtom
    (normalDVLeftVariablePhaseSpace scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd leftVariable leftTail rightBody
      sourceBody context)
    normalDVLeftVariableRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalDVScanLeftAtom,
      normalDVLeftVariablePhaseSpace, normalDVLeftVariableRule,
      runtimeSymAtom, listAtom]
  have matchCursor :
      matchAtom [] normalDVLeftVariableCursorTemplate cursor =
        some substitution := by
    simp [normalDVLeftVariableCursorTemplate, cursor,
      normalDVScanLeftAtom, substitution, normalDVLeftVariableSubstitution,
      runtimeSymAtom, listAtom, consTag, variableTag, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalDVLeftVariableDirective, matchInputSpec,
    normalDVLeftVariablePatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalDVLeftVariableDirective_fires_right_scan
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let result := fireReflectiveSourceExecFact
      (normalDVLeftVariablePhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context)
      normalDVLeftVariableDirective
    normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftVariable leftTail rightBody rightBody
          sourceBody context ∈ result ∧
      normalDVReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVLeftVariablePhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context)
      normalDVLeftVariableDirective.atom)
    normalDVLeftVariableDirective.rule.input).map Prod.fst
  let substitution := normalDVLeftVariableSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    leftTail rightBody sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVLeftVariableDirective] using
      normalDVLeftVariableMatchRow_mem scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context
  have rightInstantiates :
      instantiateTemplateAtom? substitution
          normalDVLeftVariableRightTemplate =
        some (normalDVScanRightAtom scopeOwner proofOwner proofPosition
          assertionLabel nextPairPosition pairEnd leftVariable leftTail
          rightBody rightBody sourceBody context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVPairBeginReloadTemplate =
        some (normalDVReloadAtom proofOwner proofPosition) := by
    rfl
  have rightStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVLeftVariableRightTemplate
    (normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
      nextPairPosition pairEnd leftVariable leftTail rightBody rightBody
      sourceBody context) rowMember rightInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVPairBeginReloadTemplate
    (normalDVReloadAtom proofOwner proofPosition) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVLeftVariableDirective, normalDVLeftVariableSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr rightStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVLeftVariableDirective, normalDVLeftVariableSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalDVLeftVariablePhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVLeftVariablePhaseSpace scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd leftVariable
      leftTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVLeftVariableDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
            nextPairPosition pairEnd leftVariable leftTail rightBody rightBody
            sourceBody context ∈ target ∧
        normalDVReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVLeftVariablePhase_selects_directive scopeOwner proofOwner
          proofPosition assertionLabel nextPairPosition pairEnd leftVariable
          leftTail rightBody sourceBody context))
  · exact normalDVLeftVariableDirective_fires_right_scan scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd leftVariable
      leftTail rightBody sourceBody context

/-! ### DV right-body variable and caller-obligation boundary -/

def normalDVRightVariablePatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
        .var "pc", .var "label", .var "next-hyp-position",
        .var "hyp-end", .var "variable-name", .var "source-tail",
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-variable", .var "hyp-label"],
            .var "actual-tail"],
        .var "body", .var "source-body", .var "context"],
   .expression
      [.symbol "mm-caller-dv", .var "scope",
        .var "variable-name", .var "hyp-label"]]

private def normalDVRightVariableCursorTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", .var "hyp-label"],
          .var "actual-tail"],
      .var "body", .var "source-body", .var "context"]

private def normalDVRightVariableTailTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .var "actual-tail", .var "body", .var "source-body",
      .var "context"]

private def normalDVRightVariableSinks : List Sink :=
  [.remove normalDVRightVariableCursorTemplate,
   .add normalDVRightVariableTailTemplate,
   .add normalDVPairBeginReloadTemplate]

def normalDVRightVariableDirective : SourceExecFact where
  atom := normalDVRightVariableRule
  loc := normalDVRightVariableLocation
  rule :=
    { priority := 18
      name := "mm-normal-dv-right-variable"
      input := .compat (mkPattern normalDVRightVariablePatternAtoms)
      guards := []
      tmpl := mkTemplate normalDVRightVariableSinks }

theorem extract_normalDVRightVariableRule_exact :
    extractSupportedSourceExecFact normalDVRightVariableRule =
      some normalDVRightVariableDirective := by
  rfl

def normalDVRightVariablePhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVRightVariableRule,
   normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
     nextPairPosition pairEnd leftVariable leftTail
     (.var rightVariable :: rightTail) rightBody sourceBody context,
   callerDVRow scopeOwner leftVariable rightVariable].toFinset

theorem normalDVRightVariablePhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVRightVariablePhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd leftVariable rightVariable
            leftTail rightTail rightBody sourceBody context)) =
      some normalDVRightVariableDirective := by
  let atoms :=
    [normalDVRightVariableRule,
     normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
       nextPairPosition pairEnd leftVariable leftTail
       (.var rightVariable :: rightTail) rightBody sourceBody context,
     callerDVRow scopeOwner leftVariable rightVariable]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVRightVariableDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVRightVariableDirective
    (by simp [atoms, normalDVRightVariableRule, normalDVScanRightAtom,
      callerDVRow])
    (by rfl)

private def normalDVRightVariableSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("actual-tail", listAtom runtimeSymAtom rightTail),
   ("hyp-label", stringAtom rightVariable),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("variable-name", stringAtom leftVariable),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalDVRightVariableMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVRightVariableSubstitution scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable rightVariable
        leftTail rightTail rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVRightVariablePhaseSpace scopeOwner proofOwner
            proofPosition assertionLabel nextPairPosition pairEnd
            leftVariable rightVariable leftTail rightTail rightBody
            sourceBody context)
          normalDVRightVariableRule)
        normalDVRightVariableDirective.rule.input).map Prod.fst := by
  let cursor := normalDVScanRightAtom scopeOwner proofOwner proofPosition
    assertionLabel nextPairPosition pairEnd leftVariable leftTail
    (.var rightVariable :: rightTail) rightBody sourceBody context
  let obligation := callerDVRow scopeOwner leftVariable rightVariable
  let substitution := normalDVRightVariableSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    rightVariable leftTail rightTail rightBody sourceBody context
  let read := readCopyAtom
    (normalDVRightVariablePhaseSpace scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd leftVariable rightVariable
      leftTail rightTail rightBody sourceBody context)
    normalDVRightVariableRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalDVScanRightAtom,
      normalDVRightVariablePhaseSpace, normalDVRightVariableRule,
      runtimeSymAtom, listAtom]
  have obligationMem : obligation ∈ read := by
    simp [read, readCopyAtom, consumeAtom, obligation,
      normalDVRightVariablePhaseSpace, normalDVRightVariableRule,
      callerDVRow]
  have matchCursor :
      matchAtom [] normalDVRightVariableCursorTemplate cursor =
        some substitution := by
    simp [normalDVRightVariableCursorTemplate, cursor,
      normalDVScanRightAtom, substitution,
      normalDVRightVariableSubstitution, runtimeSymAtom, listAtom, consTag,
      variableTag, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchObligation :
      matchAtom substitution
          (normalDVRightVariablePatternAtoms[1]'(by decide)) obligation =
        some substitution := by
    simp [normalDVRightVariablePatternAtoms, obligation, callerDVRow,
      substitution, normalDVRightVariableSubstitution, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor, obligation}), ?_, rfl⟩
  simp only [normalDVRightVariableDirective, matchInputSpec,
    normalDVRightVariablePatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  refine ⟨(substitution, obligation),
    matchOneInSpace_mem substitution _ read obligation obligationMem
      substitution matchObligation, ?_⟩
  simp [substitution, cursor, obligation]

theorem normalDVRightVariableDirective_fires_tail
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let result := fireReflectiveSourceExecFact
      (normalDVRightVariablePhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable rightVariable
        leftTail rightTail rightBody sourceBody context)
      normalDVRightVariableDirective
    normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
          sourceBody context ∈ result ∧
      normalDVReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVRightVariablePhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable rightVariable
        leftTail rightTail rightBody sourceBody context)
      normalDVRightVariableDirective.atom)
    normalDVRightVariableDirective.rule.input).map Prod.fst
  let substitution := normalDVRightVariableSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    rightVariable leftTail rightTail rightBody sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVRightVariableDirective] using
      normalDVRightVariableMatchRow_mem scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable rightVariable
        leftTail rightTail rightBody sourceBody context
  have tailInstantiates :
      instantiateTemplateAtom? substitution
          normalDVRightVariableTailTemplate =
        some (normalDVScanRightAtom scopeOwner proofOwner proofPosition
          assertionLabel nextPairPosition pairEnd leftVariable leftTail
          rightTail rightBody sourceBody context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVPairBeginReloadTemplate =
        some (normalDVReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVRightVariableTailTemplate
    (normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
      nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
      sourceBody context) rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVPairBeginReloadTemplate
    (normalDVReloadAtom proofOwner proofPosition) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVRightVariableDirective, normalDVRightVariableSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVRightVariableDirective, normalDVRightVariableSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalDVRightVariablePhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVRightVariablePhaseSpace scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd leftVariable
      rightVariable leftTail rightTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVRightVariableDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
            nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
            sourceBody context ∈ target ∧
        normalDVReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVRightVariablePhase_selects_directive scopeOwner proofOwner
          proofPosition assertionLabel nextPairPosition pairEnd leftVariable
          rightVariable leftTail rightTail rightBody sourceBody context))
  · exact normalDVRightVariableDirective_fires_tail scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd leftVariable
      rightVariable leftTail rightTail rightBody sourceBody context

/-- Without an explicit caller-DV row, the second pattern of the variable
branch has no match.  The generic target machine therefore cannot silently
skip one member of the required Cartesian-product check. -/
theorem normalDVRightVariable_missing_caller_rejects_obligation
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable rightVariable : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let cursor := normalDVScanRightAtom scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd leftVariable leftTail
      (.var rightVariable :: rightTail) rightBody sourceBody context
    let source : Space := [normalDVRightVariableRule, cursor].toFinset
    matchOneInSpace
        (normalDVRightVariableSubstitution scopeOwner proofOwner
          proofPosition assertionLabel nextPairPosition pairEnd leftVariable
          rightVariable leftTail rightTail rightBody sourceBody context)
        (normalDVRightVariablePatternAtoms[1]'(by decide))
        (readCopyAtom source normalDVRightVariableRule) = [] := by
  dsimp only
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨candidateSubstitution, candidateAtom⟩ candidateMember
  have candidateSpec := matchOneInSpace_spec
    (normalDVRightVariableSubstitution scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd leftVariable rightVariable
      leftTail rightTail rightBody sourceBody context)
    (normalDVRightVariablePatternAtoms[1]'(by decide))
    (readCopyAtom
      ([normalDVRightVariableRule,
        normalDVScanRightAtom scopeOwner proofOwner proofPosition
          assertionLabel nextPairPosition pairEnd leftVariable leftTail
          (.var rightVariable :: rightTail) rightBody sourceBody context]
        ).toFinset
      normalDVRightVariableRule)
    candidateSubstitution candidateAtom candidateMember
  rcases candidateSpec with ⟨candidateInRead, candidateMatches⟩
  have candidateCases :
      candidateAtom = normalDVRightVariableRule ∨
        (candidateAtom ≠ normalDVRightVariableRule ∧
          candidateAtom = normalDVScanRightAtom scopeOwner proofOwner
            proofPosition assertionLabel nextPairPosition pairEnd leftVariable
            leftTail (.var rightVariable :: rightTail) rightBody sourceBody
            context) := by
    simpa [readCopyAtom, consumeAtom] using candidateInRead
  rcases candidateCases with ruleCase | ⟨_, cursorCase⟩
  · subst candidateAtom
    simp [normalDVRightVariablePatternAtoms, normalDVRightVariableRule,
      normalDVRightVariableLocation, normalDVRightVariableInput,
      normalDVRightVariableOutput, matchAtom, matchAtom.matchAtomList]
      at candidateMatches
  · subst candidateAtom
    simp [normalDVRightVariablePatternAtoms, normalDVScanRightAtom,
      runtimeSymAtom, listAtom, consTag, variableTag, matchAtom,
      matchAtom.matchAtomList] at candidateMatches

/-! ### DV right-body constant transition -/

def normalDVRightConstPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
        .var "pc", .var "label", .var "next-hyp-position",
        .var "hyp-end", .var "variable-name", .var "source-tail",
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-const", .var "constant-name"],
            .var "actual-tail"],
        .var "body", .var "source-body", .var "context"]]

private def normalDVRightConstCursorTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "actual-tail"],
      .var "body", .var "source-body", .var "context"]

private def normalDVRightConstTailTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .var "actual-tail", .var "body", .var "source-body",
      .var "context"]

private def normalDVRightConstSinks : List Sink :=
  [.remove normalDVRightConstCursorTemplate,
   .add normalDVRightConstTailTemplate,
   .add normalDVPairBeginReloadTemplate]

def normalDVRightConstDirective : SourceExecFact where
  atom := normalDVRightConstRule
  loc := normalDVRightConstLocation
  rule :=
    { priority := 17
      name := "mm-normal-dv-right-const"
      input := .compat (mkPattern normalDVRightConstPatternAtoms)
      guards := []
      tmpl := mkTemplate normalDVRightConstSinks }

theorem extract_normalDVRightConstRule_exact :
    extractSupportedSourceExecFact normalDVRightConstRule =
      some normalDVRightConstDirective := by
  rfl

def normalDVRightConstPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVRightConstRule,
   normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
     nextPairPosition pairEnd leftVariable leftTail
     (.const constantName :: rightTail) rightBody sourceBody context].toFinset

theorem normalDVRightConstPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVRightConstPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd leftVariable constantName
            leftTail rightTail rightBody sourceBody context)) =
      some normalDVRightConstDirective := by
  let atoms :=
    [normalDVRightConstRule,
     normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
       nextPairPosition pairEnd leftVariable leftTail
       (.const constantName :: rightTail) rightBody sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVRightConstDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVRightConstDirective
    (by simp [atoms, normalDVRightConstRule, normalDVScanRightAtom])
    (by rfl)

private def normalDVRightConstSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("actual-tail", listAtom runtimeSymAtom rightTail),
   ("constant-name", stringAtom constantName),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("variable-name", stringAtom leftVariable),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalDVRightConstMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVRightConstSubstitution scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable constantName
        leftTail rightTail rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVRightConstPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd leftVariable constantName
            leftTail rightTail rightBody sourceBody context)
          normalDVRightConstRule)
        normalDVRightConstDirective.rule.input).map Prod.fst := by
  let cursor := normalDVScanRightAtom scopeOwner proofOwner proofPosition
    assertionLabel nextPairPosition pairEnd leftVariable leftTail
    (.const constantName :: rightTail) rightBody sourceBody context
  let substitution := normalDVRightConstSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    constantName leftTail rightTail rightBody sourceBody context
  let read := readCopyAtom
    (normalDVRightConstPhaseSpace scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd leftVariable constantName
      leftTail rightTail rightBody sourceBody context)
    normalDVRightConstRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalDVScanRightAtom,
      normalDVRightConstPhaseSpace, normalDVRightConstRule,
      runtimeSymAtom, listAtom]
  have matchCursor :
      matchAtom [] normalDVRightConstCursorTemplate cursor =
        some substitution := by
    simp [normalDVRightConstCursorTemplate, cursor,
      normalDVScanRightAtom, substitution, normalDVRightConstSubstitution,
      runtimeSymAtom, listAtom, consTag, constTag, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalDVRightConstDirective, matchInputSpec,
    normalDVRightConstPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalDVRightConstDirective_fires_tail
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let result := fireReflectiveSourceExecFact
      (normalDVRightConstPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable constantName
        leftTail rightTail rightBody sourceBody context)
      normalDVRightConstDirective
    normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
          sourceBody context ∈ result ∧
      normalDVReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVRightConstPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable constantName
        leftTail rightTail rightBody sourceBody context)
      normalDVRightConstDirective.atom)
    normalDVRightConstDirective.rule.input).map Prod.fst
  let substitution := normalDVRightConstSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    constantName leftTail rightTail rightBody sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVRightConstDirective] using
      normalDVRightConstMatchRow_mem scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable constantName
        leftTail rightTail rightBody sourceBody context
  have tailInstantiates :
      instantiateTemplateAtom? substitution normalDVRightConstTailTemplate =
        some (normalDVScanRightAtom scopeOwner proofOwner proofPosition
          assertionLabel nextPairPosition pairEnd leftVariable leftTail
          rightTail rightBody sourceBody context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVPairBeginReloadTemplate =
        some (normalDVReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVRightConstTailTemplate
    (normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
      nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
      sourceBody context) rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVPairBeginReloadTemplate
    (normalDVReloadAtom proofOwner proofPosition) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVRightConstDirective, normalDVRightConstSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVRightConstDirective, normalDVRightConstSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalDVRightConstPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable constantName : String)
    (leftTail rightTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVRightConstPhaseSpace scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd leftVariable
      constantName leftTail rightTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVRightConstDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
            nextPairPosition pairEnd leftVariable leftTail rightTail rightBody
            sourceBody context ∈ target ∧
        normalDVReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVRightConstPhase_selects_directive scopeOwner proofOwner
          proofPosition assertionLabel nextPairPosition pairEnd leftVariable
          constantName leftTail rightTail rightBody sourceBody context))
  · exact normalDVRightConstDirective_fires_tail scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd leftVariable
      constantName leftTail rightTail rightBody sourceBody context

/-! ### DV right-body completion transition -/

def normalDVRightNilPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
        .var "pc", .var "label", .var "next-hyp-position",
        .var "hyp-end", .var "variable-name", .var "source-tail",
        .expression [.symbol "mm-nil"], .var "body",
        .var "source-body", .var "context"]]

private def normalDVRightNilCursorTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-right", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "variable-name", .var "source-tail",
      .expression [.symbol "mm-nil"], .var "body",
      .var "source-body", .var "context"]

private def normalDVRightNilLeftTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "source-tail", .var "body",
      .var "source-body", .var "context"]

private def normalDVRightNilSinks : List Sink :=
  [.remove normalDVRightNilCursorTemplate,
   .add normalDVRightNilLeftTemplate,
   .add normalDVPairBeginReloadTemplate]

def normalDVRightNilDirective : SourceExecFact where
  atom := normalDVRightNilRule
  loc := normalDVRightNilLocation
  rule :=
    { priority := 19
      name := "mm-normal-dv-right-nil"
      input := .compat (mkPattern normalDVRightNilPatternAtoms)
      guards := []
      tmpl := mkTemplate normalDVRightNilSinks }

theorem extract_normalDVRightNilRule_exact :
    extractSupportedSourceExecFact normalDVRightNilRule =
      some normalDVRightNilDirective := by
  rfl

def normalDVRightNilPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVRightNilRule,
   normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
     nextPairPosition pairEnd leftVariable leftTail [] rightBody sourceBody
     context].toFinset

theorem normalDVRightNilPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVRightNilPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd leftVariable leftTail
            rightBody sourceBody context)) =
      some normalDVRightNilDirective := by
  let atoms :=
    [normalDVRightNilRule,
     normalDVScanRightAtom scopeOwner proofOwner proofPosition assertionLabel
       nextPairPosition pairEnd leftVariable leftTail [] rightBody sourceBody
       context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVRightNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVRightNilDirective
    (by simp [atoms, normalDVRightNilRule, normalDVScanRightAtom])
    (by rfl)

private def normalDVRightNilSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("source-tail", listAtom runtimeSymAtom leftTail),
   ("variable-name", stringAtom leftVariable),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalDVRightNilMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVRightNilSubstitution scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVRightNilPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd leftVariable leftTail
            rightBody sourceBody context)
          normalDVRightNilRule)
        normalDVRightNilDirective.rule.input).map Prod.fst := by
  let cursor := normalDVScanRightAtom scopeOwner proofOwner proofPosition
    assertionLabel nextPairPosition pairEnd leftVariable leftTail [] rightBody
    sourceBody context
  let substitution := normalDVRightNilSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    leftTail rightBody sourceBody context
  let read := readCopyAtom
    (normalDVRightNilPhaseSpace scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd leftVariable leftTail rightBody
      sourceBody context)
    normalDVRightNilRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalDVScanRightAtom,
      normalDVRightNilPhaseSpace, normalDVRightNilRule, listAtom]
  have matchCursor :
      matchAtom [] normalDVRightNilCursorTemplate cursor =
        some substitution := by
    simp [normalDVRightNilCursorTemplate, cursor, normalDVScanRightAtom,
      substitution, normalDVRightNilSubstitution, listAtom, nilTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalDVRightNilDirective, matchInputSpec,
    normalDVRightNilPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalDVRightNilDirective_fires_left_scan
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let result := fireReflectiveSourceExecFact
      (normalDVRightNilPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context)
      normalDVRightNilDirective
    normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
        result ∧
      normalDVReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVRightNilPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context)
      normalDVRightNilDirective.atom)
    normalDVRightNilDirective.rule.input).map Prod.fst
  let substitution := normalDVRightNilSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd leftVariable
    leftTail rightBody sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVRightNilDirective] using
      normalDVRightNilMatchRow_mem scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd leftVariable leftTail
        rightBody sourceBody context
  have leftInstantiates :
      instantiateTemplateAtom? substitution normalDVRightNilLeftTemplate =
        some (normalDVScanLeftAtom scopeOwner proofOwner proofPosition
          assertionLabel nextPairPosition pairEnd leftTail rightBody
          sourceBody context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVPairBeginReloadTemplate =
        some (normalDVReloadAtom proofOwner proofPosition) := by
    rfl
  have leftStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVRightNilLeftTemplate
    (normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
      nextPairPosition pairEnd leftTail rightBody sourceBody context)
    rowMember leftInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVPairBeginReloadTemplate
    (normalDVReloadAtom proofOwner proofPosition) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVRightNilDirective, normalDVRightNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr leftStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVRightNilDirective, normalDVRightNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalDVRightNilPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat) (leftVariable : String)
    (leftTail rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVRightNilPhaseSpace scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd leftVariable
      leftTail rightBody sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVRightNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
            nextPairPosition pairEnd leftTail rightBody sourceBody context ∈
          target ∧
        normalDVReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVRightNilPhase_selects_directive scopeOwner proofOwner
          proofPosition assertionLabel nextPairPosition pairEnd leftVariable
          leftTail rightBody sourceBody context))
  · exact normalDVRightNilDirective_fires_left_scan scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd leftVariable
      leftTail rightBody sourceBody context

/-! ### DV pair-completion transition -/

def normalDVLeftNilPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
        .var "pc", .var "label", .var "next-hyp-position",
        .var "hyp-end", .expression [.symbol "mm-nil"],
        .var "body", .var "source-body", .var "context"]]

private def normalDVLeftNilCursorTemplate : Atom :=
  .expression
    [.symbol "mm-dv-scan-left", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .expression [.symbol "mm-nil"],
      .var "body", .var "source-body", .var "context"]

private def normalDVLeftNilNextPairTemplate : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
      .var "pc", .var "label", .var "next-hyp-position",
      .var "hyp-end", .var "source-body", .var "context"]

private def normalDVLeftNilSinks : List Sink :=
  [.remove normalDVLeftNilCursorTemplate,
   .add normalDVLeftNilNextPairTemplate,
   .add normalDVPairBeginReloadTemplate]

def normalDVLeftNilDirective : SourceExecFact where
  atom := normalDVLeftNilRule
  loc := normalDVLeftNilLocation
  rule :=
    { priority := 20
      name := "mm-normal-dv-left-nil"
      input := .compat (mkPattern normalDVLeftNilPatternAtoms)
      guards := []
      tmpl := mkTemplate normalDVLeftNilSinks }

theorem extract_normalDVLeftNilRule_exact :
    extractSupportedSourceExecFact normalDVLeftNilRule =
      some normalDVLeftNilDirective := by
  rfl

def normalDVLeftNilPhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Space :=
  [normalDVLeftNilRule,
   normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
     nextPairPosition pairEnd [] rightBody sourceBody context].toFinset

theorem normalDVLeftNilPhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVLeftNilPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd rightBody sourceBody
            context)) =
      some normalDVLeftNilDirective := by
  let atoms :=
    [normalDVLeftNilRule,
     normalDVScanLeftAtom scopeOwner proofOwner proofPosition assertionLabel
       nextPairPosition pairEnd [] rightBody sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVLeftNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVLeftNilDirective
    (by simp [atoms, normalDVLeftNilRule, normalDVScanLeftAtom])
    (by rfl)

private def normalDVLeftNilSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("body", listAtom runtimeSymAtom rightBody),
   ("hyp-end", natAtom pairEnd),
   ("next-hyp-position", natAtom nextPairPosition),
   ("label", stringAtom assertionLabel),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalDVLeftNilMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    normalDVLeftNilSubstitution scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVLeftNilPhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel nextPairPosition pairEnd rightBody sourceBody
            context)
          normalDVLeftNilRule)
        normalDVLeftNilDirective.rule.input).map Prod.fst := by
  let cursor := normalDVScanLeftAtom scopeOwner proofOwner proofPosition
    assertionLabel nextPairPosition pairEnd [] rightBody sourceBody context
  let substitution := normalDVLeftNilSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd rightBody
    sourceBody context
  let read := readCopyAtom
    (normalDVLeftNilPhaseSpace scopeOwner proofOwner proofPosition
      assertionLabel nextPairPosition pairEnd rightBody sourceBody context)
    normalDVLeftNilRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalDVScanLeftAtom,
      normalDVLeftNilPhaseSpace, normalDVLeftNilRule, listAtom]
  have matchCursor :
      matchAtom [] normalDVLeftNilCursorTemplate cursor =
        some substitution := by
    simp [normalDVLeftNilCursorTemplate, cursor, normalDVScanLeftAtom,
      substitution, normalDVLeftNilSubstitution, listAtom, nilTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalDVLeftNilDirective, matchInputSpec,
    normalDVLeftNilPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalDVLeftNilDirective_fires_next_pair
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let result := fireReflectiveSourceExecFact
      (normalDVLeftNilPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context)
      normalDVLeftNilDirective
    normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel
          nextPairPosition pairEnd sourceBody context ∈ result ∧
      normalDVReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVLeftNilPhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context)
      normalDVLeftNilDirective.atom)
    normalDVLeftNilDirective.rule.input).map Prod.fst
  let substitution := normalDVLeftNilSubstitution scopeOwner proofOwner
    proofPosition assertionLabel nextPairPosition pairEnd rightBody
    sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVLeftNilDirective] using
      normalDVLeftNilMatchRow_mem scopeOwner proofOwner proofPosition
        assertionLabel nextPairPosition pairEnd rightBody sourceBody context
  have nextInstantiates :
      instantiateTemplateAtom? substitution normalDVLeftNilNextPairTemplate =
        some (normalDVNextPairAtom scopeOwner proofOwner proofPosition
          assertionLabel nextPairPosition pairEnd sourceBody context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution normalDVPairBeginReloadTemplate =
        some (normalDVReloadAtom proofOwner proofPosition) := by
    rfl
  have nextStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVLeftNilNextPairTemplate
    (normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel
      nextPairPosition pairEnd sourceBody context) rowMember nextInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalDVPairBeginReloadTemplate
    (normalDVReloadAtom proofOwner proofPosition) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVLeftNilDirective, normalDVLeftNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr nextStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalDVLeftNilDirective, normalDVLeftNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalDVLeftNilPhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String)
    (nextPairPosition pairEnd : Nat)
    (rightBody sourceBody : List Metamath.Verify.Sym)
    (context : Atom) :
    let source := normalDVLeftNilPhaseSpace scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd rightBody
      sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVLeftNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel
            nextPairPosition pairEnd sourceBody context ∈ target ∧
        normalDVReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVLeftNilPhase_selects_directive scopeOwner proofOwner
          proofPosition assertionLabel nextPairPosition pairEnd rightBody
          sourceBody context))
  · exact normalDVLeftNilDirective_fires_next_pair scopeOwner proofOwner
      proofPosition assertionLabel nextPairPosition pairEnd rightBody
      sourceBody context

/-! ### Persistent DV-machine reload boundary -/

private def normalDVReloadSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalDVReloadLocation,
      .var "dv-reload-self-input", .var "dv-reload-self-output"]

private def normalDVReloadRequestTemplate : Atom :=
  .expression
    [.symbol "mm-reload-dv", .var "dv-reload-proof",
      .var "dv-reload-pc"]

private def normalDVReloadBundleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-dv-rules",
      .var "dv-rule-pair-begin", .var "dv-rule-left-const",
      .var "dv-rule-left-variable", .var "dv-rule-right-const",
      .var "dv-rule-right-variable", .var "dv-rule-right-nil",
      .var "dv-rule-left-nil", .var "dv-rule-complete"]

private def normalDVReloadPatternAtoms : List Atom :=
  [normalDVReloadSelfTemplate, normalDVReloadRequestTemplate,
   normalDVReloadBundleTemplate]

private def normalDVReloadSinks : List Sink :=
  [.add normalDVReloadSelfTemplate,
   .remove normalDVReloadRequestTemplate,
   .add (.var "dv-rule-pair-begin"),
   .add (.var "dv-rule-left-const"),
   .add (.var "dv-rule-left-variable"),
   .add (.var "dv-rule-right-const"),
   .add (.var "dv-rule-right-variable"),
   .add (.var "dv-rule-right-nil"),
   .add (.var "dv-rule-left-nil"),
   .add (.var "dv-rule-complete")]

def normalDVReloadDirective : SourceExecFact where
  atom := normalDVReloadRule
  loc := normalDVReloadLocation
  rule :=
    { priority := 22
      name := "mm-normal-dv-reload"
      input := .compat (mkPattern normalDVReloadPatternAtoms)
      guards := []
      tmpl := mkTemplate normalDVReloadSinks }

theorem extract_normalDVReloadRule_exact :
    extractSupportedSourceExecFact normalDVReloadRule =
      some normalDVReloadDirective := by
  rfl

def normalDVReloadPhaseSpace (proofOwner : Atom)
    (proofPosition : Nat) : Space :=
  [normalDVReloadRule,
   normalDVReloadAtom proofOwner proofPosition,
   normalDVRuleBundle].toFinset

theorem normalDVReloadPhase_selects_directive
    (proofOwner : Atom) (proofPosition : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVReloadPhaseSpace proofOwner proofPosition)) =
      some normalDVReloadDirective := by
  let atoms :=
    [normalDVReloadRule, normalDVReloadAtom proofOwner proofPosition,
     normalDVRuleBundle]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVReloadDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVReloadDirective
    (by simp [atoms, normalDVReloadRule, normalDVReloadAtom,
      normalDVRuleBundle])
    (by rfl)

private def normalDVReloadSubstitution (proofOwner : Atom)
    (proofPosition : Nat) : Subst :=
  [("dv-rule-complete", normalDVCompleteRule),
   ("dv-rule-left-nil", normalDVLeftNilRule),
   ("dv-rule-right-nil", normalDVRightNilRule),
   ("dv-rule-right-variable", normalDVRightVariableRule),
   ("dv-rule-right-const", normalDVRightConstRule),
   ("dv-rule-left-variable", normalDVLeftVariableRule),
   ("dv-rule-left-const", normalDVLeftConstRule),
   ("dv-rule-pair-begin", normalDVPairBeginRule),
   ("dv-reload-pc", natAtom proofPosition),
   ("dv-reload-proof", proofOwner),
   ("dv-reload-self-output", normalDVReloadOutput),
   ("dv-reload-self-input", normalDVReloadInput)]

private theorem normalDVReloadMatchRow_mem
    (proofOwner : Atom) (proofPosition : Nat) :
    normalDVReloadSubstitution proofOwner proofPosition ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVReloadPhaseSpace proofOwner proofPosition)
          normalDVReloadRule)
        normalDVReloadDirective.rule.input).map Prod.fst := by
  let request := normalDVReloadAtom proofOwner proofPosition
  let read := readCopyAtom
    (normalDVReloadPhaseSpace proofOwner proofPosition)
    normalDVReloadRule
  let afterSelf : Subst :=
    [("dv-reload-self-output", normalDVReloadOutput),
     ("dv-reload-self-input", normalDVReloadInput)]
  let afterRequest : Subst :=
    [("dv-reload-pc", natAtom proofPosition),
     ("dv-reload-proof", proofOwner),
     ("dv-reload-self-output", normalDVReloadOutput),
     ("dv-reload-self-input", normalDVReloadInput)]
  let substitution := normalDVReloadSubstitution proofOwner proofPosition
  have selfMem : normalDVReloadRule ∈ read := by
    simp [read, readCopyAtom, normalDVReloadPhaseSpace]
  have requestMem : request ∈ read := by
    simp [read, readCopyAtom, consumeAtom, request,
      normalDVReloadPhaseSpace, normalDVReloadRule, normalDVReloadAtom]
  have bundleMem : normalDVRuleBundle ∈ read := by
    simp [read, readCopyAtom, consumeAtom,
      normalDVReloadPhaseSpace, normalDVReloadRule, normalDVRuleBundle]
  have matchSelf :
      matchAtom [] normalDVReloadSelfTemplate normalDVReloadRule =
        some afterSelf := by
    simp [normalDVReloadSelfTemplate, normalDVReloadRule,
      normalDVReloadLocation, normalDVReloadInput, normalDVReloadOutput,
      afterSelf,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchRequest :
      matchAtom afterSelf normalDVReloadRequestTemplate request =
        some afterRequest := by
    simp [normalDVReloadRequestTemplate, request, normalDVReloadAtom,
      afterSelf, afterRequest, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchBundle :
      matchAtom afterRequest normalDVReloadBundleTemplate
          normalDVRuleBundle = some substitution := by
    simp [normalDVReloadBundleTemplate, normalDVRuleBundle,
      afterRequest, substitution, normalDVReloadSubstitution, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution,
    {normalDVReloadRule, request, normalDVRuleBundle}), ?_, rfl⟩
  simp only [normalDVReloadDirective, matchInputSpec,
    normalDVReloadPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterSelf, normalDVReloadRule),
    matchOneInSpace_mem [] _ read normalDVReloadRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterRequest, request),
    matchOneInSpace_mem afterSelf _ read request requestMem afterRequest
      matchRequest, ?_⟩
  refine ⟨(substitution, normalDVRuleBundle),
    matchOneInSpace_mem afterRequest _ read normalDVRuleBundle bundleMem
      substitution matchBundle, ?_⟩
  simp [substitution, request]

/-- Reload is itself an ordinary selected MM2 step.  Its exact target is
therefore classified by the native type generated from the reflective-MM2
GSLT through OSLF; it is not an invisible meta-operation. -/
theorem normalDVReloadPhase_inhabits_target_native_type
    (proofOwner : Atom) (proofPosition : Nat) :
    let source := normalDVReloadPhaseSpace proofOwner proofPosition
    let target := fireReflectiveSourceExecFact source
      normalDVReloadDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred := by
  dsimp only
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected
      (normalDVReloadPhase_selects_directive proofOwner proofPosition))

/-! ### DV completion and result-body entry boundary -/

/-- Result-body construction cursor, with the accumulated body stored in
reverse order until the final reversal phase. -/
def normalBodyBuildAtom (proofOwner : Atom) (proofPosition : Nat)
    (sourceBody reversedBody : List Metamath.Verify.Sym)
    (context : Atom) : Atom :=
  .expression
    [.symbol "mm-body-build", proofOwner, natAtom proofPosition,
      listAtom runtimeSymAtom sourceBody,
      listAtom runtimeSymAtom reversedBody, context]

/-- Cursor that copies one variable's substitution body into the reversed
result accumulator. -/
def normalBodyBuildPrefixAtom (proofOwner : Atom) (proofPosition : Nat)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym)
    (context : Atom) : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", proofOwner, natAtom proofPosition,
      listAtom runtimeSymAtom replacementBody,
      listAtom runtimeSymAtom sourceTail,
      listAtom runtimeSymAtom reversedBody, context]

/-- Cursor that reverses the completed accumulator into source order. -/
def normalBodyReverseAtom (proofOwner : Atom) (proofPosition : Nat)
    (reversedTail resultBody : List Metamath.Verify.Sym)
    (context : Atom) : Atom :=
  .expression
    [.symbol "mm-body-reverse", proofOwner, natAtom proofPosition,
      listAtom runtimeSymAtom reversedTail,
      listAtom runtimeSymAtom resultBody, context]

/-- Completed substituted assertion body. -/
def normalBodyBuiltAtom (proofOwner : Atom) (proofPosition : Nat)
    (context : Atom) (resultBody : List Metamath.Verify.Sym) : Atom :=
  .expression
    [.symbol "mm-body-built", proofOwner, natAtom proofPosition,
      context, listAtom runtimeSymAtom resultBody]

/-- Explicit request to reinstall the finite body-construction machine. -/
def normalBodyBuildReloadAtom (proofOwner : Atom)
    (proofPosition : Nat) : Atom :=
  .expression
    [.symbol "mm-reload-body-build", proofOwner, natAtom proofPosition]

/-! ### Result-body constant transition -/

private def normalBodyBuildConstPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-build", .var "proof", .var "pc",
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-const", .var "constant-name"],
            .var "source-tail"],
        .var "reversed-body", .var "context"]]

private def normalBodyBuildConstCursorTemplate : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "source-tail"],
      .var "reversed-body", .var "context"]

private def normalBodyBuildConstTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .var "source-tail",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-const", .var "constant-name"],
          .var "reversed-body"],
      .var "context"]

private def normalBodyBuildReloadRequestTemplate : Atom :=
  .expression
    [.symbol "mm-reload-body-build", .var "proof", .var "pc"]

private def normalBodyBuildConstSinks : List Sink :=
  [.remove normalBodyBuildConstCursorTemplate,
   .add normalBodyBuildConstTailTemplate,
   .add normalBodyBuildReloadRequestTemplate]

def normalBodyBuildConstDirective : SourceExecFact where
  atom := normalBodyBuildConstRule
  loc := normalBodyBuildConstLocation
  rule :=
    { priority := 23
      name := "mm-normal-body-build-const"
      input := .compat (mkPattern normalBodyBuildConstPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyBuildConstSinks }

theorem extract_normalBodyBuildConstRule_exact :
    extractSupportedSourceExecFact normalBodyBuildConstRule =
      some normalBodyBuildConstDirective := by
  rfl

def normalBodyBuildConstPhaseSpace (proofOwner context : Atom)
    (proofPosition : Nat) (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyBuildConstRule,
   normalBodyBuildAtom proofOwner proofPosition
     (.const constantName :: sourceTail) reversedBody context].toFinset

theorem normalBodyBuildConstPhase_selects_directive
    (proofOwner context : Atom) (proofPosition : Nat)
    (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildConstPhaseSpace proofOwner context proofPosition
            constantName sourceTail reversedBody)) =
      some normalBodyBuildConstDirective := by
  let atoms :=
    [normalBodyBuildConstRule,
     normalBodyBuildAtom proofOwner proofPosition
       (.const constantName :: sourceTail) reversedBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildConstDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildConstDirective
    (by simp [atoms, normalBodyBuildConstRule, normalBodyBuildAtom])
    (by rfl)

private def normalBodyBuildConstSubstitution (proofOwner context : Atom)
    (proofPosition : Nat) (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("constant-name", stringAtom constantName),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyBuildConstMatchRow_mem
    (proofOwner context : Atom) (proofPosition : Nat)
    (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildConstSubstitution proofOwner context proofPosition
        constantName sourceTail reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildConstPhaseSpace proofOwner context proofPosition
            constantName sourceTail reversedBody)
          normalBodyBuildConstRule)
        normalBodyBuildConstDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildAtom proofOwner proofPosition
    (.const constantName :: sourceTail) reversedBody context
  let substitution := normalBodyBuildConstSubstitution proofOwner context
    proofPosition constantName sourceTail reversedBody
  let read := readCopyAtom
    (normalBodyBuildConstPhaseSpace proofOwner context proofPosition
      constantName sourceTail reversedBody)
    normalBodyBuildConstRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalBodyBuildAtom,
      normalBodyBuildConstPhaseSpace, normalBodyBuildConstRule,
      runtimeSymAtom, listAtom]
  have matchCursor :
      matchAtom [] normalBodyBuildConstCursorTemplate cursor =
        some substitution := by
    simp [normalBodyBuildConstCursorTemplate, cursor, normalBodyBuildAtom,
      substitution, normalBodyBuildConstSubstitution, runtimeSymAtom,
      listAtom, consTag, constTag, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalBodyBuildConstDirective, matchInputSpec,
    normalBodyBuildConstPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalBodyBuildConstDirective_fires_tail
    (proofOwner context : Atom) (proofPosition : Nat)
    (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyBuildConstPhaseSpace proofOwner context proofPosition
        constantName sourceTail reversedBody)
      normalBodyBuildConstDirective
    normalBodyBuildAtom proofOwner proofPosition sourceTail
          (.const constantName :: reversedBody) context ∈ result ∧
      normalBodyBuildReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyBuildConstPhaseSpace proofOwner context proofPosition
        constantName sourceTail reversedBody)
      normalBodyBuildConstDirective.atom)
    normalBodyBuildConstDirective.rule.input).map Prod.fst
  let substitution := normalBodyBuildConstSubstitution proofOwner context
    proofPosition constantName sourceTail reversedBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyBuildConstDirective] using
      normalBodyBuildConstMatchRow_mem proofOwner context proofPosition
        constantName sourceTail reversedBody
  have tailInstantiates :
      instantiateTemplateAtom? substitution normalBodyBuildConstTailTemplate =
        some (normalBodyBuildAtom proofOwner proofPosition sourceTail
          (.const constantName :: reversedBody) context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildReloadRequestTemplate =
        some (normalBodyBuildReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildConstTailTemplate
    (normalBodyBuildAtom proofOwner proofPosition sourceTail
      (.const constantName :: reversedBody) context)
    rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildReloadRequestTemplate
    (normalBodyBuildReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildConstDirective, normalBodyBuildConstSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildConstDirective, normalBodyBuildConstSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalBodyBuildConstPhase_inhabits_target_native_type
    (proofOwner context : Atom) (proofPosition : Nat)
    (constantName : String)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildConstPhaseSpace proofOwner context
      proofPosition constantName sourceTail reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildConstDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildAtom proofOwner proofPosition sourceTail
            (.const constantName :: reversedBody) context ∈ target ∧
        normalBodyBuildReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildConstPhase_selects_directive proofOwner context
          proofPosition constantName sourceTail reversedBody))
  · exact normalBodyBuildConstDirective_fires_tail proofOwner context
      proofPosition constantName sourceTail reversedBody

/-! ### Result-body variable transition -/

private def normalBodyBuildVariablePatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-build", .var "proof", .var "pc",
        .expression
          [.symbol "mm-cons",
            .expression [.symbol "mm-variable", .var "variable-name"],
            .var "source-tail"],
        .var "reversed-body", .var "context"],
   .expression
      [.symbol "mm-substitution", .var "proof", .var "pc",
        .var "variable-name", .var "replacement-body"]]

private def normalBodyBuildVariableCursorTemplate : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons",
          .expression [.symbol "mm-variable", .var "variable-name"],
          .var "source-tail"],
      .var "reversed-body", .var "context"]

private def normalBodyBuildVariablePrefixTemplate : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
      .var "replacement-body", .var "source-tail",
      .var "reversed-body", .var "context"]

private def normalBodyBuildVariableSinks : List Sink :=
  [.remove normalBodyBuildVariableCursorTemplate,
   .add normalBodyBuildVariablePrefixTemplate,
   .add normalBodyBuildReloadRequestTemplate]

def normalBodyBuildVariableDirective : SourceExecFact where
  atom := normalBodyBuildVariableRule
  loc := normalBodyBuildVariableLocation
  rule :=
    { priority := 24
      name := "mm-normal-body-build-variable"
      input := .compat (mkPattern normalBodyBuildVariablePatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyBuildVariableSinks }

theorem extract_normalBodyBuildVariableRule_exact :
    extractSupportedSourceExecFact normalBodyBuildVariableRule =
      some normalBodyBuildVariableDirective := by
  rfl

def normalBodyBuildVariablePhaseSpace (proofOwner context : Atom)
    (proofPosition : Nat) (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    Space :=
  [normalBodyBuildVariableRule,
   normalBodyBuildAtom proofOwner proofPosition
     (.var variableName :: sourceTail) reversedBody context,
   normalAssertionSubstitutionAtom proofOwner proofPosition variableName
     replacementBody].toFinset

theorem normalBodyBuildVariablePhase_selects_directive
    (proofOwner context : Atom) (proofPosition : Nat)
    (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildVariablePhaseSpace proofOwner context proofPosition
            variableName replacementBody sourceTail reversedBody)) =
      some normalBodyBuildVariableDirective := by
  let atoms :=
    [normalBodyBuildVariableRule,
     normalBodyBuildAtom proofOwner proofPosition
       (.var variableName :: sourceTail) reversedBody context,
     normalAssertionSubstitutionAtom proofOwner proofPosition variableName
       replacementBody]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildVariableDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildVariableDirective
    (by simp [atoms, normalBodyBuildVariableRule, normalBodyBuildAtom,
      normalAssertionSubstitutionAtom])
    (by rfl)

private def normalBodyBuildVariableSubstitution (proofOwner context : Atom)
    (proofPosition : Nat) (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    Subst :=
  [("replacement-body", listAtom runtimeSymAtom replacementBody),
   ("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("variable-name", stringAtom variableName),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyBuildVariableMatchRow_mem
    (proofOwner context : Atom) (proofPosition : Nat)
    (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildVariableSubstitution proofOwner context proofPosition
        variableName replacementBody sourceTail reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildVariablePhaseSpace proofOwner context proofPosition
            variableName replacementBody sourceTail reversedBody)
          normalBodyBuildVariableRule)
        normalBodyBuildVariableDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildAtom proofOwner proofPosition
    (.var variableName :: sourceTail) reversedBody context
  let substitutionRow := normalAssertionSubstitutionAtom proofOwner
    proofPosition variableName replacementBody
  let read := readCopyAtom
    (normalBodyBuildVariablePhaseSpace proofOwner context proofPosition
      variableName replacementBody sourceTail reversedBody)
    normalBodyBuildVariableRule
  let afterCursor : Subst :=
    [("context", context),
     ("reversed-body", listAtom runtimeSymAtom reversedBody),
     ("source-tail", listAtom runtimeSymAtom sourceTail),
     ("variable-name", stringAtom variableName),
     ("pc", natAtom proofPosition), ("proof", proofOwner)]
  let substitution := normalBodyBuildVariableSubstitution proofOwner context
    proofPosition variableName replacementBody sourceTail reversedBody
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalBodyBuildAtom,
      normalBodyBuildVariablePhaseSpace, normalBodyBuildVariableRule,
      runtimeSymAtom, listAtom]
  have substitutionMem : substitutionRow ∈ read := by
    simp [read, readCopyAtom, consumeAtom, substitutionRow,
      normalBodyBuildVariablePhaseSpace, normalBodyBuildVariableRule,
      normalAssertionSubstitutionAtom]
  have matchCursor :
      matchAtom [] normalBodyBuildVariableCursorTemplate cursor =
        some afterCursor := by
    simp [normalBodyBuildVariableCursorTemplate, cursor,
      normalBodyBuildAtom, afterCursor, runtimeSymAtom, listAtom, consTag,
      variableTag, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchSubstitution :
      matchAtom afterCursor
          (normalBodyBuildVariablePatternAtoms[1]'(by decide))
          substitutionRow = some substitution := by
    simp [normalBodyBuildVariablePatternAtoms, substitutionRow,
      normalAssertionSubstitutionAtom, afterCursor, substitution,
      normalBodyBuildVariableSubstitution, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor, substitutionRow}), ?_, rfl⟩
  simp only [normalBodyBuildVariableDirective, matchInputSpec,
    normalBodyBuildVariablePatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterCursor, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem afterCursor
      matchCursor, ?_⟩
  refine ⟨(substitution, substitutionRow),
    matchOneInSpace_mem afterCursor _ read substitutionRow substitutionMem
      substitution matchSubstitution, ?_⟩
  simp [substitution, cursor, substitutionRow]

theorem normalBodyBuildVariableDirective_fires_prefix
    (proofOwner context : Atom) (proofPosition : Nat)
    (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyBuildVariablePhaseSpace proofOwner context proofPosition
        variableName replacementBody sourceTail reversedBody)
      normalBodyBuildVariableDirective
    normalBodyBuildPrefixAtom proofOwner proofPosition replacementBody
          sourceTail reversedBody context ∈ result ∧
      normalBodyBuildReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyBuildVariablePhaseSpace proofOwner context proofPosition
        variableName replacementBody sourceTail reversedBody)
      normalBodyBuildVariableDirective.atom)
    normalBodyBuildVariableDirective.rule.input).map Prod.fst
  let substitution := normalBodyBuildVariableSubstitution proofOwner context
    proofPosition variableName replacementBody sourceTail reversedBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyBuildVariableDirective] using
      normalBodyBuildVariableMatchRow_mem proofOwner context proofPosition
        variableName replacementBody sourceTail reversedBody
  have prefixInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildVariablePrefixTemplate =
        some (normalBodyBuildPrefixAtom proofOwner proofPosition
          replacementBody sourceTail reversedBody context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildReloadRequestTemplate =
        some (normalBodyBuildReloadAtom proofOwner proofPosition) := by
    rfl
  have prefixStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildVariablePrefixTemplate
    (normalBodyBuildPrefixAtom proofOwner proofPosition replacementBody
      sourceTail reversedBody context) rowMember prefixInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildReloadRequestTemplate
    (normalBodyBuildReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildVariableDirective, normalBodyBuildVariableSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr prefixStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildVariableDirective, normalBodyBuildVariableSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalBodyBuildVariablePhase_inhabits_target_native_type
    (proofOwner context : Atom) (proofPosition : Nat)
    (variableName : String)
    (replacementBody sourceTail reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildVariablePhaseSpace proofOwner context
      proofPosition variableName replacementBody sourceTail reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildVariableDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildPrefixAtom proofOwner proofPosition replacementBody
            sourceTail reversedBody context ∈ target ∧
        normalBodyBuildReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildVariablePhase_selects_directive proofOwner context
          proofPosition variableName replacementBody sourceTail
          reversedBody))
  · exact normalBodyBuildVariableDirective_fires_prefix proofOwner context
      proofPosition variableName replacementBody sourceTail reversedBody

/-! ### Result-body substitution-prefix transitions -/

private def normalBodyBuildPrefixNilPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
        .expression [.symbol "mm-nil"], .var "source-tail",
        .var "reversed-body", .var "context"]]

private def normalBodyBuildPrefixNilCursorTemplate : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .var "source-tail",
      .var "reversed-body", .var "context"]

private def normalBodyBuildPrefixNilTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .var "source-tail", .var "reversed-body", .var "context"]

private def normalBodyBuildPrefixNilSinks : List Sink :=
  [.remove normalBodyBuildPrefixNilCursorTemplate,
   .add normalBodyBuildPrefixNilTailTemplate,
   .add normalBodyBuildReloadRequestTemplate]

def normalBodyBuildPrefixNilDirective : SourceExecFact where
  atom := normalBodyBuildPrefixNilRule
  loc := normalBodyBuildPrefixNilLocation
  rule :=
    { priority := 25
      name := "mm-normal-body-build-prefix-nil"
      input := .compat (mkPattern normalBodyBuildPrefixNilPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyBuildPrefixNilSinks }

theorem extract_normalBodyBuildPrefixNilRule_exact :
    extractSupportedSourceExecFact normalBodyBuildPrefixNilRule =
      some normalBodyBuildPrefixNilDirective := by
  rfl

def normalBodyBuildPrefixNilPhaseSpace (proofOwner context : Atom)
    (proofPosition : Nat)
    (sourceTail reversedBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyBuildPrefixNilRule,
   normalBodyBuildPrefixAtom proofOwner proofPosition [] sourceTail
     reversedBody context].toFinset

theorem normalBodyBuildPrefixNilPhase_selects_directive
    (proofOwner context : Atom) (proofPosition : Nat)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildPrefixNilPhaseSpace proofOwner context
            proofPosition sourceTail reversedBody)) =
      some normalBodyBuildPrefixNilDirective := by
  let atoms :=
    [normalBodyBuildPrefixNilRule,
     normalBodyBuildPrefixAtom proofOwner proofPosition [] sourceTail
       reversedBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildPrefixNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildPrefixNilDirective
    (by simp [atoms, normalBodyBuildPrefixNilRule,
      normalBodyBuildPrefixAtom])
    (by rfl)

private def normalBodyBuildPrefixNilSubstitution (proofOwner context : Atom)
    (proofPosition : Nat)
    (sourceTail reversedBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyBuildPrefixNilMatchRow_mem
    (proofOwner context : Atom) (proofPosition : Nat)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildPrefixNilSubstitution proofOwner context proofPosition
        sourceTail reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildPrefixNilPhaseSpace proofOwner context
            proofPosition sourceTail reversedBody)
          normalBodyBuildPrefixNilRule)
        normalBodyBuildPrefixNilDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildPrefixAtom proofOwner proofPosition []
    sourceTail reversedBody context
  let substitution := normalBodyBuildPrefixNilSubstitution proofOwner context
    proofPosition sourceTail reversedBody
  let read := readCopyAtom
    (normalBodyBuildPrefixNilPhaseSpace proofOwner context proofPosition
      sourceTail reversedBody)
    normalBodyBuildPrefixNilRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor,
      normalBodyBuildPrefixAtom, normalBodyBuildPrefixNilPhaseSpace,
      normalBodyBuildPrefixNilRule, listAtom]
  have matchCursor :
      matchAtom [] normalBodyBuildPrefixNilCursorTemplate cursor =
        some substitution := by
    simp [normalBodyBuildPrefixNilCursorTemplate, cursor,
      normalBodyBuildPrefixAtom, substitution,
      normalBodyBuildPrefixNilSubstitution, listAtom, nilTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalBodyBuildPrefixNilDirective, matchInputSpec,
    normalBodyBuildPrefixNilPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalBodyBuildPrefixNilDirective_fires_tail
    (proofOwner context : Atom) (proofPosition : Nat)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyBuildPrefixNilPhaseSpace proofOwner context proofPosition
        sourceTail reversedBody)
      normalBodyBuildPrefixNilDirective
    normalBodyBuildAtom proofOwner proofPosition sourceTail reversedBody
          context ∈ result ∧
      normalBodyBuildReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyBuildPrefixNilPhaseSpace proofOwner context proofPosition
        sourceTail reversedBody)
      normalBodyBuildPrefixNilDirective.atom)
    normalBodyBuildPrefixNilDirective.rule.input).map Prod.fst
  let substitution := normalBodyBuildPrefixNilSubstitution proofOwner context
    proofPosition sourceTail reversedBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyBuildPrefixNilDirective] using
      normalBodyBuildPrefixNilMatchRow_mem proofOwner context proofPosition
        sourceTail reversedBody
  have tailInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildPrefixNilTailTemplate =
        some (normalBodyBuildAtom proofOwner proofPosition sourceTail
          reversedBody context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildReloadRequestTemplate =
        some (normalBodyBuildReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildPrefixNilTailTemplate
    (normalBodyBuildAtom proofOwner proofPosition sourceTail reversedBody
      context) rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildReloadRequestTemplate
    (normalBodyBuildReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildPrefixNilDirective, normalBodyBuildPrefixNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildPrefixNilDirective, normalBodyBuildPrefixNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalBodyBuildPrefixNilPhase_inhabits_target_native_type
    (proofOwner context : Atom) (proofPosition : Nat)
    (sourceTail reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildPrefixNilPhaseSpace proofOwner context
      proofPosition sourceTail reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildPrefixNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildAtom proofOwner proofPosition sourceTail reversedBody
            context ∈ target ∧
        normalBodyBuildReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildPrefixNilPhase_selects_directive proofOwner context
          proofPosition sourceTail reversedBody))
  · exact normalBodyBuildPrefixNilDirective_fires_tail proofOwner context
      proofPosition sourceTail reversedBody

private def normalBodyBuildPrefixConsPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
        .expression
          [.symbol "mm-cons", .var "replacement-symbol",
            .var "replacement-tail"],
        .var "source-tail", .var "reversed-body", .var "context"]]

private def normalBodyBuildPrefixConsCursorTemplate : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons", .var "replacement-symbol",
          .var "replacement-tail"],
      .var "source-tail", .var "reversed-body", .var "context"]

private def normalBodyBuildPrefixConsTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-build-prefix", .var "proof", .var "pc",
      .var "replacement-tail", .var "source-tail",
      .expression
        [.symbol "mm-cons", .var "replacement-symbol",
          .var "reversed-body"],
      .var "context"]

private def normalBodyBuildPrefixConsSinks : List Sink :=
  [.remove normalBodyBuildPrefixConsCursorTemplate,
   .add normalBodyBuildPrefixConsTailTemplate,
   .add normalBodyBuildReloadRequestTemplate]

def normalBodyBuildPrefixConsDirective : SourceExecFact where
  atom := normalBodyBuildPrefixConsRule
  loc := normalBodyBuildPrefixConsLocation
  rule :=
    { priority := 26
      name := "mm-normal-body-build-prefix-cons"
      input := .compat (mkPattern normalBodyBuildPrefixConsPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyBuildPrefixConsSinks }

theorem extract_normalBodyBuildPrefixConsRule_exact :
    extractSupportedSourceExecFact normalBodyBuildPrefixConsRule =
      some normalBodyBuildPrefixConsDirective := by
  rfl

def normalBodyBuildPrefixConsPhaseSpace (proofOwner context : Atom)
    (proofPosition : Nat) (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    Space :=
  [normalBodyBuildPrefixConsRule,
   normalBodyBuildPrefixAtom proofOwner proofPosition
     (replacementSymbol :: replacementTail) sourceTail reversedBody
     context].toFinset

theorem normalBodyBuildPrefixConsPhase_selects_directive
    (proofOwner context : Atom) (proofPosition : Nat)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildPrefixConsPhaseSpace proofOwner context
            proofPosition replacementSymbol replacementTail sourceTail
            reversedBody)) =
      some normalBodyBuildPrefixConsDirective := by
  let atoms :=
    [normalBodyBuildPrefixConsRule,
     normalBodyBuildPrefixAtom proofOwner proofPosition
       (replacementSymbol :: replacementTail) sourceTail reversedBody
       context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildPrefixConsDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildPrefixConsDirective
    (by simp [atoms, normalBodyBuildPrefixConsRule,
      normalBodyBuildPrefixAtom])
    (by rfl)

private def normalBodyBuildPrefixConsSubstitution (proofOwner context : Atom)
    (proofPosition : Nat) (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    Subst :=
  [("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("source-tail", listAtom runtimeSymAtom sourceTail),
   ("replacement-tail", listAtom runtimeSymAtom replacementTail),
   ("replacement-symbol", runtimeSymAtom replacementSymbol),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyBuildPrefixConsMatchRow_mem
    (proofOwner context : Atom) (proofPosition : Nat)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildPrefixConsSubstitution proofOwner context proofPosition
        replacementSymbol replacementTail sourceTail reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildPrefixConsPhaseSpace proofOwner context
            proofPosition replacementSymbol replacementTail sourceTail
            reversedBody)
          normalBodyBuildPrefixConsRule)
        normalBodyBuildPrefixConsDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildPrefixAtom proofOwner proofPosition
    (replacementSymbol :: replacementTail) sourceTail reversedBody context
  let substitution := normalBodyBuildPrefixConsSubstitution proofOwner
    context proofPosition replacementSymbol replacementTail sourceTail
    reversedBody
  let read := readCopyAtom
    (normalBodyBuildPrefixConsPhaseSpace proofOwner context proofPosition
      replacementSymbol replacementTail sourceTail reversedBody)
    normalBodyBuildPrefixConsRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor,
      normalBodyBuildPrefixAtom, normalBodyBuildPrefixConsPhaseSpace,
      normalBodyBuildPrefixConsRule, listAtom]
  have matchCursor :
      matchAtom [] normalBodyBuildPrefixConsCursorTemplate cursor =
        some substitution := by
    simp [normalBodyBuildPrefixConsCursorTemplate, cursor,
      normalBodyBuildPrefixAtom, substitution,
      normalBodyBuildPrefixConsSubstitution, listAtom, consTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalBodyBuildPrefixConsDirective, matchInputSpec,
    normalBodyBuildPrefixConsPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalBodyBuildPrefixConsDirective_fires_tail
    (proofOwner context : Atom) (proofPosition : Nat)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyBuildPrefixConsPhaseSpace proofOwner context proofPosition
        replacementSymbol replacementTail sourceTail reversedBody)
      normalBodyBuildPrefixConsDirective
    normalBodyBuildPrefixAtom proofOwner proofPosition replacementTail
          sourceTail (replacementSymbol :: reversedBody) context ∈ result ∧
      normalBodyBuildReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyBuildPrefixConsPhaseSpace proofOwner context proofPosition
        replacementSymbol replacementTail sourceTail reversedBody)
      normalBodyBuildPrefixConsDirective.atom)
    normalBodyBuildPrefixConsDirective.rule.input).map Prod.fst
  let substitution := normalBodyBuildPrefixConsSubstitution proofOwner
    context proofPosition replacementSymbol replacementTail sourceTail
    reversedBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyBuildPrefixConsDirective] using
      normalBodyBuildPrefixConsMatchRow_mem proofOwner context proofPosition
        replacementSymbol replacementTail sourceTail reversedBody
  have tailInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildPrefixConsTailTemplate =
        some (normalBodyBuildPrefixAtom proofOwner proofPosition
          replacementTail sourceTail (replacementSymbol :: reversedBody)
          context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildReloadRequestTemplate =
        some (normalBodyBuildReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildPrefixConsTailTemplate
    (normalBodyBuildPrefixAtom proofOwner proofPosition replacementTail
      sourceTail (replacementSymbol :: reversedBody) context)
    rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildReloadRequestTemplate
    (normalBodyBuildReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildPrefixConsDirective, normalBodyBuildPrefixConsSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildPrefixConsDirective, normalBodyBuildPrefixConsSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalBodyBuildPrefixConsPhase_inhabits_target_native_type
    (proofOwner context : Atom) (proofPosition : Nat)
    (replacementSymbol : Metamath.Verify.Sym)
    (replacementTail sourceTail reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildPrefixConsPhaseSpace proofOwner context
      proofPosition replacementSymbol replacementTail sourceTail reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildPrefixConsDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildPrefixAtom proofOwner proofPosition replacementTail
            sourceTail (replacementSymbol :: reversedBody) context ∈ target ∧
        normalBodyBuildReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildPrefixConsPhase_selects_directive proofOwner context
          proofPosition replacementSymbol replacementTail sourceTail
          reversedBody))
  · exact normalBodyBuildPrefixConsDirective_fires_tail proofOwner context
      proofPosition replacementSymbol replacementTail sourceTail reversedBody

/-! ### Result-body source exhaustion transition -/

private def normalBodyBuildNilPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-build", .var "proof", .var "pc",
        .expression [.symbol "mm-nil"], .var "reversed-body",
        .var "context"]]

private def normalBodyBuildNilCursorTemplate : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .var "reversed-body",
      .var "context"]

private def normalBodyBuildNilReverseTemplate : Atom :=
  .expression
    [.symbol "mm-body-reverse", .var "proof", .var "pc",
      .var "reversed-body", .expression [.symbol "mm-nil"],
      .var "context"]

private def normalBodyBuildNilSinks : List Sink :=
  [.remove normalBodyBuildNilCursorTemplate,
   .add normalBodyBuildNilReverseTemplate,
   .add normalBodyBuildReloadRequestTemplate]

def normalBodyBuildNilDirective : SourceExecFact where
  atom := normalBodyBuildNilRule
  loc := normalBodyBuildNilLocation
  rule :=
    { priority := 27
      name := "mm-normal-body-build-nil"
      input := .compat (mkPattern normalBodyBuildNilPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyBuildNilSinks }

theorem extract_normalBodyBuildNilRule_exact :
    extractSupportedSourceExecFact normalBodyBuildNilRule =
      some normalBodyBuildNilDirective := by
  rfl

def normalBodyBuildNilPhaseSpace (proofOwner context : Atom)
    (proofPosition : Nat)
    (reversedBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyBuildNilRule,
   normalBodyBuildAtom proofOwner proofPosition [] reversedBody
     context].toFinset

theorem normalBodyBuildNilPhase_selects_directive
    (proofOwner context : Atom) (proofPosition : Nat)
    (reversedBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildNilPhaseSpace proofOwner context proofPosition
            reversedBody)) =
      some normalBodyBuildNilDirective := by
  let atoms :=
    [normalBodyBuildNilRule,
     normalBodyBuildAtom proofOwner proofPosition [] reversedBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildNilDirective
    (by simp [atoms, normalBodyBuildNilRule, normalBodyBuildAtom])
    (by rfl)

private def normalBodyBuildNilSubstitution (proofOwner context : Atom)
    (proofPosition : Nat)
    (reversedBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("reversed-body", listAtom runtimeSymAtom reversedBody),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyBuildNilMatchRow_mem
    (proofOwner context : Atom) (proofPosition : Nat)
    (reversedBody : List Metamath.Verify.Sym) :
    normalBodyBuildNilSubstitution proofOwner context proofPosition
        reversedBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildNilPhaseSpace proofOwner context proofPosition
            reversedBody)
          normalBodyBuildNilRule)
        normalBodyBuildNilDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyBuildAtom proofOwner proofPosition [] reversedBody
    context
  let substitution := normalBodyBuildNilSubstitution proofOwner context
    proofPosition reversedBody
  let read := readCopyAtom
    (normalBodyBuildNilPhaseSpace proofOwner context proofPosition
      reversedBody)
    normalBodyBuildNilRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalBodyBuildAtom,
      normalBodyBuildNilPhaseSpace, normalBodyBuildNilRule, listAtom]
  have matchCursor :
      matchAtom [] normalBodyBuildNilCursorTemplate cursor =
        some substitution := by
    simp [normalBodyBuildNilCursorTemplate, cursor, normalBodyBuildAtom,
      substitution, normalBodyBuildNilSubstitution, listAtom, nilTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalBodyBuildNilDirective, matchInputSpec,
    normalBodyBuildNilPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalBodyBuildNilDirective_fires_reverse
    (proofOwner context : Atom) (proofPosition : Nat)
    (reversedBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyBuildNilPhaseSpace proofOwner context proofPosition
        reversedBody)
      normalBodyBuildNilDirective
    normalBodyReverseAtom proofOwner proofPosition reversedBody [] context ∈
          result ∧
      normalBodyBuildReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyBuildNilPhaseSpace proofOwner context proofPosition
        reversedBody)
      normalBodyBuildNilDirective.atom)
    normalBodyBuildNilDirective.rule.input).map Prod.fst
  let substitution := normalBodyBuildNilSubstitution proofOwner context
    proofPosition reversedBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyBuildNilDirective] using
      normalBodyBuildNilMatchRow_mem proofOwner context proofPosition
        reversedBody
  have reverseInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildNilReverseTemplate =
        some (normalBodyReverseAtom proofOwner proofPosition reversedBody []
          context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildReloadRequestTemplate =
        some (normalBodyBuildReloadAtom proofOwner proofPosition) := by
    rfl
  have reverseStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildNilReverseTemplate
    (normalBodyReverseAtom proofOwner proofPosition reversedBody [] context)
    rowMember reverseInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildReloadRequestTemplate
    (normalBodyBuildReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildNilDirective, normalBodyBuildNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr reverseStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyBuildNilDirective, normalBodyBuildNilSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalBodyBuildNilPhase_inhabits_target_native_type
    (proofOwner context : Atom) (proofPosition : Nat)
    (reversedBody : List Metamath.Verify.Sym) :
    let source := normalBodyBuildNilPhaseSpace proofOwner context
      proofPosition reversedBody
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyReverseAtom proofOwner proofPosition reversedBody [] context ∈
            target ∧
        normalBodyBuildReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyBuildNilPhase_selects_directive proofOwner context
          proofPosition reversedBody))
  · exact normalBodyBuildNilDirective_fires_reverse proofOwner context
      proofPosition reversedBody

/-! ### Result-body reversal transitions -/

private def normalBodyReverseConsPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-reverse", .var "proof", .var "pc",
        .expression
          [.symbol "mm-cons", .var "head", .var "reversed-tail"],
        .var "result-body", .var "context"]]

private def normalBodyReverseConsCursorTemplate : Atom :=
  .expression
    [.symbol "mm-body-reverse", .var "proof", .var "pc",
      .expression
        [.symbol "mm-cons", .var "head", .var "reversed-tail"],
      .var "result-body", .var "context"]

private def normalBodyReverseConsTailTemplate : Atom :=
  .expression
    [.symbol "mm-body-reverse", .var "proof", .var "pc",
      .var "reversed-tail",
      .expression [.symbol "mm-cons", .var "head", .var "result-body"],
      .var "context"]

private def normalBodyReverseConsSinks : List Sink :=
  [.remove normalBodyReverseConsCursorTemplate,
   .add normalBodyReverseConsTailTemplate,
   .add normalBodyBuildReloadRequestTemplate]

def normalBodyReverseConsDirective : SourceExecFact where
  atom := normalBodyReverseConsRule
  loc := normalBodyReverseConsLocation
  rule :=
    { priority := 28
      name := "mm-normal-body-reverse-cons"
      input := .compat (mkPattern normalBodyReverseConsPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyReverseConsSinks }

theorem extract_normalBodyReverseConsRule_exact :
    extractSupportedSourceExecFact normalBodyReverseConsRule =
      some normalBodyReverseConsDirective := by
  rfl

def normalBodyReverseConsPhaseSpace (proofOwner context : Atom)
    (proofPosition : Nat) (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyReverseConsRule,
   normalBodyReverseAtom proofOwner proofPosition (head :: reversedTail)
     resultBody context].toFinset

theorem normalBodyReverseConsPhase_selects_directive
    (proofOwner context : Atom) (proofPosition : Nat)
    (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyReverseConsPhaseSpace proofOwner context proofPosition
            head reversedTail resultBody)) =
      some normalBodyReverseConsDirective := by
  let atoms :=
    [normalBodyReverseConsRule,
     normalBodyReverseAtom proofOwner proofPosition (head :: reversedTail)
       resultBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyReverseConsDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyReverseConsDirective
    (by simp [atoms, normalBodyReverseConsRule, normalBodyReverseAtom,
      listAtom])
    (by rfl)

private def normalBodyReverseConsSubstitution (proofOwner context : Atom)
    (proofPosition : Nat) (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("result-body", listAtom runtimeSymAtom resultBody),
   ("reversed-tail", listAtom runtimeSymAtom reversedTail),
   ("head", runtimeSymAtom head),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyReverseConsMatchRow_mem
    (proofOwner context : Atom) (proofPosition : Nat)
    (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) :
    normalBodyReverseConsSubstitution proofOwner context proofPosition head
        reversedTail resultBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyReverseConsPhaseSpace proofOwner context proofPosition
            head reversedTail resultBody)
          normalBodyReverseConsRule)
        normalBodyReverseConsDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyReverseAtom proofOwner proofPosition
    (head :: reversedTail) resultBody context
  let substitution := normalBodyReverseConsSubstitution proofOwner context
    proofPosition head reversedTail resultBody
  let read := readCopyAtom
    (normalBodyReverseConsPhaseSpace proofOwner context proofPosition head
      reversedTail resultBody)
    normalBodyReverseConsRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalBodyReverseAtom,
      normalBodyReverseConsPhaseSpace, normalBodyReverseConsRule, listAtom]
  have matchCursor :
      matchAtom [] normalBodyReverseConsCursorTemplate cursor =
        some substitution := by
    simp [normalBodyReverseConsCursorTemplate, cursor,
      normalBodyReverseAtom, substitution,
      normalBodyReverseConsSubstitution, listAtom, consTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalBodyReverseConsDirective, matchInputSpec,
    normalBodyReverseConsPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalBodyReverseConsDirective_fires_tail
    (proofOwner context : Atom) (proofPosition : Nat)
    (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyReverseConsPhaseSpace proofOwner context proofPosition head
        reversedTail resultBody)
      normalBodyReverseConsDirective
    normalBodyReverseAtom proofOwner proofPosition reversedTail
          (head :: resultBody) context ∈ result ∧
      normalBodyBuildReloadAtom proofOwner proofPosition ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyReverseConsPhaseSpace proofOwner context proofPosition head
        reversedTail resultBody)
      normalBodyReverseConsDirective.atom)
    normalBodyReverseConsDirective.rule.input).map Prod.fst
  let substitution := normalBodyReverseConsSubstitution proofOwner context
    proofPosition head reversedTail resultBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyReverseConsDirective] using
      normalBodyReverseConsMatchRow_mem proofOwner context proofPosition head
        reversedTail resultBody
  have tailInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyReverseConsTailTemplate =
        some (normalBodyReverseAtom proofOwner proofPosition reversedTail
          (head :: resultBody) context) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyBuildReloadRequestTemplate =
        some (normalBodyBuildReloadAtom proofOwner proofPosition) := by
    rfl
  have tailStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyReverseConsTailTemplate
    (normalBodyReverseAtom proofOwner proofPosition reversedTail
      (head :: resultBody) context) rowMember tailInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyBuildReloadRequestTemplate
    (normalBodyBuildReloadAtom proofOwner proofPosition) rowMember
    reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyReverseConsDirective, normalBodyReverseConsSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (List.mem_toFinset.mpr tailStaged))
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalBodyReverseConsDirective, normalBodyReverseConsSinks,
      reflectiveSupportSinkProvider]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalBodyReverseConsPhase_inhabits_target_native_type
    (proofOwner context : Atom) (proofPosition : Nat)
    (head : Metamath.Verify.Sym)
    (reversedTail resultBody : List Metamath.Verify.Sym) :
    let source := normalBodyReverseConsPhaseSpace proofOwner context
      proofPosition head reversedTail resultBody
    let target := fireReflectiveSourceExecFact source
      normalBodyReverseConsDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyReverseAtom proofOwner proofPosition reversedTail
            (head :: resultBody) context ∈ target ∧
        normalBodyBuildReloadAtom proofOwner proofPosition ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyReverseConsPhase_selects_directive proofOwner context
          proofPosition head reversedTail resultBody))
  · exact normalBodyReverseConsDirective_fires_tail proofOwner context
      proofPosition head reversedTail resultBody

private def normalBodyReverseNilPatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-reverse", .var "proof", .var "pc",
        .expression [.symbol "mm-nil"], .var "result-body",
        .var "context"]]

private def normalBodyReverseNilCursorTemplate : Atom :=
  .expression
    [.symbol "mm-body-reverse", .var "proof", .var "pc",
      .expression [.symbol "mm-nil"], .var "result-body",
      .var "context"]

private def normalBodyReverseNilBuiltTemplate : Atom :=
  .expression
    [.symbol "mm-body-built", .var "proof", .var "pc",
      .var "context", .var "result-body"]

private def normalBodyReverseNilSinks : List Sink :=
  [.remove normalBodyReverseNilCursorTemplate,
   .add normalBodyReverseNilBuiltTemplate]

def normalBodyReverseNilDirective : SourceExecFact where
  atom := normalBodyReverseNilRule
  loc := normalBodyReverseNilLocation
  rule :=
    { priority := 29
      name := "mm-normal-body-reverse-nil"
      input := .compat (mkPattern normalBodyReverseNilPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyReverseNilSinks }

theorem extract_normalBodyReverseNilRule_exact :
    extractSupportedSourceExecFact normalBodyReverseNilRule =
      some normalBodyReverseNilDirective := by
  rfl

def normalBodyReverseNilPhaseSpace (proofOwner context : Atom)
    (proofPosition : Nat)
    (resultBody : List Metamath.Verify.Sym) : Space :=
  [normalBodyReverseNilRule,
   normalBodyReverseAtom proofOwner proofPosition [] resultBody
     context].toFinset

theorem normalBodyReverseNilPhase_selects_directive
    (proofOwner context : Atom) (proofPosition : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyReverseNilPhaseSpace proofOwner context proofPosition
            resultBody)) =
      some normalBodyReverseNilDirective := by
  let atoms :=
    [normalBodyReverseNilRule,
     normalBodyReverseAtom proofOwner proofPosition [] resultBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyReverseNilDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyReverseNilDirective
    (by simp [atoms, normalBodyReverseNilRule, normalBodyReverseAtom])
    (by rfl)

private def normalBodyReverseNilSubstitution (proofOwner context : Atom)
    (proofPosition : Nat)
    (resultBody : List Metamath.Verify.Sym) : Subst :=
  [("context", context),
   ("result-body", listAtom runtimeSymAtom resultBody),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalBodyReverseNilMatchRow_mem
    (proofOwner context : Atom) (proofPosition : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    normalBodyReverseNilSubstitution proofOwner context proofPosition
        resultBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyReverseNilPhaseSpace proofOwner context proofPosition
            resultBody)
          normalBodyReverseNilRule)
        normalBodyReverseNilDirective.rule.input).map Prod.fst := by
  let cursor := normalBodyReverseAtom proofOwner proofPosition [] resultBody
    context
  let substitution := normalBodyReverseNilSubstitution proofOwner context
    proofPosition resultBody
  let read := readCopyAtom
    (normalBodyReverseNilPhaseSpace proofOwner context proofPosition
      resultBody)
    normalBodyReverseNilRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, normalBodyReverseAtom,
      normalBodyReverseNilPhaseSpace, normalBodyReverseNilRule, listAtom]
  have matchCursor :
      matchAtom [] normalBodyReverseNilCursorTemplate cursor =
        some substitution := by
    simp [normalBodyReverseNilCursorTemplate, cursor,
      normalBodyReverseAtom, substitution,
      normalBodyReverseNilSubstitution, listAtom, nilTag,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalBodyReverseNilDirective, matchInputSpec,
    normalBodyReverseNilPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalBodyReverseNilDirective_fires_built
    (proofOwner context : Atom) (proofPosition : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalBodyReverseNilPhaseSpace proofOwner context proofPosition
        resultBody)
      normalBodyReverseNilDirective
    normalBodyBuiltAtom proofOwner proofPosition context resultBody ∈
      result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalBodyReverseNilPhaseSpace proofOwner context proofPosition
        resultBody)
      normalBodyReverseNilDirective.atom)
    normalBodyReverseNilDirective.rule.input).map Prod.fst
  let substitution := normalBodyReverseNilSubstitution proofOwner context
    proofPosition resultBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalBodyReverseNilDirective] using
      normalBodyReverseNilMatchRow_mem proofOwner context proofPosition
        resultBody
  have builtInstantiates :
      instantiateTemplateAtom? substitution
          normalBodyReverseNilBuiltTemplate =
        some (normalBodyBuiltAtom proofOwner proofPosition context
          resultBody) := by
    rfl
  have builtStaged := reflectiveStage_add_contains_of_row rows substitution
    normalBodyReverseNilBuiltTemplate
    (normalBodyBuiltAtom proofOwner proofPosition context resultBody)
    rowMember builtInstantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalBodyReverseNilDirective, normalBodyReverseNilSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr builtStaged)

theorem normalBodyReverseNilPhase_inhabits_target_native_type
    (proofOwner context : Atom) (proofPosition : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    let source := normalBodyReverseNilPhaseSpace proofOwner context
      proofPosition resultBody
    let target := fireReflectiveSourceExecFact source
      normalBodyReverseNilDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuiltAtom proofOwner proofPosition context resultBody ∈
        target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalBodyReverseNilPhase_selects_directive proofOwner context
          proofPosition resultBody))
  · exact normalBodyReverseNilDirective_fires_built proofOwner context
      proofPosition resultBody

/-! ### Persistent result-builder reload boundary -/

private def normalBodyBuildReloadSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalBodyBuildReloadLocation,
      .var "build-reload-self-input", .var "build-reload-self-output"]

private def normalBodyBuildReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-body-build", .var "build-reload-proof",
      .var "build-reload-pc"]

private def normalBodyBuildReloadBundleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-body-build-rules",
      .var "build-rule-const", .var "build-rule-variable",
      .var "build-rule-prefix-nil", .var "build-rule-prefix-cons",
      .var "build-rule-nil", .var "build-rule-reverse-cons",
      .var "build-rule-reverse-nil"]

private def normalBodyBuildReloadPatternAtoms : List Atom :=
  [normalBodyBuildReloadSelfTemplate, normalBodyBuildReloadTriggerTemplate,
   normalBodyBuildReloadBundleTemplate]

private def normalBodyBuildReloadSinks : List Sink :=
  [.add normalBodyBuildReloadSelfTemplate,
   .remove normalBodyBuildReloadTriggerTemplate,
   .add (.var "build-rule-const"),
   .add (.var "build-rule-variable"),
   .add (.var "build-rule-prefix-nil"),
   .add (.var "build-rule-prefix-cons"),
   .add (.var "build-rule-nil"),
   .add (.var "build-rule-reverse-cons"),
   .add (.var "build-rule-reverse-nil")]

def normalBodyBuildReloadDirective : SourceExecFact where
  atom := normalBodyBuildReloadRule
  loc := normalBodyBuildReloadLocation
  rule :=
    { priority := 30
      name := "mm-normal-body-build-reload"
      input := .compat (mkPattern normalBodyBuildReloadPatternAtoms)
      guards := []
      tmpl := mkTemplate normalBodyBuildReloadSinks }

theorem extract_normalBodyBuildReloadRule_exact :
    extractSupportedSourceExecFact normalBodyBuildReloadRule =
      some normalBodyBuildReloadDirective := by
  rfl

def normalBodyBuildReloadPhaseSpace (proofOwner : Atom)
    (proofPosition : Nat) : Space :=
  [normalBodyBuildReloadRule,
   normalBodyBuildReloadAtom proofOwner proofPosition,
   normalBodyBuildRuleBundle].toFinset

theorem normalBodyBuildReloadPhase_selects_directive
    (proofOwner : Atom) (proofPosition : Nat) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalBodyBuildReloadPhaseSpace proofOwner proofPosition)) =
      some normalBodyBuildReloadDirective := by
  let atoms :=
    [normalBodyBuildReloadRule,
     normalBodyBuildReloadAtom proofOwner proofPosition,
     normalBodyBuildRuleBundle]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalBodyBuildReloadDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalBodyBuildReloadDirective
    (by simp [atoms, normalBodyBuildReloadRule,
      normalBodyBuildReloadAtom, normalBodyBuildRuleBundle])
    (by rfl)

private def normalBodyBuildReloadSubstitution (proofOwner : Atom)
    (proofPosition : Nat) : Subst :=
  [("build-rule-reverse-nil", normalBodyReverseNilRule),
   ("build-rule-reverse-cons", normalBodyReverseConsRule),
   ("build-rule-nil", normalBodyBuildNilRule),
   ("build-rule-prefix-cons", normalBodyBuildPrefixConsRule),
   ("build-rule-prefix-nil", normalBodyBuildPrefixNilRule),
   ("build-rule-variable", normalBodyBuildVariableRule),
   ("build-rule-const", normalBodyBuildConstRule),
   ("build-reload-pc", natAtom proofPosition),
   ("build-reload-proof", proofOwner),
   ("build-reload-self-output", normalBodyBuildReloadOutput),
   ("build-reload-self-input", normalBodyBuildReloadInput)]

private theorem normalBodyBuildReloadMatchRow_mem
    (proofOwner : Atom) (proofPosition : Nat) :
    normalBodyBuildReloadSubstitution proofOwner proofPosition ∈
      (matchInputSpec []
        (readCopyAtom
          (normalBodyBuildReloadPhaseSpace proofOwner proofPosition)
          normalBodyBuildReloadRule)
        normalBodyBuildReloadDirective.rule.input).map Prod.fst := by
  let request := normalBodyBuildReloadAtom proofOwner proofPosition
  let read := readCopyAtom
    (normalBodyBuildReloadPhaseSpace proofOwner proofPosition)
    normalBodyBuildReloadRule
  let afterSelf : Subst :=
    [("build-reload-self-output", normalBodyBuildReloadOutput),
     ("build-reload-self-input", normalBodyBuildReloadInput)]
  let afterRequest : Subst :=
    [("build-reload-pc", natAtom proofPosition),
     ("build-reload-proof", proofOwner),
     ("build-reload-self-output", normalBodyBuildReloadOutput),
     ("build-reload-self-input", normalBodyBuildReloadInput)]
  let substitution := normalBodyBuildReloadSubstitution proofOwner
    proofPosition
  have selfMem : normalBodyBuildReloadRule ∈ read := by
    simp [read, readCopyAtom, normalBodyBuildReloadPhaseSpace]
  have requestMem : request ∈ read := by
    simp [read, readCopyAtom, consumeAtom, request,
      normalBodyBuildReloadPhaseSpace, normalBodyBuildReloadRule,
      normalBodyBuildReloadAtom]
  have bundleMem : normalBodyBuildRuleBundle ∈ read := by
    simp [read, readCopyAtom, consumeAtom,
      normalBodyBuildReloadPhaseSpace, normalBodyBuildReloadRule,
      normalBodyBuildRuleBundle]
  have matchSelf :
      matchAtom [] normalBodyBuildReloadSelfTemplate
          normalBodyBuildReloadRule = some afterSelf := by
    simp [normalBodyBuildReloadSelfTemplate, normalBodyBuildReloadRule,
      normalBodyBuildReloadLocation, normalBodyBuildReloadInput,
      normalBodyBuildReloadOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchRequest :
      matchAtom afterSelf normalBodyBuildReloadTriggerTemplate request =
        some afterRequest := by
    simp [normalBodyBuildReloadTriggerTemplate, request,
      normalBodyBuildReloadAtom, afterSelf, afterRequest, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchBundle :
      matchAtom afterRequest normalBodyBuildReloadBundleTemplate
          normalBodyBuildRuleBundle = some substitution := by
    simp [normalBodyBuildReloadBundleTemplate, normalBodyBuildRuleBundle,
      afterRequest, substitution, normalBodyBuildReloadSubstitution,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution,
    {normalBodyBuildReloadRule, request, normalBodyBuildRuleBundle}), ?_, rfl⟩
  simp only [normalBodyBuildReloadDirective, matchInputSpec,
    normalBodyBuildReloadPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterSelf, normalBodyBuildReloadRule),
    matchOneInSpace_mem [] _ read normalBodyBuildReloadRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterRequest, request),
    matchOneInSpace_mem afterSelf _ read request requestMem afterRequest
      matchRequest, ?_⟩
  refine ⟨(substitution, normalBodyBuildRuleBundle),
    matchOneInSpace_mem afterRequest _ read normalBodyBuildRuleBundle
      bundleMem substitution matchBundle, ?_⟩
  simp [substitution, request]

/-- Reload is part of the authored MM2 dynamics: OSLF classifies its exact
target rather than treating rule reinstallation as a host-side operation. -/
theorem normalBodyBuildReloadPhase_inhabits_target_native_type
    (proofOwner : Atom) (proofPosition : Nat) :
    let source := normalBodyBuildReloadPhaseSpace proofOwner proofPosition
    let target := fireReflectiveSourceExecFact source
      normalBodyBuildReloadDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred := by
  dsimp only
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected
      (normalBodyBuildReloadPhase_selects_directive proofOwner
        proofPosition))

/-! ### Completed assertion-result publication -/

/-- Control returned to the ordered normal-proof fold after one assertion. -/
def normalControlAtom (scopeOwner proofOwner : Atom)
    (proofPosition stackTop : Nat) : Atom :=
  .expression
    [.symbol "mm-normal-control", scopeOwner, proofOwner,
      natAtom proofPosition, natAtom stackTop]

/-- Exact source assertion occurrence retained by the result stack cell. -/
def normalAssertionOccurrenceAtom (proofPosition : Nat)
    (assertionLabel : String) : Atom :=
  .expression
    [.symbol "mm-assertion-occurrence", natAtom proofPosition,
      stringAtom assertionLabel]

/-- Result stack cell produced by an assertion application. -/
def normalAssertionStackAtom (proofOwner : Atom) (stackPosition : Nat)
    (resultTypecode : String) (resultBody : List Metamath.Verify.Sym)
    (proofPosition : Nat) (assertionLabel : String) : Atom :=
  .expression
    [.symbol "mm-stack-cell", proofOwner, natAtom stackPosition,
      .expression
        [.symbol "mm-formula", stringAtom resultTypecode,
          listAtom runtimeSymAtom resultBody],
      normalAssertionOccurrenceAtom proofPosition assertionLabel]

private def normalAssertionResultCompletePatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-body-built", .var "proof", .var "pc",
        .expression
          [.symbol "mm-assertion-result-context", .var "scope",
            .var "next-pc", .var "label", .var "result-typecode",
            .var "stack-base", .var "next-top"],
        .var "result-body"]]

private def normalAssertionResultCompleteCursorTemplate : Atom :=
  .expression
    [.symbol "mm-body-built", .var "proof", .var "pc",
      .expression
        [.symbol "mm-assertion-result-context", .var "scope",
          .var "next-pc", .var "label", .var "result-typecode",
          .var "stack-base", .var "next-top"],
      .var "result-body"]

private def normalAssertionResultCompleteControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope", .var "proof",
      .var "next-pc", .var "next-top"]

private def normalAssertionResultCompleteStackTemplate : Atom :=
  .expression
    [.symbol "mm-stack-cell", .var "proof", .var "stack-base",
      .expression
        [.symbol "mm-formula", .var "result-typecode",
          .var "result-body"],
      .expression
        [.symbol "mm-assertion-occurrence", .var "pc", .var "label"]]

private def normalAssertionResultCompleteReloadTemplate : Atom :=
  .expression [.symbol "mm-reload-normal-dispatch", .var "proof"]

private def normalAssertionResultCompleteSinks : List Sink :=
  [.remove normalAssertionResultCompleteCursorTemplate,
   .add normalAssertionResultCompleteControlTemplate,
   .add normalAssertionResultCompleteStackTemplate,
   .add normalAssertionResultCompleteReloadTemplate]

def normalAssertionResultCompleteDirective : SourceExecFact where
  atom := normalAssertionResultCompleteRule
  loc := normalAssertionResultCompleteLocation
  rule :=
    { priority := 31
      name := "mm-normal-result-complete"
      input := .compat (mkPattern normalAssertionResultCompletePatternAtoms)
      guards := []
      tmpl := mkTemplate normalAssertionResultCompleteSinks }

theorem extract_normalAssertionResultCompleteRule_exact :
    extractSupportedSourceExecFact normalAssertionResultCompleteRule =
      some normalAssertionResultCompleteDirective := by
  rfl

def normalAssertionResultCompletePhaseSpace
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat)
    (assertionLabel resultTypecode : String)
    (stackBase nextTop : Nat)
    (resultBody : List Metamath.Verify.Sym) : Space :=
  [normalAssertionResultCompleteRule,
   normalBodyBuiltAtom proofOwner proofPosition
     (normalAssertionResultContextAtom scopeOwner nextProofPosition
       assertionLabel resultTypecode stackBase nextTop)
     resultBody].toFinset

theorem normalAssertionResultCompletePhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat)
    (assertionLabel resultTypecode : String)
    (stackBase nextTop : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalAssertionResultCompletePhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertionLabel resultTypecode
            stackBase nextTop resultBody)) =
      some normalAssertionResultCompleteDirective := by
  let atoms :=
    [normalAssertionResultCompleteRule,
     normalBodyBuiltAtom proofOwner proofPosition
       (normalAssertionResultContextAtom scopeOwner nextProofPosition
         assertionLabel resultTypecode stackBase nextTop)
       resultBody]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalAssertionResultCompleteDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalAssertionResultCompleteDirective
    (by simp [atoms, normalAssertionResultCompleteRule,
      normalBodyBuiltAtom, normalAssertionResultContextAtom])
    (by rfl)

private def normalAssertionResultCompleteSubstitution
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat)
    (assertionLabel resultTypecode : String)
    (stackBase nextTop : Nat)
    (resultBody : List Metamath.Verify.Sym) : Subst :=
  [("result-body", listAtom runtimeSymAtom resultBody),
   ("next-top", natAtom nextTop), ("stack-base", natAtom stackBase),
   ("result-typecode", stringAtom resultTypecode),
   ("label", stringAtom assertionLabel),
   ("next-pc", natAtom nextProofPosition), ("scope", scopeOwner),
   ("pc", natAtom proofPosition), ("proof", proofOwner)]

private theorem normalAssertionResultCompleteMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat)
    (assertionLabel resultTypecode : String)
    (stackBase nextTop : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    normalAssertionResultCompleteSubstitution scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel resultTypecode
        stackBase nextTop resultBody ∈
      (matchInputSpec []
        (readCopyAtom
          (normalAssertionResultCompletePhaseSpace scopeOwner proofOwner
            proofPosition nextProofPosition assertionLabel resultTypecode
            stackBase nextTop resultBody)
          normalAssertionResultCompleteRule)
        normalAssertionResultCompleteDirective.rule.input).map Prod.fst := by
  let context := normalAssertionResultContextAtom scopeOwner
    nextProofPosition assertionLabel resultTypecode stackBase nextTop
  let cursor := normalBodyBuiltAtom proofOwner proofPosition context resultBody
  let substitution := normalAssertionResultCompleteSubstitution scopeOwner
    proofOwner proofPosition nextProofPosition assertionLabel resultTypecode
    stackBase nextTop resultBody
  let read := readCopyAtom
    (normalAssertionResultCompletePhaseSpace scopeOwner proofOwner
      proofPosition nextProofPosition assertionLabel resultTypecode stackBase
      nextTop resultBody)
    normalAssertionResultCompleteRule
  have cursorMem : cursor ∈ read := by
    simp [read, readCopyAtom, consumeAtom, cursor, context,
      normalBodyBuiltAtom, normalAssertionResultContextAtom,
      normalAssertionResultCompletePhaseSpace,
      normalAssertionResultCompleteRule]
  have matchCursor :
      matchAtom [] normalAssertionResultCompleteCursorTemplate cursor =
        some substitution := by
    simp [normalAssertionResultCompleteCursorTemplate, cursor, context,
      normalBodyBuiltAtom, normalAssertionResultContextAtom, substitution,
      normalAssertionResultCompleteSubstitution, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalAssertionResultCompleteDirective, matchInputSpec,
    normalAssertionResultCompletePatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution
      matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalAssertionResultCompleteDirective_fires_result
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat)
    (assertionLabel resultTypecode : String)
    (stackBase nextTop : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    let result := fireReflectiveSourceExecFact
      (normalAssertionResultCompletePhaseSpace scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel resultTypecode
        stackBase nextTop resultBody)
      normalAssertionResultCompleteDirective
    normalControlAtom scopeOwner proofOwner nextProofPosition nextTop ∈
          result ∧
      normalAssertionStackAtom proofOwner stackBase resultTypecode resultBody
            proofPosition assertionLabel ∈ result ∧
        normalAssertionReloadAtom proofOwner ∈ result := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalAssertionResultCompletePhaseSpace scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel resultTypecode
        stackBase nextTop resultBody)
      normalAssertionResultCompleteDirective.atom)
    normalAssertionResultCompleteDirective.rule.input).map Prod.fst
  let substitution := normalAssertionResultCompleteSubstitution scopeOwner
    proofOwner proofPosition nextProofPosition assertionLabel resultTypecode
    stackBase nextTop resultBody
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution,
      normalAssertionResultCompleteDirective] using
      normalAssertionResultCompleteMatchRow_mem scopeOwner proofOwner
        proofPosition nextProofPosition assertionLabel resultTypecode
        stackBase nextTop resultBody
  have controlInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionResultCompleteControlTemplate =
        some (normalControlAtom scopeOwner proofOwner nextProofPosition
          nextTop) := by
    rfl
  have stackInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionResultCompleteStackTemplate =
        some (normalAssertionStackAtom proofOwner stackBase resultTypecode
          resultBody proofPosition assertionLabel) := by
    rfl
  have reloadInstantiates :
      instantiateTemplateAtom? substitution
          normalAssertionResultCompleteReloadTemplate =
        some (normalAssertionReloadAtom proofOwner) := by
    rfl
  have controlStaged := reflectiveStage_add_contains_of_row rows substitution
    normalAssertionResultCompleteControlTemplate
    (normalControlAtom scopeOwner proofOwner nextProofPosition nextTop)
    rowMember controlInstantiates
  have stackStaged := reflectiveStage_add_contains_of_row rows substitution
    normalAssertionResultCompleteStackTemplate
    (normalAssertionStackAtom proofOwner stackBase resultTypecode resultBody
      proofPosition assertionLabel) rowMember stackInstantiates
  have reloadStaged := reflectiveStage_add_contains_of_row rows substitution
    normalAssertionResultCompleteReloadTemplate
    (normalAssertionReloadAtom proofOwner) rowMember reloadInstantiates
  constructor
  · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
      normalAssertionResultCompleteDirective,
      normalAssertionResultCompleteSinks, reflectiveSupportSinkProvider]
    exact Finset.mem_union_left _
      (Finset.mem_union_left _
        (Finset.mem_union_right _ (List.mem_toFinset.mpr controlStaged)))
  · constructor
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
        normalAssertionResultCompleteDirective,
        normalAssertionResultCompleteSinks, reflectiveSupportSinkProvider]
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (List.mem_toFinset.mpr stackStaged))
    · simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
        normalAssertionResultCompleteDirective,
        normalAssertionResultCompleteSinks, reflectiveSupportSinkProvider]
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr reloadStaged)

theorem normalAssertionResultCompletePhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition nextProofPosition : Nat)
    (assertionLabel resultTypecode : String)
    (stackBase nextTop : Nat)
    (resultBody : List Metamath.Verify.Sym) :
    let source := normalAssertionResultCompletePhaseSpace scopeOwner
      proofOwner proofPosition nextProofPosition assertionLabel
      resultTypecode stackBase nextTop resultBody
    let target := fireReflectiveSourceExecFact source
      normalAssertionResultCompleteDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalControlAtom scopeOwner proofOwner nextProofPosition nextTop ∈
            target ∧
        normalAssertionStackAtom proofOwner stackBase resultTypecode resultBody
              proofPosition assertionLabel ∈ target ∧
          normalAssertionReloadAtom proofOwner ∈ target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalAssertionResultCompletePhase_selects_directive scopeOwner
          proofOwner proofPosition nextProofPosition assertionLabel
          resultTypecode stackBase nextTop resultBody))
  · exact normalAssertionResultCompleteDirective_fires_result scopeOwner
      proofOwner proofPosition nextProofPosition assertionLabel resultTypecode
      stackBase nextTop resultBody

/-- Result occurrences cannot be collapsed merely because two applications
produce an equal formula. -/
theorem normalAssertionStackAtom_occurrence_injective
    (proofOwner : Atom) (stackPosition : Nat)
    (resultTypecode : String) (resultBody : List Metamath.Verify.Sym)
    (leftPosition rightPosition : Nat)
    (leftLabel rightLabel : String)
    (equal :
      normalAssertionStackAtom proofOwner stackPosition resultTypecode
          resultBody leftPosition leftLabel =
        normalAssertionStackAtom proofOwner stackPosition resultTypecode
          resultBody rightPosition rightLabel) :
    leftPosition = rightPosition ∧ leftLabel = rightLabel := by
  simp [normalAssertionStackAtom, normalAssertionOccurrenceAtom,
    natAtom] at equal
  exact ⟨equal.1, stringAtom_injective equal.2⟩

def normalDVCompletePatternAtoms : List Atom :=
  [.expression
      [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
        .var "pc", .var "label", .var "hyp-end", .var "hyp-end",
        .var "source-body", .var "context"]]

private def normalDVCompleteCursorTemplate : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", .var "scope", .var "proof",
      .var "pc", .var "label", .var "hyp-end", .var "hyp-end",
      .var "source-body", .var "context"]

private def normalDVCompleteBodyTemplate : Atom :=
  .expression
    [.symbol "mm-body-build", .var "proof", .var "pc",
      .var "source-body", .expression [.symbol "mm-nil"],
      .var "context"]

private def normalDVCompleteSinks : List Sink :=
  [.remove normalDVCompleteCursorTemplate,
   .add normalDVCompleteBodyTemplate]

def normalDVCompleteDirective : SourceExecFact where
  atom := normalDVCompleteRule
  loc := normalDVCompleteLocation
  rule :=
    { priority := 21
      name := "mm-normal-dv-complete"
      input := .compat (mkPattern normalDVCompletePatternAtoms)
      guards := []
      tmpl := mkTemplate normalDVCompleteSinks }

theorem extract_normalDVCompleteRule_exact :
    extractSupportedSourceExecFact normalDVCompleteRule =
      some normalDVCompleteDirective := by
  rfl

def normalDVCompletePhaseSpace (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) : Space :=
  [normalDVCompleteRule,
   normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel
     pairEnd pairEnd sourceBody context].toFinset

theorem normalDVCompletePhase_selects_directive
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDVCompletePhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel pairEnd sourceBody context)) =
      some normalDVCompleteDirective := by
  let atoms :=
    [normalDVCompleteRule,
     normalDVNextPairAtom scopeOwner proofOwner proofPosition assertionLabel
       pairEnd pairEnd sourceBody context]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDVCompleteDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDVCompleteDirective
    (by simp [atoms, normalDVCompleteRule, normalDVCompleteLocation,
      normalDVCompleteInput, normalDVCompleteOutput,
      normalDVNextPairAtom])
    (by rfl)

private def normalDVCompleteSubstitution (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) : Subst :=
  [("context", context),
   ("source-body", listAtom runtimeSymAtom sourceBody),
   ("hyp-end", natAtom pairEnd), ("label", stringAtom assertionLabel),
   ("pc", natAtom proofPosition), ("proof", proofOwner),
   ("scope", scopeOwner)]

private theorem normalDVCompleteMatchRow_mem
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    normalDVCompleteSubstitution scopeOwner proofOwner proofPosition
        assertionLabel pairEnd sourceBody context ∈
      (matchInputSpec []
        (readCopyAtom
          (normalDVCompletePhaseSpace scopeOwner proofOwner proofPosition
            assertionLabel pairEnd sourceBody context)
          normalDVCompleteRule)
        normalDVCompleteDirective.rule.input).map Prod.fst := by
  let cursor := normalDVNextPairAtom scopeOwner proofOwner proofPosition
    assertionLabel pairEnd pairEnd sourceBody context
  let substitution := normalDVCompleteSubstitution scopeOwner proofOwner
    proofPosition assertionLabel pairEnd sourceBody context
  let read := readCopyAtom
    (normalDVCompletePhaseSpace scopeOwner proofOwner proofPosition
      assertionLabel pairEnd sourceBody context)
    normalDVCompleteRule
  have cursorMem : cursor ∈ read := by
    simp [read, cursor, readCopyAtom, consumeAtom,
      normalDVCompletePhaseSpace, normalDVCompleteRule,
      normalDVCompleteLocation, normalDVCompleteInput,
      normalDVCompleteOutput, normalDVNextPairAtom]
  have matchCursor :
      matchAtom [] normalDVCompleteCursorTemplate cursor =
        some substitution := by
    simp [normalDVCompleteCursorTemplate, cursor, normalDVNextPairAtom,
      substitution,
      normalDVCompleteSubstitution, matchAtom, matchAtom.matchAtomList,
      Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution, {cursor}), ?_, rfl⟩
  simp only [normalDVCompleteDirective, matchInputSpec,
    normalDVCompletePatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(substitution, cursor),
    matchOneInSpace_mem [] _ read cursor cursorMem substitution matchCursor, ?_⟩
  simp [substitution, cursor]

theorem normalDVCompleteDirective_fires_body_build
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    normalBodyBuildAtom proofOwner proofPosition sourceBody [] context ∈
      fireReflectiveSourceExecFact
        (normalDVCompletePhaseSpace scopeOwner proofOwner proofPosition
          assertionLabel pairEnd sourceBody context)
        normalDVCompleteDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom
      (normalDVCompletePhaseSpace scopeOwner proofOwner proofPosition
        assertionLabel pairEnd sourceBody context)
      normalDVCompleteDirective.atom)
    normalDVCompleteDirective.rule.input).map Prod.fst
  let substitution := normalDVCompleteSubstitution scopeOwner proofOwner
    proofPosition assertionLabel pairEnd sourceBody context
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDVCompleteDirective] using
      normalDVCompleteMatchRow_mem scopeOwner proofOwner proofPosition
        assertionLabel pairEnd sourceBody context
  have instantiates :
      instantiateTemplateAtom? substitution normalDVCompleteBodyTemplate =
        some (normalBodyBuildAtom proofOwner proofPosition sourceBody []
          context) := by
    rfl
  have staged := reflectiveStage_add_contains_of_row rows substitution
    normalDVCompleteBodyTemplate
    (normalBodyBuildAtom proofOwner proofPosition sourceBody [] context)
    rowMember instantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalDVCompleteDirective, normalDVCompleteSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr staged)

theorem normalDVCompletePhase_inhabits_target_native_type
    (scopeOwner proofOwner : Atom)
    (proofPosition : Nat) (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    let source := normalDVCompletePhaseSpace scopeOwner proofOwner
      proofPosition assertionLabel pairEnd sourceBody context
    let target := fireReflectiveSourceExecFact source
      normalDVCompleteDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ∧
      normalBodyBuildAtom proofOwner proofPosition sourceBody [] context ∈
        target := by
  dsimp only
  constructor
  · exact reflective_event_inhabits_exact_target
      (reflectiveEventOfSelected
        (normalDVCompletePhase_selects_directive scopeOwner proofOwner
          proofPosition assertionLabel pairEnd sourceBody context))
  · exact normalDVCompleteDirective_fires_body_build scopeOwner proofOwner
      proofPosition assertionLabel pairEnd sourceBody context

private def normalDispatchReloadableRules : List Atom :=
  [normalHypothesisStepRule, normalAssertionStartRule,
   normalAssertionPopRule, normalAssertionBeginRule,
   normalAssertionFloatingRule, normalAssertionEssentialRule,
   normalBodyMatchConstRule, normalBodyMatchVariableRule,
   normalBodyPrefixNilRule, normalBodyPrefixConsRule,
   normalBodyMatchNilRule, normalBodyReloadRule,
   normalAssertionEssentialCompleteRule,
   normalAssertionFinishRule,
   normalDVPairBeginRule, normalDVLeftConstRule,
   normalDVLeftVariableRule, normalDVRightConstRule,
   normalDVRightVariableRule, normalDVRightNilRule,
   normalDVLeftNilRule, normalDVCompleteRule, normalDVReloadRule,
   normalBodyBuildConstRule, normalBodyBuildVariableRule,
   normalBodyBuildPrefixNilRule, normalBodyBuildPrefixConsRule,
   normalBodyBuildNilRule, normalBodyReverseConsRule,
   normalBodyReverseNilRule, normalBodyBuildReloadRule,
   normalAssertionResultCompleteRule]

/-- One verifier-owned row containing one executable rule as opaque data.
Keeping rules in separate rows is semantically the same finite relation as a
single wide bundle, but it also respects the ordinary MM2 parser's bound on
expression-local variables. -/
def normalDispatchRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-normal-dispatch-rule", rule]

def normalDispatchRuleRows : List Atom :=
  normalDispatchReloadableRules.map normalDispatchRuleRow

private def normalDispatchReloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-normal-dispatch-rule", .var "reload-rule"]

private def normalDispatchReloadInput : Atom :=
  .expression
    [.symbol ",",
      .expression
        [.symbol "exec", normalDispatchReloadLocation,
          .var "reload-self-input", .var "reload-self-output"],
      .expression
        [.symbol "mm-reload-normal-dispatch", .var "reload-proof"],
      normalDispatchReloadRuleTemplate]

private def normalDispatchReloadOutput : Atom :=
  .expression
    [.symbol "O",
      .expression
        [.symbol "+",
          .expression
            [.symbol "exec", normalDispatchReloadLocation,
              .var "reload-self-input", .var "reload-self-output"]],
      .expression
        [.symbol "-",
          .expression
            [.symbol "mm-reload-normal-dispatch", .var "reload-proof"]],
      .expression [.symbol "+", .var "reload-rule"]]

/-- Reinstall the normal dispatch and assertion micro-rules after an assertion
step.  MM2 removes every selected `exec` before interpreting it, including a
rule whose pattern does not match.  Reinstallation is therefore required for
a later assertion occurrence; it is explicit MM2 scheduling, not a hidden
host worklist. -/
def normalDispatchReloadRule : Atom :=
  .expression
    [.symbol "exec", normalDispatchReloadLocation,
      normalDispatchReloadInput, normalDispatchReloadOutput]

private def normalDispatchReloadSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalDispatchReloadLocation,
      .var "reload-self-input", .var "reload-self-output"]

private def normalDispatchReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-normal-dispatch", .var "reload-proof"]

private def normalDispatchReloadPatternAtoms : List Atom :=
  [normalDispatchReloadSelfTemplate, normalDispatchReloadTriggerTemplate,
   normalDispatchReloadRuleTemplate]

private def normalDispatchReloadSinks : List Sink :=
  [.add normalDispatchReloadSelfTemplate,
   .remove normalDispatchReloadTriggerTemplate,
   .add (.var "reload-rule")]

/-- The ordinary-MM2 directive represented by the whole-proof dispatch
reloader.  Its rule payload is captured from verifier-owned inert data rather
than reconstructed through an outer substitution. -/
def normalDispatchReloadDirective : SourceExecFact where
  atom := normalDispatchReloadRule
  loc := normalDispatchReloadLocation
  rule :=
    { priority := 32
      name := "mm-normal-dispatch-reload"
      input := .compat (mkPattern normalDispatchReloadPatternAtoms)
      guards := []
      tmpl := mkTemplate normalDispatchReloadSinks }

theorem extract_normalDispatchReloadRule_exact :
    extractSupportedSourceExecFact normalDispatchReloadRule =
      some normalDispatchReloadDirective := by
  rfl

def normalDispatchReloadPhaseSpace (proofOwner rule : Atom) : Space :=
  [normalDispatchReloadRule,
   .expression [.symbol "mm-reload-normal-dispatch", proofOwner],
   normalDispatchRuleRow rule].toFinset

theorem normalDispatchReloadPhase_selects_directive
    (proofOwner rule : Atom) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace
          (normalDispatchReloadPhaseSpace proofOwner rule)) =
      some normalDispatchReloadDirective := by
  let atoms :=
    [normalDispatchReloadRule,
     .expression [.symbol "mm-reload-normal-dispatch", proofOwner],
     normalDispatchRuleRow rule]
  change selectNextScheduled
      (supportedSourceExecFactsOfSpace atoms.toFinset) =
    some normalDispatchReloadDirective
  exact reflective_selects_of_computable_supported_singleton atoms
    normalDispatchReloadDirective
    (by simp [atoms, normalDispatchReloadRule, normalDispatchRuleRow])
    (by rfl)

private def normalDispatchReloadSubstitution (proofOwner rule : Atom) : Subst :=
  [("reload-rule", rule),
     ("reload-proof", proofOwner),
     ("reload-self-output", normalDispatchReloadOutput),
     ("reload-self-input", normalDispatchReloadInput)]

private theorem normalDispatchReloadMatchRow_mem (proofOwner rule : Atom) :
    normalDispatchReloadSubstitution proofOwner rule ∈
      (matchInputSpec []
        (readCopyAtom (normalDispatchReloadPhaseSpace proofOwner rule)
          normalDispatchReloadRule)
        normalDispatchReloadDirective.rule.input).map Prod.fst := by
  let request : Atom :=
    .expression [.symbol "mm-reload-normal-dispatch", proofOwner]
  let read := readCopyAtom (normalDispatchReloadPhaseSpace proofOwner rule)
    normalDispatchReloadRule
  let afterSelf : Subst :=
    [("reload-self-output", normalDispatchReloadOutput),
     ("reload-self-input", normalDispatchReloadInput)]
  let afterRequest : Subst :=
    [("reload-proof", proofOwner),
     ("reload-self-output", normalDispatchReloadOutput),
     ("reload-self-input", normalDispatchReloadInput)]
  let ruleRow := normalDispatchRuleRow rule
  let substitution := normalDispatchReloadSubstitution proofOwner rule
  have selfMem : normalDispatchReloadRule ∈ read := by
    simp [read, readCopyAtom, normalDispatchReloadPhaseSpace]
  have requestMem : request ∈ read := by
    simp [read, readCopyAtom, consumeAtom, request,
      normalDispatchReloadPhaseSpace, normalDispatchReloadRule]
  have ruleRowMem : ruleRow ∈ read := by
    simp [read, readCopyAtom, consumeAtom,
      normalDispatchReloadPhaseSpace, normalDispatchReloadRule,
      normalDispatchRuleRow, ruleRow]
  have matchSelf :
      matchAtom [] normalDispatchReloadSelfTemplate
          normalDispatchReloadRule = some afterSelf := by
    simp [normalDispatchReloadSelfTemplate, normalDispatchReloadRule,
      normalDispatchReloadLocation, normalDispatchReloadInput,
      normalDispatchReloadOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchRequest :
      matchAtom afterSelf normalDispatchReloadTriggerTemplate request =
        some afterRequest := by
    simp [normalDispatchReloadTriggerTemplate, request, afterSelf,
      afterRequest, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchRuleRow :
      matchAtom afterRequest normalDispatchReloadRuleTemplate ruleRow =
        some substitution := by
    simp [normalDispatchReloadRuleTemplate, normalDispatchRuleRow, ruleRow,
      normalDispatchReloadSubstitution, afterRequest, substitution,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution,
    {normalDispatchReloadRule, request, ruleRow}), ?_, rfl⟩
  simp only [normalDispatchReloadDirective, matchInputSpec,
    normalDispatchReloadPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterSelf, normalDispatchReloadRule),
    matchOneInSpace_mem [] _ read normalDispatchReloadRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterRequest, request),
    matchOneInSpace_mem afterSelf _ read request requestMem afterRequest
      matchRequest, ?_⟩
  refine ⟨(substitution, ruleRow),
    matchOneInSpace_mem afterRequest _ read ruleRow
      ruleRowMem substitution matchRuleRow, ?_⟩
  simp [substitution, request, ruleRow]

/-- The real reload space contains the whole verifier-owned rule relation.
The unary row representation keeps each stored MM2 expression within the
target parser's expression-local variable bound. -/
def normalDispatchReloadFullPhaseSpace (proofOwner : Atom) : Space :=
  (normalDispatchReloadRule ::
    .expression [.symbol "mm-reload-normal-dispatch", proofOwner] ::
    normalDispatchRuleRows).toFinset

private theorem normalDispatchReloadFullMatchRow_mem
    (proofOwner rule : Atom)
    (ruleMember : rule ∈ normalDispatchReloadableRules) :
    normalDispatchReloadSubstitution proofOwner rule ∈
      (matchInputSpec []
        (readCopyAtom (normalDispatchReloadFullPhaseSpace proofOwner)
          normalDispatchReloadRule)
        normalDispatchReloadDirective.rule.input).map Prod.fst := by
  let request : Atom :=
    .expression [.symbol "mm-reload-normal-dispatch", proofOwner]
  let ruleRow := normalDispatchRuleRow rule
  let read := readCopyAtom (normalDispatchReloadFullPhaseSpace proofOwner)
    normalDispatchReloadRule
  let afterSelf : Subst :=
    [("reload-self-output", normalDispatchReloadOutput),
     ("reload-self-input", normalDispatchReloadInput)]
  let afterRequest : Subst :=
    [("reload-proof", proofOwner),
     ("reload-self-output", normalDispatchReloadOutput),
     ("reload-self-input", normalDispatchReloadInput)]
  let substitution := normalDispatchReloadSubstitution proofOwner rule
  have selfMem : normalDispatchReloadRule ∈ read := by
    simp [read, readCopyAtom, normalDispatchReloadFullPhaseSpace]
  have requestMem : request ∈ read := by
    simp [read, readCopyAtom, consumeAtom, request,
      normalDispatchReloadFullPhaseSpace, normalDispatchReloadRule]
  have ruleRowMem : ruleRow ∈ read := by
    simp [read, readCopyAtom, consumeAtom,
      normalDispatchReloadFullPhaseSpace, normalDispatchReloadRule,
      normalDispatchRuleRows, normalDispatchRuleRow, ruleRow, ruleMember]
  have matchSelf :
      matchAtom [] normalDispatchReloadSelfTemplate
          normalDispatchReloadRule = some afterSelf := by
    simp [normalDispatchReloadSelfTemplate, normalDispatchReloadRule,
      normalDispatchReloadLocation, normalDispatchReloadInput,
      normalDispatchReloadOutput, afterSelf, matchAtom,
      matchAtom.matchAtomList, Subst.lookup]
  have matchRequest :
      matchAtom afterSelf normalDispatchReloadTriggerTemplate request =
        some afterRequest := by
    simp [normalDispatchReloadTriggerTemplate, request, afterSelf,
      afterRequest, matchAtom, matchAtom.matchAtomList, Subst.lookup]
  have matchRuleRow :
      matchAtom afterRequest normalDispatchReloadRuleTemplate ruleRow =
        some substitution := by
    simp [normalDispatchReloadRuleTemplate, normalDispatchRuleRow, ruleRow,
      normalDispatchReloadSubstitution, afterRequest, substitution,
      matchAtom, matchAtom.matchAtomList, Subst.lookup]
  rw [List.mem_map]
  refine ⟨(substitution,
    {normalDispatchReloadRule, request, ruleRow}), ?_, rfl⟩
  simp only [normalDispatchReloadDirective, matchInputSpec,
    normalDispatchReloadPatternAtoms, mkPattern, matchPattern,
    matchPattern.go, List.mem_flatMap]
  refine ⟨(afterSelf, normalDispatchReloadRule),
    matchOneInSpace_mem [] _ read normalDispatchReloadRule selfMem afterSelf
      matchSelf, ?_⟩
  refine ⟨(afterRequest, request),
    matchOneInSpace_mem afterSelf _ read request requestMem afterRequest
      matchRequest, ?_⟩
  refine ⟨(substitution, ruleRow),
    matchOneInSpace_mem afterRequest _ read ruleRow
      ruleRowMem substitution matchRuleRow, ?_⟩
  simp [substitution, request, ruleRow]

/-- Dispatch reinstallation is one real authored target step and therefore
inhabits the exact OSLF-derived target native type for its successor. -/
theorem normalDispatchReloadPhase_inhabits_target_native_type
    (proofOwner rule : Atom) :
    let source := normalDispatchReloadPhaseSpace proofOwner rule
    let target := fireReflectiveSourceExecFact source
      normalDispatchReloadDirective
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred := by
  dsimp only
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected
      (normalDispatchReloadPhase_selects_directive proofOwner rule))

/-- Firing the reloader over the complete verifier-owned relation restores
every rule in that relation.  The result follows from one genuine match row
per stored rule rather than from a host-side list append. -/
theorem normalDispatchReloadDirective_fires_rule
    (proofOwner rule : Atom)
    (ruleMember : rule ∈ normalDispatchReloadableRules) :
    rule ∈
      fireReflectiveSourceExecFact
        (normalDispatchReloadFullPhaseSpace proofOwner)
        normalDispatchReloadDirective := by
  let rows := (matchInputSpec []
    (readCopyAtom (normalDispatchReloadFullPhaseSpace proofOwner)
      normalDispatchReloadDirective.atom)
    normalDispatchReloadDirective.rule.input).map Prod.fst
  let substitution := normalDispatchReloadSubstitution proofOwner
    rule
  have rowMember : substitution ∈ rows := by
    simpa [rows, substitution, normalDispatchReloadDirective] using
      normalDispatchReloadFullMatchRow_mem proofOwner rule ruleMember
  have instantiates :
      instantiateTemplateAtom? substitution (.var "reload-rule") =
        some rule := by
    rfl
  have staged := reflectiveStage_add_contains_of_row rows substitution
    (.var "reload-rule") rule rowMember instantiates
  simp only [fireReflectiveSourceExecFact, applyReflectiveSinkBatch,
    normalDispatchReloadDirective, normalDispatchReloadSinks,
    reflectiveSupportSinkProvider]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr staged)

theorem normalDispatchReloadDirective_fires_last_rule
    (proofOwner : Atom) :
    normalAssertionResultCompleteRule ∈
      fireReflectiveSourceExecFact
        (normalDispatchReloadFullPhaseSpace proofOwner)
        normalDispatchReloadDirective :=
  normalDispatchReloadDirective_fires_rule proofOwner
    normalAssertionResultCompleteRule (by
      simp [normalDispatchReloadableRules])

def normalProofMachineRules : List Atom :=
  [normalHypothesisStepRule, normalAssertionStartRule,
   normalAssertionPopRule, normalAssertionBeginRule,
   normalAssertionFloatingRule, normalAssertionEssentialRule,
   normalBodyMatchConstRule, normalBodyMatchVariableRule,
   normalBodyPrefixNilRule, normalBodyPrefixConsRule,
   normalBodyMatchNilRule, normalBodyReloadRule,
   normalAssertionEssentialCompleteRule,
   normalAssertionFinishRule,
   normalDVPairBeginRule, normalDVLeftConstRule,
   normalDVLeftVariableRule, normalDVRightConstRule,
   normalDVRightVariableRule, normalDVRightNilRule,
   normalDVLeftNilRule, normalDVCompleteRule, normalDVReloadRule,
   normalBodyBuildConstRule, normalBodyBuildVariableRule,
   normalBodyBuildPrefixNilRule, normalBodyBuildPrefixConsRule,
   normalBodyBuildNilRule, normalBodyReverseConsRule,
   normalBodyReverseNilRule, normalBodyBuildReloadRule,
   normalAssertionResultCompleteRule,
   normalDispatchReloadRule, normalAcceptRule]

/-- The supported directives obtained by parsing the actual emitted normal
verifier rules.  This is derived from the target artifact rather than being a
second handwritten directive inventory. -/
def normalProofMachineDirectives : List SourceExecFact :=
  normalProofMachineRules.filterMap extractSupportedSourceExecFact

def normalProofMachineRawFacts : List RawExecFact :=
  normalProofMachineRules.filterMap extractRawExecFact

/-- Parsing loses no emitted normal-verifier rule: every rule has one
supported directive whose retained surface atom is exactly that rule. -/
theorem normalProofMachineDirectives_atoms_exact :
    normalProofMachineDirectives.map SourceExecFact.atom =
      normalProofMachineRules := by
  decide +kernel

theorem normalProofMachineRawFacts_atoms_exact :
    normalProofMachineRawFacts.map RawExecFact.atom =
      normalProofMachineRules := by
  decide +kernel

theorem normalProofMachineRawFacts_decode_exact :
    normalProofMachineRawFacts.map decodeSupportedSourceExec =
      normalProofMachineDirectives.map some := by
  decide +kernel

theorem normalProofMachineRawFact_decodes_in_directives
    {raw : RawExecFact} {directive : SourceExecFact}
    (member : raw ∈ normalProofMachineRawFacts)
    (decoded : decodeSupportedSourceExec raw = some directive) :
    directive ∈ normalProofMachineDirectives := by
  have decodedMember : some directive ∈
      normalProofMachineRawFacts.map decodeSupportedSourceExec := by
    exact List.mem_map.mpr ⟨raw, member, decoded⟩
  rw [normalProofMachineRawFacts_decode_exact] at decodedMember
  rcases List.mem_map.mp decodedMember with
    ⟨actual, actualMember, equal⟩
  exact (Option.some.inj equal) ▸ actualMember

/-- Raw-shell containment already implies supported-directive containment,
because every raw shell in the generated normal verifier decodes to the
corresponding supported directive. -/
theorem normalProofMachine_supportedWithin_of_rawWithin
    (space : List Atom)
    (rawWithin : RawExecFactsWithin normalProofMachineRawFacts space) :
    ∀ directive ∈ cSupportedSourceExecFacts space,
      directive ∈ normalProofMachineDirectives := by
  intro directive member
  rcases List.mem_filterMap.mp member with
    ⟨atom, atomMember, extracted⟩
  unfold extractSupportedSourceExecFact at extracted
  cases rawEq : extractRawExecFact atom with
  | none => simp [rawEq] at extracted
  | some raw =>
      simp [rawEq] at extracted
      have rawMember : raw ∈ cRawExecFacts space :=
        List.mem_filterMap.mpr ⟨atom, atomMember, rawEq⟩
      exact normalProofMachineRawFact_decodes_in_directives
        (rawWithin raw rawMember) extracted

/-- The complete emitted normal verifier has one directive per scheduling
key.  Any reachable subset therefore inherits scheduler-key uniqueness. -/
theorem normalProofMachineDirectives_key_injective :
    KeyInjective normalProofMachineDirectives := by
  intro left right leftMember rightMember keysEqual
  exact List.inj_on_of_nodup_map
    (l := normalProofMachineDirectives)
    (f := fun directive => SchedulerKey.key directive)
    (by decide +kernel) leftMember rightMember keysEqual

theorem normalProofMachineRawFacts_key_injective :
    KeyInjective normalProofMachineRawFacts := by
  intro left right leftMember rightMember keysEqual
  exact List.inj_on_of_nodup_map
    (l := normalProofMachineRawFacts)
    (f := fun raw => SchedulerKey.key raw)
    (by decide +kernel) leftMember rightMember keysEqual

/-- Any reachable candidate list drawn from the emitted normal verifier
inherits scheduler-key uniqueness from the complete artifact. -/
theorem normalProofMachineDirectiveSubset_key_injective
    (directives : List SourceExecFact)
    (subset : ∀ directive ∈ directives,
      directive ∈ normalProofMachineDirectives) :
    KeyInjective directives := by
  intro left right leftMember rightMember keysEqual
  exact normalProofMachineDirectives_key_injective left right
    (subset left leftMember) (subset right rightMember) keysEqual

theorem normalProofMachineRawSubset_key_injective
    (facts : List RawExecFact)
    (subset : ∀ fact ∈ facts, fact ∈ normalProofMachineRawFacts) :
    KeyInjective facts := by
  intro left right leftMember rightMember keysEqual
  exact normalProofMachineRawFacts_key_injective left right
    (subset left leftMember) (subset right rightMember) keysEqual

/-- Every supported directive parsed from the emitted normal verifier lies in
the add/remove-only sink fragment.  Consequently matcher enumeration order is
not an observable of any normal-verifier firing. -/
theorem normalProofMachineDirectives_all_support_set :
    normalProofMachineDirectives.all (fun directive =>
      directive.rule.tmpl.sinks.all reflectiveSupportSetSinkB) = true := by
  decide +kernel

theorem normalProofMachineDirective_support_set
    {directive : SourceExecFact}
    (member : directive ∈ normalProofMachineDirectives) :
    ReflectiveSupportSetTemplate directive.rule.tmpl := by
  apply (all_reflectiveSupportSetSinkB_eq_true_iff directive.rule.tmpl).1
  exact (List.all_eq_true.mp
    normalProofMachineDirectives_all_support_set) directive member

/-- A concrete space whose executable facts are drawn from the emitted normal
verifier satisfies the full list-to-support realization invariant.  The
remaining whole-run proof must show that these membership and duplicate-free
conditions are preserved by every actual transition. -/
theorem normalProofMachine_reflective_invariant
    (space : List Atom)
    (nodup : space.Nodup)
    (supportedSubset : ∀ directive ∈ cSupportedSourceExecFacts space,
      directive ∈ normalProofMachineDirectives)
    (rawSubset : ∀ raw ∈ cRawExecFacts space,
      raw ∈ normalProofMachineRawFacts) :
    ReflectiveWorkQueueInvariant space := by
  apply reflectiveWorkQueueInvariant_of_supportSet space nodup
    (normalProofMachineDirectiveSubset_key_injective _ supportedSubset)
    (normalProofMachineRawSubset_key_injective _ rawSubset)
  · intro directive selected
    exact normalProofMachineDirective_support_set
      (supportedSubset directive (selectNextScheduled_mem selected))
  · intro raw directive selected decoded
    exact normalProofMachineDirective_support_set
      (normalProofMachineRawFact_decodes_in_directives
        (rawSubset raw (selectNextScheduled_mem selected)) decoded)

theorem normalProofMachine_reflective_invariant_of_rawWithin
    (space : List Atom)
    (nodup : space.Nodup)
    (rawWithin : RawExecFactsWithin normalProofMachineRawFacts space) :
    ReflectiveWorkQueueInvariant space :=
  normalProofMachine_reflective_invariant space nodup
    (normalProofMachine_supportedWithin_of_rawWithin space rawWithin)
    rawWithin

/-- Decidable replay certificate for one concrete normal-verifier state.  It
checks duplicate freedom and that every supported/raw executable fact belongs
to the parsed generic verifier artifact. -/
def normalProofMachineInvariantCheck (space : List Atom) : Bool :=
  decide space.Nodup &&
    (cSupportedSourceExecFacts space).all (fun directive =>
      decide (directive ∈ normalProofMachineDirectives)) &&
    (cRawExecFacts space).all (fun raw =>
      decide (raw ∈ normalProofMachineRawFacts))

theorem normalProofMachineInvariantCheck_sound
    {space : List Atom}
    (accepted : normalProofMachineInvariantCheck space = true) :
    ReflectiveWorkQueueInvariant space := by
  simp only [normalProofMachineInvariantCheck, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at accepted
  exact normalProofMachine_reflective_invariant space accepted.1.1
    accepted.1.2 accepted.2

/-! ## Structural closure of arbitrary normal-machine runs -/

/-- The minimal structural state needed by the executable-to-authored proof.
All supported-directive, key-injectivity, and matcher-agreement obligations
are derived from these two fields. -/
def NormalProofMachineState (space : List Atom) : Prop :=
  space.Nodup ∧ RawExecFactsWithin normalProofMachineRawFacts space

theorem NormalProofMachineState.reflectiveInvariant
    {space : List Atom} (state : NormalProofMachineState space) :
    ReflectiveWorkQueueInvariant space :=
  normalProofMachine_reflective_invariant_of_rawWithin space
    state.1 state.2

/-- The sole code-origin obligation left for one state: every executable atom
instantiated by the selected directive's add sinks belongs to the parsed
generic verifier artifact. -/
def NormalProofMachineAdditionsClosed (space : List Atom) : Prop :=
  ∀ directive,
    selectNextScheduled (cSupportedSourceExecFacts space) = some directive →
    let rows := (Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom)
      directive.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      directive.rule.tmpl

theorem NormalProofMachineState.fire
    {space : List Atom} (state : NormalProofMachineState space)
    (directive : SourceExecFact)
    (directiveMember : directive ∈ normalProofMachineDirectives)
    (addedWithin :
      ReflectiveAddedRawWithin normalProofMachineRawFacts
        ((Conformance.Computable.cmatchInputSpec []
          (directive.atom :: space.erase directive.atom)
          directive.rule.input).map Prod.fst)
        directive.rule.tmpl) :
    NormalProofMachineState
      (cFireReflectiveSourceExecFact space directive) := by
  have supported := normalProofMachineDirective_support_set directiveMember
  exact ⟨cFireReflectiveSourceExecFact_nodup space directive supported state.1,
    cFireReflectiveSourceExecFact_rawExecFactsWithin
      normalProofMachineRawFacts space directive supported state.2
      addedWithin⟩

/-- A concrete scheduler step preserves the minimal state exactly when its
actual additions satisfy the explicit code-origin obligation. -/
theorem NormalProofMachineState.step
    {space target : List Atom}
    (state : NormalProofMachineState space)
    (closed : NormalProofMachineAdditionsClosed space)
    (moved : cReflectiveSourceWorkQueueStep .leaveInert space = some target) :
    NormalProofMachineState target := by
  unfold cReflectiveSourceWorkQueueStep at moved
  cases selected : selectNextScheduled (cSupportedSourceExecFacts space) with
  | none => simp [selected] at moved
  | some directive =>
      simp only [selected] at moved
      have targetEq : cFireReflectiveSourceExecFact space directive = target :=
        Option.some.inj moved
      subst target
      apply state.fire directive
      · exact normalProofMachine_supportedWithin_of_rawWithin space state.2
          directive (selectNextScheduled_mem selected)
      · exact closed directive selected

/-- Code-origin closure along the states actually reachable from one admitted
source.  The weaker `NormalProofMachineState` deliberately does not claim that
arbitrary hostile spaces are closed: verifier-owned inert rule rows must be
established separately at the admitted entry boundary. -/
def NormalProofMachineClosedFrom (fuel : Nat) (source : List Atom) : Prop :=
  ∀ residual,
    CReflectiveReachable .leaveInert fuel source residual →
    NormalProofMachineAdditionsClosed residual

/-! The raw-exec whitelist is necessary but intentionally not sufficient.
An adversary who can forge verifier-internal inert rows can feed arbitrary
code to the legitimate dispatch reloader.  This concrete negative control
prevents later proofs from silently treating the minimal state as an admitted
entry state. -/

private def forgedNormalExec : Atom :=
  .expression
    [.symbol "exec", .expression [.symbol "999", .symbol "forged"],
      .expression [.symbol ","], .expression [.symbol "O"]]

private def forgedNormalExecRaw : RawExecFact where
  atom := forgedNormalExec
  loc := .expression [.symbol "999", .symbol "forged"]
  inputExpr := .expression [.symbol ","]
  templateExpr := .expression [.symbol "O"]

private def forgedNormalReloadSpace : List Atom :=
  [normalDispatchReloadRule,
   .expression [.symbol "mm-reload-normal-dispatch",
     .symbol "forged-proof"],
   normalDispatchRuleRow forgedNormalExec]

private theorem forgedNormalExec_extracts :
    extractRawExecFact forgedNormalExec = some forgedNormalExecRaw := by
  rfl

private theorem forgedNormalExec_not_authorized :
    forgedNormalExecRaw ∉ normalProofMachineRawFacts := by
  decide +kernel

private theorem forgedNormalReload_selects :
    selectNextScheduled
        (cSupportedSourceExecFacts forgedNormalReloadSpace) =
      some normalDispatchReloadDirective := by
  decide +kernel

private theorem forgedNormalReload_row_mem :
    normalDispatchReloadSubstitution (.symbol "forged-proof")
        forgedNormalExec ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          forgedNormalReloadSpace.erase normalDispatchReloadDirective.atom)
        normalDispatchReloadDirective.rule.input).map Prod.fst := by
  decide +kernel

/-- The weak structural state admits this hostile row, but its selected
reloader can add an executable atom outside the verifier artifact. -/
theorem forged_internal_reload_refutes_minimal_global_closure :
    ¬ NormalProofMachineAdditionsClosed forgedNormalReloadSpace := by
  intro closed
  have addedWithin := closed normalDispatchReloadDirective
    forgedNormalReload_selects
  have added : ReflectiveAddedAtom
      ((Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          forgedNormalReloadSpace.erase normalDispatchReloadDirective.atom)
        normalDispatchReloadDirective.rule.input).map Prod.fst)
      normalDispatchReloadDirective.rule.tmpl.sinks forgedNormalExec := by
    refine ⟨.add (.var "reload-rule"), ?_, .var "reload-rule", rfl,
      normalDispatchReloadSubstitution (.symbol "forged-proof")
        forgedNormalExec, forgedNormalReload_row_mem, ?_⟩
    · simp [normalDispatchReloadDirective, normalDispatchReloadSinks,
        mkTemplate]
    · rfl
  exact forgedNormalExec_not_authorized
    (addedWithin forgedNormalExec added forgedNormalExecRaw
      forgedNormalExec_extracts)

theorem NormalProofMachineState.of_reachable
    {fuel : Nat} {source target : List Atom}
    (initial : NormalProofMachineState source)
    (closedFrom : NormalProofMachineClosedFrom fuel source)
    (reachable : CReflectiveReachable .leaveInert fuel source target) :
    NormalProofMachineState target := by
  induction reachable with
  | refl => exact initial
  | step moved tail induction =>
      have middleState := initial.step (closedFrom _ .refl) moved
      apply induction middleState
      intro residual residualReachable
      exact closedFrom residual (.step moved residualReachable)

/-- Source-relative code-origin closure upgrades one bounded concrete
normal-machine run to a proof-relevant trace in the authored support-valued
MM2 GSLT. -/
def normalProofMachineAdequateTrace_of_closedFrom
    (fuel : Nat) (source : List Atom)
    (initial : NormalProofMachineState source)
    (closedFrom : NormalProofMachineClosedFrom fuel source) :
    CReflectiveAdequateTrace .leaveInert fuel source
      (cReflectiveSourceWorkQueueRunN .leaveInert fuel source).1 :=
  cReflectiveSourceWorkQueueRunN_adequateTrace .leaveInert fuel source
    (fun _ reachable =>
      (initial.of_reachable closedFrom reachable).reflectiveInvariant)

/-- Verifier-owned inert data used to capture variable-bearing executable
code before reinstallation.  These rows are part of the generic verifier,
never part of source event input. -/
def normalVerifierInternalRows : List Atom :=
  [normalBodyMatchRuleBundle, normalDVRuleBundle,
    normalBodyBuildRuleBundle] ++
    normalDispatchRuleRows

/-- Any inert atom whose head marks it as verifier-owned code must be one of
the exact rows emitted by the generic verifier transformation. -/
def NormalVerifierInternalRowIntact (atom : Atom) : Prop :=
  isVerifierOwnedInternalRowShape atom = true →
    atom ∈ normalVerifierInternalRows

def NormalVerifierInternalRowsIntact (space : List Atom) : Prop :=
  AtomsWithin NormalVerifierInternalRowIntact space

theorem normalVerifierInternalRows_intact :
    NormalVerifierInternalRowsIntact normalVerifierInternalRows := by
  unfold NormalVerifierInternalRowsIntact AtomsWithin
  intro atom member
  unfold NormalVerifierInternalRowIntact
  intro _
  exact member

/-- The structural state used by the assembled verifier proof: executable
shells come from the generated rule inventory, and every inert carrier capable
of reinstalling code is one of the exact rows owned by that verifier. -/
def NormalProofMachineOwnedState (space : List Atom) : Prop :=
  NormalProofMachineState space ∧ NormalVerifierInternalRowsIntact space

/-- The additions made by the selected directive preserve both halves of the
owned state.  This is a local semantic obligation on the actual matched rows,
not a syntactic promise attached to a rule name. -/
def NormalProofMachineOwnedAdditionsClosed (space : List Atom) : Prop :=
  ∀ directive,
    selectNextScheduled (cSupportedSourceExecFacts space) = some directive →
    let rows := (Conformance.Computable.cmatchInputSpec []
      (directive.atom :: space.erase directive.atom)
      directive.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
        directive.rule.tmpl ∧
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact rows
        directive.rule.tmpl

/-! ## Matcher-backed origin of reflectively reloaded code -/

/-- In a three-factor compatible input, every returned substitution records
an actual witness for the final factor.  Keeping this witness is essential
when the final factor is a verifier-owned row whose payload is later emitted
as executable code. -/
private theorem cmatchInputSpec_three_last_witness
    {space : List Atom} {first second third : Atom}
    {substitution : Subst}
    (member : substitution ∈
      (Conformance.Computable.cmatchInputSpec [] space
        (.compat (mkPattern [first, second, third]))).map Prod.fst) :
    ∃ before atom,
      atom ∈ space ∧
        Conformance.Computable.cmatchAtom before third atom =
          some substitution := by
  rw [List.mem_map] at member
  obtain ⟨⟨found, witnesses⟩, foundMember, foundEq⟩ := member
  change found = substitution at foundEq
  subst substitution
  simp only [Conformance.Computable.cmatchInputSpec, mkPattern,
    Conformance.Computable.cmatchPattern,
    Conformance.Computable.cmatchPattern.go, List.mem_flatMap] at foundMember
  obtain ⟨⟨afterFirst, firstAtom⟩, _firstMatch,
    afterFirstMember⟩ := foundMember
  obtain ⟨⟨afterSecond, secondAtom⟩, _secondMatch,
    afterSecondMember⟩ := afterFirstMember
  obtain ⟨⟨afterThird, thirdAtom⟩, thirdMatch,
    finished⟩ := afterSecondMember
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  rcases finished with ⟨substEq, _witnessEq⟩
  subst afterThird
  refine ⟨afterSecond, thirdAtom, ?_, ?_⟩
  · rw [List.mem_filterMap] at thirdMatch
    obtain ⟨candidate, candidateMember, candidateMatch⟩ := thirdMatch
    simp only [Option.map_eq_some_iff] at candidateMatch
    obtain ⟨candidateSubst, _matched, pairEq⟩ := candidateMatch
    cases pairEq
    exact candidateMember
  · rw [List.mem_filterMap] at thirdMatch
    obtain ⟨candidate, _candidateMember, candidateMatch⟩ := thirdMatch
    simp only [Option.map_eq_some_iff] at candidateMatch
    obtain ⟨candidateSubst, matched, pairEq⟩ := candidateMatch
    cases pairEq
    exact matched

/-- The same three-factor match retains the whole substitution chain.  This
lets later factors be proved not to alter opaque values captured by the first
factor. -/
private theorem cmatchInputSpec_three_match_chain
    {space : List Atom} {first second third : Atom}
    {substitution : Subst}
    (member : substitution ∈
      (Conformance.Computable.cmatchInputSpec [] space
        (.compat (mkPattern [first, second, third]))).map Prod.fst) :
    ∃ afterFirst afterSecond firstAtom secondAtom thirdAtom,
      firstAtom ∈ space ∧ secondAtom ∈ space ∧ thirdAtom ∈ space ∧
        Conformance.Computable.cmatchAtom [] first firstAtom =
          some afterFirst ∧
        Conformance.Computable.cmatchAtom afterFirst second secondAtom =
          some afterSecond ∧
        Conformance.Computable.cmatchAtom afterSecond third thirdAtom =
          some substitution := by
  rw [List.mem_map] at member
  obtain ⟨⟨found, witnesses⟩, foundMember, foundEq⟩ := member
  change found = substitution at foundEq
  subst substitution
  simp only [Conformance.Computable.cmatchInputSpec, mkPattern,
    Conformance.Computable.cmatchPattern,
    Conformance.Computable.cmatchPattern.go, List.mem_flatMap] at foundMember
  obtain ⟨⟨afterFirst, firstAtom⟩, firstMatch,
    afterFirstMember⟩ := foundMember
  obtain ⟨⟨afterSecond, secondAtom⟩, secondMatch,
    afterSecondMember⟩ := afterFirstMember
  obtain ⟨⟨afterThird, thirdAtom⟩, thirdMatch,
    finished⟩ := afterSecondMember
  simp only [List.mem_singleton, Prod.mk.injEq] at finished
  rcases finished with ⟨substEq, _witnessEq⟩
  subst afterThird
  rw [List.mem_filterMap] at firstMatch secondMatch thirdMatch
  obtain ⟨firstCandidate, firstMember, firstResult⟩ := firstMatch
  obtain ⟨secondCandidate, secondMember, secondResult⟩ := secondMatch
  obtain ⟨thirdCandidate, thirdMember, thirdResult⟩ := thirdMatch
  simp only [Option.map_eq_some_iff] at firstResult secondResult thirdResult
  obtain ⟨firstSubst, firstMatched, firstEq⟩ := firstResult
  obtain ⟨secondSubst, secondMatched, secondEq⟩ := secondResult
  obtain ⟨thirdSubst, thirdMatched, thirdEq⟩ := thirdResult
  cases firstEq
  cases secondEq
  cases thirdEq
  exact ⟨afterFirst, afterSecond, firstAtom, secondAtom, thirdAtom,
    firstMember, secondMember, thirdMember,
    firstMatched, secondMatched, thirdMatched⟩

/-- Matching a two-cell tagged row recovers both the concrete payload and its
binding, even when the payload itself contains expression-local variables. -/
private theorem matchAtom_tagged_row_payload
    {substitution result : Subst} {atom : Atom} {tag variableName : String}
    (matched : matchAtom substitution
      (.expression [.symbol tag, .var variableName]) atom = some result) :
    ∃ payload,
      atom = .expression [.symbol tag, payload] ∧
        result.lookup variableName = some payload := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons head tail =>
      cases head
      cases tail with
      | expr_cons payloadMatch nilMatch =>
          cases payloadMatch with
          | var_fresh _ =>
              cases nilMatch
              refine ⟨_, rfl, ?_⟩
              simp [Subst.lookup]
          | var_bound lookup =>
              cases nilMatch
              exact ⟨_, rfl, lookup⟩

/-- Matching the dispatch reloader's executable shell recovers its opaque
input and output byte expressions without requiring those captured values to
be structurally ground. -/
private theorem matchAtom_dispatch_reload_shell
    {result : Subst} {atom : Atom}
    (matched : matchAtom [] normalDispatchReloadSelfTemplate atom =
      some result) :
    ∃ input output,
      atom = .expression
        [.symbol "exec", normalDispatchReloadLocation, input, output] ∧
        result.lookup "reload-self-input" = some input ∧
        result.lookup "reload-self-output" = some output := by
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons execMatch tail1 =>
      cases execMatch
      cases tail1 with
      | expr_cons locationMatch tail2 =>
          cases locationMatch with
          | expr_cons locationHead locationTail =>
              cases locationHead
              cases locationTail with
              | expr_cons locationName locationNil =>
                  cases locationName
                  cases locationNil
                  cases tail2 with
                  | expr_cons inputMatch tail3 =>
                      cases inputMatch with
                      | var_fresh _ =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  refine ⟨_, _, rfl, ?_, ?_⟩
                                  · simp [Subst.lookup]
                                  · simp [Subst.lookup]
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, by simp [Subst.lookup],
                                    outputLookup⟩
                      | var_bound inputLookup =>
                          cases tail3 with
                          | expr_cons outputMatch nilMatch =>
                              cases outputMatch with
                              | var_fresh _ =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    by simp [Subst.lookup]⟩
                              | var_bound outputLookup =>
                                  cases nilMatch
                                  exact ⟨_, _, rfl, inputLookup,
                                    outputLookup⟩

/-- Reinstalling the dispatch reloader preserves any ambient executable
inventory that already contains both the live space and the selected shell. -/
theorem normalDispatchReload_captured_self_raw_within
    {allowed : List RawExecFact}
    {space : List Atom} {substitution : Subst} {captured : Atom}
    {raw : RawExecFact}
    (rawWithin : RawExecFactsWithin allowed space)
    (selectedWithin : ∀ selectedRaw,
      extractRawExecFact normalDispatchReloadDirective.atom =
        some selectedRaw → selectedRaw ∈ allowed)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          space.erase normalDispatchReloadDirective.atom)
        normalDispatchReloadDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution
          normalDispatchReloadSelfTemplate = some captured)
    (extracts : extractRawExecFact captured = some raw) :
    raw ∈ allowed := by
  have rowMember' : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          space.erase normalDispatchReloadDirective.atom)
        (.compat (mkPattern
          [normalDispatchReloadSelfTemplate,
           normalDispatchReloadTriggerTemplate,
           normalDispatchReloadRuleTemplate]))).map Prod.fst := by
    simpa [normalDispatchReloadDirective, normalDispatchReloadPatternAtoms]
      using rowMember
  obtain ⟨afterFirst, afterSecond, firstAtom, secondAtom, thirdAtom,
      firstMember, _secondMember, _thirdMember,
      firstMatched, secondMatched, thirdMatched⟩ :=
    cmatchInputSpec_three_match_chain rowMember'
  rw [Conformance.cmatchAtom_eq_matchAtom] at firstMatched secondMatched
  rw [Conformance.cmatchAtom_eq_matchAtom] at thirdMatched
  obtain ⟨input, output, firstEq, inputLookup, outputLookup⟩ :=
    matchAtom_dispatch_reload_shell firstMatched
  have finalExtends : substitution.lookupExtends afterFirst :=
    Subst.lookupExtends_trans
      (matchAtom_lookupExtends secondMatched)
      (matchAtom_lookupExtends thirdMatched)
  have finalInputLookup : substitution.lookup "reload-self-input" =
      some input :=
    finalExtends "reload-self-input" input inputLookup
  have finalOutputLookup : substitution.lookup "reload-self-output" =
      some output :=
    finalExtends "reload-self-output" output outputLookup
  have instantiationFacts :
      templateCovered substitution normalDispatchReloadSelfTemplate = true ∧
        applySubst substitution normalDispatchReloadSelfTemplate = captured := by
    simpa [instantiateTemplateAtom?] using instantiates
  have appliedEq :
      applySubst substitution normalDispatchReloadSelfTemplate = captured :=
    instantiationFacts.2
  have appliedFirst :
      applySubst substitution normalDispatchReloadSelfTemplate = firstAtom := by
    rw [firstEq]
    change Atom.expression
      [.symbol "exec", normalDispatchReloadLocation,
        (substitution.lookup "reload-self-input").getD
          (.var "reload-self-input"),
        (substitution.lookup "reload-self-output").getD
          (.var "reload-self-output")] =
      Atom.expression
        [.symbol "exec", normalDispatchReloadLocation, input, output]
    rw [finalInputLookup, finalOutputLookup]
    rfl
  have capturedEq : captured = firstAtom := by
    exact appliedEq.symm.trans appliedFirst
  rw [capturedEq] at extracts
  rcases List.mem_cons.mp firstMember with selected | prior
  · rw [selected] at extracts
    exact selectedWithin raw extracts
  · apply rawWithin raw
    exact List.mem_filterMap.mpr
      ⟨firstAtom, List.mem_of_mem_erase prior, extracts⟩

/-- Normal-only code origin is the exact-inventory instance of the ambient
self-shell theorem. -/
theorem normalDispatchReload_captured_self_raw_authorized
    {space : List Atom} {substitution : Subst} {captured : Atom}
    {raw : RawExecFact}
    (state : NormalProofMachineOwnedState space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          space.erase normalDispatchReloadDirective.atom)
        normalDispatchReloadDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution
          normalDispatchReloadSelfTemplate = some captured)
    (extracts : extractRawExecFact captured = some raw) :
    raw ∈ normalProofMachineRawFacts := by
  exact normalDispatchReload_captured_self_raw_within state.1.2
    (fun selectedRaw selectedExtract =>
      List.mem_filterMap.mpr
        ⟨normalDispatchReloadDirective.atom,
          by simp [normalProofMachineRules, normalDispatchReloadDirective],
          selectedExtract⟩)
    rowMember instantiates extracts

/-- The dispatch reloader can emit only a rule recovered from the exact
verifier-owned dispatch relation.  This is the symbolic dual of the hostile
row counterexample above: ownership, not a suggestive row name, authorizes the
captured executable payload. -/
theorem normalDispatchReload_captured_rule_authorized_of_internal
    {space : List Atom} {substitution : Subst} {captured : Atom}
    (internal : NormalVerifierInternalRowsIntact space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          space.erase normalDispatchReloadDirective.atom)
        normalDispatchReloadDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution (.var "reload-rule") =
        some captured) :
    captured ∈ normalProofMachineRules := by
  have rowMember' : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          space.erase normalDispatchReloadDirective.atom)
        (.compat (mkPattern
          [normalDispatchReloadSelfTemplate,
           normalDispatchReloadTriggerTemplate,
           normalDispatchReloadRuleTemplate]))).map Prod.fst := by
    simpa [normalDispatchReloadDirective, normalDispatchReloadPatternAtoms]
      using rowMember
  obtain ⟨before, witness, witnessMember, matched⟩ :=
    cmatchInputSpec_three_last_witness rowMember'
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  obtain ⟨payload, witnessEq, payloadLookup⟩ :=
    matchAtom_tagged_row_payload matched
  have capturedEq : captured = payload := by
    simp [instantiateTemplateAtom?, templateCovered, applySubst,
      payloadLookup] at instantiates
    exact instantiates.symm
  subst captured
  have witnessInSpace : witness ∈ space := by
    rcases List.mem_cons.mp witnessMember with equal | erased
    · rw [witnessEq] at equal
      simp [normalDispatchReloadDirective, normalDispatchReloadRule] at equal
    · exact List.mem_of_mem_erase erased
  have authorizedRow := internal witness witnessInSpace
  have protectedShape : isVerifierOwnedInternalRowShape witness = true := by
    rw [witnessEq]
    rfl
  have authorized := authorizedRow protectedShape
  rw [witnessEq] at authorized
  have payloadMember : payload ∈ normalDispatchReloadableRules := by
    simpa [normalVerifierInternalRows, normalDispatchRuleRows,
      normalDispatchRuleRow, normalBodyMatchRuleBundle, normalDVRuleBundle,
      normalBodyBuildRuleBundle] using authorized
  change payload ∈
    normalDispatchReloadableRules ++
      [normalDispatchReloadRule, normalAcceptRule]
  exact List.mem_append_left _ payloadMember

theorem normalDispatchReload_captured_rule_authorized
    {space : List Atom} {substitution : Subst} {captured : Atom}
    (state : NormalProofMachineOwnedState space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          space.erase normalDispatchReloadDirective.atom)
        normalDispatchReloadDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution (.var "reload-rule") =
        some captured) :
    captured ∈ normalProofMachineRules :=
  normalDispatchReload_captured_rule_authorized_of_internal state.2
    rowMember instantiates

/-- Consequently, any captured dispatch payload which parses as executable
belongs to the exact raw-executable inventory generated for the verifier. -/
theorem normalDispatchReload_captured_raw_authorized
    {space : List Atom} {substitution : Subst} {captured : Atom}
    {raw : RawExecFact}
    (state : NormalProofMachineOwnedState space)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalDispatchReloadDirective.atom ::
          space.erase normalDispatchReloadDirective.atom)
        normalDispatchReloadDirective.rule.input).map Prod.fst)
    (instantiates :
      instantiateTemplateAtom? substitution (.var "reload-rule") =
        some captured)
    (extracts : extractRawExecFact captured = some raw) :
    raw ∈ normalProofMachineRawFacts := by
  exact List.mem_filterMap.mpr
    ⟨captured,
      normalDispatchReload_captured_rule_authorized state rowMember
      instantiates,
      extracts⟩

/-- Ambient-inventory dispatch closure: the persistent self shell is inherited
from the selected/live space, while a variable payload is reconstructed from
the exact verifier-owned dispatch relation. -/
theorem normalDispatchReload_additions_raw_within
    (allowed : List RawExecFact)
    {space : List Atom}
    (rawWithin : RawExecFactsWithin allowed space)
    (internal : NormalVerifierInternalRowsIntact space)
    (selectedWithin : ∀ selectedRaw,
      extractRawExecFact normalDispatchReloadDirective.atom =
        some selectedRaw → selectedRaw ∈ allowed)
    (normalWithin : ∀ normalRaw ∈ normalProofMachineRawFacts,
      normalRaw ∈ allowed) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDispatchReloadDirective.atom ::
        space.erase normalDispatchReloadDirective.atom)
      normalDispatchReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin allowed rows
      normalDispatchReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  have authoredCases :
      authored = normalDispatchReloadSelfTemplate ∨
        authored = .var "reload-rule" := by
    simpa [normalDispatchReloadDirective, normalDispatchReloadSinks,
      mkTemplate] using sinkMember
  cases authoredCases with
  | inl selfSink =>
    rw [selfSink] at instantiates
    exact normalDispatchReload_captured_self_raw_within rawWithin
      selectedWithin rowMember instantiates extracts
  | inr ruleSink =>
    rw [ruleSink] at instantiates
    apply normalWithin raw
    exact List.mem_filterMap.mpr
      ⟨atom,
        normalDispatchReload_captured_rule_authorized_of_internal internal
          rowMember instantiates,
        extracts⟩

/-- Every executable atom introduced by the dispatch reloader is authorized:
the self shell comes from an existing executable witness, and the variable
payload comes from an exact verifier-owned dispatch row. -/
theorem normalDispatchReload_additions_raw_closed
    {space : List Atom} (state : NormalProofMachineOwnedState space) :
    let rows := (Conformance.Computable.cmatchInputSpec []
      (normalDispatchReloadDirective.atom ::
        space.erase normalDispatchReloadDirective.atom)
      normalDispatchReloadDirective.rule.input).map Prod.fst
    ReflectiveAddedRawWithin normalProofMachineRawFacts rows
      normalDispatchReloadDirective.rule.tmpl := by
  dsimp only
  intro atom added raw extracts
  rcases added with
    ⟨sink, sinkMember, authored, sinkEq,
      substitution, rowMember, instantiates⟩
  subst sink
  have authoredCases :
      authored = normalDispatchReloadSelfTemplate ∨
        authored = .var "reload-rule" := by
    simpa [normalDispatchReloadDirective, normalDispatchReloadSinks,
      mkTemplate] using sinkMember
  cases authoredCases with
  | inl selfSink =>
    rw [selfSink] at instantiates
    exact normalDispatchReload_captured_self_raw_authorized state rowMember
      instantiates extracts
  | inr ruleSink =>
    rw [ruleSink] at instantiates
    exact normalDispatchReload_captured_raw_authorized state rowMember
      instantiates extracts

theorem NormalProofMachineOwnedState.fire
    {space : List Atom} (state : NormalProofMachineOwnedState space)
    (directive : SourceExecFact)
    (directiveMember : directive ∈ normalProofMachineDirectives)
    (addedRawWithin :
      ReflectiveAddedRawWithin normalProofMachineRawFacts
        ((Conformance.Computable.cmatchInputSpec []
          (directive.atom :: space.erase directive.atom)
          directive.rule.input).map Prod.fst)
        directive.rule.tmpl)
    (addedInternalWithin :
      ReflectiveAddedAtomsWithin NormalVerifierInternalRowIntact
        ((Conformance.Computable.cmatchInputSpec []
          (directive.atom :: space.erase directive.atom)
          directive.rule.input).map Prod.fst)
        directive.rule.tmpl) :
    NormalProofMachineOwnedState
      (cFireReflectiveSourceExecFact space directive) := by
  have supported := normalProofMachineDirective_support_set directiveMember
  exact ⟨state.1.fire directive directiveMember addedRawWithin,
    cFireReflectiveSourceExecFact_atomsWithin
      NormalVerifierInternalRowIntact space directive supported state.2
        addedInternalWithin⟩

/-- One scheduler-selected step preserves verifier code ownership whenever the
selected rule's concrete additions satisfy the two explicit origin checks. -/
theorem NormalProofMachineOwnedState.step
    {space target : List Atom}
    (state : NormalProofMachineOwnedState space)
    (closed : NormalProofMachineOwnedAdditionsClosed space)
    (moved : cReflectiveSourceWorkQueueStep .leaveInert space = some target) :
    NormalProofMachineOwnedState target := by
  unfold cReflectiveSourceWorkQueueStep at moved
  cases selected : selectNextScheduled (cSupportedSourceExecFacts space) with
  | none => simp [selected] at moved
  | some directive =>
      simp only [selected] at moved
      have targetEq : cFireReflectiveSourceExecFact space directive = target :=
        Option.some.inj moved
      subst target
      rcases closed directive selected with ⟨rawClosed, internalClosed⟩
      exact state.fire directive
        (normalProofMachine_supportedWithin_of_rawWithin space state.1.2
          directive (selectNextScheduled_mem selected))
        rawClosed internalClosed

/-- Source-relative closure for the strong assembled-machine invariant. -/
def NormalProofMachineOwnedClosedFrom (fuel : Nat)
    (source : List Atom) : Prop :=
  ∀ residual,
    CReflectiveReachable .leaveInert fuel source residual →
    NormalProofMachineOwnedAdditionsClosed residual

theorem NormalProofMachineOwnedState.of_reachable
    {fuel : Nat} {source target : List Atom}
    (initial : NormalProofMachineOwnedState source)
    (closedFrom : NormalProofMachineOwnedClosedFrom fuel source)
    (reachable : CReflectiveReachable .leaveInert fuel source target) :
    NormalProofMachineOwnedState target := by
  induction reachable with
  | refl => exact initial
  | step moved tail induction =>
      have middleState := initial.step (closedFrom _ .refl) moved
      apply induction middleState
      intro residual residualReachable
      exact closedFrom residual (.step moved residualReachable)

/-- A source-relative proof of both executable origin and protected-row
ownership constructs an authored-MM2 adequacy trace for the whole bounded run.
This is the scalable theorem used by symbolic assembled-machine inductions. -/
def normalProofMachineOwnedAdequateTrace_of_closedFrom
    (fuel : Nat) (source : List Atom)
    (initial : NormalProofMachineOwnedState source)
    (closedFrom : NormalProofMachineOwnedClosedFrom fuel source) :
    CReflectiveAdequateTrace .leaveInert fuel source
      (cReflectiveSourceWorkQueueRunN .leaveInert fuel source).1 :=
  cReflectiveSourceWorkQueueRunN_adequateTrace .leaveInert fuel source
    (fun _ reachable =>
      (initial.of_reachable closedFrom reachable).1.reflectiveInvariant)

private def normalDispatchReloadRawFact : RawExecFact where
  atom := normalDispatchReloadRule
  loc := normalDispatchReloadLocation
  inputExpr := normalDispatchReloadInput
  templateExpr := normalDispatchReloadOutput

private theorem normalDispatchReloadRawFact_authorized :
    normalDispatchReloadRawFact ∈ normalProofMachineRawFacts := by
  decide +kernel

private theorem forgedNormalReloadSpace_minimal_state :
    NormalProofMachineState forgedNormalReloadSpace := by
  constructor
  · decide +kernel
  · intro raw member
    have equal : raw = normalDispatchReloadRawFact := by
      simpa [cRawExecFacts, forgedNormalReloadSpace,
        normalDispatchReloadRawFact, normalDispatchReloadRule,
        normalDispatchRuleRow, extractRawExecFact] using member
    exact equal ▸ normalDispatchReloadRawFact_authorized

/-- The hostile reload carrier passes the raw-executable whitelist but fails
the verifier-owned-row invariant.  This separates the strong admission state
from the deliberately minimal execution state. -/
theorem forged_internal_reload_refutes_owned_state :
    ¬ NormalProofMachineOwnedState forgedNormalReloadSpace := by
  intro state
  have intact := state.2 (normalDispatchRuleRow forgedNormalExec)
    (by simp [forgedNormalReloadSpace])
  have internalShape :
      isVerifierOwnedInternalRowShape
          (normalDispatchRuleRow forgedNormalExec) = true := by
    rfl
  have authorized := intact internalShape
  have notAuthorized :
      normalDispatchRuleRow forgedNormalExec ∉ normalVerifierInternalRows := by
    decide +kernel
  exact notAuthorized authorized

/-- The negative example genuinely isolates the missing ownership half: its
minimal structural state is valid even though its strong state is not. -/
theorem forged_internal_reload_minimal_but_not_owned :
    NormalProofMachineState forgedNormalReloadSpace ∧
      ¬ NormalProofMachineOwnedState forgedNormalReloadSpace :=
  ⟨forgedNormalReloadSpace_minimal_state,
    forged_internal_reload_refutes_owned_state⟩

def normalAssertionReloadRules : List Atom :=
  normalDispatchReloadableRules

/-- Reload-control bindings are hygienically disjoint from the code they
reinsert.  This prevents outer MM2 substitution from specializing or
corrupting the expression-local variables of a nested `exec`. -/
theorem normalAssertionReloadRules_hygienic :
    normalAssertionReloadRules.all (fun rule =>
      isAtomFresh "reload-self-input" rule &&
        isAtomFresh "reload-self-output" rule &&
        isAtomFresh "reload-proof" rule) = true := by
  decide +kernel

theorem normalBodyMatchMachineRules_surface_safe :
    normalBodyMatchMachineRules.all atomSafe = true := by
  decide +kernel

/-- The body-machine reload bindings cannot capture variables in the five
case rules they reinsert. -/
theorem normalBodyMatchReload_hygienic :
    normalBodyMatchMachineRules.dropLast.all (fun rule =>
      isAtomFresh "body-reload-self-input" rule &&
        isAtomFresh "body-reload-self-output" rule &&
        isAtomFresh "body-reload-proof" rule &&
        isAtomFresh "body-reload-pc" rule) = true := by
  decide +kernel

theorem normalBodyBuildMachineRules_surface_safe :
    normalBodyBuildMachineRules.all atomSafe = true := by
  decide +kernel

theorem normalDVMachineRules_surface_safe :
    normalDVMachineRules.all atomSafe = true := by
  decide +kernel

/-- DV reload-control bindings cannot capture the variables of any case rule
that they reinsert. -/
theorem normalDVReload_hygienic :
    normalDVMachineRules.dropLast.all (fun rule =>
      isAtomFresh "dv-reload-self-input" rule &&
        isAtomFresh "dv-reload-self-output" rule &&
        isAtomFresh "dv-reload-proof" rule &&
        isAtomFresh "dv-reload-pc" rule) = true := by
  decide +kernel

/-- The result-builder reload bindings cannot capture variables in the seven
case rules they reinsert. -/
theorem normalBodyBuildReload_hygienic :
    normalBodyBuildMachineRules.dropLast.all (fun rule =>
      isAtomFresh "build-reload-self-input" rule &&
        isAtomFresh "build-reload-self-output" rule &&
        isAtomFresh "build-reload-proof" rule &&
        isAtomFresh "build-reload-pc" rule) = true := by
  decide +kernel

/-! ## Database-independent verifier transformation -/

/-- The rules contributed by the normal-proof operation.  Other source
operations deliberately contribute no rules in this still-partial slice;
their absence remains explicit in `uncoveredOperations` below. -/
def verifierRulesForNormalSlice : SourceOperation → List Atom
  | .checkTheoremNormal => normalProofMachineRules
  | _ => []

/-- Database-independent rules that admit the ordered event stream before
any declaration or proof operation is attempted. -/
def orderedSourceEventPreludeRules : List Atom :=
  [sourceEventBootstrapRule, sourceEventDispatchRule,
   sourceTheoremStartRule, sourceTheoremSuccessRule,
   sourceTheoremCommitRule]

theorem normalProofMachineRules_no_internal_row_shape :
    normalProofMachineRules.all (fun atom =>
      !(isVerifierOwnedInternalRowShape atom)) = true := by
  decide +kernel

theorem orderedSourceEventPreludeRules_no_internal_row_shape :
    orderedSourceEventPreludeRules.all (fun atom =>
      !(isVerifierOwnedInternalRowShape atom)) = true := by
  decide +kernel

theorem verifierRulesForNormalSlice_no_internal_row_shape
    (operation : SourceOperation) :
    (verifierRulesForNormalSlice operation).all (fun atom =>
      !(isVerifierOwnedInternalRowShape atom)) = true := by
  cases operation <;>
    simp [verifierRulesForNormalSlice,
      normalProofMachineRules_no_internal_row_shape]

theorem verifierRulesForNormalSpine_no_internal_row_shape
    (operations : List SourceOperation) :
    (operations.flatMap verifierRulesForNormalSlice).all (fun atom =>
      !(isVerifierOwnedInternalRowShape atom)) = true := by
  rw [List.all_eq_true]
  intro atom member
  rw [List.mem_flatMap] at member
  obtain ⟨operation, _, atomMember⟩ := member
  exact (List.all_eq_true.mp
    (verifierRulesForNormalSlice_no_internal_row_shape operation))
      atom atomMember

/-- A database- and proof-independent verifier artifact generated from the
supplied Metamath operation language for the supplied MM2 target.  The
coverage split prevents the current normal slice from masquerading as the
complete `mmverify.mm2` artifact. -/
structure GenericVerifierSliceArtifact (target : MM2Target) where
  sourceOperations : List SourceOperation
  coveredOperations : List SourceOperation
  uncoveredOperations : List SourceOperation
  internalRows : List Atom
  rules : List Atom

def GenericVerifierSliceArtifact.program {target : MM2Target}
    (artifact : GenericVerifierSliceArtifact target) : List Atom :=
  artifact.internalRows ++ artifact.rules

/-- Transform the actual supplied Metamath verifier GSLT and MM2 target into
the generic normal-proof rule slice.  The output contains no source state,
database row, theorem, or proof input. -/
def transformNormalVerifierSlice (source : MetamathVerifierGSLT)
    (target : MM2Target) : GenericVerifierSliceArtifact target where
  sourceOperations := source.operations
  coveredOperations :=
    source.operations.filter (fun operation => operation == .checkTheoremNormal)
  uncoveredOperations :=
    source.operations.filter (fun operation => operation != .checkTheoremNormal)
  internalRows := normalVerifierInternalRows
  rules := orderedSourceEventPreludeRules ++
    source.operations.flatMap verifierRulesForNormalSlice

theorem transformNormalVerifierSlice_rules_no_internal_row_shape
    (source : MetamathVerifierGSLT) (target : MM2Target) :
    (transformNormalVerifierSlice source target).rules.all (fun atom =>
      !(isVerifierOwnedInternalRowShape atom)) = true := by
  change (orderedSourceEventPreludeRules ++
      source.operations.flatMap verifierRulesForNormalSlice).all (fun atom =>
        !(isVerifierOwnedInternalRowShape atom)) = true
  simpa only [List.all_append, Bool.and_eq_true] using
    And.intro orderedSourceEventPreludeRules_no_internal_row_shape
      (verifierRulesForNormalSpine_no_internal_row_shape source.operations)

/-- The generated verifier artifact owns every protected inert row in its
program.  Its executable rules cannot forge a second protected row because
their top-level shape is disjoint. -/
theorem transformNormalVerifierSlice_internal_rows_intact
    (source : MetamathVerifierGSLT) (target : MM2Target) :
    NormalVerifierInternalRowsIntact
      (transformNormalVerifierSlice source target).program := by
  unfold NormalVerifierInternalRowsIntact AtomsWithin
  intro atom member
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rw [GenericVerifierSliceArtifact.program, List.mem_append] at member
  rcases member with internal | rule
  · simpa [transformNormalVerifierSlice] using internal
  · have safe :=
      (List.all_eq_true.mp
        (transformNormalVerifierSlice_rules_no_internal_row_shape source target))
        atom rule
    have absent : isVerifierOwnedInternalRowShape atom = false := by
      simpa only [Bool.not_eq_true'] using safe
    rw [absent] at internalShape
    contradiction

/-- The sole clean composition boundary for source-event input.  External
callers supply the proof-carrying admission object, not an arbitrary list of
MM2 atoms; the program contains exactly the generated verifier followed by
the decoded event rows and proof-neutral rows recomputed from them. -/
def composeAdmittedNormalProgram (source : MetamathVerifierGSLT)
    (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner) : List Atom :=
  (transformNormalVerifierSlice source target).program ++ input.initialRows

/-- The executable entry space contains protected code rows only from the
generated verifier artifact.  Canonicalized source data cannot contribute a
row whose payload is later reinstalled as executable code. -/
theorem composeAdmittedNormalProgram_internal_rows_intact
    (source : MetamathVerifierGSLT) (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner) :
    NormalVerifierInternalRowsIntact
      (composeAdmittedNormalProgram source target input) := by
  unfold NormalVerifierInternalRowsIntact AtomsWithin
  intro atom member
  unfold NormalVerifierInternalRowIntact
  intro internalShape
  rw [composeAdmittedNormalProgram, List.mem_append] at member
  rcases member with verifier | external
  · exact transformNormalVerifierSlice_internal_rows_intact source target
      atom verifier internalShape
  · have absent := input.initialRows_no_verifier_internal atom external
    rw [absent] at internalShape
    contradiction

@[simp] theorem composeAdmittedNormalProgram_exact
    (source : MetamathVerifierGSLT) (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner) :
    composeAdmittedNormalProgram source target input =
      (transformNormalVerifierSlice source target).program ++
        input.rows ++ input.derivedRows := by
  simp [composeAdmittedNormalProgram, AdmittedSourceEventInput.initialRows,
    List.append_assoc]

def renderAdmittedNormalProgram? (source : MetamathVerifierGSLT)
    (target : MM2Target) {owner : Atom}
    (input : AdmittedSourceEventInput owner) : Option String :=
  target.render (composeAdmittedNormalProgram source target input)

/-- Fixed-profile bootstrap inventory.  The authored operation spine licenses
the covered normal-proof operation, while the emitted rules are the existing
generic normal-proof machine rather than a synthesis from `source.operational`. -/
theorem authored_transformNormalVerifierSlice_rules
    (target : MM2Target) :
    (transformNormalVerifierSlice authoredMetamathVerifierGSLT target).rules =
      sourceEventBootstrapRule :: sourceEventDispatchRule ::
        sourceTheoremStartRule :: sourceTheoremSuccessRule ::
        sourceTheoremCommitRule :: normalProofMachineRules := by
  rfl

/-- Exact executable-rule inventory of the currently covered authored
Metamath verifier slice.  It includes ordered source-event admission and the
normal proof machine, but not the protected inert code carriers. -/
def authoredNormalVerifierRules : List Atom :=
  orderedSourceEventPreludeRules ++ normalProofMachineRules

def authoredNormalVerifierDirectives : List SourceExecFact :=
  authoredNormalVerifierRules.filterMap extractSupportedSourceExecFact

def authoredNormalVerifierRawFacts : List RawExecFact :=
  authoredNormalVerifierRules.filterMap extractRawExecFact

theorem authoredNormalVerifierRules_eq_transform
    (target : MM2Target) :
    authoredNormalVerifierRules =
      (transformNormalVerifierSlice authoredMetamathVerifierGSLT target).rules := by
  rw [authored_transformNormalVerifierSlice_rules]
  rfl

theorem authoredNormalVerifierDirectives_atoms_exact :
    authoredNormalVerifierDirectives.map SourceExecFact.atom =
      authoredNormalVerifierRules := by
  decide +kernel

theorem authoredNormalVerifierRawFacts_atoms_exact :
    authoredNormalVerifierRawFacts.map RawExecFact.atom =
      authoredNormalVerifierRules := by
  decide +kernel

theorem authoredNormalVerifierRawFacts_decode_exact :
    authoredNormalVerifierRawFacts.map decodeSupportedSourceExec =
      authoredNormalVerifierDirectives.map some := by
  decide +kernel

theorem authoredNormalVerifierRawFact_decodes
    {raw : RawExecFact} {directive : SourceExecFact}
    (member : raw ∈ authoredNormalVerifierRawFacts)
    (decoded : decodeSupportedSourceExec raw = some directive) :
    directive ∈ authoredNormalVerifierDirectives := by
  have decodedMember : some directive ∈
      authoredNormalVerifierRawFacts.map decodeSupportedSourceExec :=
    List.mem_map.mpr ⟨raw, member, decoded⟩
  rw [authoredNormalVerifierRawFacts_decode_exact] at decodedMember
  rcases List.mem_map.mp decodedMember with
    ⟨actual, actualMember, equal⟩
  exact (Option.some.inj equal) ▸ actualMember

theorem authoredNormalVerifierDirectives_key_injective :
    KeyInjective authoredNormalVerifierDirectives := by
  intro left right leftMember rightMember keysEqual
  exact List.inj_on_of_nodup_map
    (l := authoredNormalVerifierDirectives)
    (f := fun directive => SchedulerKey.key directive)
    (by decide +kernel) leftMember rightMember keysEqual

theorem authoredNormalVerifierRawFacts_key_injective :
    KeyInjective authoredNormalVerifierRawFacts := by
  intro left right leftMember rightMember keysEqual
  exact List.inj_on_of_nodup_map
    (l := authoredNormalVerifierRawFacts)
    (f := fun raw => SchedulerKey.key raw)
    (by decide +kernel) leftMember rightMember keysEqual

theorem authoredNormalVerifierDirectives_all_support_set :
    authoredNormalVerifierDirectives.all (fun directive =>
      directive.rule.tmpl.sinks.all reflectiveSupportSetSinkB) = true := by
  decide +kernel

theorem authoredNormalVerifierDirective_support_set
    {directive : SourceExecFact}
    (member : directive ∈ authoredNormalVerifierDirectives) :
    ReflectiveSupportSetTemplate directive.rule.tmpl := by
  apply (all_reflectiveSupportSetSinkB_eq_true_iff directive.rule.tmpl).1
  exact (List.all_eq_true.mp
    authoredNormalVerifierDirectives_all_support_set) directive member

/-- Any duplicate-free state whose executable shells come from the actual
authored verifier transformation is adequate to the support-valued MM2
semantics for its next scheduled step. -/
theorem authoredNormalVerifier_reflective_invariant
    (space : List Atom) (nodup : space.Nodup)
    (rawWithin : RawExecFactsWithin authoredNormalVerifierRawFacts space) :
    ReflectiveWorkQueueInvariant space :=
  reflectiveWorkQueueInvariant_of_ruleInventory
    authoredNormalVerifierRawFacts authoredNormalVerifierDirectives space
    nodup rawWithin authoredNormalVerifierRawFact_decodes
    authoredNormalVerifierDirectives_key_injective
    authoredNormalVerifierRawFacts_key_injective
    (fun _ member =>
      authoredNormalVerifierDirective_support_set member)

@[simp] theorem authored_transformNormalVerifierSlice_internalRows
    (target : MM2Target) :
    (transformNormalVerifierSlice authoredMetamathVerifierGSLT target).internalRows =
      normalVerifierInternalRows := by
  rfl

/-- The current artifact is honestly partial.  Declaration/scope and
compressed-proof operations remain uncovered rather than being silently
treated as prevalidated source data. -/
theorem authored_transformNormalVerifierSlice_uncovered_nonempty
    (target : MM2Target) :
    (transformNormalVerifierSlice authoredMetamathVerifierGSLT target).uncoveredOperations ≠
      [] := by
  intro empty
  change
    [SourceOperation.openScope, SourceOperation.closeScope,
      SourceOperation.declareConstants, SourceOperation.declareVariables,
      SourceOperation.declareDisjoint, SourceOperation.declareFloating,
      SourceOperation.declareEssential, SourceOperation.declareAxiom,
      SourceOperation.checkTheoremCompressed,
      SourceOperation.completeBlock] = [] at empty
  contradiction

/-- Surface lowering is owned by the supplied MM2 target and is independent
of every particular source database and proof. -/
def renderNormalVerifierSlice? (source : MetamathVerifierGSLT)
    (target : MM2Target) : Option String :=
  target.render (transformNormalVerifierSlice source target).program

/-! ## Scope-row calibration composition and target-owned surface lowering -/

/-- Calibration artifact used by the existing phase proofs: exact
source-derived scope rows composed with the database-independent normal
verifier slice.  It is not the final ordered-event verifier interface; the
clean source-data transformation emits statement events instead. -/
structure CompiledNormalScope (target : MM2Target) where
  sourceData : ScopeDataArtifact
  lookupRows : List Atom
  executionRows : List Atom
  internalRows : List Atom
  rules : List Atom

def CompiledNormalScope.program {target : MM2Target}
    (artifact : CompiledNormalScope target) : List Atom :=
  artifact.sourceData.rows ++ artifact.lookupRows ++
    artifact.executionRows ++ artifact.internalRows ++ artifact.rules

/-- Calibration program for the selected MM2 profile.  Database-derived rows
remain here only to qualify the proof-machine phases while the generic
statement-event ingestion machine is constructed. -/
def compileNormalScopeProgram (source : AdmittedSourceScope)
    (scopeOwner : Atom) : List Atom :=
  (transformScopeData scopeOwner source).rows ++
    hypothesisLookupRows scopeOwner source.state ++
    normalExecutionRows scopeOwner source.state ++
    normalVerifierInternalRows ++
    normalProofMachineRules

/-- Compose source-derived calibration rows with the existing normal machine.
The ordered-event prelude belongs only to the clean verifier artifact above;
this calibration route starts after source ingestion by construction. -/
def transformNormalScope (source : AdmittedSourceScope)
    (target : MM2Target) (scopeOwner : Atom) :
    CompiledNormalScope target where
  sourceData := transformScopeData scopeOwner source
  lookupRows := hypothesisLookupRows scopeOwner source.state
  executionRows := normalExecutionRows scopeOwner source.state
  internalRows := normalVerifierInternalRows
  rules := normalProofMachineRules

@[simp] theorem transformNormalScope_program
    (source : AdmittedSourceScope) (target : MM2Target)
    (scopeOwner : Atom) :
    (transformNormalScope source target scopeOwner).program =
      compileNormalScopeProgram source scopeOwner := by
  rfl

/-- The second stage is owned by the supplied MM2 target: abstract MM2 atoms
become ordinary `.mm2` text through its renderer. -/
def lowerProgram? (target : MM2Target) (program : List Atom) : Option String :=
  target.render program

def renderNormalScope? (source : AdmittedSourceScope)
    (target : MM2Target) (scopeOwner : Atom) : Option String :=
  lowerProgram? target
    (transformNormalScope source target scopeOwner).program

/-- Dynamic proof data is appended after scope compilation; it is not used to
choose or generate database-specific rules. -/
def invocationProgram (source : AdmittedSourceScope) (target : MM2Target)
    (scopeOwner proofOwner : Atom) (proof : ProofInput) : List Atom :=
  (transformNormalScope source target scopeOwner).program ++
    proofInputRows scopeOwner proofOwner proof

def renderInvocation? (source : AdmittedSourceScope) (target : MM2Target)
    (scopeOwner proofOwner : Atom) (proof : ProofInput) : Option String :=
  lowerProgram? target
    (invocationProgram source target scopeOwner proofOwner proof)

/-! ## Calculus-language sensitivity and executable controls -/

/-- A changed authored checker-facing calculus language changes the concrete
compiler artifact even when the scope identity and target are held fixed. -/
theorem transformNormalScope_language_sensitive
    (target : MM2Target) (scopeOwner : Atom)
    (left right : AdmittedSourceScope)
    (changed :
      Mettapedia.GSLT.LanguageDef.InferenceLanguageWire.RuntimeInferenceLanguage.ofDefinition
          left.language ≠
        Mettapedia.GSLT.LanguageDef.InferenceLanguageWire.RuntimeInferenceLanguage.ofDefinition
          right.language) :
    transformNormalScope left target scopeOwner ≠
      transformNormalScope right target scopeOwner := by
  intro equal
  have sourceDataEqual := congrArg
    (fun artifact => artifact.sourceData.languageFact) equal
  exact (transformScopeData_language_sensitive scopeOwner left right changed)
    sourceDataEqual

theorem normalHypothesisStepRule_surface_safe :
    atomSafe normalHypothesisStepRule = true := by
  decide +kernel

theorem normalAcceptRule_surface_safe :
    atomSafe normalAcceptRule = true := by
  decide +kernel

/-- Every fixed rule emitted by the current normal-proof machine belongs to
the ordinary MM2 surface.  Adding a new machine phase must re-prove this
closed gate before its programs can be exported. -/
theorem normalProofMachineRules_surface_safe :
    normalProofMachineRules.all atomSafe = true := by
  decide +kernel

/-- The inert verifier-owned code bundles are ordinary MM2 data as well.
They are emitted only by the generic verifier transform, never accepted from
the source-event decoder. -/
theorem normalVerifierInternalRows_surface_safe :
    normalVerifierInternalRows.all atomSafe = true := by
  decide +kernel

/-- Removing the source-derived lookup rows removes the only data path by
which the hypothesis-step rule can recognize an active hypothesis. -/
theorem empty_state_has_no_hypothesis_lookup_rows (scopeOwner : Atom) :
    hypothesisLookupRows scopeOwner initialState = [] := by
  rfl

/-- The persistent rule requires reflective capture: its re-emitted input and
output values contain the rule-local variables of the captured code. -/
theorem normal_step_rule_uses_reflective_capture :
    isGroundAtom
      (applySubst
        [("self-input", normalStepInput), ("self-output", normalStepOutput)]
        (.expression
          [.symbol "exec", normalStepLocation,
            .var "self-input", .var "self-output"])) = false := by
  decide +kernel

/-! ## Loaded DV scheduler boundary -/

/-- The eight phase rules installed by the verifier-owned DV reloader, in
strict scheduler order. -/
def normalDVLoadedPhaseRules : List Atom :=
  [normalDVPairBeginRule, normalDVLeftConstRule,
   normalDVLeftVariableRule, normalDVRightConstRule,
   normalDVRightVariableRule, normalDVRightNilRule,
   normalDVLeftNilRule, normalDVCompleteRule]

def normalDVLoadedPhaseDirectives : List SourceExecFact :=
  [normalDVPairBeginDirective, normalDVLeftConstDirective,
   normalDVLeftVariableDirective, normalDVRightConstDirective,
   normalDVRightVariableDirective, normalDVRightNilDirective,
   normalDVLeftNilDirective, normalDVCompleteDirective]

/-- A loaded terminal DV cursor.  The earlier phase rules are present and are
therefore observable administrative probes before completion. -/
def normalDVLoadedCompleteSpaceAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) : List Atom :=
  normalDVLoadedPhaseRules ++
    [.expression
      [.symbol "mm-dv-next-pair", scopeOwner, proofOwner, proofAddress,
        stringAtom assertionLabel, natAtom pairEnd, natAtom pairEnd,
        listAtom runtimeSymAtom sourceBody, context]]

theorem normalDVLoadedComplete_supported_exact
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cSupportedSourceExecFacts
        (normalDVLoadedCompleteSpaceAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd sourceBody context) =
      normalDVLoadedPhaseDirectives := by
  rfl

/-- At the terminal pair cursor the first loaded rule has no complete input:
there is no pair row at the exclusive endpoint. -/
theorem normalDVLoadedComplete_pairBegin_no_matches
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    Conformance.Computable.cmatchInputSpec []
        (normalDVPairBeginDirective.atom ::
          (normalDVLoadedCompleteSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd sourceBody context).erase
              normalDVPairBeginDirective.atom)
        normalDVPairBeginDirective.rule.input = [] := by
  have readSpaceExact :
      normalDVPairBeginDirective.atom ::
          (normalDVLoadedCompleteSpaceAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd sourceBody context).erase
              normalDVPairBeginDirective.atom =
        normalDVLoadedCompleteSpaceAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd sourceBody context := by
    rfl
  rw [readSpaceExact]
  change
    Conformance.Computable.cmatchInputSpec []
        (normalDVLoadedCompleteSpaceAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd sourceBody context)
        (.compat (mkPattern normalDVPairBeginPatternAtoms)) = []
  apply Conformance.Computable.cmatchInputSpec_compat_eq_nil_of_factor_never_matches
    (before := [normalDVPairBeginPatternAtoms[0]])
    (factor := normalDVPairBeginPatternAtoms[1])
    (after := normalDVPairBeginPatternAtoms.drop 2)
  intro beforeFactor carrier carrierMember
  simp only [normalDVLoadedCompleteSpaceAt, normalDVLoadedPhaseRules,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at carrierMember
  rcases carrierMember with phaseMember | cursorEqual
  · rcases phaseMember with h | h | h | h | h | h | h | h
    all_goals subst carrier <;> rfl
  · subst carrier
    rfl

#print axioms normalDVLoadedComplete_supported_exact
#print axioms normalDVLoadedComplete_pairBegin_no_matches
#print axioms transformNormalScope_language_sensitive
#print axioms MM2Target.native_type_iff_step
#print axioms MM2Target.no_invented_native_step
#print axioms callerDVRow_mem_callerDVRows_iff
#print axioms callerDVRow_mem_callerDVRowsOfPairs_iff
#print axioms mem_assertionExecutionRowsFor_iff
#print axioms mem_assertionExecutionRows_iff
#print axioms mem_callerDVRows_iff
#print axioms mem_normalExecutionRows_iff
#print axioms normalHypothesisStepRule_surface_safe
#print axioms extract_normalHypothesisStepRule_exact
#print axioms normalHypothesisDirective_fires_stack
#print axioms normalHypothesisPhase_selects_directive
#print axioms normalHypothesisPhase_inhabits_target_native_type
#print axioms assertionHeaderRow_mem_normalExecutionRows
#print axioms assertionHypothesisSuccessorRow_mem_normalExecutionRows
#print axioms assertionHypothesisRow_mem_normalExecutionRows
#print axioms extract_normalAssertionStartRule_exact
#print axioms normalAssertionStartPhase_selects_directive
#print axioms normalAssertionStartDirective_fires_pop
#print axioms normalAssertionStartPhase_inhabits_target_native_type
#print axioms extract_normalAssertionPopRule_exact
#print axioms normalAssertionPopPhase_selects_directive
#print axioms normalAssertionPopDirective_fires_previous
#print axioms normalAssertionPopPhase_inhabits_target_native_type
#print axioms extract_normalAssertionBeginRule_exact
#print axioms normalAssertionBeginPhase_selects_directive
#print axioms normalAssertionBeginDirective_fires_bind
#print axioms normalAssertionBeginPhase_inhabits_target_native_type
#print axioms extract_normalAssertionFloatingRule_exact
#print axioms normalAssertionFloatingPhase_selects_directive
#print axioms normalAssertionFloatingDirective_fires_evidence
#print axioms normalAssertionFloatingPhase_inhabits_target_native_type
#print axioms normalAssertionChildAtom_occurrence_injective
#print axioms extract_normalAssertionEssentialRule_exact
#print axioms normalAssertionEssentialPhase_selects_directive
#print axioms normalAssertionEssentialDirective_fires_match
#print axioms normalAssertionEssentialPhase_inhabits_target_native_type
#print axioms extract_normalAssertionEssentialCompleteRule_exact
#print axioms normalAssertionEssentialCompletePhase_selects_directive
#print axioms normalAssertionEssentialCompleteDirective_fires_evidence
#print axioms normalAssertionEssentialCompletePhase_inhabits_target_native_type
#print axioms extract_normalBodyMatchConstRule_exact
#print axioms normalBodyMatchConstPhase_selects_directive
#print axioms normalBodyMatchConstDirective_fires_tail
#print axioms normalBodyMatchConstPhase_inhabits_target_native_type
#print axioms normalBodyMatchConstPattern_rejects_mismatched_constant
#print axioms decodeNormalAssertionSubstitutionAtom_encode
#print axioms normalAssertionSubstitutionAtom_injective_payload
#print axioms extract_normalBodyMatchVariableRule_exact
#print axioms normalBodyMatchVariablePhase_selects_directive
#print axioms normalBodyMatchVariableDirective_fires_prefix
#print axioms normalBodyMatchVariablePhase_inhabits_target_native_type
#print axioms extract_normalBodyPrefixNilRule_exact
#print axioms normalBodyPrefixNilPhase_selects_directive
#print axioms normalBodyPrefixNilDirective_fires_match
#print axioms normalBodyPrefixNilPhase_inhabits_target_native_type
#print axioms extract_normalBodyPrefixConsRule_exact
#print axioms normalBodyPrefixConsPhase_selects_directive
#print axioms normalBodyPrefixConsDirective_fires_tail
#print axioms normalBodyPrefixConsPhase_inhabits_target_native_type
#print axioms normalBodyPrefixConsPattern_rejects_mismatched_symbol
#print axioms extract_normalBodyMatchNilRule_exact
#print axioms normalBodyMatchNilPhase_selects_directive
#print axioms normalBodyMatchNilDirective_fires_continuation
#print axioms normalBodyMatchNilPhase_inhabits_target_native_type
#print axioms normalBodyMatchNilPattern_rejects_actual_remainder
#print axioms normalAcceptRule_surface_safe
#print axioms normalAcceptRule_sinks_exact
#print axioms sourceTheoremNormalAcceptedAtom_eq_normalAcceptedAtom
#print axioms normalAcceptedTemplate_instantiates
#print axioms extract_normalAcceptRule_exact
#print axioms normalAcceptPhase_selects_directive
#print axioms normalAcceptDirective_fires_terminal
#print axioms normalAcceptPhase_inhabits_target_native_type
#print axioms extract_normalAssertionFinishRule_exact
#print axioms normalAssertionFinishPhaseAtoms_nodup
#print axioms normalAssertionFinishPhase_selects_directive
#print axioms normalAssertionFinishDirective_fires_dv_entry
#print axioms normalAssertionFinishPhase_inhabits_target_native_type
#print axioms extract_normalDVPairBeginRule_exact
#print axioms normalDVPairBeginPhase_selects_directive
#print axioms normalDVPairBeginDirective_fires_scan
#print axioms normalDVPairBeginPhase_inhabits_target_native_type
#print axioms extract_normalDVLeftConstRule_exact
#print axioms normalDVLeftConstPhase_selects_directive
#print axioms normalDVLeftConstDirective_fires_tail
#print axioms normalDVLeftConstPhase_inhabits_target_native_type
#print axioms extract_normalDVLeftVariableRule_exact
#print axioms normalDVLeftVariablePhase_selects_directive
#print axioms normalDVLeftVariableDirective_fires_right_scan
#print axioms normalDVLeftVariablePhase_inhabits_target_native_type
#print axioms extract_normalDVRightVariableRule_exact
#print axioms normalDVRightVariablePhase_selects_directive
#print axioms normalDVRightVariableDirective_fires_tail
#print axioms normalDVRightVariablePhase_inhabits_target_native_type
#print axioms normalDVRightVariable_missing_caller_rejects_obligation
#print axioms extract_normalDVRightConstRule_exact
#print axioms normalDVRightConstPhase_selects_directive
#print axioms normalDVRightConstDirective_fires_tail
#print axioms normalDVRightConstPhase_inhabits_target_native_type
#print axioms extract_normalDVRightNilRule_exact
#print axioms normalDVRightNilPhase_selects_directive
#print axioms normalDVRightNilDirective_fires_left_scan
#print axioms normalDVRightNilPhase_inhabits_target_native_type
#print axioms extract_normalDVLeftNilRule_exact
#print axioms normalDVLeftNilPhase_selects_directive
#print axioms normalDVLeftNilDirective_fires_next_pair
#print axioms normalDVLeftNilPhase_inhabits_target_native_type
#print axioms extract_normalDVReloadRule_exact
#print axioms normalDVReloadPhase_selects_directive
#print axioms normalDVReloadPhase_inhabits_target_native_type
#print axioms extract_normalDVCompleteRule_exact
#print axioms normalDVCompletePhase_selects_directive
#print axioms normalDVCompleteDirective_fires_body_build
#print axioms normalDVCompletePhase_inhabits_target_native_type
#print axioms extract_normalBodyBuildConstRule_exact
#print axioms normalBodyBuildConstPhase_selects_directive
#print axioms normalBodyBuildConstDirective_fires_tail
#print axioms normalBodyBuildConstPhase_inhabits_target_native_type
#print axioms extract_normalBodyBuildVariableRule_exact
#print axioms normalBodyBuildVariablePhase_selects_directive
#print axioms normalBodyBuildVariableDirective_fires_prefix
#print axioms normalBodyBuildVariablePhase_inhabits_target_native_type
#print axioms extract_normalBodyBuildPrefixNilRule_exact
#print axioms normalBodyBuildPrefixNilPhase_selects_directive
#print axioms normalBodyBuildPrefixNilDirective_fires_tail
#print axioms normalBodyBuildPrefixNilPhase_inhabits_target_native_type
#print axioms extract_normalBodyBuildPrefixConsRule_exact
#print axioms normalBodyBuildPrefixConsPhase_selects_directive
#print axioms normalBodyBuildPrefixConsDirective_fires_tail
#print axioms normalBodyBuildPrefixConsPhase_inhabits_target_native_type
#print axioms extract_normalBodyBuildNilRule_exact
#print axioms normalBodyBuildNilPhase_selects_directive
#print axioms normalBodyBuildNilDirective_fires_reverse
#print axioms normalBodyBuildNilPhase_inhabits_target_native_type
#print axioms extract_normalBodyReverseConsRule_exact
#print axioms normalBodyReverseConsPhase_selects_directive
#print axioms normalBodyReverseConsDirective_fires_tail
#print axioms normalBodyReverseConsPhase_inhabits_target_native_type
#print axioms extract_normalBodyReverseNilRule_exact
#print axioms normalBodyReverseNilPhase_selects_directive
#print axioms normalBodyReverseNilDirective_fires_built
#print axioms normalBodyReverseNilPhase_inhabits_target_native_type
#print axioms extract_normalBodyBuildReloadRule_exact
#print axioms normalBodyBuildReloadPhase_selects_directive
#print axioms normalBodyBuildReloadPhase_inhabits_target_native_type
#print axioms extract_normalAssertionResultCompleteRule_exact
#print axioms normalAssertionResultCompletePhase_selects_directive
#print axioms normalAssertionResultCompleteDirective_fires_result
#print axioms normalAssertionResultCompletePhase_inhabits_target_native_type
#print axioms normalAssertionStackAtom_occurrence_injective
#print axioms normalProofMachineDirectives_atoms_exact
#print axioms normalProofMachineRawFacts_atoms_exact
#print axioms normalProofMachineRawFacts_decode_exact
#print axioms normalProofMachineRawFact_decodes_in_directives
#print axioms normalProofMachine_supportedWithin_of_rawWithin
#print axioms normalProofMachineDirectives_key_injective
#print axioms normalProofMachineRawFacts_key_injective
#print axioms normalProofMachineDirectiveSubset_key_injective
#print axioms normalProofMachineRawSubset_key_injective
#print axioms normalProofMachineDirectives_all_support_set
#print axioms normalProofMachineDirective_support_set
#print axioms normalProofMachine_reflective_invariant
#print axioms normalProofMachine_reflective_invariant_of_rawWithin
#print axioms normalProofMachineInvariantCheck_sound
#print axioms NormalProofMachineState.reflectiveInvariant
#print axioms NormalProofMachineState.fire
#print axioms NormalProofMachineState.step
#print axioms NormalProofMachineState.of_reachable
#print axioms normalProofMachineAdequateTrace_of_closedFrom
#print axioms forged_internal_reload_refutes_minimal_global_closure
#print axioms normalVerifierInternalRows_intact
#print axioms normalDispatchReload_captured_self_raw_within
#print axioms normalDispatchReload_captured_rule_authorized_of_internal
#print axioms normalDispatchReload_captured_rule_authorized
#print axioms normalDispatchReload_captured_raw_authorized
#print axioms normalDispatchReload_additions_raw_within
#print axioms NormalProofMachineOwnedState.fire
#print axioms NormalProofMachineOwnedState.step
#print axioms NormalProofMachineOwnedState.of_reachable
#print axioms normalProofMachineOwnedAdequateTrace_of_closedFrom
#print axioms forged_internal_reload_refutes_owned_state
#print axioms forged_internal_reload_minimal_but_not_owned
#print axioms normalProofMachineRules_no_internal_row_shape
#print axioms verifierRulesForNormalSpine_no_internal_row_shape
#print axioms transformNormalVerifierSlice_internal_rows_intact
#print axioms composeAdmittedNormalProgram_internal_rows_intact
#print axioms normalProofMachineRules_surface_safe
#print axioms normalVerifierInternalRows_surface_safe
#print axioms extract_normalBodyReloadRule_exact
#print axioms normalBodyReloadPhase_selects_directive
#print axioms normalBodyReloadPhase_inhabits_target_native_type
#print axioms normalBodyReloadDirective_fires_boundary_rules
#print axioms extract_normalDispatchReloadRule_exact
#print axioms normalDispatchReloadPhase_selects_directive
#print axioms normalDispatchReloadPhase_inhabits_target_native_type
#print axioms normalDispatchReloadDirective_fires_last_rule
#print axioms normalAssertionReloadRules_hygienic
#print axioms normalBodyMatchMachineRules_surface_safe
#print axioms normalBodyMatchReload_hygienic
#print axioms normalBodyBuildMachineRules_surface_safe
#print axioms normalBodyBuildReload_hygienic
#print axioms normalDVMachineRules_surface_safe
#print axioms normalDVReload_hygienic
#print axioms MetamathVerifierGSLT.step_iff
#print axioms MetamathVerifierGSLT.normal_operation_mem
#print axioms MetamathVerifierGSLT.no_input_without_normal_operation
#print axioms MetamathVerifierGSLT.native_type_iff_source_step
#print axioms authored_transformNormalVerifierSlice_rules
#print axioms authoredNormalVerifierRules_eq_transform
#print axioms authoredNormalVerifierDirectives_atoms_exact
#print axioms authoredNormalVerifierRawFacts_atoms_exact
#print axioms authoredNormalVerifierRawFacts_decode_exact
#print axioms authoredNormalVerifierRawFact_decodes
#print axioms authoredNormalVerifierDirectives_key_injective
#print axioms authoredNormalVerifierRawFacts_key_injective
#print axioms authoredNormalVerifierDirectives_all_support_set
#print axioms authoredNormalVerifierDirective_support_set
#print axioms authoredNormalVerifier_reflective_invariant
#print axioms composeAdmittedNormalProgram_exact
#print axioms authored_transformNormalVerifierSlice_uncovered_nonempty
#print axioms empty_state_has_no_hypothesis_lookup_rows
#print axioms normal_step_rule_uses_reflective_capture

end Mettapedia.Languages.Metamath.MM2Transformation
