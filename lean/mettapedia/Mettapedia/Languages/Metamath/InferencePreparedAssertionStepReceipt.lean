import Mettapedia.Languages.Metamath.InferenceAssertionSliceCompilation
import Mettapedia.Languages.Metamath.InferenceAssertionStackInvariant
import Mettapedia.Languages.Metamath.InferenceAssertionStepForward
import Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation

/-!
# Proof-relevant receipts for prepared Metamath assertion steps

Prepared assertion selection, generated inference evidence, slice-backed
substitution, and the live verifier step are already independently exact.  A
`PreparedAssertionStepReceipt` retains their common occurrence in one
proof-relevant value.  The runtime substitution remains related extensionally
to the authored finite substitution; no hash-table insertion history is made
semantic.

The constructor consumes explicit generated-node data.  It does not extract a
computational witness from the propositional assertion semantics, and it does
not assume success of any runtime checker.
-/

namespace Mettapedia.Languages.Metamath.InferencePreparedAssertionStepReceipt

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceRuntimeAssertionGraph
open Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceAssertionFusedCompilation
open Mettapedia.Languages.Metamath.InferenceAssertionSliceCompilation
open Mettapedia.Languages.Metamath.InferenceAssertionStackInvariant
open Mettapedia.Languages.Metamath.InferenceAssertionStepForward
open Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation

/-- The complete proof state produced by consuming one assertion's mandatory
stack suffix and pushing its instantiated conclusion. -/
def assertionStepResult (pr : RuntimeProofState) (assertion : AssertionView)
    (result : ConstantHeadedFormula) : RuntimeProofState :=
  { pr with
    stack :=
      (pr.stack.shrink
        (pr.stack.size - assertion.frame.hyps.size)).push result.toRuntime }

/-- One prepared assertion occurrence from source-derived record selection all
the way through the proof-relevant live verifier step.  The generated node is
retained rather than collapsed to mere applicability, and the runtime receipt
retains exact substitution correspondence. -/
structure PreparedAssertionStepReceipt
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation) (assertion : AssertionView)
    (pr : RuntimeProofState) (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution) : Type where
  projected : projectPrefix? db = some projection
  presentation : presentationOfProjection? projection = some target.1
  member : assertion ∈ projection.assertions
  selected :
    compiledAssertionRecord? projection assertion.label = some assertion
  generated :
    GeneratedAssertionNode projection target assertion actuals result
      substitution
  runtime :
    RuntimeAssertionApplicationReceipt db pr assertion.label
      (assertionStepResult pr assertion result) substitution
  inputStackRespects :
    Metamath.Kernel.StackRespectsFrame db db.frame pr.stack
  outputStackRespects :
    Metamath.Kernel.StackRespectsFrame db db.frame
      (assertionStepResult pr assertion result).stack

/-- The generated application retains the exact ordered mandatory-hypothesis
instantiation used by both the side evidence and the runtime substitution. -/
def PreparedAssertionStepReceipt.instances
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution) :
    HypothesisInstances assertion.hypotheses actuals substitution :=
  ((assertionRuleApplication_iff_instances projection target
    receipt.presentation receipt.member).mp receipt.generated.application).1

/-- The generated result derivation has the independent substitution
semantics for this exact authored substitution and conclusion. -/
theorem PreparedAssertionStepReceipt.resultSemantics
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution) :
    FormulaSubstitutionSemantics substitution assertion.formula result := by
  have sideSemantics :=
    (assertionSideEvidence_nonempty_iff_semantics projection target
      receipt.presentation receipt.instances).mp
        ⟨receipt.generated.sideEvidence⟩
  exact sideSemantics.2.2

/-- A live prefix projection and ordered hypothesis instantiation supply the
unique-key premise needed by the slice-backed substitution provider. -/
theorem PreparedAssertionStepReceipt.substitutionKeysUnique
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution) :
    SubstitutionKeysUnique substitution :=
  receipt.instances.substitutionKeysUnique_of_projectedAssertion
    db projection receipt.projected receipt.member

/-- The compact slice provider accepts exactly the generated conclusion. -/
theorem PreparedAssertionStepReceipt.sliceConclusionAccepted
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution) :
    fusedMatch (sliceLookupBody? substitution)
        (formulaTemplate assertion.formula) (formulaTokens result) = some () :=
  (fusedMatch_formula_slices_iff receipt.substitutionKeysUnique
    assertion.formula result).2 receipt.resultSemantics

/-- The retained operational witness reassembles the actual verifier step. -/
theorem PreparedAssertionStepReceipt.stepNormal_ok
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution) :
    db.stepNormal pr assertion.label =
      .ok (assertionStepResult pr assertion result) :=
  receipt.runtime.step.stepNormal_ok

/-- Construct the complete receipt from one proof-relevant generated node and
the independently required stack-window invariant.  Record selection and all
runtime checker successes are derived conclusions. -/
def ofGeneratedNode
    (db : RuntimeDB) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (assertion : AssertionView) (pr : RuntimeProofState)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula)
    (substitution : FiniteSubstitution)
    (projected : projectPrefix? db = some projection)
    (presentation : presentationOfProjection? projection = some target.1)
    (member : assertion ∈ projection.assertions)
    (node : GeneratedAssertionNode projection target assertion actuals result
      substitution)
    (stackEnough : assertion.frame.hyps.size ≤ pr.stack.size)
    (window :
      pr.stack.extract
          (pr.stack.size - assertion.frame.hyps.size) pr.stack.size =
        (actuals.map ConstantHeadedFormula.toRuntime).toArray)
    (stackRespects :
      Metamath.Kernel.StackRespectsFrame db db.frame pr.stack) :
    PreparedAssertionStepReceipt db projection target assertion pr actuals
      result substitution := by
  have applicationData :=
    (assertionRuleApplication_iff_instances projection target presentation
      member).mp node.application
  have sideSemantics :=
    (assertionSideEvidence_nonempty_iff_semantics projection target
      presentation applicationData.1).mp ⟨node.sideEvidence⟩
  have valid :=
    prefixProjectionValid_of_projectPrefix?_eq_some db projection projected
  refine
    { projected := projected
      presentation := presentation
      member := member
      selected := compiledAssertionRecord_lookup_of_mem projection assertion
        valid member
      generated := node
      runtime := ?_
      inputStackRespects := stackRespects
      outputStackRespects := ?_ }
  · simpa [assertionStepResult] using
      assertionApplicationData_to_stepReceipt db projection assertion pr
        actuals result projected member substitution applicationData.1
          sideSemantics.1 sideSemantics.2.1 sideSemantics.2.2 stackEnough
          window stackRespects
  · simpa [assertionStepResult] using
      generatedAssertionNode_stackResult_respects_callerFrame db projection
        target presentation assertion pr.stack actuals result projected member
          ⟨⟨substitution, node⟩⟩ window stackRespects

/-- Positive end-to-end observation: prepared record identity, slice-backed
conclusion matching, exact runtime substitution, and executable success all
belong to the same retained occurrence. -/
theorem PreparedAssertionStepReceipt.preservesAllLayers
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (receipt : PreparedAssertionStepReceipt db projection target assertion pr
      actuals result substitution) :
    compiledAssertionRecord? projection assertion.label = some assertion ∧
      fusedMatch (sliceLookupBody? substitution)
          (formulaTemplate assertion.formula) (formulaTokens result) = some () ∧
      RuntimeSubstitutionCorrespondence substitution
        receipt.runtime.step.substitution ∧
      db.stepNormal pr assertion.label =
        .ok (assertionStepResult pr assertion result) :=
  ⟨receipt.selected, receipt.sliceConclusionAccepted,
    receipt.runtime.substitutionCorrespondence, receipt.stepNormal_ok⟩

/-- Negative control: a conclusion outside the authored substitution
semantics cannot inhabit the prepared end-to-end receipt. -/
theorem no_receipt_of_resultSubstitution_failure
    {db : RuntimeDB} {projection : PrefixProjection}
    {target : ValidatedPresentation} {assertion : AssertionView}
    {pr : RuntimeProofState} {actuals : List ConstantHeadedFormula}
    {result : ConstantHeadedFormula} {substitution : FiniteSubstitution}
    (failure :
      ¬ FormulaSubstitutionSemantics substitution assertion.formula result) :
    ¬ Nonempty
      (PreparedAssertionStepReceipt db projection target assertion pr actuals
        result substitution) := by
  rintro ⟨receipt⟩
  exact failure receipt.resultSemantics

#print axioms PreparedAssertionStepReceipt.preservesAllLayers
#print axioms no_receipt_of_resultSubstitution_failure
#print axioms ofGeneratedNode

end Mettapedia.Languages.Metamath.InferencePreparedAssertionStepReceipt
