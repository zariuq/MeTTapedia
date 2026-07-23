import Mettapedia.Languages.Metamath.SourceGSLTState
import Mettapedia.Languages.Metamath.SourceInferenceDeclarativeAdequacy

/-!
# Normal theorem occurrences in the source-owned Metamath GSLT

A normal theorem transition is admitted only by an exact source-owned proof
occurrence tree over the pre-insertion database prefix.  The submitted postfix
labels are part of the witness, and the successful transition inserts the
trimmed source assertion into the scoped state.

This relation is independent of the `mm-lean4` execution function.  Existing
adequacy theorems show that its proof tree defines the same operational and
supported declarative proof language; implementation refinement remains a
separate theorem.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTNormalTheorem

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceOperationalSpecStepSoundness
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceDeclarativeAdequacy
open Mettapedia.Languages.Metamath.SourceInferenceExecution
open Mettapedia.Languages.Metamath.SourceInferenceOperationalAdequacy
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Metamath.Spec.Equivalence

/-- Proof-relevant semantics of one normal `$p` occurrence. -/
structure NormalTheoremStep
    (before after : SourceState)
    (label : String)
    (formula : ConstantHeadedFormula)
    (proofLabels : List String) : Type where
  sourceValid : sourceStateValid before = true
  target : ValidatedPresentation
  presentation_eq :
    presentationOfSourcePrefix? before.toSourcePrefix = some target.1
  tree :
    SourceGeneratedProvesTree before.toSourcePrefix target formula
  labels_eq : tree.labels = proofLabels
  inserted : insertAssertion? before label formula = some after

def NormalTheoremStep.operation
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula} {proofLabels : List String}
    (_ : NormalTheoremStep before after label formula proofLabels) :
    SourceOperation :=
  .checkTheoremNormal

/-- The state transition inserts precisely the assertion whose mandatory
frame was trimmed from the pre-insertion source state. -/
theorem NormalTheoremStep.insertedAssertion
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula} {proofLabels : List String}
    (step : NormalTheoremStep before after label formula proofLabels) :
    sourceAssertion before label formula ∈ after.assertions := by
  have shape := insertAssertion?_eq_some_shape step.inserted
  rw [shape.1]
  simp

/-- A successful theorem occurrence cannot have an empty normal proof. -/
theorem NormalTheoremStep.proofLabels_ne_nil
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula} {proofLabels : List String}
    (step : NormalTheoremStep before after label formula proofLabels) :
    proofLabels ≠ [] := by
  intro empty
  apply SourceGeneratedProvesTree.labels_ne_nil step.tree
  rw [step.labels_eq, empty]

/-- Positive semantic direction: the source GSLT theorem occurrence proves
its conclusion in the source-derived operational Metamath semantics. -/
theorem NormalTheoremStep.toOperationalProvable
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula} {proofLabels : List String}
    (step : NormalTheoremStep before after label formula proofLabels)
    (fallback : Metamath.Spec.Subst) :
    Metamath.Spec.Provable
      (sourceOperationalDatabase before.toSourcePrefix)
      (sourceOperationalCallerFrame before.toSourcePrefix)
      (operationalExpr formula) := by
  exact sourceTree_to_sourceOperationalProvable
    step.presentation_eq step.tree fallback

/-- The same occurrence inhabits the supported declarative semantics. -/
theorem NormalTheoremStep.toSupportedDeclarative
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula} {proofLabels : List String}
    (step : NormalTheoremStep before after label formula proofLabels) :
    SupportedProvable
      (sourceOperationalDatabase before.toSourcePrefix)
      (sourceOperationalCallerFrame before.toSourcePrefix)
      (exprToFormula
        (varMapOfFrame
          (sourceOperationalCallerFrame before.toSourcePrefix))
        (operationalExpr formula)) := by
  have respects :
      formulaSymbolsRespectFrame
          (floatingVariableNames
            before.toSourcePrefix.activeHypotheses)
          formula =
        true :=
    sourceTree_result_respects step.presentation_eq step.tree
  exact
    (sourceGeneratedProvesTree_nonempty_iff_supportedDeclarative
      before.toSourcePrefix step.target step.presentation_eq formula
        respects).mp
      ⟨step.tree⟩

/-- Forgetting derivation-local support yields the canonical declarative
Metamath semantics, without consulting an implementation checker. -/
theorem NormalTheoremStep.toSemanticProvable
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula} {proofLabels : List String}
    (step : NormalTheoremStep before after label formula proofLabels) :
    Metamath.Spec.Semantic.Provable
      (dbToAxioms
        (sourceOperationalDatabase before.toSourcePrefix))
      (frameToContext
        (sourceOperationalCallerFrame before.toSourcePrefix))
      (exprToFormula
        (varMapOfFrame
          (sourceOperationalCallerFrame before.toSourcePrefix))
        (operationalExpr formula)) := by
  exact step.toSupportedDeclarative.toSemantic

/-- Negative boundary: local declaration payloads cannot witness a normal
theorem transition. -/
theorem normalTheorem_not_local :
    SourceOperation.checkTheoremNormal ∉ localOperations :=
  nonlocalOperations_absent.1

end Mettapedia.Languages.Metamath.SourceGSLTNormalTheorem
