import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorBindingObservation
import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorSuccessPriorityConformance

/-!
# Service-aware evaluator result composition

The original evaluator composition interfaces use the structural type-binding
carrier.  General evaluation can additionally return opaque binding payloads,
so the final seal uses the service-aware observation relation and carries the
runtime input-extension property required by continuation-time merge-back.

This module owns only composition.  Selected-application and tuple workers
remain separate proofs of the published two-stage evaluator judgments.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorServiceAwareConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EvaluatorBindingExtension
open LeaTTaEvaluatorBindingObservation
open LeaTTaEvaluatorConfigurationConformance
open LeaTTaSpecTypeService
open LeaTTaSpecConformance
open Spec.Eval

/-- One service-aware evaluator result together with the runtime theorem that
its binding output preserves every constraint of the runtime input.  The two
facts are bundled because the latter is consumed immediately by
continuation-time projection and merge. -/
structure ExtendingServiceAwareEvaluatorResultRuntimeRel
    (services : Spec.Eval.Minimal.Services) (scope : List String)
    (runtimeInput : Metta.Bindings)
    (result : ResultPair) (runtimeResult : Metta.Atom × Metta.Bindings) : Prop where
  observation : ServiceAwareScopedEvaluatorResultRuntimeRel services scope
    result runtimeResult
  extension : LeaBindingTheoryExtends runtimeInput runtimeResult.2

namespace ExtendingServiceAwareEvaluatorResultRuntimeRel

/-- Forget the input-extension evidence when only the public result
observation is consumed. -/
theorem toObservation
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {runtimeInput : Metta.Bindings}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (relation : ExtendingServiceAwareEvaluatorResultRuntimeRel services scope
      runtimeInput result runtimeResult) :
    ServiceAwareScopedEvaluatorResultRuntimeRel services scope
      result runtimeResult :=
  relation.observation

/-- Result witnesses restrict contravariantly in the public observation
scope without changing their runtime extension theorem. -/
theorem mono
    {services : Spec.Eval.Minimal.Services} {large small : List String}
    {runtimeInput : Metta.Bindings}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (relation : ExtendingServiceAwareEvaluatorResultRuntimeRel services large
      runtimeInput result runtimeResult)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ExtendingServiceAwareEvaluatorResultRuntimeRel services small
      runtimeInput result runtimeResult :=
  ⟨relation.observation.mono subset, relation.extension⟩

/-- Reconcile one recursive result with the binding state that seeded it.
The result relation's common-model theorem makes the executable's totalized
merge-head fallback unreachable and preserves the input-extension evidence
needed by the following continuation. -/
theorem mergeHead
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {runtimeInput runtimeOutput : Metta.Bindings}
    {result : ResultPair} {runtimeAtom : Metta.Atom}
    (relation : ExtendingServiceAwareEvaluatorResultRuntimeRel services scope
      runtimeInput result (runtimeAtom, runtimeOutput))
    (inputInvariant : LeaRuntimeBindingInvariant runtimeInput) :
    let selected :=
      (Metta.Bindings.merge runtimeInput runtimeOutput).head?.getD runtimeOutput
    ExtendingServiceAwareEvaluatorResultRuntimeRel services scope runtimeInput
      result (runtimeAtom, selected) := by
  dsimp only
  obtain ⟨observation, _selectedInvariant, selectedExtension⟩ :=
    relation.observation.mergeHead_extending inputInvariant relation.extension
  exact ⟨observation, selectedExtension⟩

/-- Reconcile one recursive result and immediately apply the selected
worker's repaired retention policy.  The result atom remains the emitted
observable, while the projected binding still extends the input theory. -/
theorem mergeHead_then_restrict_expectedApplicationRetentionScope
    {services : Spec.Eval.Minimal.Services} {publicScope : List String}
    {runtimeInput runtimeOutput : Metta.Bindings}
    {result : ResultPair} {runtimeAtom : Metta.Atom}
    (arguments : List Metta.Atom)
    (relation : ExtendingServiceAwareEvaluatorResultRuntimeRel services
      publicScope runtimeInput result (runtimeAtom, runtimeOutput))
    (inputInvariant : LeaRuntimeBindingInvariant runtimeInput)
    (publicRetained : ∀ name, name ∈ publicScope →
      name ∈ Metta.Minimal.expectedApplicationRetentionScope
        runtimeInput arguments) :
    let selected :=
      (Metta.Bindings.merge runtimeInput runtimeOutput).head?.getD runtimeOutput
    let retained := Metta.Minimal.restrictBnd
      (Metta.Minimal.expectedApplicationRetentionScope runtimeInput arguments)
      selected
    ExtendingServiceAwareEvaluatorResultRuntimeRel services publicScope
      runtimeInput result (runtimeAtom, retained) := by
  dsimp only
  obtain ⟨observation, _retainedInvariant, extension⟩ :=
    relation.observation.mergeHead_then_restrict_expectedApplicationRetentionScope
      arguments inputInvariant relation.extension publicRetained
  exact ⟨observation, extension⟩

end ExtendingServiceAwareEvaluatorResultRuntimeRel

/-- Soundness-only result-list interface for arbitrary-fuel evaluation.
Every concrete result has a fuel-free specification derivation, a
service-aware observation, and a runtime input-extension proof. -/
def ServiceAwareRawEvaluatorResultsRuntimeSound
    (services : Spec.Eval.Minimal.Services) (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (atom expectedType : Atom) (bindings : Bindings)
    (runtimeInput : Metta.Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop :=
  ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ result,
      EvalAtomRawRel space dispatch live (typing := typing)
          atom expectedType bindings result ∧
        ExtendingServiceAwareEvaluatorResultRuntimeRel services scope
          runtimeInput result runtimeResult

/-- Expression-interpreter soundness before the outer success-priority
boundary. -/
def ServiceAwareInterpretExpressionResultsRuntimeSound
    (services : Spec.Eval.Minimal.Services) (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (expression expectedType : Atom) (bindings : Bindings)
    (runtimeInput : Metta.Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop :=
  ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ result,
      InterpretExpressionRel space dispatch live (typing := typing)
          expression expectedType bindings result ∧
        ExtendingServiceAwareEvaluatorResultRuntimeRel services scope
          runtimeInput result runtimeResult

/-- Complete selected-application worker interface.  The intermediate
function interpretation and subsequent call remain separate derivations,
matching the published `interpret_expression` rule. -/
def ServiceAwareSelectedApplicationResultsRuntimeSound
    (services : Spec.Eval.Minimal.Services) (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (expression expectedType : Atom) (policy : SelectedTypePolicy)
    (applicableBindings : Bindings) (runtimeInput : Metta.Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop :=
  ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ interpreted callResult,
      InterpretFunctionRel space dispatch live (typing := typing)
          expression policy.functionType expectedType applicableBindings
            interpreted ∧
        CallRel space dispatch live (typing := typing)
          interpreted.1
          (if policy.returnType = Atom.expressionType
            then Atom.undefinedType else policy.returnType)
          interpreted.2 callResult ∧
        ExtendingServiceAwareEvaluatorResultRuntimeRel services scope
          runtimeInput callResult runtimeResult

/-- Tuple-fallback worker interface.  Tuple evaluation and expected-result
calling remain separate evidence, as required by the published tuple rule. -/
def ServiceAwareTupleApplicationResultsRuntimeSound
    (services : Spec.Eval.Minimal.Services) (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (expression expectedType : Atom) (bindings : Bindings)
    (runtimeInput : Metta.Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop :=
  ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ tupleResult callResult,
      InterpretTupleRel space dispatch live (typing := typing)
          expression bindings tupleResult ∧
        CallRel space dispatch live (typing := typing)
          tupleResult.1 expectedType tupleResult.2 callResult ∧
        ExtendingServiceAwareEvaluatorResultRuntimeRel services scope
          runtimeInput callResult runtimeResult

/-- Assemble the service-aware selected worker into the expression
interpreter without reopening either worker derivation. -/
theorem ServiceAwareInterpretExpressionResultsRuntimeSound.of_functionPath
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {expression expectedType operator : Atom}
    {arguments types : List Atom} {bindings applicableBindings : Bindings}
    {policy : SelectedTypePolicy} {runtimeInput : Metta.Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService}
    (expressionShape : expression = .expression (operator :: arguments))
    (typesOf : typing.typesOf space operator types)
    (scan : typing.candidateScan space expression expectedType bindings
      types (.success policy applicableBindings))
    (worker : ServiceAwareSelectedApplicationResultsRuntimeSound services
      scope space dispatch live expression expectedType policy
        applicableBindings runtimeInput runtimeResults typing) :
    ServiceAwareInterpretExpressionResultsRuntimeSound services scope space
      dispatch live expression expectedType bindings runtimeInput
        runtimeResults typing := by
  intro runtimeResult member
  obtain ⟨interpreted, callResult, interpretedDerivation, callDerivation,
      resultRelation⟩ := worker runtimeResult member
  exact ⟨callResult,
    InterpretExpressionRel.functionPath expression expectedType operator
      arguments types policy
      (if policy.returnType = Atom.expressionType
        then Atom.undefinedType else policy.returnType)
      bindings applicableBindings interpreted callResult expressionShape
      typesOf scan rfl interpretedDerivation callDerivation,
    resultRelation⟩

/-- Assemble the service-aware tuple worker into the expression interpreter
without duplicating tuple or call semantics at the selector boundary. -/
theorem ServiceAwareInterpretExpressionResultsRuntimeSound.of_tuplePath
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {expression expectedType operator : Atom}
    {arguments types errors : List Atom} {bindings : Bindings}
    {runtimeInput : Metta.Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService}
    (expressionShape : expression = .expression (operator :: arguments))
    (typesOf : typing.typesOf space operator types)
    (scan : typing.candidateScan space expression expectedType bindings
      types (.exhausted errors true))
    (worker : ServiceAwareTupleApplicationResultsRuntimeSound services scope
      space dispatch live expression expectedType bindings runtimeInput
        runtimeResults typing) :
    ServiceAwareInterpretExpressionResultsRuntimeSound services scope space
      dispatch live expression expectedType bindings runtimeInput
        runtimeResults typing := by
  intro runtimeResult member
  obtain ⟨tupleResult, callResult, tupleDerivation, callDerivation,
      resultRelation⟩ := worker runtimeResult member
  exact ⟨callResult,
    InterpretExpressionRel.tuplePath expression expectedType operator
      arguments types errors bindings tupleResult callResult expressionShape
      typesOf scan tupleDerivation callDerivation,
    resultRelation⟩

/-- Lift an expression-interpreter result through the corresponding outer
raw-evaluator success or error constructor. -/
theorem ServiceAwareRawEvaluatorResultsRuntimeSound.of_interpretExpression
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {atom expectedType metaType : Atom} {bindings : Bindings}
    {runtimeInput : Metta.Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService}
    (notEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (doesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType))
    (expressionShape : ∃ head tail, atom = .expression (head :: tail))
    (expressionSound : ServiceAwareInterpretExpressionResultsRuntimeSound
      services scope space dispatch live atom expectedType bindings
        runtimeInput runtimeResults typing) :
    ServiceAwareRawEvaluatorResultsRuntimeSound services scope space dispatch
      live atom expectedType bindings runtimeInput runtimeResults typing := by
  intro runtimeResult member
  obtain ⟨result, interpretation, relation⟩ :=
    expressionSound runtimeResult member
  by_cases error : IsErrorRel result.1
  · exact ⟨result,
      EvalAtomRawRel.interpretError atom expectedType metaType bindings result
        notEmptyOrError metaTypeRelation doesNotPass expressionShape
          interpretation error,
      relation⟩
  · exact ⟨result,
      EvalAtomRawRel.interpretSuccess atom expectedType metaType bindings result
        notEmptyOrError metaTypeRelation doesNotPass expressionShape
          interpretation error,
      relation⟩

/-! ## Boundary canaries -/

/-- Positive: the empty symbol result carries reflexive runtime extension. -/
example (services : Spec.Eval.Minimal.Services) (scope : List String) :
    ExtendingServiceAwareEvaluatorResultRuntimeRel services scope []
      (.symbol "a", Bindings.empty) (.sym "a", []) :=
  ⟨serviceAwareResultRuntimeRel_emptySymbol services scope,
    LeaBindingTheoryExtends.refl []⟩

/-- Negative: a result observation alone cannot manufacture the missing
runtime extension theorem. -/
theorem replacement_result_not_extending
    (services : Spec.Eval.Minimal.Services) (scope : List String) :
    ¬ExtendingServiceAwareEvaluatorResultRuntimeRel services scope
      [.val "x" (.sym "A")]
      (.symbol "a", Bindings.empty)
      (.sym "a", [.val "x" (.sym "B")]) := by
  intro relation
  let valuation : String → Metta.Atom := fun name =>
    if name = "x" then .sym "B" else .var name
  have satisfiesB : LeaTTaBridge.LeaBindingSatisfied valuation
      [.val "x" (.sym "B")] := by
    constructor
    · intro name value member
      simp at member
      rcases member with ⟨rfl, rfl⟩
      simp [valuation, LeaTTaBridge.applyClassSolution]
    · intro left right member
      simp at member
  have satisfiesA := relation.extension valuation satisfiesB
  have forced := satisfiesA.1 "x" (.sym "A") (by simp)
  simp [valuation, LeaTTaBridge.applyClassSolution] at forced

end Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorServiceAwareConformance
