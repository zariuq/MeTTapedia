import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorConfigurationConformance
import Mettapedia.Languages.MeTTa.HE.EvaluatorBindingExtension
import MettaHyperonFull.Proofs.Substitution

/-!
# LeaTTa evaluator success-priority conformance

The mutually recursive evaluator judgments describe individual raw results.
The public evaluator suppresses every error result whenever at least one
non-error result exists.  LeaTTa performs the same operation with
`prioritizeSemanticResults` after computing an ordered runtime result list.

This module proves that boundary once.  Constructor-local evaluator proofs
only need to establish bidirectional correspondence for the raw result list;
they never unfold or reproduce the success-priority policy.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorSuccessPriorityConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge
open LeaTTaBranchLocalTypeScanConformance
open LeaTTaEvaluatorConfigurationConformance
open LeaTTaMinimalInstructionConformance
open LeaTTaSpecTypeService
open LeaTTaTypeConformance
open LeaTTaTypeServiceConformance
open LeaTTaTypePresentationFoldConformance
open EvaluatorBindingExtension
open Spec.Bindings.ScopeObservation
open Spec.Eval
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.ScopeObservation

/-- Soundness-only half of raw evaluator correspondence.  Keeping this
direction named lets the arbitrary-fuel soundness induction advance without
assuming the independent completeness theorem for relational type services. -/
def RawEvaluatorResultsRuntimeSound
    (services : Spec.Eval.Minimal.Services)
    (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (atom expectedType : Atom) (bindings : Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop :=
  ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ result,
      EvalAtomRawRel space dispatch live (typing := typing)
          atom expectedType bindings result ∧
        ScopedEvaluatorResultRuntimeRel services scope
          result runtimeResult

/-- Every recursively related result of the repaired evaluator also carries
the semantic input-extension fact needed by the executable's defensive
merge-back.  This is derived from the specification judgment; it is not an
additional recursive hypothesis. -/
theorem RawEvaluatorResultsRuntimeSound.withBindingExtension
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType : Atom} {bindings : Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {oracle : TypePreparationOracle}
    (sound : RawEvaluatorResultsRuntimeSound services scope space dispatch
      live atom expectedType bindings runtimeResults
        (preparedPackageTypeService oracle)) :
    ∀ runtimeResult, runtimeResult ∈ runtimeResults →
      ∃ result,
        EvalAtomRawRel space dispatch live
            (typing := preparedPackageTypeService oracle)
            atom expectedType bindings result ∧
          ScopedEvaluatorResultRuntimeRel services scope
            result runtimeResult ∧
          BindingTheoryExtends bindings result.2 := by
  intro runtimeResult member
  obtain ⟨result, derivation, relation⟩ := sound runtimeResult member
  exact ⟨result, derivation, relation,
    prepared_evalAtomRawRel_bindingTheoryExtends derivation⟩

/-- A runtime result list is sound and complete for the raw evaluator
judgment, with every paired result compared at one public observation scope.

This relation deliberately says nothing about runtime state.  State threading
belongs to the configuration simulation; success prioritization only changes
the result list and leaves the state untouched. -/
structure RawEvaluatorResultsRuntimeRel
    (services : Spec.Eval.Minimal.Services)
    (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (atom expectedType : Atom) (bindings : Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop where
  sound : ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ result,
      EvalAtomRawRel space dispatch live (typing := typing)
          atom expectedType bindings result ∧
        ScopedEvaluatorResultRuntimeRel services scope
          result runtimeResult
  complete : ∀ result,
    EvalAtomRawRel space dispatch live (typing := typing)
        atom expectedType bindings result →
      ∃ runtimeResult, runtimeResult ∈ runtimeResults ∧
        ScopedEvaluatorResultRuntimeRel services scope
          result runtimeResult

/-- Forget completeness when composing the runtime-to-spec soundness
induction. -/
theorem RawEvaluatorResultsRuntimeRel.toSound
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType : Atom} {bindings : Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService}
    (relation : RawEvaluatorResultsRuntimeRel services scope space dispatch
      live atom expectedType bindings runtimeResults typing) :
    RawEvaluatorResultsRuntimeSound services scope space dispatch live atom
      expectedType bindings runtimeResults typing :=
  relation.sound

/-- Public counterpart of `RawEvaluatorResultsRuntimeRel`, stated against
`EvalRel` after success prioritization. -/
structure EvaluatorResultsRuntimeRel
    (services : Spec.Eval.Minimal.Services)
    (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (atom expectedType : Atom) (bindings : Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop where
  sound : ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ result,
      EvalRel space dispatch live atom expectedType bindings result typing ∧
        ScopedEvaluatorResultRuntimeRel services scope
          result runtimeResult
  complete : ∀ result,
    EvalRel space dispatch live atom expectedType bindings result typing →
      ∃ runtimeResult, runtimeResult ∈ runtimeResults ∧
        ScopedEvaluatorResultRuntimeRel services scope
          result runtimeResult

/-- Bidirectional correspondence for the expression interpreter before the
outer `EvalAtomRawRel` constructor records whether an individual result is an
error.  This is a separate carrier because success priority belongs only to
the outer evaluator boundary; `InterpretExpressionRel` itself exposes every
raw expression result. -/
structure InterpretExpressionResultsRuntimeRel
    (services : Spec.Eval.Minimal.Services)
    (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (expression expectedType : Atom) (bindings : Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop where
  sound : ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ result,
      InterpretExpressionRel space dispatch live (typing := typing)
          expression expectedType bindings result ∧
        ScopedEvaluatorResultRuntimeRel services scope
          result runtimeResult
  complete : ∀ result,
    InterpretExpressionRel space dispatch live (typing := typing)
        expression expectedType bindings result →
      ∃ runtimeResult, runtimeResult ∈ runtimeResults ∧
        ScopedEvaluatorResultRuntimeRel services scope
          result runtimeResult

/-- Soundness-only expression boundary used by the arbitrary-fuel evaluator
induction.  Completeness is intentionally absent: a finite runtime fuel may
replace an unfinished branch by `StackOverflow`, while the fuel-free
specification still contains the eventual derivation. -/
def InterpretExpressionResultsRuntimeSound
    (services : Spec.Eval.Minimal.Services)
    (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (expression expectedType : Atom) (bindings : Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop :=
  ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ result,
      InterpretExpressionRel space dispatch live (typing := typing)
          expression expectedType bindings result ∧
        ScopedEvaluatorResultRuntimeRel services scope
          result runtimeResult

/-- Soundness interface for the complete selected-application executor.
Each runtime result carries the intermediate `InterpretFunctionRel` result
and the subsequent `CallRel` derivation separately, matching the two-stage
published `interpret_expression` rule rather than collapsing them into an
opaque evaluator hypothesis. -/
def SelectedApplicationResultsRuntimeSound
    (services : Spec.Eval.Minimal.Services)
    (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (expression expectedType : Atom) (policy : SelectedTypePolicy)
    (applicableBindings : Bindings)
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
        ScopedEvaluatorResultRuntimeRel services scope
          callResult runtimeResult

/-- Soundness interface for the tuple-fallback executor.  The tuple
interpretation and expected-result call remain distinct evidence, exactly as
in `InterpretExpressionRel.tuplePath`. -/
def TupleApplicationResultsRuntimeSound
    (services : Spec.Eval.Minimal.Services)
    (scope : List String)
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch) (live : List Atom)
    (expression expectedType : Atom) (bindings : Bindings)
    (runtimeResults : List (Metta.Atom × Metta.Bindings))
    (typing : EvalTypeService := publishedTypeService) : Prop :=
  ∀ runtimeResult, runtimeResult ∈ runtimeResults →
    ∃ tupleResult callResult,
      InterpretTupleRel space dispatch live (typing := typing)
          expression bindings tupleResult ∧
        CallRel space dispatch live (typing := typing)
          tupleResult.1 expectedType tupleResult.2 callResult ∧
        ScopedEvaluatorResultRuntimeRel services scope
          callResult runtimeResult

/-- Forget expression completeness when entering the arbitrary-fuel
soundness induction. -/
theorem InterpretExpressionResultsRuntimeRel.toSound
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {expression expectedType : Atom} {bindings : Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService}
    (relation : InterpretExpressionResultsRuntimeRel services scope
      space dispatch live expression expectedType bindings runtimeResults
        typing) :
    InterpretExpressionResultsRuntimeSound services scope space dispatch live
      expression expectedType bindings runtimeResults typing :=
  relation.sound

/-- Assemble the selected application worker into the expression
interpreter.  Candidate selection remains the sole owner of the selected
policy and applicability output; the worker only supplies the two semantic
continuations for each concrete result. -/
theorem InterpretExpressionResultsRuntimeSound.of_functionPath
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {expression expectedType operator : Atom}
    {arguments types : List Atom} {bindings applicableBindings : Bindings}
    {policy : SelectedTypePolicy}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService}
    (expressionShape : expression = .expression (operator :: arguments))
    (typesOf : typing.typesOf space operator types)
    (scan : typing.candidateScan space expression expectedType bindings types
      (.success policy applicableBindings))
    (worker : SelectedApplicationResultsRuntimeSound services scope space
      dispatch live expression expectedType policy applicableBindings
        runtimeResults typing) :
    InterpretExpressionResultsRuntimeSound services scope space dispatch live
      expression expectedType bindings runtimeResults typing := by
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

/-- Assemble tuple fallback into the expression interpreter without
duplicating tuple or call semantics at the selector boundary. -/
theorem InterpretExpressionResultsRuntimeSound.of_tuplePath
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {expression expectedType operator : Atom}
    {arguments types errors : List Atom} {bindings : Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService}
    (expressionShape : expression = .expression (operator :: arguments))
    (typesOf : typing.typesOf space operator types)
    (scan : typing.candidateScan space expression expectedType bindings types
      (.exhausted errors true))
    (worker : TupleApplicationResultsRuntimeSound services scope space
      dispatch live expression expectedType bindings runtimeResults typing) :
    InterpretExpressionResultsRuntimeSound services scope space dispatch live
      expression expectedType bindings runtimeResults typing := by
  intro runtimeResult member
  obtain ⟨tupleResult, callResult, tupleDerivation, callDerivation,
      resultRelation⟩ := worker runtimeResult member
  exact ⟨callResult,
    InterpretExpressionRel.tuplePath expression expectedType operator
      arguments types errors bindings tupleResult callResult expressionShape
      typesOf scan tupleDerivation callDerivation,
    resultRelation⟩

/-- The raw empty/error constructor is complete as well as sound: every other
raw constructor carries the contradictory premise that the source is neither
empty nor an error. -/
theorem RawEvaluatorResultsRuntimeRel.of_emptyOrError
    {services : Spec.Eval.Minimal.Services}
    {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType : Atom} {bindings : Bindings}
    {runtimeResult : Metta.Atom × Metta.Bindings}
    {typing : EvalTypeService}
    (emptyOrError : IsEmptyOrErrorRel atom)
    (resultRelation : ScopedEvaluatorResultRuntimeRel services scope
      (atom, bindings) runtimeResult) :
    RawEvaluatorResultsRuntimeRel services scope
      space dispatch live atom expectedType bindings [runtimeResult] typing := by
  constructor
  · intro candidate member
    have candidateEq : candidate = runtimeResult := by simpa using member
    subst candidate
    exact ⟨(atom, bindings),
      EvalAtomRawRel.emptyOrError atom expectedType bindings emptyOrError,
      resultRelation⟩
  · intro result rawResult
    have resultEq : result = (atom, bindings) := by
      cases rawResult with
      | emptyOrError => rfl
      | typePass _ _ _ _ notEmptyOrError _ _ =>
          exact (notEmptyOrError emptyOrError).elim
      | cast _ _ _ _ _ notEmptyOrError _ _ _ _ =>
          exact (notEmptyOrError emptyOrError).elim
      | interpretSuccess _ _ _ _ _ notEmptyOrError _ _ _ _ _ =>
          exact (notEmptyOrError emptyOrError).elim
      | interpretError _ _ _ _ _ notEmptyOrError _ _ _ _ _ =>
          exact (notEmptyOrError emptyOrError).elim
    subst result
    exact ⟨runtimeResult, by simp, resultRelation⟩

/-- The raw meta-type passthrough constructor is likewise exact.  Intrinsic
meta-type functionality makes every cast or expression constructor
contradict the same passthrough disjunction. -/
theorem RawEvaluatorResultsRuntimeRel.of_typePass
    {services : Spec.Eval.Minimal.Services}
    {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType metaType : Atom}
    {bindings : Bindings}
    {runtimeResult : Metta.Atom × Metta.Bindings}
    {typing : EvalTypeService}
    (notEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (passes : expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType)
    (resultRelation : ScopedEvaluatorResultRuntimeRel services scope
      (atom, bindings) runtimeResult) :
    RawEvaluatorResultsRuntimeRel services scope
      space dispatch live atom expectedType bindings [runtimeResult] typing := by
  constructor
  · intro candidate member
    have candidateEq : candidate = runtimeResult := by simpa using member
    subst candidate
    exact ⟨(atom, bindings), EvalAtomRawRel.typePass atom expectedType
      metaType bindings notEmptyOrError metaTypeRelation passes,
      resultRelation⟩
  · intro result rawResult
    have resultEq : result = (atom, bindings) := by
      cases rawResult with
      | emptyOrError _ _ _ emptyOrError =>
          exact (notEmptyOrError emptyOrError).elim
      | typePass => rfl
      | cast _ _ competingMetaType _ _ _ competingMetaTypeRelation
          doesNotPass _ _ =>
          have metaTypeEq := metaTypeRelation.eq competingMetaTypeRelation
          subst competingMetaType
          exact (doesNotPass passes).elim
      | interpretSuccess _ _ competingMetaType _ _ _
          competingMetaTypeRelation doesNotPass _ _ _ =>
          have metaTypeEq := metaTypeRelation.eq competingMetaTypeRelation
          subst competingMetaType
          exact (doesNotPass passes).elim
      | interpretError _ _ competingMetaType _ _ _
          competingMetaTypeRelation doesNotPass _ _ _ =>
          have metaTypeEq := metaTypeRelation.eq competingMetaTypeRelation
          subst competingMetaType
          exact (doesNotPass passes).elim
    subst result
    exact ⟨runtimeResult, by simp, resultRelation⟩

/-- Once the mutually exclusive empty/error and meta-type passthrough gates
have failed on a non-expression source, every raw derivation is necessarily a
type-cast derivation.  This inversion is shared by successful and failed
runtime cast arms. -/
theorem EvalAtomRawRel.typeCast_of_castGate
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType metaType : Atom}
    {bindings : Bindings} {result : ResultPair} {typing : EvalTypeService}
    {protectedScope : List String}
    (notEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (doesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType))
    (castShape :
      (∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit)
    (rawResult : EvalAtomRawRel space dispatch live
      (protectedScope := protectedScope) (typing := typing)
      atom expectedType bindings result) :
    typing.typeCast protectedScope space atom expectedType bindings result := by
  cases rawResult with
  | emptyOrError _ _ _ emptyOrError =>
      exact (notEmptyOrError emptyOrError).elim
  | typePass _ _ competingMetaType _ _ competingMetaTypeRelation passes =>
      have metaTypeEq := metaTypeRelation.eq competingMetaTypeRelation
      subst competingMetaType
      exact (doesNotPass passes).elim
  | cast _ _ _ _ _ _ _ _ _ serviceCast =>
      exact serviceCast
  | interpretSuccess _ _ _ _ _ _ _ _ expressionShape _ _ =>
      rcases castShape with ⟨name, rfl⟩ | ⟨value, rfl⟩ | rfl <;>
        rcases expressionShape with ⟨head, tail, equation⟩ <;>
        simp [Atom.unit] at equation
  | interpretError _ _ _ _ _ _ _ _ expressionShape _ _ =>
      rcases castShape with ⟨name, rfl⟩ | ⟨value, rfl⟩ | rfl <;>
        rcases expressionShape with ⟨head, tail, equation⟩ <;>
        simp [Atom.unit] at equation

/-- Once the empty/error, meta-type passthrough, and non-expression cast
gates have failed, a raw derivation for a nonempty expression necessarily
comes from the expression interpreter. -/
theorem EvalAtomRawRel.interpretExpression_of_expressionGate
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType metaType : Atom}
    {bindings : Bindings} {result : ResultPair} {typing : EvalTypeService}
    (notEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (doesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType))
    (expressionShape : ∃ head tail, atom = .expression (head :: tail))
    (rawResult : EvalAtomRawRel space dispatch live (typing := typing)
      atom expectedType bindings result) :
    InterpretExpressionRel space dispatch live (typing := typing)
      atom expectedType bindings result := by
  cases rawResult with
  | emptyOrError _ _ _ emptyOrError =>
      exact (notEmptyOrError emptyOrError).elim
  | typePass _ _ competingMetaType _ _ competingMetaTypeRelation passes =>
      have metaTypeEq := metaTypeRelation.eq competingMetaTypeRelation
      subst competingMetaType
      exact (doesNotPass passes).elim
  | cast _ _ competingMetaType _ _ _ competingMetaTypeRelation _ castShape _ =>
      have metaTypeEq := metaTypeRelation.eq competingMetaTypeRelation
      subst competingMetaType
      rcases expressionShape with ⟨head, tail, rfl⟩
      rcases castShape with ⟨name, equation⟩ | ⟨value, equation⟩ | equation <;>
        simp [Atom.unit] at equation
  | interpretSuccess _ _ competingMetaType _ _ _ competingMetaTypeRelation
      competingDoesNotPass _ interpreted _ =>
      have metaTypeEq := metaTypeRelation.eq competingMetaTypeRelation
      subst competingMetaType
      exact interpreted
  | interpretError _ _ competingMetaType _ _ _ competingMetaTypeRelation
      competingDoesNotPass _ interpreted _ =>
      have metaTypeEq := metaTypeRelation.eq competingMetaTypeRelation
      subst competingMetaType
      exact interpreted

/-- The expression-interpreter result list is exactly the raw evaluator
result list once the three preceding dispatch gates select the expression
arm.  Error classification is reconstructed per result, without filtering or
reordering; public success priority remains the separate outer theorem. -/
theorem RawEvaluatorResultsRuntimeRel.of_interpretExpression
    {services : Spec.Eval.Minimal.Services}
    {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType metaType : Atom}
    {bindings : Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService}
    (notEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (doesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType))
    (expressionShape : ∃ head tail, atom = .expression (head :: tail))
    (relation : InterpretExpressionResultsRuntimeRel services scope
      space dispatch live atom expectedType bindings runtimeResults typing) :
    RawEvaluatorResultsRuntimeRel services scope space dispatch live atom
      expectedType bindings runtimeResults typing := by
  constructor
  · intro runtimeResult member
    obtain ⟨result, interpreted, resultRelation⟩ :=
      relation.sound runtimeResult member
    by_cases resultError : IsErrorRel result.1
    · exact ⟨result,
        EvalAtomRawRel.interpretError atom expectedType metaType bindings result
          notEmptyOrError metaTypeRelation doesNotPass expressionShape
          interpreted resultError,
        resultRelation⟩
    · exact ⟨result,
        EvalAtomRawRel.interpretSuccess atom expectedType metaType bindings result
          notEmptyOrError metaTypeRelation doesNotPass expressionShape
          interpreted resultError,
        resultRelation⟩
  · intro result rawResult
    exact relation.complete result
      (EvalAtomRawRel.interpretExpression_of_expressionGate notEmptyOrError
        metaTypeRelation doesNotPass expressionShape rawResult)

/-- Soundness-only companion of `of_interpretExpression`.  This is the form
consumed by the arbitrary-fuel evaluator proof: each emitted runtime result
selects exactly one of the raw success/error constructors, while no semantic
completeness claim is made at finite fuel. -/
theorem RawEvaluatorResultsRuntimeSound.of_interpretExpression
    {services : Spec.Eval.Minimal.Services}
    {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType metaType : Atom}
    {bindings : Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService}
    (notEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (doesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType))
    (expressionShape : ∃ head tail, atom = .expression (head :: tail))
    (relation : InterpretExpressionResultsRuntimeSound services scope
      space dispatch live atom expectedType bindings runtimeResults typing) :
    RawEvaluatorResultsRuntimeSound services scope space dispatch live atom
      expectedType bindings runtimeResults typing := by
  intro runtimeResult member
  obtain ⟨result, interpreted, resultRelation⟩ := relation runtimeResult member
  by_cases resultError : IsErrorRel result.1
  · exact ⟨result,
      EvalAtomRawRel.interpretError atom expectedType metaType bindings result
        notEmptyOrError metaTypeRelation doesNotPass expressionShape
        interpreted resultError,
      resultRelation⟩
  · exact ⟨result,
      EvalAtomRawRel.interpretSuccess atom expectedType metaType bindings result
        notEmptyOrError metaTypeRelation doesNotPass expressionShape
        interpreted resultError,
      resultRelation⟩

/-- The executable empty/error arm is independent of the expected type once
the outer call has positive fuel.  The source equation is explicit because
LeaTTa instantiates the input binding before inspecting the atom. -/
theorem mettaEvalExpected_succ_emptyOrError
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (runtimeBindings : Metta.Bindings) (runtimeAtom runtimeExpected
      runtimeSource : Metta.Atom)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (emptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = true) :
    Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected =
      ([(runtimeSource, runtimeBindings)], state) := by
  by_cases expectedUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = true
  · simp [Metta.Minimal.mettaEvalExpected, expectedUndefined,
      Metta.Minimal.mettaEval, sourceEquation, emptyOrError]
  · have expectedUndefinedFalse :
        (runtimeExpected == Metta.Atom.sym "%Undefined%") = false := by
      cases equation : runtimeExpected == Metta.Atom.sym "%Undefined%" <;>
        simp_all
    simp [Metta.Minimal.mettaEvalExpected, expectedUndefinedFalse,
      sourceEquation, emptyOrError]

/-- Constructor-local simulation of `EvalAtomRawRel.emptyOrError` through the
actual positive-fuel `mettaEvalExpected` entry point.  The result relation is
the incoming configuration correspondence reused unchanged by the runtime's
passthrough arm; no recursive evaluator premise is needed. -/
theorem rawEvaluatorResultsRuntimeRel_mettaEvalExpected_emptyOrError
    {services : Spec.Eval.Minimal.Services}
    {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType : Atom} {bindings : Bindings}
    {runtimeAtom runtimeExpected runtimeSource : Metta.Atom}
    {runtimeBindings : Metta.Bindings} {typing : EvalTypeService}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (runtimeEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = true)
    (specEmptyOrError : IsEmptyOrErrorRel atom)
    (resultRelation : ScopedEvaluatorResultRuntimeRel services scope
      (atom, bindings) (runtimeSource, runtimeBindings)) :
    RawEvaluatorResultsRuntimeRel services scope
      space dispatch live atom expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1 typing := by
  rw [mettaEvalExpected_succ_emptyOrError env fuel state runtimeBindings
    runtimeAtom runtimeExpected runtimeSource sourceEquation runtimeEmptyOrError]
  exact .of_emptyOrError specEmptyOrError resultRelation

/-- Relation-driven empty/error constructor bridge.  The runtime gate is
derived from the atom carrier rather than repeated as an independent premise. -/
theorem rawEvaluatorResultsRuntimeRel_mettaEvalExpected_emptyOrError_of_relation
    {services : Spec.Eval.Minimal.Services}
    {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType : Atom} {bindings : Bindings}
    {runtimeAtom runtimeExpected runtimeSource : Metta.Atom}
    {runtimeBindings : Metta.Bindings} {typing : EvalTypeService}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (specEmptyOrError : IsEmptyOrErrorRel atom)
    (resultRelation : ScopedEvaluatorResultRuntimeRel services scope
      (atom, bindings) (runtimeSource, runtimeBindings)) :
    RawEvaluatorResultsRuntimeRel services scope
      space dispatch live atom expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1 typing := by
  have runtimeEmptyOrError :=
    (atomRuntimeRel_isEmptyOrError_iff sourceRelation).mp specEmptyOrError
  exact rawEvaluatorResultsRuntimeRel_mettaEvalExpected_emptyOrError
    env fuel state sourceEquation runtimeEmptyOrError specEmptyOrError
      resultRelation

/-- Empty/error passthrough from one exact incoming presentation state.  The
classification equation is intentionally constructor-local: finite
substitution does not preserve `Error`-headedness for arbitrary atoms. -/
theorem rawEvaluatorResultsRuntimeRel_mettaEvalExpected_emptyOrError_of_exactState
    {services : Spec.Eval.Minimal.Services}
    {scope : List String} {space : Space}
    {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {atom expectedType : Atom} {bindings : Bindings}
    {presentation : TypeSubst} {runtimeBindings : Metta.Bindings}
    {runtimeAtom runtimeExpected runtimeSource : Metta.Atom}
    {typing : EvalTypeService}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (runtimeEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = true)
    (specEmptyOrError : IsEmptyOrErrorRel atom)
    (incomingState : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (sourceRelation : AtomRuntimeRel services
      (presentation.apply atom) runtimeSource)
    (errorShape : IsErrorRel atom ↔ runtimeSource.isError = true) :
    RawEvaluatorResultsRuntimeRel services scope space dispatch live atom
      expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1 typing := by
  apply rawEvaluatorResultsRuntimeRel_mettaEvalExpected_emptyOrError
    env fuel state sourceEquation runtimeEmptyOrError specEmptyOrError
  exact ScopedEvaluatorResultRuntimeRel.ofExactAppliedAtom
    incomingState sourceRelation errorShape

/-- The executable meta-type passthrough arm for a non-undefined expected
type.  All three Boolean gates are named so later correspondence proofs can
discharge them from atom/type translation without unfolding the evaluator. -/
theorem mettaEvalExpected_succ_typePass
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (runtimeBindings : Metta.Bindings) (runtimeAtom runtimeExpected
      runtimeSource : Metta.Atom)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (expectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (sourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (passes :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = true) :
    Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected =
      ([(runtimeSource, runtimeBindings)], state) := by
  simp [Metta.Minimal.mettaEvalExpected, expectedNotUndefined,
    sourceEquation, sourceNotEmptyOrError, passes]

/-- Constructor-local simulation of `EvalAtomRawRel.typePass` through the
actual non-undefined expected-evaluation arm. -/
theorem rawEvaluatorResultsRuntimeRel_mettaEvalExpected_typePass
    {services : Spec.Eval.Minimal.Services}
    {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType metaType : Atom}
    {bindings : Bindings}
    {runtimeAtom runtimeExpected runtimeSource : Metta.Atom}
    {runtimeBindings : Metta.Bindings} {typing : EvalTypeService}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (expectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (sourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (runtimePasses :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = true)
    (specNotEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (specPasses : expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType)
    (resultRelation : ScopedEvaluatorResultRuntimeRel services scope
      (atom, bindings) (runtimeSource, runtimeBindings)) :
    RawEvaluatorResultsRuntimeRel services scope
      space dispatch live atom expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1 typing := by
  rw [mettaEvalExpected_succ_typePass env fuel state runtimeBindings
    runtimeAtom runtimeExpected runtimeSource sourceEquation
    expectedNotUndefined sourceNotEmptyOrError runtimePasses]
  exact .of_typePass specNotEmptyOrError metaTypeRelation specPasses
    resultRelation

/-- Relation-driven non-undefined meta-type passthrough bridge.  All three
runtime Boolean premises are consequences of the two atom carriers and the
published `MetaTypeRel`; only the semantic negative facts remain explicit. -/
theorem rawEvaluatorResultsRuntimeRel_mettaEvalExpected_typePass_of_relations
    {services : Spec.Eval.Minimal.Services}
    {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType metaType : Atom}
    {bindings : Bindings}
    {runtimeAtom runtimeExpected runtimeSource : Metta.Atom}
    {runtimeBindings : Metta.Bindings} {typing : EvalTypeService}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (expectedRelation :
      AtomRuntimeRel services expectedType runtimeExpected)
    (specNotEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (expectedNotUndefined : expectedType ≠ Atom.undefinedType)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (specPasses : expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType)
    (resultRelation : ScopedEvaluatorResultRuntimeRel services scope
      (atom, bindings) (runtimeSource, runtimeBindings)) :
    RawEvaluatorResultsRuntimeRel services scope
      space dispatch live atom expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1 typing := by
  have runtimeExpectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false := by
    cases equation : runtimeExpected == Metta.Atom.sym "%Undefined%" with
    | false => rfl
    | true =>
        exact (expectedNotUndefined
          ((atomRuntimeRel_isUndefined_iff expectedRelation).mpr equation)).elim
  have runtimeSourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) =
        false := by
    cases equation :
        runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError with
    | false => rfl
    | true =>
        exact (specNotEmptyOrError
          ((atomRuntimeRel_isEmptyOrError_iff sourceRelation).mpr equation)).elim
  have runtimePasses :=
    (atomRuntimeRel_typePass_iff sourceRelation expectedRelation
      metaTypeRelation).mp specPasses
  exact rawEvaluatorResultsRuntimeRel_mettaEvalExpected_typePass
    env fuel state sourceEquation runtimeExpectedNotUndefined
      runtimeSourceNotEmptyOrError runtimePasses specNotEmptyOrError
      metaTypeRelation specPasses resultRelation

/-- Meta-type passthrough from one exact incoming presentation state. -/
theorem rawEvaluatorResultsRuntimeRel_mettaEvalExpected_typePass_of_exactState
    {services : Spec.Eval.Minimal.Services}
    {scope : List String} {space : Space}
    {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {atom expectedType metaType : Atom} {bindings : Bindings}
    {presentation : TypeSubst} {runtimeBindings : Metta.Bindings}
    {runtimeAtom runtimeExpected runtimeSource : Metta.Atom}
    {typing : EvalTypeService}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (expectedRelation : AtomRuntimeRel services expectedType runtimeExpected)
    (presentationSourceRelation : AtomRuntimeRel services
      (presentation.apply atom) runtimeSource)
    (errorShape : IsErrorRel atom ↔ runtimeSource.isError = true)
    (incomingState : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (specNotEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (expectedNotUndefined : expectedType ≠ Atom.undefinedType)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (specPasses : expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType) :
    RawEvaluatorResultsRuntimeRel services scope space dispatch live atom
      expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1 typing := by
  apply rawEvaluatorResultsRuntimeRel_mettaEvalExpected_typePass_of_relations
    env fuel state sourceEquation sourceRelation expectedRelation
      specNotEmptyOrError expectedNotUndefined metaTypeRelation specPasses
  exact ScopedEvaluatorResultRuntimeRel.ofExactAppliedAtom
    incomingState presentationSourceRelation errorShape

/-- A failed non-expression cast emits every rejected actual type in source
order.  All emitted atoms are errors, so success prioritization leaves the
complete negative ledger unchanged. -/
theorem mettaEvalExpected_succ_castFailure
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (runtimeBindings : Metta.Bindings) (runtimeAtom runtimeExpected
      runtimeSource : Metta.Atom) (rejected : List Metta.Atom)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (expectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (sourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (doesNotPass :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = false)
    (castShape :
      (∃ name, runtimeSource = .sym name) ∨
        (∃ value, runtimeSource = .gnd value) ∨
        runtimeSource = .expr [])
    (castFailure : Metta.Minimal.mettaTypeCast env state.world
      runtimeBindings runtimeSource runtimeExpected = .inl rejected) :
    Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected =
      (rejected.map (fun actual =>
        (Metta.Minimal.badTypeAtom runtimeSource runtimeExpected actual,
          runtimeBindings)), state) := by
  have priority :
      Metta.Minimal.prioritizeSemanticResults
          (rejected.map (fun actual =>
            (Metta.Minimal.badTypeAtom runtimeSource runtimeExpected actual,
              runtimeBindings)), state) =
        (rejected.map (fun actual =>
          (Metta.Minimal.badTypeAtom runtimeSource runtimeExpected actual,
            runtimeBindings)), state) := by
    simp [Metta.Minimal.prioritizeSemanticResults,
      Metta.Minimal.badTypeAtom, Metta.Atom.isError]
  rw [Metta.Minimal.mettaEvalExpected.eq_1]
  simp only [expectedNotUndefined, Bool.false_eq_true, ↓reduceIte,
    sourceEquation, sourceNotEmptyOrError, doesNotPass]
  rcases castShape with ⟨name, sourceEq⟩ | ⟨value, sourceEq⟩ | sourceEq
  all_goals
    rw [sourceEq] at castFailure priority ⊢
    simp only [castFailure]
    exact priority

/-- One rejected prepared type produces the corresponding structured runtime
`BadType` result.  Expected and actual fields use the diagnostic structural
readout; the source retains the ordinary evaluator atom relation. -/
theorem scopedEvaluatorResultRuntimeRel_badType
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {presentation : TypeSubst} {bindings : Bindings}
    {runtimeBindings : Metta.Bindings}
    {atom expectedType actualType : Atom}
    {runtimeSource runtimeExpected : Metta.Atom}
    (state : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (sourceUnchanged : presentation.apply atom = atom)
    (expectedEquation : runtimeExpected = toLeaTTaAtom expectedType) :
    ScopedEvaluatorResultRuntimeRel services scope
      (mkError atom (.badType expectedType actualType), bindings)
      (Metta.Minimal.badTypeAtom runtimeSource runtimeExpected
        (toLeaTTaAtom actualType), runtimeBindings) := by
  apply ScopedEvaluatorResultRuntimeRel.ofBadType state
  · exact ⟨atom, runtimeSource, by simpa [sourceUnchanged] using
        (ObservedTypeAlphaRel.refl atom), sourceRelation, rfl⟩
  · rw [expectedEquation]
    exact ScopedEvaluatorResultRuntimeRel.structuralAtom expectedType
  · exact ScopedEvaluatorResultRuntimeRel.structuralAtom actualType

/-- Private-alpha rejected candidates yield the same observable `BadType`
diagnostic while retaining their independent specification spelling. -/
theorem scopedEvaluatorResultRuntimeRel_badType_privateCandidate
    {services : Spec.Eval.Minimal.Services} {scope fixedScope : List String}
    {presentation : TypeSubst} {bindings : Bindings}
    {runtimeBindings : Metta.Bindings}
    {atom expectedType leftActual rightActual : Atom}
    {runtimeSource runtimeExpected : Metta.Atom}
    (state : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (actualAlpha : PrivateCandidateAlphaRel
      fixedScope leftActual rightActual)
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (sourceUnchanged : presentation.apply atom = atom)
    (expectedEquation : runtimeExpected = toLeaTTaAtom expectedType) :
    ScopedEvaluatorResultRuntimeRel services scope
      (mkError atom (.badType expectedType leftActual), bindings)
      (Metta.Minimal.badTypeAtom runtimeSource runtimeExpected
        (toLeaTTaAtom rightActual), runtimeBindings) := by
  apply ScopedEvaluatorResultRuntimeRel.ofBadType state
  · exact ⟨atom, runtimeSource, by simpa [sourceUnchanged] using
        (ObservedTypeAlphaRel.refl atom), sourceRelation, rfl⟩
  · rw [expectedEquation]
    exact ScopedEvaluatorResultRuntimeRel.structuralAtom expectedType
  · exact ScopedEvaluatorResultRuntimeRel.structuralPrivateCandidate actualAlpha

/-- Every field-wise selector diagnostic is an evaluator result observation
under the unchanged incoming binding state.  This is the sole conversion from
the type-service error vocabulary to the evaluator error vocabulary; order
and multiplicity are handled by the list theorem below. -/
theorem candidateErrorAtomRuntimeRel_toScopedEvaluatorResult
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {presentation : TypeSubst} {bindings : Bindings}
    {runtimeBindings : Metta.Bindings}
    {expression specError : Atom}
    {runtimeExpression : Metta.Atom}
    {runtimeError : Metta.Minimal.ExpectedFunctionTypeError}
    (state : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (sourceObservation : EvaluatorAtomObservationRel services presentation
      runtimeBindings expression runtimeExpression)
    (errorRelation : CandidateErrorAtomRuntimeRel expression
      specError runtimeError) :
    ScopedEvaluatorResultRuntimeRel services scope (specError, bindings)
      (runtimeError.toAtom runtimeExpression, runtimeBindings) := by
  cases errorRelation with
  | incorrectArity =>
      simpa [Metta.Minimal.ExpectedFunctionTypeError.toAtom,
        Metta.Minimal.FunctionTypeError.toAtom] using
        ScopedEvaluatorResultRuntimeRel.ofIncorrectNumberOfArguments
          state sourceObservation
  | @badArgument diagnostic runtime diagnosticRelation =>
      apply ScopedEvaluatorResultRuntimeRel.ofBadArgType state
        diagnosticRelation.position sourceObservation
      · unfold StructuralAtomObservationRel
        exact diagnosticRelation.expected
      · unfold StructuralAtomObservationRel
        exact diagnosticRelation.actual
  | @badReturn diagnostic runtime diagnosticRelation =>
      cases diagnosticRelation with
      | @badReturn expected actual runtimeActual actualRelation =>
          apply ScopedEvaluatorResultRuntimeRel.ofBadType state
            sourceObservation
          · exact ScopedEvaluatorResultRuntimeRel.structuralAtom expected
          · unfold StructuralAtomObservationRel
            exact actualRelation

/-- Pointwise candidate-error correspondence is total from the runtime list
back to the specification list.  This preserves duplicate diagnostics and
their declaration order; it is only a membership projection for the
single-result relational semantics. -/
theorem candidateErrorBlockRuntimeRel_exists_left_of_mem_right
    {expression : Atom} {specErrors : List Atom}
    {runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError}
    (relation : CandidateErrorBlockRuntimeRel expression specErrors
      runtimeErrors) :
    ∀ runtimeError ∈ runtimeErrors,
      ∃ specError ∈ specErrors,
        CandidateErrorAtomRuntimeRel expression specError runtimeError := by
  intro runtimeError member
  induction relation with
  | nil => simp at member
  | @cons specHead runtimeHead specTail runtimeTail head tail
      inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨specHead, by simp, head⟩
      · obtain ⟨specError, specMember, errorRelation⟩ :=
          inductionHypothesis tailMember
        exact ⟨specError, by simp [specMember], errorRelation⟩

/-- An exhausted selector's ordered runtime error list is sound for the
`InterpretExpressionRel.functionError` constructor.  Tuple results, when the
same exhausted outcome permits them, are composed separately; this theorem
accounts for exactly the appended error block and nothing else. -/
theorem InterpretExpressionResultsRuntimeSound.of_functionErrors
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {expression expectedType operator : Atom}
    {arguments types specErrors : List Atom} {tupleEligible : Bool}
    {bindings : Bindings} {runtimeBindings : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError}
    {typing : EvalTypeService} {presentation : TypeSubst}
    (expressionShape : expression = .expression (operator :: arguments))
    (typesOf : typing.typesOf space operator types)
    (scan : typing.candidateScan space expression expectedType bindings types
      (.exhausted specErrors tupleEligible))
    (state : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (sourceObservation : EvaluatorAtomObservationRel services presentation
      runtimeBindings expression runtimeExpression)
    (errors : CandidateErrorBlockRuntimeRel expression specErrors
      runtimeErrors) :
    InterpretExpressionResultsRuntimeSound services scope space dispatch live
      expression expectedType bindings
      (runtimeErrors.map fun error =>
        (error.toAtom runtimeExpression, runtimeBindings)) typing := by
  intro runtimeResult member
  obtain ⟨runtimeError, runtimeErrorMember, runtimeResultEquation⟩ :=
    List.mem_map.mp member
  subst runtimeResult
  obtain ⟨specError, specErrorMember, errorRelation⟩ :=
    candidateErrorBlockRuntimeRel_exists_left_of_mem_right errors
      runtimeError runtimeErrorMember
  exact ⟨(specError, bindings),
    InterpretExpressionRel.functionError expression expectedType operator
      specError arguments types specErrors tupleEligible bindings
      expressionShape typesOf scan specErrorMember,
    candidateErrorAtomRuntimeRel_toScopedEvaluatorResult state
      sourceObservation errorRelation⟩

/-- Outcome-facing form of `of_functionErrors`.  The complete A1 scan
correspondence supplies the specification exhaustion witness and the exact
flat error ledger; no evaluator proof unfolds candidate classification. -/
theorem InterpretExpressionResultsRuntimeSound.of_runtimeExhausted
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {expression expectedType operator : Atom}
    {arguments types : List Atom} {bindings : Bindings}
    {runtimeBindings : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError}
    {typing : EvalTypeService} {presentation : TypeSubst}
    {outcome : FunctionCandidateScanOutcome}
    (expressionShape : expression = .expression (operator :: arguments))
    (typesOf : typing.typesOf space operator types)
    (scan : typing.candidateScan space expression expectedType bindings
      types outcome)
    (runtimeOutcome : FunctionCandidateScanOutcomeRuntimeRel scope expression
      bindings outcome (.exhausted runtimeErrors false))
    (state : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (sourceObservation : EvaluatorAtomObservationRel services presentation
      runtimeBindings expression runtimeExpression) :
    InterpretExpressionResultsRuntimeSound services scope space dispatch live
      expression expectedType bindings
      (runtimeErrors.map fun error =>
        (error.toAtom runtimeExpression, runtimeBindings)) typing := by
  cases runtimeOutcome with
  | exhausted errors tupleEquation =>
      have tupleFalse : _ = false := tupleEquation
      subst tupleFalse
      exact .of_functionErrors expressionShape typesOf scan state
        sourceObservation errors

/-- Every structured selector failure is already an evaluator error atom.
Keeping this constructor fact named prevents success-priority proofs from
unfolding the mutually recursive evaluator merely to inspect diagnostics. -/
@[simp] theorem expectedFunctionTypeError_toAtom_isError
    (expression : Metta.Atom)
    (error : Metta.Minimal.ExpectedFunctionTypeError) :
    (error.toAtom expression).isError = true := by
  cases error with
  | ordinary error => cases error <;> rfl
  | badReturn expected actual => rfl

/-- The concrete positive-fuel evaluator returns exactly the selector's flat
error ledger when exhaustion does not permit tuple fallback.  Every mapped
atom is an error, so the outer success-priority pass is definitionally inert. -/
theorem mettaEvalExpected_succ_functionErrors
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (runtimeBindings : Metta.Bindings)
    (runtimeAtom runtimeExpected runtimeSource runtimeExpression : Metta.Atom)
    (operator : String) (arguments : List Metta.Atom)
    (runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (expectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (sourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (doesNotPass :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = false)
    (sourceExpressionShape :
      ∃ head tail, runtimeSource = .expr (head :: tail))
    (selectedSourceEquation :
      Metta.instantiate runtimeBindings runtimeSource = runtimeExpression)
    (sourceShape : runtimeExpression =
      .expr (.sym operator :: arguments))
    (selectorEquation :
      Metta.Minimal.selectFunctionTypeForExpectedFrom env state.world
        (.sym operator) arguments runtimeExpected runtimeBindings =
          .exhausted runtimeErrors false) :
    Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected =
      (runtimeErrors.map fun error =>
        (error.toAtom runtimeExpression, runtimeBindings), state) := by
  obtain ⟨sourceHead, sourceTail, rfl⟩ := sourceExpressionShape
  rw [Metta.Minimal.mettaEvalExpected.eq_1]
  simp only [expectedNotUndefined, Bool.false_eq_true, if_false,
    sourceEquation, sourceNotEmptyOrError, doesNotPass,
    selectedSourceEquation, sourceShape]
  rw [selectorEquation]
  simp only [Bool.false_eq_true, if_false]
  unfold Metta.Minimal.prioritizeSemanticResults
  simp

/-- Soundness of the complete non-tuple exhaustion arm.  The executable
equation fixes the flat runtime ledger; the A1 outcome relation supplies the
matching specification ledger, and the ordinary evaluator constructor only
classifies each already-related diagnostic as an error result. -/
theorem rawEvaluatorResultsRuntimeSound_mettaEvalExpected_functionErrors
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {expression expectedType metaType operator : Atom}
    {arguments types specErrors : List Atom} {bindings : Bindings}
    {presentation : TypeSubst}
    {runtimeAtom runtimeExpected runtimeSource runtimeExpression : Metta.Atom}
    {runtimeBindings : Metta.Bindings}
    {runtimeOperator : String} {runtimeArguments : List Metta.Atom}
    {runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError}
    {typing : EvalTypeService}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (runtimeExpectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (runtimeSourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (runtimeDoesNotPass :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = false)
    (runtimeSourceShape :
      ∃ head tail, runtimeSource = .expr (head :: tail))
    (selectedSourceEquation :
      Metta.instantiate runtimeBindings runtimeSource = runtimeExpression)
    (runtimeExpressionShape : runtimeExpression =
      .expr (.sym runtimeOperator :: runtimeArguments))
    (selectorEquation :
      Metta.Minimal.selectFunctionTypeForExpectedFrom env state.world
        (.sym runtimeOperator) runtimeArguments runtimeExpected
          runtimeBindings =
          .exhausted runtimeErrors false)
    (expressionShape : expression = .expression (operator :: arguments))
    (typesOf : typing.typesOf space operator types)
    (scan : typing.candidateScan space expression expectedType bindings types
      (.exhausted specErrors false))
    (inputState : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (sourceObservation : EvaluatorAtomObservationRel services presentation
      runtimeBindings expression runtimeExpression)
    (errors : CandidateErrorBlockRuntimeRel expression specErrors
      runtimeErrors)
    (specNotEmptyOrError : ¬IsEmptyOrErrorRel expression)
    (metaTypeRelation : MetaTypeRel expression metaType)
    (specDoesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType)) :
    RawEvaluatorResultsRuntimeSound services scope space dispatch live
      expression expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1 typing := by
  rw [mettaEvalExpected_succ_functionErrors env fuel state runtimeBindings
    runtimeAtom runtimeExpected runtimeSource runtimeExpression
    runtimeOperator runtimeArguments runtimeErrors sourceEquation
    runtimeExpectedNotUndefined runtimeSourceNotEmptyOrError
    runtimeDoesNotPass runtimeSourceShape selectedSourceEquation
    runtimeExpressionShape selectorEquation]
  apply RawEvaluatorResultsRuntimeSound.of_interpretExpression
    specNotEmptyOrError metaTypeRelation specDoesNotPass
      ⟨operator, arguments, expressionShape⟩
  exact InterpretExpressionResultsRuntimeSound.of_functionErrors
    expressionShape typesOf scan inputState sourceObservation errors

/-- A1-outcome form of the non-tuple exhaustion theorem.  This is the
constructor boundary used by the concrete configuration: the specification
outcome remains existential, while the executable equation fixes it to the
observed exhausted selector result. -/
theorem rawEvaluatorResultsRuntimeSound_mettaEvalExpected_functionErrors_of_runtimeOutcome
    {services : Spec.Eval.Minimal.Services} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {expression expectedType metaType operator : Atom}
    {arguments types : List Atom} {bindings : Bindings}
    {presentation : TypeSubst}
    {runtimeAtom runtimeExpected runtimeSource runtimeExpression : Metta.Atom}
    {runtimeBindings : Metta.Bindings}
    {runtimeOperator : String} {runtimeArguments : List Metta.Atom}
    {runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError}
    {typing : EvalTypeService} {outcome : FunctionCandidateScanOutcome}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (runtimeExpectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (runtimeSourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (runtimeDoesNotPass :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = false)
    (runtimeSourceShape :
      ∃ head tail, runtimeSource = .expr (head :: tail))
    (selectedSourceEquation :
      Metta.instantiate runtimeBindings runtimeSource = runtimeExpression)
    (runtimeExpressionShape : runtimeExpression =
      .expr (.sym runtimeOperator :: runtimeArguments))
    (selectorEquation :
      Metta.Minimal.selectFunctionTypeForExpectedFrom env state.world
        (.sym runtimeOperator) runtimeArguments runtimeExpected
          runtimeBindings =
          .exhausted runtimeErrors false)
    (expressionShape : expression = .expression (operator :: arguments))
    (typesOf : typing.typesOf space operator types)
    (scan : typing.candidateScan space expression expectedType bindings
      types outcome)
    (runtimeOutcome : FunctionCandidateScanOutcomeRuntimeRel scope expression
      bindings outcome (.exhausted runtimeErrors false))
    (inputState : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (sourceObservation : EvaluatorAtomObservationRel services presentation
      runtimeBindings expression runtimeExpression)
    (specNotEmptyOrError : ¬IsEmptyOrErrorRel expression)
    (metaTypeRelation : MetaTypeRel expression metaType)
    (specDoesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType)) :
    RawEvaluatorResultsRuntimeSound services scope space dispatch live
      expression expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1 typing := by
  rw [mettaEvalExpected_succ_functionErrors env fuel state runtimeBindings
    runtimeAtom runtimeExpected runtimeSource runtimeExpression
    runtimeOperator runtimeArguments runtimeErrors sourceEquation
    runtimeExpectedNotUndefined runtimeSourceNotEmptyOrError
    runtimeDoesNotPass runtimeSourceShape selectedSourceEquation
    runtimeExpressionShape selectorEquation]
  apply RawEvaluatorResultsRuntimeSound.of_interpretExpression
    specNotEmptyOrError metaTypeRelation specDoesNotPass
      ⟨operator, arguments, expressionShape⟩
  exact InterpretExpressionResultsRuntimeSound.of_runtimeExhausted
    expressionShape typesOf scan runtimeOutcome inputState sourceObservation

/-- **A1-to-evaluator composition for the exhausted non-tuple branch.**
A canonical runtime configuration supplies both the exact prepared type list
and its expected-aware scan witness.  Once the concrete selector is observed
to exhaust without tuple eligibility, every emitted runtime result is a
specification `functionError` result at the full service observation scope. -/
theorem RuntimeConfigurationRel.functionErrorsSound
    {services : Spec.Eval.Minimal.Services}
    {oracle : TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state)
    {operator : String} {arguments : List Atom}
    {expectedType metaType : Atom} {bindings : Bindings}
    {presentation : TypeSubst}
    {runtimeAtom runtimeSource : Metta.Atom}
    {runtimeBindings : Metta.Bindings}
    {runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError}
    (fuel : Nat)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (runtimeExpectedNotUndefined :
      (toLeaTTaAtom expectedType == Metta.Atom.sym "%Undefined%") = false)
    (runtimeSourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (runtimeDoesNotPass :
      (toLeaTTaAtom expectedType == Metta.Atom.atomType ||
        toLeaTTaAtom expectedType ==
          Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = false)
    (runtimeSourceShape :
      ∃ head tail, runtimeSource = .expr (head :: tail))
    (selectedSourceEquation :
      Metta.instantiate runtimeBindings runtimeSource =
        toLeaTTaAtom
          (.expression (.symbol operator :: arguments)))
    (selectorEquation :
      Metta.Minimal.selectFunctionTypeForExpectedFrom env state.world
        (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeBindings =
        .exhausted runtimeErrors false)
    (inputState : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (initialSupport : ∀ name,
      name ∈ specBindingVars (⟨presentation, []⟩ : Bindings) →
        name ∈ specBindingVars bindings)
    (bindingSupport : ∀ name, name ∈ specBindingVars bindings →
      name ∈ runtimeBindings.vars)
    (sourceObservation : EvaluatorAtomObservationRel services presentation
      runtimeBindings (.expression (.symbol operator :: arguments))
        (toLeaTTaAtom (.expression (.symbol operator :: arguments))))
    (specNotEmptyOrError :
      ¬IsEmptyOrErrorRel (.expression (.symbol operator :: arguments)))
    (metaTypeRelation :
      MetaTypeRel (.expression (.symbol operator :: arguments)) metaType)
    (specDoesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType)) :
    RawEvaluatorResultsRuntimeSound services
      (typeServiceObservationScope space
        (.expression (.symbol operator :: arguments)) expectedType)
      space dispatch live
      (.expression (.symbol operator :: arguments)) expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom (toLeaTTaAtom expectedType)).1
      (preparedPackageTypeService oracle) := by
  let types := fromLeaTTaAtoms
    (Metta.Minimal.getTypes env
      (Metta.Minimal.typePrep state.world (.sym operator)))
  have typesOf : (preparedPackageTypeService oracle).typesOf space
      (.symbol operator) types := by
    simpa [types, toLeaTTaAtom] using
      configuration.typesOf (.symbol operator)
  obtain ⟨outcome, scan, runtimeOutcome⟩ :=
    configuration.candidateScanFrom operator expectedType arguments bindings
      ⟨LeaTTaTypeServiceConformance.TypePresentationSimulationState.toTypeBindingPresentationRel
          inputState,
        initialSupport⟩ inputState bindingSupport
  rw [selectorEquation] at runtimeOutcome
  apply rawEvaluatorResultsRuntimeSound_mettaEvalExpected_functionErrors_of_runtimeOutcome
    (scope := typeServiceObservationScope space
      (.expression (.symbol operator :: arguments)) expectedType)
    (dispatch := dispatch) (live := live)
    (expression := .expression (.symbol operator :: arguments))
    (metaType := metaType) (operator := .symbol operator)
    (arguments := arguments) (types := types)
    (presentation := presentation)
    (runtimeSource := runtimeSource)
    (runtimeExpression := toLeaTTaAtom
      (.expression (.symbol operator :: arguments)))
    (runtimeOperator := operator)
    (runtimeArguments := toLeaTTaAtoms arguments)
    (runtimeErrors := runtimeErrors) (outcome := outcome)
    env fuel state sourceEquation runtimeExpectedNotUndefined
      runtimeSourceNotEmptyOrError runtimeDoesNotPass runtimeSourceShape
      selectedSourceEquation
      (by simp [toLeaTTaAtom, toLeaTTaAtoms_eq_map]) selectorEquation
      rfl typesOf scan runtimeOutcome inputState sourceObservation
      specNotEmptyOrError metaTypeRelation specDoesNotPass

/-- Every rejected runtime type has the corresponding exact specification
cast failure and diagnostic observation. -/
theorem preparedTypeCastOutcomeRuntimeRel_failure_sound
    {services : Spec.Eval.Minimal.Services}
    {oracle : TypePreparationOracle} {scope : List String}
    {space : Space} {atom expectedType : Atom} {bindings : Bindings}
    {presentation : TypeSubst} {runtimeBindings : Metta.Bindings}
    {runtimeSource runtimeExpected : Metta.Atom}
    {rejected : List Metta.Atom}
    (inputState : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (sourceUnchanged : presentation.apply atom = atom)
    (expectedEquation : runtimeExpected = toLeaTTaAtom expectedType)
    (outcome : PreparedTypeCastOutcomeRuntimeRel oracle space atom
      expectedType bindings (.inl rejected)) :
    ∀ runtimeActual, runtimeActual ∈ rejected →
      ∃ result,
        PreparedTypeCastRel oracle space atom expectedType bindings result ∧
        ScopedEvaluatorResultRuntimeRel services scope result
          (Metta.Minimal.badTypeAtom runtimeSource runtimeExpected
            runtimeActual, runtimeBindings) := by
  cases outcome with
  | failure present variants _nonempty allFailed =>
      intro runtimeActual runtimeMember
      rw [toLeaTTaAtoms_eq_map] at runtimeMember
      obtain ⟨actualType, actualMember, rfl⟩ :=
        List.mem_map.mp runtimeMember
      refine ⟨(mkError atom (.badType expectedType actualType), bindings),
        PreparedTypeCastRel.failure present variants actualMember allFailed,
        ?_⟩
      exact scopedEvaluatorResultRuntimeRel_badType inputState
        sourceRelation sourceUnchanged expectedEquation

/-- Every specification cast derivation is represented in the runtime's
complete rejected-type ledger.  A competing success is impossible by
first-success/all-failure transport; a competing failure is paired at the
same list position modulo private alpha. -/
theorem preparedTypeCastOutcomeRuntimeRel_failure_complete
    {services : Spec.Eval.Minimal.Services}
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {scope : List String} {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {atom expectedType : Atom} {bindings : Bindings}
    {presentation : TypeSubst} {runtimeBindings : Metta.Bindings}
    {runtimeSource runtimeExpected : Metta.Atom}
    {rejected : List Metta.Atom}
    (inputState : TypePresentationSimulationState
      presentation bindings runtimeBindings)
    (inputCovered : ∀ name,
      name ∈ specBindingVars (⟨presentation, []⟩ : Bindings) →
        name ∈ typeServicePrivateAvoid
          space atom expectedType bindings)
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (sourceUnchanged : presentation.apply atom = atom)
    (expectedEquation : runtimeExpected = toLeaTTaAtom expectedType)
    (outcome : PreparedTypeCastOutcomeRuntimeRel oracle space atom
      expectedType bindings (.inl rejected)) :
    ∀ result,
      PreparedTypeCastRel oracle space atom expectedType bindings result →
      ∃ runtimeActual, runtimeActual ∈ rejected ∧
        ScopedEvaluatorResultRuntimeRel services scope result
          (Metta.Minimal.badTypeAtom runtimeSource runtimeExpected
            runtimeActual, runtimeBindings) := by
  have expectedCovered : ∀ name,
      name ∈ TypeSubst.typeVars expectedType →
        name ∈ typeServicePrivateAvoid
          space atom expectedType bindings := by
    intro name member
    apply List.mem_append_left
    rw [typeServiceObservationScope]
    exact Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
      (atoms := space.atoms ++ [atom, expectedType])
      (atom := expectedType) (by simp) name member
  cases outcome with
  | failure selectedPresent selectedVariants _nonempty selectedAllFailed =>
      intro result competingCast
      cases competingCast with
      | success competingPresent competingVariants competingFirst =>
          have candidatesAlpha :=
            preparedTypeCastCandidateFamilies_privateAlpha functional index
              competingPresent selectedPresent competingVariants
                selectedVariants
          exact (FirstTypeCastSuccessRel.not_allFailures_of_privateAlpha
            inputState candidatesAlpha inputCovered expectedCovered
              competingFirst selectedAllFailed).elim
      | failure competingPresent competingVariants competingMember
          _competingAllFailed =>
          have candidatesAlpha :=
            preparedTypeCastCandidateFamilies_privateAlpha functional index
              competingPresent selectedPresent competingVariants
                selectedVariants
          obtain ⟨runtimeActual, runtimeMember, actualAlpha⟩ :=
            PrivateCandidateFamilyAlphaRel.exists_right_of_mem_left
              candidatesAlpha competingMember
          refine ⟨toLeaTTaAtom runtimeActual, ?_, ?_⟩
          · rw [toLeaTTaAtoms_eq_map]
            exact List.mem_map.mpr ⟨runtimeActual, runtimeMember, rfl⟩
          · exact scopedEvaluatorResultRuntimeRel_badType_privateCandidate
              inputState actualAlpha sourceRelation
                sourceUnchanged expectedEquation

/-- A successful positive-fuel cast of a symbol, grounded atom, or unit
returns that atom with the cast output binding.  These three published cast
shapes contain no variables, so the output binding cannot change the atom. -/
theorem mettaEvalExpected_succ_castSuccess
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (runtimeBindings runtimeOutput : Metta.Bindings)
    (runtimeAtom runtimeExpected runtimeSource : Metta.Atom)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (expectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (sourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (doesNotPass :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = false)
    (castShape :
      (∃ name, runtimeSource = .sym name) ∨
        (∃ value, runtimeSource = .gnd value) ∨
        runtimeSource = .expr [])
    (castSuccess : Metta.Minimal.mettaTypeCast env state.world
      runtimeBindings runtimeSource runtimeExpected = .inr runtimeOutput) :
    Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
      runtimeAtom runtimeExpected =
      ([(runtimeSource, runtimeOutput)], state) := by
  have sourceGates := Bool.or_eq_false_iff.mp sourceNotEmptyOrError
  have priority :
      Metta.Minimal.prioritizeSemanticResults
          ([(runtimeSource, runtimeOutput)], state) =
        ([(runtimeSource, runtimeOutput)], state) := by
    simp [Metta.Minimal.prioritizeSemanticResults, sourceGates.2]
  rw [Metta.Minimal.mettaEvalExpected.eq_1]
  simp only [expectedNotUndefined, Bool.false_eq_true, ↓reduceIte,
    sourceEquation, sourceNotEmptyOrError, doesNotPass]
  rcases castShape with ⟨name, sourceEq⟩ | ⟨value, sourceEq⟩ | sourceEq
  all_goals
    rw [sourceEq] at castSuccess priority ⊢
    simp only [castSuccess]
    rw [Metta.instantiate_of_closed runtimeOutput _ (by simp [Metta.Atom.vars])]
    exact priority

/-- A successful exact cast outcome supplies both the specification cast
derivation and the scoped result witness consumed by evaluator soundness.
The published non-expression cast shapes are fixed points of every finite
type presentation, so no cross-implementation exactness is assumed. -/
theorem preparedTypeCastOutcomeRuntimeRel_success_result
    {services : Spec.Eval.Minimal.Services}
    {oracle : TypePreparationOracle} {space : Space}
    {atom expectedType : Atom} {incoming : Bindings}
    {runtimeOutput : Metta.Bindings} {runtimeSource : Metta.Atom}
    {scope : List String}
    (outcome : PreparedTypeCastOutcomeRuntimeRel oracle space atom
      expectedType incoming (.inr runtimeOutput))
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (castShape :
      (∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit) :
    ∃ output,
      PreparedTypeCastRel oracle space atom expectedType incoming
          (atom, output) ∧
        ScopedEvaluatorResultRuntimeRel services scope
          (atom, output) (runtimeSource, runtimeOutput) := by
  cases outcome with
  | success cast state =>
      refine ⟨_, cast,
        ScopedEvaluatorResultRuntimeRel.ofExactUnchangedAtom
          state sourceRelation ?_⟩
      rcases castShape with ⟨name, rfl⟩ | ⟨value, rfl⟩ | rfl
      all_goals simp [TypeSubst.apply, Atom.unit]

/-- Completeness of one successful prepared cast across every lawful
preparation of the same candidate list.  Functionality aligns the recovered
raw package lists; first-success lockstep aligns the commit position; output
bindings are exact within the specification and scoped-equivalent across the
runtime boundary. -/
theorem preparedTypeCastOutcomeRuntimeRel_success_complete
    {services : Spec.Eval.Minimal.Services}
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {atom expectedType : Atom} {incoming : Bindings}
    {inputPresentation : TypeSubst}
    {runtimeIncoming runtimeOutput : Metta.Bindings}
    {runtimeSource : Metta.Atom} {scope : List String}
    (inputState : TypePresentationSimulationState
      inputPresentation incoming runtimeIncoming)
    (inputCovered : ∀ name,
      name ∈ specBindingVars (⟨inputPresentation, []⟩ : Bindings) →
        name ∈ typeServicePrivateAvoid
          space atom expectedType incoming)
    (scopeCovered : ∀ name, name ∈ scope →
      name ∈ typeServicePrivateAvoid space atom expectedType incoming)
    (outcome : PreparedTypeCastOutcomeRuntimeRel oracle space atom
      expectedType incoming (.inr runtimeOutput))
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (castShape :
      (∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit) :
    ∀ result,
      PreparedTypeCastRel oracle space atom expectedType incoming result →
        ScopedEvaluatorResultRuntimeRel services scope result
          (runtimeSource, runtimeOutput) := by
  have expectedCovered : ∀ name,
      name ∈ TypeSubst.typeVars expectedType →
        name ∈ typeServicePrivateAvoid
          space atom expectedType incoming := by
    intro name member
    apply List.mem_append_left
    rw [typeServiceObservationScope]
    exact Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
      (atoms := space.atoms ++ [atom, expectedType])
      (atom := expectedType) (by simp) name member
  cases outcome with
  | success selectedCast selectedState =>
      obtain ⟨selectedSources, selectedCandidates, selectedPresent,
          selectedVariants, selectedFirst⟩ := selectedCast.of_atom_result
      intro result competingCast
      cases competingCast with
      | success competingPresent competingVariants competingFirst =>
          have candidatesAlpha :=
            preparedTypeCastCandidateFamilies_privateAlpha
              functional index competingPresent selectedPresent
                competingVariants selectedVariants
          obtain ⟨presentation, specSolutions, runtimeState⟩ :=
            FirstTypeCastSuccessRel.outputsScoped inputState selectedState
              candidatesAlpha inputCovered expectedCovered scopeCovered
                competingFirst selectedFirst
          apply ScopedEvaluatorResultRuntimeRel.ofScopedUnchangedAtom
            specSolutions runtimeState sourceRelation
          rcases castShape with ⟨name, rfl⟩ | ⟨value, rfl⟩ | rfl
          all_goals simp [TypeSubst.apply, Atom.unit]
      | failure competingPresent competingVariants _actualMember allFailed =>
          have candidatesAlpha :=
            preparedTypeCastCandidateFamilies_privateAlpha
              functional index selectedPresent competingPresent
                selectedVariants competingVariants
          exact (FirstTypeCastSuccessRel.not_allFailures_of_privateAlpha
            inputState candidatesAlpha inputCovered expectedCovered
              selectedFirst allFailed).elim

/-- Soundness of the complete executable cast-success arm.  Exact type
service correspondence supplies the selected specification binding theory;
the evaluator equation contributes no additional semantic premise. -/
theorem rawEvaluatorResultsRuntimeSound_mettaEvalExpected_castSuccess
    {services : Spec.Eval.Minimal.Services}
    {oracle : TypePreparationOracle} {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {atom expectedType metaType : Atom}
    {bindings : Bindings}
    {runtimeAtom runtimeExpected runtimeSource : Metta.Atom}
    {runtimeBindings runtimeOutput : Metta.Bindings}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (runtimeExpectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (runtimeSourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (runtimeDoesNotPass :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = false)
    (runtimeCastShape :
      (∃ name, runtimeSource = .sym name) ∨
        (∃ value, runtimeSource = .gnd value) ∨
        runtimeSource = .expr [])
    (castSuccess : Metta.Minimal.mettaTypeCast env state.world
      runtimeBindings runtimeSource runtimeExpected = .inr runtimeOutput)
    (outcome : PreparedTypeCastOutcomeRuntimeRel oracle space atom
      expectedType bindings (.inr runtimeOutput))
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (specNotEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (specDoesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType))
    (specCastShape :
      (∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit) :
    RawEvaluatorResultsRuntimeSound services scope space dispatch live atom
      expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1
      (preparedPackageTypeService oracle) := by
  obtain ⟨output, cast, resultRelation⟩ :=
    preparedTypeCastOutcomeRuntimeRel_success_result
      (scope := scope) outcome sourceRelation specCastShape
  have serviceCast :
      (preparedPackageTypeService oracle).typeCast [] space atom expectedType
        bindings (atom, output) := by
    simpa using cast
  rw [mettaEvalExpected_succ_castSuccess env fuel state runtimeBindings
    runtimeOutput runtimeAtom runtimeExpected runtimeSource sourceEquation
    runtimeExpectedNotUndefined runtimeSourceNotEmptyOrError
    runtimeDoesNotPass runtimeCastShape castSuccess]
  intro runtimeResult member
  have runtimeResultEq : runtimeResult = (runtimeSource, runtimeOutput) := by
    simpa using member
  subst runtimeResult
  exact ⟨(atom, output),
    EvalAtomRawRel.cast atom expectedType metaType bindings (atom, output)
      specNotEmptyOrError metaTypeRelation specDoesNotPass specCastShape
      serviceCast,
    resultRelation⟩

/-- Bidirectional correspondence for the executable cast-success arm.  The
runtime singleton is complete because every lawful prepared cast uses the
same ordered first-success position modulo private alpha-renaming. -/
theorem rawEvaluatorResultsRuntimeRel_mettaEvalExpected_castSuccess
    {services : Spec.Eval.Minimal.Services}
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {scope : List String} {space : Space}
    {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {atom expectedType metaType : Atom} {bindings : Bindings}
    {inputPresentation : TypeSubst}
    {runtimeAtom runtimeExpected runtimeSource : Metta.Atom}
    {runtimeBindings runtimeOutput : Metta.Bindings}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (index : TypeEnvironmentRel space env)
    (inputState : TypePresentationSimulationState
      inputPresentation bindings runtimeBindings)
    (inputCovered : ∀ name,
      name ∈ specBindingVars (⟨inputPresentation, []⟩ : Bindings) →
        name ∈ typeServicePrivateAvoid
          space atom expectedType bindings)
    (scopeCovered : ∀ name, name ∈ scope →
      name ∈ typeServicePrivateAvoid space atom expectedType bindings)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (runtimeExpectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (runtimeSourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (runtimeDoesNotPass :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = false)
    (runtimeCastShape :
      (∃ name, runtimeSource = .sym name) ∨
        (∃ value, runtimeSource = .gnd value) ∨
        runtimeSource = .expr [])
    (castSuccess : Metta.Minimal.mettaTypeCast env state.world
      runtimeBindings runtimeSource runtimeExpected = .inr runtimeOutput)
    (outcome : PreparedTypeCastOutcomeRuntimeRel oracle space atom
      expectedType bindings (.inr runtimeOutput))
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (specNotEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (specDoesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType))
    (specCastShape :
      (∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit) :
    RawEvaluatorResultsRuntimeRel services scope space dispatch live atom
      expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1
      (preparedPackageTypeService oracle) := by
  have sound : RawEvaluatorResultsRuntimeSound services scope space dispatch
      live atom expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1
      (preparedPackageTypeService oracle) :=
    rawEvaluatorResultsRuntimeSound_mettaEvalExpected_castSuccess
    (scope := scope) (dispatch := dispatch) (live := live)
      env fuel state sourceEquation
      runtimeExpectedNotUndefined runtimeSourceNotEmptyOrError
      runtimeDoesNotPass runtimeCastShape castSuccess outcome sourceRelation
      specNotEmptyOrError metaTypeRelation specDoesNotPass specCastShape
  constructor
  · exact sound
  · intro result rawResult
    have serviceCast :
        PreparedTypeCastRel oracle space atom expectedType bindings result := by
      exact EvalAtomRawRel.typeCast_of_castGate specNotEmptyOrError
        metaTypeRelation specDoesNotPass specCastShape rawResult
    have resultRelation :=
      preparedTypeCastOutcomeRuntimeRel_success_complete functional index
        inputState inputCovered scopeCovered outcome sourceRelation
          specCastShape result serviceCast
    refine ⟨(runtimeSource, runtimeOutput), ?_, resultRelation⟩
    rw [mettaEvalExpected_succ_castSuccess env fuel state runtimeBindings
      runtimeOutput runtimeAtom runtimeExpected runtimeSource sourceEquation
      runtimeExpectedNotUndefined runtimeSourceNotEmptyOrError
      runtimeDoesNotPass runtimeCastShape castSuccess]
    simp

/-- Bidirectional correspondence for the executable cast-failure arm.  The
runtime emits the complete ordered rejected-type ledger, and the strengthened
outcome carrier proves that every entry comes from one shared all-failure
candidate family. -/
theorem rawEvaluatorResultsRuntimeRel_mettaEvalExpected_castFailure
    {services : Spec.Eval.Minimal.Services}
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {scope : List String} {space : Space}
    {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {atom expectedType metaType : Atom} {bindings : Bindings}
    {inputPresentation : TypeSubst}
    {runtimeAtom runtimeExpected runtimeSource : Metta.Atom}
    {runtimeBindings : Metta.Bindings} {rejected : List Metta.Atom}
    (env : Metta.Minimal.MinEnv) (fuel : Nat) (state : Metta.Minimal.St)
    (index : TypeEnvironmentRel space env)
    (inputState : TypePresentationSimulationState
      inputPresentation bindings runtimeBindings)
    (inputCovered : ∀ name,
      name ∈ specBindingVars (⟨inputPresentation, []⟩ : Bindings) →
        name ∈ typeServicePrivateAvoid
          space atom expectedType bindings)
    (sourceEquation :
      Metta.instantiate runtimeBindings runtimeAtom = runtimeSource)
    (runtimeExpectedNotUndefined :
      (runtimeExpected == Metta.Atom.sym "%Undefined%") = false)
    (runtimeSourceNotEmptyOrError :
      (runtimeSource == Metta.Minimal.emptyA || runtimeSource.isError) = false)
    (runtimeDoesNotPass :
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected == Metta.Atom.typeAtomOfMetaType runtimeSource.metaType ||
        runtimeSource.metaType == .variable) = false)
    (runtimeCastShape :
      (∃ name, runtimeSource = .sym name) ∨
        (∃ value, runtimeSource = .gnd value) ∨
        runtimeSource = .expr [])
    (castFailure : Metta.Minimal.mettaTypeCast env state.world
      runtimeBindings runtimeSource runtimeExpected = .inl rejected)
    (outcome : PreparedTypeCastOutcomeRuntimeRel oracle space atom
      expectedType bindings (.inl rejected))
    (sourceRelation : AtomRuntimeRel services atom runtimeSource)
    (expectedEquation : runtimeExpected = toLeaTTaAtom expectedType)
    (specNotEmptyOrError : ¬IsEmptyOrErrorRel atom)
    (metaTypeRelation : MetaTypeRel atom metaType)
    (specDoesNotPass : ¬(expectedType = Atom.atomType ∨
      expectedType = metaType ∨ metaType = Atom.variableType))
    (specCastShape :
      (∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit) :
    RawEvaluatorResultsRuntimeRel services scope space dispatch live atom
      expectedType bindings
      (Metta.Minimal.mettaEvalExpected env (fuel + 1) state runtimeBindings
        runtimeAtom runtimeExpected).1
      (preparedPackageTypeService oracle) := by
  have sourceUnchanged : inputPresentation.apply atom = atom := by
    rcases specCastShape with ⟨name, rfl⟩ | ⟨value, rfl⟩ | rfl
    all_goals simp [TypeSubst.apply, Atom.unit]
  rw [mettaEvalExpected_succ_castFailure env fuel state runtimeBindings
    runtimeAtom runtimeExpected runtimeSource rejected sourceEquation
    runtimeExpectedNotUndefined runtimeSourceNotEmptyOrError
    runtimeDoesNotPass runtimeCastShape castFailure]
  constructor
  · intro runtimeResult runtimeMember
    obtain ⟨runtimeActual, actualMember, rfl⟩ :=
      List.mem_map.mp runtimeMember
    obtain ⟨result, serviceCast, resultRelation⟩ :=
      preparedTypeCastOutcomeRuntimeRel_failure_sound inputState
        sourceRelation sourceUnchanged expectedEquation outcome
          runtimeActual actualMember
    exact ⟨result,
      EvalAtomRawRel.cast atom expectedType metaType bindings result
        specNotEmptyOrError metaTypeRelation specDoesNotPass specCastShape
          serviceCast,
      resultRelation⟩
  · intro result rawResult
    have serviceCast :
        PreparedTypeCastRel oracle space atom expectedType bindings result :=
      EvalAtomRawRel.typeCast_of_castGate specNotEmptyOrError
        metaTypeRelation specDoesNotPass specCastShape rawResult
    obtain ⟨runtimeActual, actualMember, resultRelation⟩ :=
      preparedTypeCastOutcomeRuntimeRel_failure_complete functional index
        inputState inputCovered sourceRelation sourceUnchanged
          expectedEquation outcome result serviceCast
    refine ⟨(Metta.Minimal.badTypeAtom runtimeSource runtimeExpected
      runtimeActual, runtimeBindings), ?_, resultRelation⟩
    exact List.mem_map.mpr ⟨runtimeActual, actualMember, rfl⟩

/-- Membership in LeaTTa's prioritized list is exactly raw membership plus
the published error condition: an error remains visible only when every raw
result is also an error.  Order and multiplicity are inherited from the raw
list because prioritization is either the identity or a stable filter. -/
theorem mem_prioritizeSemanticResults_iff
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {state : Metta.Minimal.St} {runtimeResult : Metta.Atom × Metta.Bindings} :
    runtimeResult ∈
        (Metta.Minimal.prioritizeSemanticResults (runtimeResults, state)).1 ↔
      runtimeResult ∈ runtimeResults ∧
        (runtimeResult.1.isError = true →
          ∀ candidate ∈ runtimeResults, candidate.1.isError = true) := by
  unfold Metta.Minimal.prioritizeSemanticResults
  let successes := runtimeResults.filter (fun result => !result.1.isError)
  by_cases empty : successes.isEmpty = true
  · rw [if_pos empty]
    refine ⟨fun member => ⟨member, ?_⟩, fun pair => pair.1⟩
    intro _ candidate candidateMember
    have successesNil : successes = [] := by simpa using empty
    cases error : candidate.1.isError with
    | false =>
        have candidateSuccess : candidate ∈ successes := by
          exact List.mem_filter.mpr ⟨candidateMember, by simp [error]⟩
        rw [successesNil] at candidateSuccess
        simp at candidateSuccess
    | true => rfl
  · rw [if_neg empty]
    constructor
    · intro member
      have filtered := List.mem_filter.mp member
      refine ⟨filtered.1, ?_⟩
      intro isError
      simp [isError] at filtered
    · rintro ⟨member, errorCondition⟩
      apply List.mem_filter.mpr
      refine ⟨member, ?_⟩
      cases error : runtimeResult.1.isError with
      | false => simp
      | true =>
          have allError := errorCondition error
          have noSuccess : successes = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro candidate candidateMember
            have filtered := List.mem_filter.mp candidateMember
            have candidateError := allError candidate filtered.1
            simp [candidateError] at filtered
          exact (empty (by simp [successes, noSuccess])).elim

/-! ## Concrete priority canaries -/

private def priorityError : Metta.Atom × Metta.Bindings :=
  (.expr [.sym "Error"], [])

private def prioritySuccess : Metta.Atom × Metta.Bindings :=
  (.sym "ok", [])

/-- Positive: when every result is an error, the complete ordered error list
is retained. -/
example (state : Metta.Minimal.St) :
    (Metta.Minimal.prioritizeSemanticResults
      ([priorityError, priorityError], state)).1 =
        [priorityError, priorityError] := by
  rfl

/-- Negative: one successful result makes the competing error unobservable. -/
example (state : Metta.Minimal.St) :
    priorityError ∉
      (Metta.Minimal.prioritizeSemanticResults
        ([priorityError, prioritySuccess], state)).1 := by
  simp [Metta.Minimal.prioritizeSemanticResults, priorityError,
    prioritySuccess, Metta.Atom.isError]

/-- **Success-priority bridge.**  Bidirectional raw evaluator correspondence
is preserved exactly by LeaTTa's public success filter and the specification's
`EvalRel` side condition.  This theorem is the only evaluator-conformance
result that needs both raw soundness and raw completeness: each direction is
needed to rule out a hidden non-error result on the opposite side. -/
theorem RawEvaluatorResultsRuntimeRel.prioritize
    {services : Spec.Eval.Minimal.Services}
    {scope : List String}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {atom expectedType : Atom} {bindings : Bindings}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    {typing : EvalTypeService} {state : Metta.Minimal.St}
    (relation : RawEvaluatorResultsRuntimeRel services scope
      space dispatch live atom expectedType bindings runtimeResults typing) :
    EvaluatorResultsRuntimeRel services scope
      space dispatch live atom expectedType bindings
      (Metta.Minimal.prioritizeSemanticResults (runtimeResults, state)).1
      typing := by
  constructor
  · intro runtimeResult prioritizedMember
    have memberCondition :=
      mem_prioritizeSemanticResults_iff.mp prioritizedMember
    obtain ⟨result, rawResult, resultRelation⟩ :=
      relation.sound runtimeResult memberCondition.1
    refine ⟨result, ⟨rawResult, ?_⟩, resultRelation⟩
    intro resultError candidate candidateRaw
    obtain ⟨runtimeCandidate, runtimeCandidateMember,
        candidateRelation⟩ := relation.complete candidate candidateRaw
    have runtimeResultError : runtimeResult.1.isError = true :=
      resultRelation.isError_iff.mp resultError
    have runtimeCandidateError :=
      memberCondition.2 runtimeResultError runtimeCandidate
        runtimeCandidateMember
    exact candidateRelation.isError_iff.mpr runtimeCandidateError
  · intro result publicResult
    obtain ⟨runtimeResult, runtimeMember, resultRelation⟩ :=
      relation.complete result publicResult.1
    refine ⟨runtimeResult, mem_prioritizeSemanticResults_iff.mpr
      ⟨runtimeMember, ?_⟩, resultRelation⟩
    intro runtimeResultError runtimeCandidate runtimeCandidateMember
    obtain ⟨candidate, candidateRaw, candidateRelation⟩ :=
      relation.sound runtimeCandidate runtimeCandidateMember
    have resultError := resultRelation.isError_iff.mpr runtimeResultError
    have candidateError := publicResult.2 resultError candidate candidateRaw
    exact candidateRelation.isError_iff.mp candidateError

end Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorSuccessPriorityConformance
