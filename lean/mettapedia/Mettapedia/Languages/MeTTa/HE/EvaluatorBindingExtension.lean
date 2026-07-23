import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeServiceConformance
import Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory

/-!
# Evaluator binding-theory extension

Recursive evaluation may add constraints, but it must not forget constraints
already visible at its input.  This module states that property semantically:
every model of an output binding record is also a model of the input record.

The type service supplies the two primitive extension laws used by evaluator
dispatch.  The remaining control steps derive extension from the exact
solution theory of specification matching and merging.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatorBindingExtension

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge
open LeaTTaSpecTypeService
open LeaTTaTypeConformance
open LeaTTaTypeServiceConformance
open Spec.Bindings.ScopeObservation
open Spec.Eval
open Spec.Eval.Steps
open Spec.Match.SolutionTheory
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement

/-- `output` presents at least every constraint presented by `input`. -/
def BindingTheoryExtends (input output : Bindings) : Prop :=
  ∀ valuation, TypeBindingSatisfied valuation output →
    TypeBindingSatisfied valuation input

namespace BindingTheoryExtends

@[simp] theorem refl (bindings : Bindings) :
    BindingTheoryExtends bindings bindings := by
  intro _ satisfied
  exact satisfied

theorem trans {first second third : Bindings}
    (left : BindingTheoryExtends first second)
    (right : BindingTheoryExtends second third) :
    BindingTheoryExtends first third := by
  intro valuation satisfied
  exact left valuation (right valuation satisfied)

theorem of_presentationExtension {input output : Bindings}
    {presentation : Spec.Type.Presentation.TypeSubst}
    (extension : PresentationExtensionRel input presentation output) :
    BindingTheoryExtends input output := by
  intro valuation satisfied
  exact (extension valuation).mp satisfied |>.1

end BindingTheoryExtends

/-- The two binding-extension obligations owned by an evaluator type service.
Lookup is absent because it returns types without changing bindings. -/
structure EvalTypeServiceBindingLaws (typing : EvalTypeService) : Prop where
  typeCast : ∀ {protectedScope space atom expectedType input result},
    typing.typeCast protectedScope space atom expectedType input result →
      BindingTheoryExtends input result.2
  candidateScanSuccess : ∀ {space expression expectedType input candidates
      policy output},
    typing.candidateScan space expression expectedType input candidates
        (.success policy output) →
      BindingTheoryExtends input output

/-- Specification merging conjoins its two input theories, so its output
extends the left input. -/
theorem mergeRel_extends_left {left right output : Bindings}
    (merge : Spec.Match.Merge.MergeRel
      Spec.Match.Merge.equalityGroundedSemantic left right output) :
    BindingTheoryExtends left output := by
  intro valuation outputSatisfied
  apply (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
    valuation left).mpr
  exact ((mergeRel_solution_iff merge
    (fun name => toLeaTTaAtom (valuation name))).mp
      ((specTypeBindingSatisfied_iff_heBindingSatisfied_translated
        valuation output).mp outputSatisfied)).1

/-- Specification merging conjoins its two input theories, so its output
also extends the right input. -/
theorem mergeRel_extends_right {left right output : Bindings}
    (merge : Spec.Match.Merge.MergeRel
      Spec.Match.Merge.equalityGroundedSemantic left right output) :
    BindingTheoryExtends right output := by
  intro valuation outputSatisfied
  apply (specTypeBindingSatisfied_iff_heBindingSatisfied_translated
    valuation right).mpr
  exact ((mergeRel_solution_iff merge
    (fun name => toLeaTTaAtom (valuation name))).mp
      ((specTypeBindingSatisfied_iff_heBindingSatisfied_translated
        valuation output).mp outputSatisfied)).2

/-- Primitive `unify` either retains the incoming record or selects a merged
record containing it. -/
theorem unifyStep_bindingTheoryExtends
    {target pattern thenBranch elseBranch : Atom}
    {input output : Bindings} {result : Atom}
    (step : UnifyStep target pattern thenBranch elseBranch input result output) :
    BindingTheoryExtends input output := by
  cases step with
  | success success =>
      rcases success.1 with ⟨matched, _matched, merged, _loopFree, _model⟩
      exact mergeRel_extends_right merged
  | noMatch => exact BindingTheoryExtends.refl input

/-- A selected switch branch has the same binding-extension property as its
underlying unify candidate. -/
theorem switchRawRel_bindingTheoryExtends_selected
    {scrutinee : Atom} {branches : List Atom} {input output : Bindings}
    {result : Atom}
    (scan : SwitchRawRel scrutinee input branches (.selected result output)) :
    BindingTheoryExtends input output := by
  generalize outcomeEquation :
      SwitchRawOutcome.selected result output = outcome at scan
  induction scan with
  | nil => cases outcomeEquation
  | malformed _ tail ih => exact ih outcomeEquation
  | hit success =>
      cases outcomeEquation
      rcases success.1 with ⟨matched, _matched, merged, _loopFree, _model⟩
      exact mergeRel_extends_right merged
  | miss _ tail ih => exact ih outcomeEquation

/-- `switch-minimal` either keeps its input or returns the selected unify
candidate's extension. -/
theorem switchStep_bindingTheoryExtends
    {scrutinee result : Atom} {branches : List Atom}
    {input output : Bindings}
    (step : SwitchStep scrutinee branches input result output) :
    BindingTheoryExtends input output := by
  cases step with
  | noMatch => exact BindingTheoryExtends.refl input
  | notReducible scan =>
      exact switchRawRel_bindingTheoryExtends_selected scan
  | selected scan _ =>
      exact switchRawRel_bindingTheoryExtends_selected scan

/-- A selected equation candidate merges the match presentation into the
incoming evaluator theory. -/
theorem equationQueryCandidateRel_bindingTheoryExtends
    {space : Space} {live : List Atom} {query emitted : Atom}
    {input output : Bindings}
    (candidate : EquationQueryCandidateRel
      space live query input emitted output) :
    BindingTheoryExtends input output := by
  rcases candidate with
    ⟨_freshPattern, _freshRhs, matched, _rule, merged, _loopFree,
      _model, _observation⟩
  exact mergeRel_extends_left merged

/-- A successful core-plus-R2 match exposes the incoming theory as the first
conjunct of its exact solution characterization. -/
theorem corePlusR2TypeMatchRel_bindingTheoryExtends
    {left right : Atom} {input output : Bindings}
    (matched : CorePlusR2TypeMatchRel left right input output) :
    BindingTheoryExtends input output := by
  intro valuation satisfied
  exact (matched.solutions valuation).mp satisfied |>.1

/-- First-success type casting inherits extension from the selected match. -/
theorem firstTypeCastSuccessRel_bindingTheoryExtends
    {expectedType : Atom} {input output : Bindings} {candidates : List Atom}
    (selected : FirstTypeCastSuccessRel
      expectedType input candidates output) :
    BindingTheoryExtends input output := by
  induction selected with
  | head matched => exact corePlusR2TypeMatchRel_bindingTheoryExtends matched
  | tail _ _ ih => exact ih

/-- The repaired prepared cast either returns a selected extension or leaves
the incoming binding record unchanged in every diagnostic result. -/
theorem preparedTypeCastRel_bindingTheoryExtends
    {oracle : TypePreparationOracle} {space : Space}
    {atom expectedType : Atom} {input : Bindings} {result : ResultPair}
    {protectedScope : List String}
    (cast : PreparedTypeCastRel oracle space atom expectedType input result
      protectedScope) :
    BindingTheoryExtends input result.2 := by
  cases cast with
  | success _ _ selected =>
      exact firstTypeCastSuccessRel_bindingTheoryExtends selected
  | failure => exact BindingTheoryExtends.refl input

/-- Every successful prepared package scan carries the exact presentation
extension selected by its winning candidate. -/
theorem preparedPackageCandidateScanRel_bindingTheoryExtends
    {oracle : TypePreparationOracle} {space : Space}
    {expression expectedType : Atom} {input : Bindings}
    {packages : List Spec.Type.Presentation.Exact.TypePackage}
    {policy : SelectedTypePolicy}
    {output : Bindings}
    (scan : PreparedPackageCandidateScanRel oracle space expression
      expectedType input packages (.success policy output)) :
    BindingTheoryExtends input output := by
  rcases scan with
    ⟨initialPresentation, candidates, _initial, _variants, candidatesScan⟩
  obtain ⟨candidate, _member, applicable⟩ := candidatesScan.success_candidate
  rcases applicable with
    ⟨_operator, _arguments, _argumentTypes, _returnType, _candidateLists,
      _argumentOutcome, _returnOutcome, presentation, _expressionShape,
      _functionType, _arity, _prepared, _separated, _argumentScan,
      _returnScan, _selected, _policy, extension⟩
  exact BindingTheoryExtends.of_presentationExtension extension

/-- The package-recovery wrapper preserves the extension theorem of its
package scan. -/
theorem recoveredPackageCandidateScanRel_bindingTheoryExtends
    {oracle : TypePreparationOracle} {space : Space}
    {expression expectedType : Atom} {input : Bindings}
    {presented : List Atom} {policy : SelectedTypePolicy}
    {output : Bindings}
    (scan : RecoveredPackageCandidateScanRel oracle
      (PreparedPackageCandidateScanRel oracle) space expression expectedType
        input presented (.success policy output)) :
    BindingTheoryExtends input output := by
  rcases scan with
    ⟨_operator, _arguments, _prepared, _packages, _shape,
      _preparation, _packagesRelation, _alpha, packageScan⟩
  exact preparedPackageCandidateScanRel_bindingTheoryExtends packageScan

/-- The exact prepared package service satisfies both primitive extension
laws without any additional freshness assumption. -/
theorem preparedPackageTypeService_bindingLaws
    (oracle : TypePreparationOracle) :
    EvalTypeServiceBindingLaws (preparedPackageTypeService oracle) := by
  constructor
  · intro protectedScope space atom expectedType input result cast
    exact preparedTypeCastRel_bindingTheoryExtends cast
  · intro space expression expectedType input candidates policy output scan
    exact recoveredPackageCandidateScanRel_bindingTheoryExtends scan

/-! ## Mutual evaluator preservation -/

/-- Every raw evaluator derivation extends its input binding theory.  The
mutual induction simultaneously proves the same invariant for expression,
function, argument, tuple, and call subderivations. -/
theorem evalAtomRawRel_bindingTheoryExtends
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom}
    {atom expectedType : Atom} {input : Bindings} {result : ResultPair}
    {typing : EvalTypeService}
    (laws : EvalTypeServiceBindingLaws typing)
    (derivation : EvalAtomRawRel space dispatch live (typing := typing)
      atom expectedType input result) :
    BindingTheoryExtends input result.2 := by
  have generalized : typing = typing →
      BindingTheoryExtends input result.2 := by
    apply EvalAtomRawRel.rec
      (motive_1 := fun _ _ input result _protectedScope currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_2 := fun _ _ input result currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_3 := fun _ _ _ input result currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_4 := fun _ _ input result currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_5 := fun _ input result currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (motive_6 := fun _ _ input result currentTyping _ =>
        currentTyping = typing → BindingTheoryExtends input result.2)
      (t := derivation)
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact laws.typeCast (by assumption)
    · intros
      subst_vars
      solve_by_elim [rfl]
    · intros
      subst_vars
      solve_by_elim [rfl]
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (laws.candidateScanSuccess (by assumption))
        (BindingTheoryExtends.trans
          (by solve_by_elim [rfl]) (by solve_by_elim [rfl]))
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (by solve_by_elim [rfl]) (by solve_by_elim [rfl])
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      solve_by_elim [rfl]
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (by solve_by_elim [rfl]) (by solve_by_elim [rfl])
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (by solve_by_elim [rfl]) (by solve_by_elim [rfl])
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      solve_by_elim [rfl]
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (by solve_by_elim [rfl]) (by solve_by_elim [rfl])
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (by solve_by_elim [rfl]) (by solve_by_elim [rfl])
    · intros
      subst_vars
      solve_by_elim [rfl]
    · intros
      subst_vars
      solve_by_elim [rfl]
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (by solve_by_elim [rfl]) (by solve_by_elim [rfl])
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (by solve_by_elim [rfl]) (by solve_by_elim [rfl])
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact unifyStep_bindingTheoryExtends (by assumption)
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact switchStep_bindingTheoryExtends (by assumption)
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (mergeRel_extends_right (by assumption))
        (by solve_by_elim [rfl])
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact BindingTheoryExtends.trans
        (equationQueryCandidateRel_bindingTheoryExtends (by assumption))
        (by solve_by_elim [rfl])
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
    · intros
      subst_vars
      exact BindingTheoryExtends.refl _
  exact generalized rfl

/-- The repaired evaluator service therefore preserves every incoming
binding constraint throughout all six semantic judgments. -/
theorem prepared_evalAtomRawRel_bindingTheoryExtends
    {oracle : TypePreparationOracle}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom}
    {atom expectedType : Atom} {input : Bindings} {result : ResultPair}
    (derivation : EvalAtomRawRel space dispatch live
      (typing := preparedPackageTypeService oracle)
      atom expectedType input result) :
    BindingTheoryExtends input result.2 :=
  evalAtomRawRel_bindingTheoryExtends
    (preparedPackageTypeService_bindingLaws oracle) derivation

/-! ## Boundary canaries -/

/-- Positive: the empty binding theory extends itself. -/
example : BindingTheoryExtends Bindings.empty Bindings.empty :=
  BindingTheoryExtends.refl _

private def forgottenBinding : Bindings :=
  ⟨[("x", .symbol "A")], []⟩

/-- Negative: replacing a visible assignment by the empty theory forgets a
constraint and therefore is not an extension. -/
example : ¬BindingTheoryExtends forgottenBinding Bindings.empty := by
  intro extension
  let valuation : String → Atom := fun name =>
    if name = "x" then .symbol "B" else .var name
  have emptySatisfied : TypeBindingSatisfied valuation Bindings.empty := by
    simp [TypeBindingSatisfied, Bindings.empty]
  have forgottenSatisfied := extension valuation emptySatisfied
  have equation := forgottenSatisfied.1 "x" (.symbol "A") (by
    simp [forgottenBinding])
  simp [valuation, applyTypeValuation] at equation

end Mettapedia.Languages.MeTTa.HE.EvaluatorBindingExtension
