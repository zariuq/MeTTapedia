import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentShortClosurePrune

/-!
# The stratified Miller class in the general setting, and under twin retyping and general intersection

* **The bridge** (`computation_empty`): a rule package whose constants are all rigid has no root computation at all,
  since the package's root shape puts every root step at a computing constant. So R116's closure lemmas, stated for a
  package with no root computation (`RootComputation.empty`), hold in the general setting of the conditional decisions, which excludes
  root computation only through `rigid` and the root shape (`stratifiedMiller_prune_rigid`,
  `stratifiedMiller_intersect_rigid`, `stratifiedMiller_applyStore_rigid`).
* **Twin retyping** (`stratifiedMiller_collapse`): R99's homogeneous forms keep the sides and make the annotations
  equal codes, so the store with its convertible twins made homogeneous stays in the class.
* **General intersection** (`generalIntersect_spec`, `stratifiedMiller_generalIntersect`): every progress of the
  general intersection rule prunes the store by a restriction and drops the first equation, which the answer makes
  valid; so it keeps the class.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableReduction ContextualDependentExecutableJoin ContextualDependentDynamicFragment
open ContextualDependentEta ContextualDependentClosure ContextualDependentShortClosure
open ContextualDependentPiSpine ContextualDependentPrune ContextualDependentUpdate ContextualDependentWorklist

/-! ## The bridge -/

/-- A root computation with no step is the empty one. -/
theorem RootComputation.eq_empty_of {Head : Type} (computation : RootComputation Head)
    (none : ∀ {n : Nat} {t u : Tm Head n}, ¬ computation.step t u) : computation = RootComputation.empty := by
  cases computation with
  | mk step rename substitute =>
      have stepEmpty : @step = fun {n : Nat} (_ _ : Tm Head n) => False :=
        funext fun _ => funext fun _ => funext fun _ => propext ⟨fun held => none held, False.elim⟩
      subst stepEmpty
      rfl

section Bridge

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)
include rigid

/-- **A package of rigid constants has no root computation.** -/
theorem computation_empty : S.R.computation = RootComputation.empty :=
  RootComputation.eq_empty_of _ fun step => ContextualDependentNormalObservations.no_root rigid step

/-- R116's closure under every pattern answer between contexts, in the general setting. -/
theorem stratifiedMiller_applyStore_rigid {Θ Δ : Context S.R} (σ : Δ ⟶ Θ)
    (answer : ContextualDependentHereditary.PatternAnswer S.R (bodyFlexible (o := Θ.arity) 0)
      (bodyFlexible (o := Δ.arity) 0) σ.substitution)
    {problem : EquationStore (TotalTerm Θ)} (stratified : StratifiedMiller S.levels problem)
    (normalizes : ∀ equation ∈ problem,
      (∃ opened, Star (R := S.R)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal S.R opened) ∧
      (∃ opened, Star (R := S.R)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal S.R opened)) :
    StratifiedMiller S.levels ((frames S.levels).applyStore σ problem) :=
  stratifiedMiller_applyStore (computation_empty rigid) σ answer stratified normalizes

/-- R116's closure under pruning, in the general setting. -/
theorem stratifiedMiller_prune_rigid {Γ : Context S.R} {type keptType : TypeOver Γ} {spine : Spine type}
    {kept : Spine keptType} (restriction : Restriction spine kept)
    {problem : EquationStore (TotalTerm (extend Γ type))} (stratified : StratifiedMiller S.levels problem)
    (normalizes : ∀ equation ∈ problem,
      (∃ opened, Star (R := S.R)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal S.R opened) ∧
      (∃ opened, Star (R := S.R)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal S.R opened)) :
    StratifiedMiller S.levels ((frames S.levels).applyStore restriction.answer problem) :=
  stratifiedMiller_prune (computation_empty rigid) restriction stratified normalizes

/-- R116's closure under the intersection step, in the general setting. -/
theorem stratifiedMiller_intersect_rigid {Γ : Context S.R} {type keptType : TypeOver Γ} {spine : Spine type}
    {kept : Spine keptType} (restriction : Restriction spine kept) {first : Equation (TotalTerm (extend Γ type))}
    {rest : EquationStore (TotalTerm (extend Γ type))} (stratified : StratifiedMiller S.levels (first :: rest))
    (normalizes : ∀ equation ∈ first :: rest,
      (∃ opened, Star (R := S.R)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal S.R opened) ∧
      (∃ opened, Star (R := S.R)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal S.R opened))
    (valid : (frames S.levels).E (first.1.reindex restriction.answer) (first.2.reindex restriction.answer)) :
    StratifiedMiller S.levels ((frames S.levels).applyStore restriction.answer rest) :=
  stratifiedMiller_intersect (computation_empty rigid) restriction stratified normalizes valid

end Bridge

/-! ## Twin retyping -/

section Twins

open ContextualDependentTwinsUnder

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- The homogeneous form is the equation, or its retyping. -/
theorem collapseOne_cases (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    collapseOne facts roots heads algebra reducer fuel equation = equation ∨
      ∃ same, collapseOne facts roots heads algebra reducer fuel equation = retype equation same := by
  unfold collapseOne
  split
  · exact .inl rfl
  · split
    · rename_i same _
      exact .inr ⟨same.down, rfl⟩
    · exact .inl rfl

/-- The homogeneous form keeps the left side and the right side's code. -/
theorem collapseOne_codes (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    (collapseOne facts roots heads algebra reducer fuel equation).1 = equation.1 ∧
      (collapseOne facts roots heads algebra reducer fuel equation).2.2.code = equation.2.2.code := by
  rcases collapseOne_cases facts roots heads algebra reducer fuel equation with same | ⟨_, same⟩ <;>
    rw [same] <;> exact ⟨rfl, rfl⟩

/-- **Twin retyping keeps the stratified Miller class.** -/
theorem stratifiedMiller_collapse (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (stratified : StratifiedMiller S.levels problem) :
    StratifiedMiller S.levels (problem.map (collapseOne facts roots heads algebra reducer fuel)) := by
  refine StratifiedMiller.map stratified _ (fun equation _ σ => collapseOne_solves facts roots heads algebra reducer
    fuel σ equation) (fun equation _ sides => ?_) (fun equation _ before at₀ => ?_)
  · obtain ⟨left, right⟩ := collapseOne_codes facts roots heads algebra reducer fuel equation
    unfold FragmentSidesMiller
    rw [left, right]
    exact sides
  · rcases collapseOne_cases facts roots heads algebra reducer fuel equation with same | ⟨_, same⟩
    · rw [same]
      exact at₀
    · rw [same]
      intro Δ σ _
      exact IsType.refl (equation.1.1.reindex σ).isType

/-- **The collapse update of the twin round keeps the class.** -/
theorem stratifiedMiller_collapse_update (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (stratified : StratifiedMiller S.levels problem) :
    StratifiedMiller S.levels (collapse facts roots heads algebra reducer fuel problem).remaining :=
  stratifiedMiller_collapse facts roots heads algebra reducer fuel stratified

end Twins

end ContextualDependentMillerClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
