import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralInPlaceRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosureIntersect

/-!
# The stratified Miller class under in-place intersection

Every progress of the in-place intersection rule **drops the first equation under a pattern answer**
(`HeadDrop`): its residual store is the store's other equations, in their order, instantiated by an answer that makes
the first equation valid, and the answer is a pattern answer in R116's sense (`PatternAnswer`, every variable read as
a metavariable).

* At depth `0` this is general intersection: R76's pruning answer (`pruneAnswer`) and the certified drop
  (`generalIntersectRule_headDrop`).
* Carrying past a later declaration lifts the answer (`PatternAnswer.liftAll`, the later declaration a metavariable
  too), keeps the other equations in place, and keeps the first equation valid (`carrySited_headDrop`).

So the class is closed under every in-place intersection progress (`stratifiedMiller_inPlaceIntersectAt`), by R116's
answer-then-drop closure in the general setting.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPrune ContextualDependentPatternSolver ContextualDependentDecisiveFragment
open ContextualDependentFragment ContextualDependentRank ContextualDependentConversionBudget
open ContextualDependentIntersection ContextualDependentIntersectionGeneral ContextualDependentDynamicFragment
open ContextualDependentShortClosure ContextualDependentHereditary ContextualDependentInPlace

/-! ## Pattern answers under a later metavariable -/

section Lift

variable {Head : Type} {R : Rules Head}

/-- **A pattern answer under one more metavariable**: the new variable is a metavariable, renamed to the new one. -/
def PatternAnswer.liftAll {n m : Nat} {σ : Sub Head n m}
    (answer : PatternAnswer R (bodyFlexible (o := n) 0) (bodyFlexible (o := m) 0) σ) :
    PatternAnswer R (bodyFlexible (o := n + 1) 0) (bodyFlexible (o := m + 1) 0) (liftSub σ) where
  target := answer.target.succ
  flexibleTarget := rfl
  rename i := Fin.cases (motive := fun i => i ≠ answer.target.succ → Fin (m + 1)) (fun _ => 0)
    (fun j hj => (answer.rename j (fun h => hj (congrArg Fin.succ h))).succ) i
  injective := by
    intro i j hi hj same
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;> rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rfl
    · exact absurd same (Fin.succ_ne_zero _).symm
    · exact absurd same (Fin.succ_ne_zero _)
    · exact congrArg Fin.succ (answer.injective i j _ _ (Fin.succ_injective _ same))
  respects := fun _ _ => rfl
  others := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rfl
    · change Presentation.rename wk (σ i) = _
      rw [answer.others i (fun h => hi (congrArg Fin.succ h))]
      rfl
  outerArity := answer.outerArity
  outer := fun j => (answer.outer j).succ
  outerInjective := fun _ _ same => answer.outerInjective (Fin.succ_injective _ same)
  outerFlexible := fun _ => rfl
  value := answer.value
  solution := by
    change Presentation.rename wk (σ answer.target) = _
    rw [answer.solution, rename_comp]
    rfl
  valueMiller := answer.valueMiller
  valueNormal := answer.valueNormal

end Lift

/-! ## Dropping the first equation under a pattern answer -/

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **An update drops the first equation under a pattern answer.** -/
def HeadDrop {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (update : Update S.levels problem) : Prop :=
  ∃ (first : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) (σ : update.target ⟶ Θ),
    problem = first :: rest ∧ σ = update.answer ∧ update.remaining = (frames S.levels).applyStore σ rest ∧
    (∀ {Δ : Context S.R} (τ : Δ ⟶ update.target), (frames S.levels).Solves τ (first.1.reindex σ, first.2.reindex σ)) ∧
    Nonempty (PatternAnswer S.R (bodyFlexible (o := Θ.arity) 0) (bodyFlexible (o := update.target.arity) 0)
      σ.substitution)

/-- **Dropping the first equation under a pattern answer keeps the class.** -/
theorem stratifiedMiller_of_headDrop (rigid : ∀ name, S.roles name = .rigid) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem}
    (stratified : StratifiedMiller S.levels problem) (opened : OpenedNormal problem) (drops : HeadDrop problem update) :
    StratifiedMiller S.levels update.remaining := by
  obtain ⟨first, rest, σ, rfl, _, remaining, valid, ⟨answer⟩⟩ := drops
  rw [remaining]
  exact stratifiedMiller_answer_drop (computation_empty rigid) σ answer stratified opened valid

/-- Solving an instantiated equation is solving the equation at the composite. -/
theorem solves_reindex {Θ Θ' Δ : Context S.R} (σ : Θ' ⟶ Θ) (τ : Δ ⟶ Θ') (x y : TotalTerm Θ) :
    (frames S.levels).Solves τ (x.reindex σ, y.reindex σ) ↔ (frames S.levels).Solves (τ ≫ σ) (x, y) := by
  have moved := Frames.models_applyStore (X := frames S.levels) σ τ [(x, y)]
  change (∀ e ∈ [(x.reindex σ, y.reindex σ)], (frames S.levels).Solves τ e) ↔
    (∀ e ∈ [(x, y)], (frames S.levels).Solves (τ ≫ σ) e) at moved
  simp only [List.mem_singleton, forall_eq] at moved
  exact moved

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include rigid in
/-- **General intersection on one recognized pattern drops the first equation under a pattern answer.** -/
theorem generalIntersect_headDrop (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    {scopeType : TypeOver (extend Γ₀ newer)} (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ₀ newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ₀ newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ₀ newer))) (spine : Spine newer)
    (recognized : Recognized spine scope active)
    {found : Progress facts roots heads algebra rigid complete (equation :: rest)}
    (fired : generalIntersect facts roots heads algebra rigid complete declared choices reducer normalizes
      headTypingUnique fuel newer scope active equation view rest spine recognized = some found) :
    HeadDrop (equation :: rest) found.val := by
  unfold generalIntersect at fired
  dsimp only at fired
  repeat' (first | (split at fired) | (cases fired))
  rename_i certificate _
  exact ⟨equation, rest, _, rfl, (Category.id_comp _).symm, rfl,
    fun τ => (frames S.levels).preserves τ certificate.down, ⟨pruneAnswer (computation_empty rigid) _⟩⟩

include rigid in
theorem generalIntersectEquation_headDrop (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    (equation : Equation (TotalTerm (extend Γ₀ newer))) (rest : EquationStore (TotalTerm (extend Γ₀ newer)))
    {found : Progress facts roots heads algebra rigid complete (equation :: rest)}
    (fired : generalIntersectEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel newer equation rest = some found) :
    HeadDrop (equation :: rest) found.val := by
  unfold generalIntersectEquation at fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  exact generalIntersect_headDrop facts roots heads algebra rigid complete declared choices reducer normalizes
    headTypingUnique fuel newer _ _ equation _ rest _ _ fired

include rigid in
/-- **Every progress of the general intersection rule drops the first equation under a pattern answer.** -/
theorem generalIntersectRule_headDrop (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {found : Progress facts roots heads algebra rigid complete problem}
    (fired : generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem = some found) :
    HeadDrop problem found.val := by
  unfold generalIntersectRule at fired
  split at fired
  · cases fired
  rename_i view _
  rcases view with ⟨base, type, same⟩
  subst same
  cases problem with
  | nil => cases fired
  | cons equation rest =>
      exact generalIntersectEquation_headDrop facts roots heads algebra rigid complete declared choices reducer root
        normalizes headTypingUnique fuel type equation rest fired

include rigid in
/-- The general intersection rule with its sites drops the first equation under a pattern answer. -/
theorem sitedRule_headDrop (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {found : SitedProgress facts roots heads algebra rigid complete problem}
    (fired : sitedRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem = some found) :
    HeadDrop problem found.val := by
  unfold sitedRule at fired
  split at fired
  · rename_i progress computed
    cases fired
    exact generalIntersectRule_headDrop facts roots heads algebra rigid complete declared choices reducer root
      normalizes headTypingUnique fuel problem computed
  · cases fired

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **Carrying past a later declaration keeps the first equation dropped under a pattern answer.** -/
theorem carrySited_headDrop {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type)))
    (left : {strong : TotalTerm Γ // rename wk strong.1.code = equation.1.1.code ∧
      rename wk strong.2.code = equation.1.2.code})
    (right : {strong : TotalTerm Γ // rename wk strong.1.code = equation.2.1.code ∧
      rename wk strong.2.code = equation.2.2.code})
    (same : (frames S.levels).Equivalent (equation :: rest)
      (rest ++ (frames S.levels).applyStore (projectionHom Γ type) [(left.val, right.val)]))
    (weights : storeWeight facts roots heads algebra rigid complete
        (rest ++ (frames S.levels).applyStore (projectionHom Γ type) [(left.val, right.val)]) =
      storeWeight facts roots heads algebra rigid complete (equation :: rest))
    (found : SitedProgress facts roots heads algebra rigid complete [(left.val, right.val)])
    (drops : HeadDrop [(left.val, right.val)] found.val) :
    HeadDrop (equation :: rest) (carrySited facts roots heads algebra rigid complete type same weights found).val := by
  obtain ⟨first, rest', σ, listed, answered, remaining, valid, ⟨answer⟩⟩ := drops
  simp only [List.cons.injEq] at listed
  obtain ⟨firstSame, restSame⟩ := listed
  subst firstSame restSame answered
  refine ⟨equation, rest, rawLift found.val.answer type, rfl, rfl, ?_, ?_, ⟨PatternAnswer.liftAll answer⟩⟩
  · change (frames S.levels).applyStore (rawLift found.val.answer type) rest ++
        (frames S.levels).applyStore (projectionHom found.val.target (type.reindex found.val.answer))
          found.val.remaining = _
    rw [remaining]
    exact List.append_nil _
  · intro Δ τ
    have earlier := (solves_reindex (projectionHom found.val.target (type.reindex found.val.answer)) τ
      (left.val.reindex found.val.answer) (right.val.reindex found.val.answer)).mpr
      (valid (τ ≫ projectionHom found.val.target (type.reindex found.val.answer)))
    refine (solves_of_codes τ ?_ ?_ ?_ ?_).mp earlier
    · change subst projection (subst found.val.answer.substitution left.val.1.code) =
        subst (liftSub found.val.answer.substitution) equation.1.1.code
      rw [subst_projection]
      exact (subst_liftSub_wk _ _).symm.trans (congrArg _ left.property.1)
    · change subst projection (subst found.val.answer.substitution left.val.2.code) =
        subst (liftSub found.val.answer.substitution) equation.1.2.code
      rw [subst_projection]
      exact (subst_liftSub_wk _ _).symm.trans (congrArg _ left.property.2)
    · change subst projection (subst found.val.answer.substitution right.val.1.code) =
        subst (liftSub found.val.answer.substitution) equation.2.1.code
      rw [subst_projection]
      exact (subst_liftSub_wk _ _).symm.trans (congrArg _ right.property.1)
    · change subst projection (subst found.val.answer.substitution right.val.2.code) =
        subst (liftSub found.val.answer.substitution) equation.2.2.code
      rw [subst_projection]
      exact (subst_liftSub_wk _ _).symm.trans (congrArg _ right.property.2)

include rigid in
/-- **Every in-place intersection progress drops the first equation under a pattern answer.** -/
theorem inPlaceIntersectAt_headDrop (fuel : Nat) :
    ∀ (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
      {found : SitedProgress facts roots heads algebra rigid complete problem},
      inPlaceIntersectAt facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel depth problem = some found → HeadDrop problem found.val
  | 0, _, problem, _, fired => sitedRule_headDrop facts roots heads algebra rigid complete declared choices reducer
      root normalizes headTypingUnique fuel problem fired
  | depth + 1, Θ, problem, found, fired => by
      simp only [inPlaceIntersectAt] at fired
      split at fired
      · cases fired
      rename_i view _
      rcases view with ⟨base, type, same⟩
      subst same
      change carryHead facts roots heads algebra rigid complete type problem
        (fun strong => inPlaceIntersectAt facts roots heads algebra rigid complete declared choices reducer root
          normalizes headTypingUnique fuel depth strong)
        (headSplit facts roots heads algebra rigid complete declared choices reducer fuel type problem) = some found
        at fired
      cases problem with
      | nil => cases fired
      | cons equation rest =>
          simp only [headSplit] at fired
          split at fired
          · rename_i left right _ _
            unfold carryHead at fired
            obtain ⟨inner, innerFired, carried⟩ := Option.map_eq_some_iff.mp fired
            subst carried
            exact carrySited_headDrop facts roots heads algebra rigid complete type equation rest left right _ _ inner
              (inPlaceIntersectAt_headDrop fuel depth _ innerFired)
          · cases fired

include rigid in
/-- **The stratified Miller class is closed under every in-place intersection progress.** -/
theorem stratifiedMiller_inPlaceIntersectAt (fuel depth : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) (stratified : StratifiedMiller S.levels problem)
    (opened : OpenedNormal problem) {found : SitedProgress facts roots heads algebra rigid complete problem}
    (fired : inPlaceIntersectAt facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel depth problem = some found) :
    StratifiedMiller S.levels found.val.remaining :=
  stratifiedMiller_of_headDrop rigid stratified opened
    (inPlaceIntersectAt_headDrop facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel depth problem fired)

end ContextualDependentMillerClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
