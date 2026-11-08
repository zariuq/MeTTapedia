import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureDecompose

/-!
# Closure of the cumulative round: replacing an equation by closed scoped pieces

R98's and R99's decompositions read an equation under its abstractions, split the reading into scoped pieces, close
each piece back into a store equation by abstracting the locals (`Scoped.closeWith`), and replace the equation by the
closed pieces. Such a replacement keeps the permuted class stably (`replaced_stable`) when:

* the pieces have exactly the equation's solutions;
* each piece's codes reduce to normal codes with Miller occurrences, the outer variables flexible and the locals rigid
  (`MarkedReduct`); closing abstracts the locals, so a closed piece's codes reduce to closed normal Miller codes
  (`closeWith_reduct`), whence Miller sides at every opening depth (`sides_of_reducts`, by R116's `sides_of_closed`);
* closed pieces have one annotation on both sides, so they are stratified among themselves.

R99's decomposition of local applications (`decomposeSearch`) replaces `x ā ≐ x b̄` by the argument equation, whose
codes are the arguments of the reading's rigid applications (`decomposeActive_codes`), then runs R75's pattern rule; it
keeps the permuted class (`decomposeSearch_keeps`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentDynamicFragment
open ContextualDependentExecutableJoin ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentGeneralPattern (liftFlexible)

/-! ## Codes with Miller normal reducts -/

section Reducts

variable {Head : Type} {R : Rules Head}

/-- **A code with a normal reduct of Miller occurrences** at a marking. -/
def MarkedReduct (R : Rules Head) {n : Nat} (mark : Fin n → Bool) (t : Tm Head n) : Prop :=
  ∃ t', Star (R := R) t t' ∧ Normal R t' ∧ miller mark t' = true

theorem MarkedReduct.lam (empty : R.computation = RootComputation.empty) {n : Nat} {mark : Fin n → Bool}
    {t : Tm Head (n + 1)} (inner : MarkedReduct R (liftFlexible mark) t) : MarkedReduct R mark (.lam t) := by
  obtain ⟨t', steps, normal, millerT⟩ := inner
  exact ⟨.lam t', star_map Tm.lam (fun step => .congLam step) steps, (normal_lam_iff empty).mpr normal, millerT⟩

/-- **A code with a closed normal Miller reduct has Miller normal forms at every opening depth.** -/
theorem opened_of_reduct (empty : R.computation = RootComputation.empty) {n : Nat} {code : Tm Head n}
    (reduct : MarkedReduct R (fun _ => true) code) (count : Nat) :
    ∀ opened, Star (R := R) (openCode count code) opened → Normal R opened →
      miller (openedFlexible count) opened = true := by
  obtain ⟨code', steps, normal, closed⟩ := reduct
  obtain ⟨N, toN, normalN, millerN⟩ := sides_of_closed empty normal closed count
  exact all_miller_of_one empty ⟨N, (ContextualDependentOpenedNormal.star_openCode steps count).trans toN, normalN,
    millerN⟩

end Reducts

section Equations

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **Miller sides from closed normal Miller reducts of both codes.** -/
theorem sides_of_reducts (empty : rules.computation = RootComputation.empty) {Θ : Context rules}
    {equation : Equation (TotalTerm Θ)} (left : MarkedReduct rules (fun _ => true) equation.1.2.code)
    (right : MarkedReduct rules (fun _ => true) equation.2.2.code) : FragmentSidesMiller equation :=
  ⟨opened_of_reduct empty left _, opened_of_reduct empty right _⟩

/-- The marking of a spine's target from a marking of its outer context: the spine's locals rigid. -/
def scopeMark : {Γ : Context rules} → {type : TypeOver Γ} → (Fin Γ.arity → Bool) → (scope : Spine type) →
    Fin scope.target.arity → Bool
  | _, _, outer, .stop _ => outer
  | _, _, outer, .bind _ rest => scopeMark (liftFlexible outer) rest

theorem scopeMark_val : ∀ {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type) (k : Nat)
    (outer : Fin Γ.arity → Bool), (∀ j, outer j = decide (k ≤ j.val)) →
    ∀ i, scopeMark outer scope i = decide (k + scope.length ≤ i.val)
  | _, _, .stop _, k, outer, marked, i => by
      change outer i = decide (k + 0 ≤ i.val)
      rw [marked i]
      rfl
  | _, _, .bind _ rest, k, outer, marked, i => by
      change scopeMark (liftFlexible outer) rest i = decide (k + (rest.length + 1) ≤ i.val)
      have lifted : ∀ j, liftFlexible outer j = decide (k + 1 ≤ j.val) := by
        intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [liftFlexible]
        · change outer j = _
          rw [marked j]
          simp
      rw [scopeMark_val rest (k + 1) _ lifted i, show k + 1 + rest.length = k + (rest.length + 1) by omega]

/-- On the empty outer marking, the scope marking is the spine marking. -/
theorem scopeMark_spineMark {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type) (i : Fin scope.target.arity) :
    scopeMark (fun _ => true) scope i = ContextualDependentShortClosure.spineMark scope i := by
  rw [scopeMark_val scope 0 _ (fun _ => by simp) i]
  simp [ContextualDependentShortClosure.spineMark]

variable (empty : rules.computation = RootComputation.empty) (choices : ExecutableChecking.HeadChoices rules)
include empty

/-- **Closing a scoped piece abstracts its locals**: codes with marked normal Miller reducts close to codes with outer
normal Miller reducts. -/
theorem closeWith_reduct : ∀ {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type)
    (outer : Fin Γ.arity → Bool) (active : Active scope.target) {closed : Active Γ},
    (scope.toScoped active).closeWith levels choices = some closed →
    MarkedReduct rules (scopeMark outer scope) active.left.code →
    MarkedReduct rules (scopeMark outer scope) active.right.code →
    MarkedReduct rules outer closed.left.code ∧ MarkedReduct rules outer closed.right.code
  | _, _, .stop _, outer, active, closed, computed, left, right => by
      cases computed
      exact ⟨left, right⟩
  | _, _, .bind shape rest, outer, active, closed, computed, left, right => by
      change (Scoped.bind shape.domain (rest.toScoped active)).closeWith levels choices = some closed at computed
      unfold Scoped.closeWith at computed
      obtain ⟨inner, innerComputed, computed⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨result, _, computed⟩ := Option.bind_eq_some_iff.mp computed
      cases computed
      obtain ⟨innerLeft, innerRight⟩ := closeWith_reduct rest (liftFlexible outer) active innerComputed left right
      exact ⟨MarkedReduct.lam empty innerLeft, MarkedReduct.lam empty innerRight⟩

/-- **A closed scoped piece has Miller sides** when the piece's codes have Miller normal reducts with the locals
rigid. -/
theorem closed_sides {Γ : Context rules} {type : TypeOver Γ} (scope : Spine type) (active : Active scope.target)
    {closed : Active Γ} (computed : (scope.toScoped active).closeWith levels choices = some closed)
    (left : MarkedReduct rules (ContextualDependentShortClosure.spineMark scope) active.left.code)
    (right : MarkedReduct rules (ContextualDependentShortClosure.spineMark scope) active.right.code) :
    FragmentSidesMiller closed.equation := by
  have marking : scopeMark (fun _ => true) scope = ContextualDependentShortClosure.spineMark scope :=
    funext (scopeMark_spineMark scope)
  rw [← marking] at left right
  obtain ⟨closedLeft, closedRight⟩ := closeWith_reduct empty choices scope (fun _ => true) active computed left right
  exact sides_of_reducts empty closedLeft closedRight

end Equations

/-! ## Replacing an equation by pieces -/

section Replace

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem applyStore_identity {Θ : Context S.R} (store : EquationStore (TotalTerm Θ)) :
    (frames S.levels).applyStore (𝟙 Θ) store = store := by
  induction store with
  | nil => rfl
  | cons equation rest ih =>
      change ((frames S.levels).act (𝟙 Θ) equation.1, (frames S.levels).act (𝟙 Θ) equation.2) ::
        (frames S.levels).applyStore (𝟙 Θ) rest = _
      rw [show (frames S.levels).act (𝟙 Θ) equation.1 = equation.1 from (frames S.levels).act_id equation.1,
        show (frames S.levels).act (𝟙 Θ) equation.2 = equation.2 from (frames S.levels).act_id equation.2, ih]

/-- **Replacing an equation by pieces with exactly its solutions, Miller sides and one annotation each is stable.** -/
theorem replaced_stable {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (pieces : EquationStore (TotalTerm Θ))
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), (frames S.levels).Models σ pieces ↔ (frames S.levels).Solves σ equation)
    (sides : ∀ piece ∈ pieces, FragmentSidesMiller piece) (single : ∀ piece ∈ pieces, piece.1.1 = piece.2.1)
    (same : (frames S.levels).Equivalent (equation :: rest) (pieces ++ rest)) :
    StableKeeps ((Update.pending S.levels (pieces ++ rest)).rephrase same) := by
  intro before permuted
  change PermutedMiller S.levels ((frames S.levels).applyStore (𝟙 Θ) before ++ (pieces ++ rest))
  rw [applyStore_identity]
  have front : PermutedMiller S.levels (equation :: (before ++ rest)) := permuted.perm List.perm_middle
  have spliced := PermutedMiller.splice_of (pieces := pieces) front fun before' after' stratified =>
    StratifiedMiller.splice stratified exact sides fun first last piece split Δ σ _ => by
      have member : piece ∈ pieces := by
        rw [split]
        exact List.mem_append_right _ List.mem_cons_self
      rw [single piece member]
      exact (piece.2.1.reindex σ).isType.refl
  exact spliced.perm (by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right rest)

end Replace

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
