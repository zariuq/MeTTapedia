import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDeclarationNormalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantDispatch

/-!
# Retrying actual pruning after certified declaration normalization

Direct recognition is attempted first. If unfinished, the independently
formed newest annotation is normalized, the entire store is transported
through the typed extension comparison, and recognition is retried. Both
updates are composed. If neither route recognizes a pruning step, the exact
original problem remains pending.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalizedPruning

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

variable {L : Type} [UniverseLevel.LevelOrder L] (valuation : Nat → L)
variable [DecidableEq (LevelTower.Head L)] [DecidableRel (TowerModel.setting valuation).R.headEq]
  [∀ head, Decidable ((TowerModel.setting valuation).R.isUniverse head)] [DecidableRel (TowerModel.setting valuation).R.cumulative]

def solve (fuel : Nat) {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) :
    Option (Update (TowerModel.setting valuation).levels problem) :=
  match ContextualDependentConstantDispatch.search valuation fuel whole problem with
  | some direct => some direct
  | none => do
      let normalized ← ContextualDependentDeclarationNormalization.normalize (S := TowerModel.setting valuation)
        (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads fuel whole
      let prepared := normalized.update problem
      let pruned ← ContextualDependentConstantDispatch.search valuation fuel normalized.annotation prepared.remaining
      return prepared.then pruned

def step (fuel : Nat) {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) : Update (TowerModel.setting valuation).levels problem :=
  (solve valuation fuel whole problem).getD (Update.pending (TowerModel.setting valuation).levels problem)

theorem solve_preserves_direct {fuel : Nat} {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) (result : Update (TowerModel.setting valuation).levels problem)
    (computed : ContextualDependentConstantDispatch.search valuation fuel whole problem = some result) :
    solve valuation fuel whole problem = some result := by
  unfold solve
  rw [computed]

set_option backward.isDefEq.respectTransparency false in
theorem solve_zero {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) : solve valuation 0 whole problem = none := by
  unfold solve
  rw [ContextualDependentConstantDispatch.search_zero]
  rfl

theorem step_zero {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) :
    step valuation 0 whole problem = Update.pending (TowerModel.setting valuation).levels problem := by
  unfold step
  rw [solve_zero]
  rfl

theorem step_of_unfinished {fuel : Nat} {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) (unfinished : solve valuation fuel whole problem = none) :
    step valuation fuel whole problem = Update.pending (TowerModel.setting valuation).levels problem := by
  unfold step
  rw [unfinished]
  rfl

omit [DecidableEq (LevelTower.Head L)] [DecidableRel (TowerModel.setting valuation).R.headEq]
  [∀ head, Decidable ((TowerModel.setting valuation).R.isUniverse head)] [DecidableRel (TowerModel.setting valuation).R.cumulative] in
theorem declaration_eventually_normalizes {Γ : Context (LevelTower.rules L)} (whole : TypeOver Γ) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      (ContextualDependentDeclarationNormalization.normalize (S := TowerModel.setting valuation) (fun _ => none)
        TowerModel.facts TowerModel.roots TowerModel.heads larger whole).isSome = true := by
  obtain ⟨fuel, result, _, stable⟩ := ContextualDependentTowerBudget.type_eventually_stable whole
  refine ⟨fuel, fun larger enough => ?_⟩
  apply (ContextualDependentDeclarationNormalization.normalize_success_iff (S := TowerModel.setting valuation)
    (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger whole).mpr
  exact congrArg Option.isSome (stable larger enough)

end ContextualDependentNormalizedPruning
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
