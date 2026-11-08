import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTowerBudget

/-!
# Finite typed stores reach beta-normal endpoints at a sufficient budget

The original input store and its future solutions are retained as the
specification. For every finite typed store in the pure cumulative tower,
one budget suffices to normalize both endpoints and their annotations in
every equation. This is beta/projection normalization, not eta-long
completion or a complete unification procedure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalizationTower

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {L : Type} [UniverseLevel.LevelOrder L] (valuation : Nat → L)

def TermNormal {Γ : Context (LevelTower.rules L)} (term : TotalTerm Γ) : Prop :=
  (∀ target, ¬ StrongNormalization.Reduces (LevelTower.rules L) term.1.code target) ∧
  (∀ target, ¬ StrongNormalization.Reduces (LevelTower.rules L) term.2.code target)

def StoreNormal {Γ : Context (LevelTower.rules L)} (problem : EquationStore (TotalTerm Γ)) : Prop :=
  ∀ equation ∈ problem, TermNormal equation.1 ∧ TermNormal equation.2

theorem term_eventually_normal {Γ : Context (LevelTower.rules L)} (term : TotalTerm Γ) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      TermNormal (ContextualDependentNormalization.termAt (S := TowerModel.setting valuation)
        (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger term) := by
  obtain ⟨fuel, value, annotation, _, _, stable⟩ := ContextualDependentTowerBudget.annotated_eventually_stable term
  refine ⟨fuel, fun larger enough => ?_⟩
  have runs := stable larger enough
  apply ContextualDependentNormalization.termAt_normal_of_success
    (S := TowerModel.setting valuation) (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads
    (fun _ _ _ impossible => impossible.elim) term
  apply (ContextualDependentNormalization.reduceTerm_success_iff
    (S := TowerModel.setting valuation) (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger term).mpr
  exact ⟨congrArg Option.isSome runs.2, congrArg Option.isSome runs.1⟩

theorem store_eventually_normal {Γ : Context (LevelTower.rules L)} (problem : EquationStore (TotalTerm Γ)) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      StoreNormal (ContextualDependentNormalization.storeAt (S := TowerModel.setting valuation)
        (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger problem) := by
  induction problem with
  | nil => exact ⟨0, fun _ _ _ member => False.elim (List.not_mem_nil member)⟩
  | cons equation rest ih =>
    obtain ⟨firstFuel, firstNormal⟩ := term_eventually_normal valuation equation.1
    obtain ⟨secondFuel, secondNormal⟩ := term_eventually_normal valuation equation.2
    obtain ⟨restFuel, restNormal⟩ := ih
    refine ⟨max firstFuel (max secondFuel restFuel), fun larger enough entry member => ?_⟩
    change entry ∈
      (ContextualDependentNormalization.termAt (S := TowerModel.setting valuation)
        (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger equation.1,
       ContextualDependentNormalization.termAt (S := TowerModel.setting valuation)
        (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger equation.2) ::
      ContextualDependentNormalization.storeAt (S := TowerModel.setting valuation)
        (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger rest at member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨firstNormal larger ((Nat.le_max_left _ _).trans enough),
        secondNormal larger ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans enough))⟩
    · exact restNormal larger ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans enough)) entry member

/-- One finite budget yields normal endpoints and preserves/reflects every
future solution of the original store; all larger budgets do too. -/
theorem all_large_normal_and_equivalent {Γ : Context (LevelTower.rules L)}
    (problem : EquationStore (TotalTerm Γ)) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      StoreNormal (ContextualDependentNormalization.storeAt (S := TowerModel.setting valuation)
        (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger problem) ∧
      (frames (TowerModel.setting valuation).levels).Equivalent problem
        (ContextualDependentNormalization.storeAt (S := TowerModel.setting valuation)
          (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger problem) := by
  obtain ⟨fuel, normal⟩ := store_eventually_normal valuation problem
  exact ⟨fuel, fun larger enough => ⟨normal larger enough, fun _ solution =>
    ContextualDependentNormalization.storeAt_models (S := TowerModel.setting valuation)
      (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads larger solution problem⟩⟩

end ContextualDependentNormalizationTower
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
