import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentContextNormalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTowerBudget

/-!
# Every formed cumulative telescope reaches a normal presentation

Strong normalization is applied to each independently formed declaration
in its original prefix. A single maximum budget covers the finite context,
and every larger budget succeeds. No closed point of the context is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentContextNormalizationTower

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentContextNormalization

variable {L : Type} [UniverseLevel.LevelOrder L] (valuation : Nat → L)

theorem declarations_eventually_finish {n : Nat} (raw : LevelTower.Ctx L n)
    (formed : CtxFormed (LevelTower.rules L) raw) :
    ∃ fuel, ∀ larger, fuel ≤ larger → Finished (S := TowerModel.setting valuation) (fun _ => none) larger raw := by
  induction raw with
  | nil => exact ⟨0, fun _ _ => .nil⟩
  | snoc raw type ih =>
      cases formed with
      | snoc prior typeFormed =>
          obtain ⟨prefixFuel, prefixFinished⟩ := ih prior
          obtain ⟨level, _, typed⟩ := typeFormed
          obtain ⟨typeFuel, result, _, stable⟩ := ContextualDependentTowerBudget.typed_eventually_stable prior typed
          refine ⟨max prefixFuel typeFuel, fun larger enough => .snoc
            (prefixFinished larger ((Nat.le_max_left _ _).trans enough)) ?_⟩
          change (ContextualDependentTowerBudget.reducer larger type).isSome = true
          rw [stable larger ((Nat.le_max_right _ _).trans enough)]
          rfl

theorem context_eventually_normalizes (Γ : Context (LevelTower.rules L)) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      (normalize (S := TowerModel.setting valuation) (fun _ => none) (fun _ _ _ impossible => impossible.elim)
        TowerModel.facts TowerModel.roots TowerModel.heads larger Γ.raw Γ.formed).isSome = true := by
  obtain ⟨fuel, finished⟩ := declarations_eventually_finish valuation Γ.raw Γ.formed
  exact ⟨fuel, fun larger enough =>
    (normalize_success_iff (S := TowerModel.setting valuation) (fun _ => none) (fun _ _ _ impossible => impossible.elim)
      TowerModel.facts TowerModel.roots TowerModel.heads larger Γ.raw Γ.formed).mpr (finished larger enough)⟩

end ContextualDependentContextNormalizationTower
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
