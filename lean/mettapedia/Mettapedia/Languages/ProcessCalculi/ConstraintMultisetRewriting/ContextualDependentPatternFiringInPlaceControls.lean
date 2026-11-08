import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringInPlace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringNullary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringCensusControls

/-!
# Controls for firing in place

* **The placed row is inhabited** (`placed_row`): over `A : U0, F : U0, G : U0`, the equation `F ≐ A` for the older
  metavariable `F` is in the placed row at depth one. Every view of `G` is read off the context, every reading of the
  equation without `G` has the codes of `F ≐ A` over `A, F`, and each such reading is in the inversion row.
* **The placed round is not stuck on it** from some budget on (`placed_fires`), by the firing theorem in place, and
  the placed solver commits at budget 16 (`placed_committed`), as it does on the census control with an older
  metavariable (`olderInversion_placed_committed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentDynamicFragment ContextualDependentExecutableJoin

/-- The placed solver of the tower controls, as a fuel-indexed family. -/
noncomputable def placedTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  placedFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The placed solver at budget 16. -/
noncomputable def placedOnly : Solver setting.levels := placedTower.solver 16

/-- `A : U0, F : U0, G : U0`. -/
abbrev withFG := extend withF universeF

/-- `U0`, over `A, F, G`. -/
def universeFG : TypeOver withFG := formIn withFG (.head (.sort Tower.zero)) (by decide +kernel)

theorem universeFG_code : universeFG.code = .head (.sort Tower.zero) :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 withFG (.head (.sort Tower.zero))).get
      (by decide +kernel)).property

/-- `F ≐ A`, below `G`. -/
def placedStore : EquationStore (TotalTerm withFG) :=
  [(termIn withFG universeFG (.var 1) (by decide +kernel), termIn withFG universeFG (.var 2) (by decide +kernel))]

theorem placedStore_length : placedStore.length = 1 := rfl

def placedEquation : Equation (TotalTerm withFG) :=
  placedStore.head (List.ne_nil_of_length_pos (by rw [placedStore_length]; decide))

theorem placedStore_eq : placedStore = [placedEquation] := rfl

theorem universe_isType : IsType setting.R withF.raw (.head (.sort Tower.zero)) := by
  have isType := universeF.isType
  rw [universeF_code] at isType
  exact isType

theorem universe_normal {n : Nat} : Normal (LevelTower.rules Nat) (.head (.sort Tower.zero) : Tower.Tm n) :=
  ContextualDependentDynamicFragment.normal_head rfl _

/-- **`F ≐ A` below `G` is in the placed row at depth one.** -/
theorem placed_row_at (depth : Nat) (zero : depth = 0) :
    PlacedRow (fun _ => (0 : Nat)) (depth + 1) placedEquation := by
  show _ ∧ _
  subst zero
  refine ⟨⟨Nat.succ_pos _, ?_⟩, ?_, ContextualDependentDynamicFragment.normal_var rfl _, ?_,
    ContextualDependentDynamicFragment.normal_var rfl _, ?_⟩
  · change Normal (LevelTower.rules Nat) (Presentation.rename wk universeF.code)
    rw [universeF_code]
    exact universe_normal
  · change Normal (LevelTower.rules Nat) universeFG.code
    rw [universeFG_code]
    exact universe_normal
  · change Normal (LevelTower.rules Nat) universeFG.code
    rw [universeFG_code]
    exact universe_normal
  · rintro ⟨⟨arity, raw, formed⟩, ⟨code, level, witness, typed⟩, same⟩
    injection same with arityEq rawEq
    have arityEq' : withF.arity = arity := Nat.succ.inj arityEq
    subst arityEq'
    have rawEq' := eq_of_heq rawEq
    cases rawEq'
    refine ⟨⟨nullaryEquation, ?_⟩, ?_⟩
    · refine ⟨?_, rfl, ?_, rfl⟩
      · change Presentation.rename wk universeF.code = universeFG.code
        rw [universeF_code, universeFG_code]
        rfl
      · change Presentation.rename wk universeF.code = universeFG.code
        rw [universeF_code, universeFG_code]
        rfl
    · rintro strong ⟨w₁, w₂, w₃, w₄⟩
      have injective := ContextualDependentVariableFactorization.rename_injective (Head := Tower.Head)
        (wk : Ren 2 3) (Fin.succ_injective _)
      have weakenedType : Presentation.rename wk universeF.code = universeFG.code := by
        rw [universeF_code, universeFG_code]
        rfl
      have c₁ : strong.1.1.code = universeF.code := injective (w₁.trans weakenedType.symm)
      have c₂ : strong.1.2.code = .var 0 := injective (w₂.trans rfl)
      have c₃ : strong.2.1.code = universeF.code := injective (w₃.trans weakenedType.symm)
      have c₄ : strong.2.2.code = .var 1 := injective (w₄.trans rfl)
      show _ ∧ _
      refine ⟨?_, Nat.succ_pos _, nullary_newest_normal, ?_⟩
      · have base := nullary_in_fragment nullaryEquation (by rw [nullaryStore_eq]; exact List.mem_singleton_self _)
        unfold InFragment at base ⊢
        rw [c₁, c₂, c₃, c₄]
        exact base
      · refine inversionRow_nullary_views (S := setting) strong (Nat.succ_pos _) (c₂.trans rfl)
          (ContextualDependentDynamicFragment.normal_var rfl _)
          (by rw [c₄]; exact ContextualDependentDynamicFragment.normal_var rfl _) ?_ ?_
        · intro index member
          rw [c₄] at member
          rw [Finset.mem_singleton.mp member]
          exact Nat.one_pos
        · rw [c₁]
          change TypeEq setting.R withF.raw universeF.code (Presentation.rename wk universeHere.code)
          rw [universeF_code, universeHere_code]
          exact IsType.refl universe_isType

theorem placed_row : PlacedRow (fun _ => (0 : Nat)) (0 + 1) placedEquation := placed_row_at 0 rfl

/-- **The placed round is not stuck on `F ≐ A` below `G`** from some budget on, by the firing theorem in place. -/
theorem placed_fires :
    ∃ bound, ∀ larger, bound ≤ larger → placedTower.round larger placedStore ≠ .stuck :=
  placedRound_fires (fun _ => (0 : Nat)) ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique placedStore
    (by rw [placedStore_eq]; exact List.mem_singleton_self _) placed_row

/-- **The placed solver commits on `F ≐ A` below `G`** at budget 16. -/
theorem placed_committed : (run placedOnly placedStore 8).readout = .commit := by decide +kernel

/-- **The placed solver commits on the census control with an older metavariable.** -/
theorem olderInversion_placed_committed : (run placedOnly olderInversionStore 8).readout = .commit := by
  decide +kernel

end ContextualDependentPatternFiring.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
