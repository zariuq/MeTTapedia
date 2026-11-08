import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringPi
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentFiringForeignControls

/-!
# The Π solver on a Π-former store and on the earlier witnesses

* **Π decomposition solves.** Over `A X : U0`, the store `Π A X ≐ Π A A` is in the dynamic pattern
  fragment. The fragment solver and the identity solver leave it suspended; the Π solver decomposes
  it to `X ≐ A` under a local of type `A`, solves `X := A`, and commits with a principal answer.
* **Σ types too.** `Σ A X ≐ Σ A A` commits the same way, and the identity solver leaves it suspended.
* **Nothing else changes.** On R86's pruning store and crossed store the Π solver still commits; on
  the identity witness it still refutes; R77's non-pattern store and the solving-in-place witness
  stay suspended.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDynamicFragment ContextualDependentDecisiveFragment

/-- The Π solver in the tower at budget 16. -/
def piOnly : Solver setting.levels :=
  piSolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16

/-! ## The store -/

theorem constant_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.pi (.var 1) (.var 2))).isSome := by decide +kernel

/-- `(x : A) → A` over `A X : U0`. -/
def constantType : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.pi (.var 1) (.var 2))).get constant_formed).val

theorem function_levels : constantType.level = familyType.level := by decide +kernel

theorem functionUniverse_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.head familyType.level)).isSome := by decide +kernel

/-- The universe of both function types. -/
def functionUniverse : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.head familyType.level)).get functionUniverse_formed).val

theorem functionUniverse_code : functionUniverse.code = .head familyType.level :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.head familyType.level)).get
      functionUniverse_formed).property

/-- `Π A X`. -/
def towardX : Term twoTypes functionUniverse :=
  ⟨familyType.code, by rw [functionUniverse_code]; exact familyType.formed⟩

/-- `Π A A`. -/
def towardA : Term twoTypes functionUniverse :=
  ⟨constantType.code, by rw [functionUniverse_code, ← function_levels]; exact constantType.formed⟩

/-- `Π A X ≐ Π A A` over `A X : U0`. -/
def piStore : EquationStore (TotalTerm twoTypes) :=
  closeStore ((Spine.stop functionUniverse).toScoped ⟨functionUniverse, towardX, towardA⟩)

theorem piStore_length : piStore.length = 1 := by decide +kernel

def piEquation : Equation (TotalTerm twoTypes) :=
  piStore.head (List.ne_nil_of_length_pos (by rw [piStore_length]; decide))

theorem piStore_eq : piStore = [piEquation] :=
  ContextualDependentDynamicFragment.Controls.singleton_of_length piStore piStore_length

/-- **`Π A X ≐ Π A A` is in the dynamic pattern fragment.** -/
theorem pi_in_fragment : InFragmentStore piStore := by
  rw [piStore_eq]
  intro equation member
  rw [List.mem_singleton.mp member]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have same : piEquation.2.1.code = piEquation.1.1.code := by decide +kernel
    rw [same]
    exact IsType.refl piEquation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-! ## Runs -/

/-- **The fragment solver leaves it suspended.** -/
theorem pi_fragment_suspended : (run fragmentOnly piStore 4).readout = .suspended := by decide +kernel

/-- **The identity solver leaves it suspended.** -/
theorem pi_identity_suspended : (run identityOnly piStore 4).readout = .suspended := by decide +kernel

/-- **The Π solver commits on it**, with a principal answer. -/
theorem pi_solved : (run piOnly piStore 2).readout = .commit := by decide +kernel

theorem pi_principal :
    ∃ state finished, run piOnly piStore 2 = .solved state finished ∧
      (frames setting.levels).Principal piStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit pi_solved
  exact ⟨state, finished, solved, drive_solved_principal piOnly solved⟩

/-! ## Dependent pair types -/

theorem pairX_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.sigma (.var 1) (.var 1))).isSome := by decide +kernel

theorem pairA_formed : (ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer 16 twoTypes
    (.sigma (.var 1) (.var 2))).isSome := by decide +kernel

/-- `Σ A X` over `A X : U0`. -/
def pairXType : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.sigma (.var 1) (.var 1))).get pairX_formed).val

/-- `Σ A A` over `A X : U0`. -/
def pairAType : TypeOver twoTypes :=
  ((ContextualDependentPruning.formType (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes (.sigma (.var 1) (.var 2))).get pairA_formed).val

theorem pairX_level : pairXType.level = familyType.level := by decide +kernel
theorem pairA_level : pairAType.level = familyType.level := by decide +kernel

/-- `Σ A X ≐ Σ A A` over `A X : U0`. -/
def sigmaStore : EquationStore (TotalTerm twoTypes) :=
  closeStore ((Spine.stop functionUniverse).toScoped ⟨functionUniverse,
    ⟨pairXType.code, by rw [functionUniverse_code, ← pairX_level]; exact pairXType.formed⟩,
    ⟨pairAType.code, by rw [functionUniverse_code, ← pairA_level]; exact pairAType.formed⟩⟩)

/-- **The Π solver decomposes Σ types too**: `Σ A X ≐ Σ A A` commits with `X := A`; the identity
solver leaves it suspended. -/
theorem sigma_solved : (run piOnly sigmaStore 2).readout = .commit := by decide +kernel

theorem sigma_identity_suspended : (run identityOnly sigmaStore 4).readout = .suspended := by decide +kernel

/-! ## No regression on the earlier stores -/

theorem flexFlex_pi_solved : (run piOnly flexFlexStore 2).readout = .commit := by decide +kernel

theorem crossed_pi_solved : (run piOnly crossedStore 2).readout = .commit := by decide +kernel

theorem id_pi_refuted : (run piOnly idStore 2).readout = .refuted := by decide +kernel

theorem repeated_pi_suspended : (run piOnly repeatedStore 4).readout = .suspended := by decide +kernel

theorem blocked_pi_suspended : (run piOnly blockedStore 4).readout = .suspended := by decide +kernel

/-! ## The solving-in-place witness stays undecided -/

/-- **The binder decomposition never fires on a lone foreign equation whose left side is not a
binder type.** -/
theorem piDecomposeSearch_foreign (fuel : Nat) {Θ : Context setting.R} (equation : Equation (TotalTerm Θ))
    (foreign : ForeignEquation (S := setting) (fun _ => none) equation)
    (notBinder : ∀ A B, equation.1.2.code ≠ .pi A B ∧ equation.1.2.code ≠ .sigma A B) :
    piDecomposeSearch (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel [equation] = none := by
  have single : piDecomposeEquation (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel equation [] = none := by
    unfold piDecomposeEquation
    split
    · rfl
    · rename_i scope active view read
      obtain ⟨same, leftIs, _⟩ := foreign_reading (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
        TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
        ContextualDependentInversion.Controls.reducer (fun _ => none) fuel equation foreign read
      change scope = Spine.stop equation.1.1 at same
      subst same
      change active.left.code = equation.1.2.code at leftIs
      have none : binderDecomposeActive (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
          TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
          ContextualDependentInversion.Controls.reducer TowerModel.complete fuel (Spine.stop equation.1.1) active =
            none := by
        have piNone : piDecomposeActive (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
            TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
            ContextualDependentInversion.Controls.reducer TowerModel.complete fuel (Spine.stop equation.1.1) active =
              none := by
          unfold piDecomposeActive
          split
          · rename_i A B A' B' u leftCode rightCode typeCode
            rw [leftIs] at leftCode
            exact absurd leftCode (notBinder _ _).1
          · rfl
        have sigmaNone : sigmaDecomposeActive (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
            TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
            ContextualDependentInversion.Controls.reducer TowerModel.complete fuel (Spine.stop equation.1.1) active =
              none := by
          unfold sigmaDecomposeActive
          split
          · rename_i A B A' B' u leftCode rightCode typeCode
            rw [leftIs] at leftCode
            exact absurd leftCode (notBinder _ _).2
          · rfl
        unfold binderDecomposeActive
        rw [piNone, sigmaNone]
        rfl
      rw [none]
  simp only [piDecomposeSearch, single]
  rfl

/-- The Π family in the tower. -/
abbrev piTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  piFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- **The Π round is stuck on the solving-in-place witness at every budget.** -/
theorem blocked_piRound_stuck (fuel : Nat) :
    piRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) fuel blockedStore = .stuck := by
  have searched : piDecomposeSearch (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel
      (ContextualDependentNormalizing.prepare (S := setting) (fun _ => none)
        (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
        TowerModel.heads fuel blockedStore).remaining = none := by
    rw [prepare_stopped (S := setting) (fun _ => none)
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
      TowerModel.heads fuel blockedStore blocked_context_stopped blocked_codes_stopped]
    change piDecomposeSearch (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal fuel blockedStore = none
    rw [blockedStore_eq]
    exact piDecomposeSearch_foreign fuel blockedEquation blocked_foreign
      (fun A B => ⟨(fun same => by rw [blocked_left] at same; cases same),
        (fun same => by rw [blocked_left] at same; cases same)⟩)
  unfold piRound
  split
  · rename_i update smaller found
    rw [searched] at found
    cases found
  · rename_i absent found
    rw [searched] at found
    cases found
  · exact blocked_identityRound_stuck fuel

/-- **The solving-in-place witness is never decided by the Π family either.** -/
theorem blocked_pi_never_decided (fuel rounds : Nat) : ¬ (run (piTower.solver fuel) blockedStore rounds).Decided :=
  never_decided_of_stuck _ blockedStore_nonempty (blocked_piRound_stuck fuel) rounds

end ContextualDependentFragment.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
