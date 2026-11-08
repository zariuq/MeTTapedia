import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentDecidedIdentity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNonPatternPending

/-!
# The identity solver on the fragment's witnesses

* **The repaired witness.** `λ a b. Id T a b ≐ λ a b. Id T b a`, which no earlier solver decides at
  any budget, is refuted by the identity solver: the endpoints `a ≐ b` are distinct rigid locals.
* **Nothing else changes.** R86's pruning store `G y z ≐ F x y` still commits, and R77's non-pattern
  store `F x x ≐ Id T y x` still stays suspended: its left side is not an identity type.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentPiSpine ContextualDependentScope
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls

/-- The identity solver in the tower at budget 16. -/
def identityOnly : Solver setting.levels :=
  identitySolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16

/-- **The identity solver refutes `λ a b. Id T a b ≐ λ a b. Id T b a`.** -/
theorem id_identity_refuted : (run identityOnly idStore 2).readout = .refuted := by decide +kernel

/-- The refutation is certified: it carries the absence of solutions. -/
theorem id_identity_unsolvable : ¬ (frames setting.levels).Solvable idStore :=
  drive_refuted identityOnly 2 _ id_identity_refuted

/-- **R86's pruning store still commits.** -/
theorem flexFlex_identity_solved :
    (run identityOnly ContextualDependentPatternSolver.Controls.flexFlexStore 2).readout = .commit := by
  decide +kernel

/-- **The crossed pattern `F y x ≐ Id T x y` still commits.** -/
theorem crossed_identity_solved : (run identityOnly crossedStore 2).readout = .commit := by decide +kernel

/-- **R77's non-pattern store stays suspended.** -/
theorem repeated_identity_suspended : (run identityOnly repeatedStore 4).readout = .suspended := by decide +kernel

/-! ## Decided at one joint budget -/

/-- The identity family in the tower. -/
abbrev identityTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  identityFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- At budget 16 the identity refutation needs no more budget. -/
theorem id_identity_firm : identityFirm (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) 16 idEquation [] = true := by decide +kernel

/-- **The identity family decides `λ a b. Id T a b ≐ λ a b. Id T b a` at one joint budget**: from
one budget on, used for the executables and the rounds, it refutes the store with a certificate,
the same at every larger budget. -/
theorem id_identity_decided :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (identityTower.solver larger) idStore larger = run (identityTower.solver budget) idStore budget ∧
      ((∃ state finished, run (identityTower.solver larger) idStore larger = .solved state finished ∧
          (frames setting.levels).Principal idStore state.answer) ∨
        (∃ absent, run (identityTower.solver larger) idStore larger = .refuted absent)) := by
  exact (identitySettled (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique ContextualDependentDecisiveFragment.Controls.stable
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) idEquation types_stopped
    (fun other member => idStore_stopped other (by rw [idStore_eq]; exact member)) id_identity_firm).decided
    (show ∃ same : ContextualDependentGeneralPattern.Controls.types = ContextualDependentGeneralPattern.Controls.types,
      same ▸ idStore = [idEquation] from ⟨rfl, idStore_eq⟩)

end ContextualDependentFragment.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
