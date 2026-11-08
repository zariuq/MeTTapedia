import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFull
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentCompleteRecognitionControls

/-!
# The full occurs check on concrete stores

* **R94's gap is closed.** Over `A X : U0`, `X ≐ Π A X` is in the dynamic pattern fragment and the
  recognition solver leaves it suspended. It has no solution: `X` occurs in the codomain. The full
  occurs solver refutes it with a certificate.
* **Deeper codomains and carriers.** `X ≐ Σ A (Π A X)` (a codomain inside a codomain) is refuted, and
  over `X : U0, x : X`, so is `X ≐ Id X x x` (a carrier).
* **A flexible occurrence is not refused.** Over `A : U0, G : U0 → U0, X : U0`, `X ≐ Π (G X) A` is
  solvable; the full occurs rule does not fire on it and the run never refutes it.
* **The earlier witnesses keep their readouts.**

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentOccursFull.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentGeneralPattern

/-- The full occurs solver of the tower controls, as a fuel-indexed family. -/
abbrev occursFullTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  occursFullFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The full occurs solver at budget 16. -/
def occursFullOnly : Solver setting.levels := occursFullTower.solver 16

/-- The full occurs rule of the tower controls. -/
abbrev search {Θ : Context Tower.rules} (problem : EquationStore (TotalTerm Θ)) :=
  occursFullSearch (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete problem

/-! ## R94's gap: an occurrence in a codomain -/

/-- **The full occurs rule reads `X ≐ Π A X`.** -/
theorem codomain_read : (search ContextualDependentFragmentComplete.Controls.codomainStore).isSome = true := by
  decide +kernel

/-- **The full occurs solver refutes `X ≐ Π A X`**, which the recognition solver leaves suspended. -/
theorem codomain_refuted :
    (run occursFullOnly ContextualDependentFragmentComplete.Controls.codomainStore 2).readout = .refuted := by
  decide +kernel

/-- **`X ≐ Π A X` has no solution**: the refutation is certified. -/
theorem codomain_unsolvable :
    ¬ (frames setting.levels).Solvable ContextualDependentFragmentComplete.Controls.codomainStore :=
  drive_refuted occursFullOnly 2 _ codomain_refuted

/-- **So the fragment store `X ≐ Π A X` is decided, by a certified refutation.** -/
theorem codomain_in_fragment_refuted :
    ContextualDependentDynamicFragment.InFragmentStore ContextualDependentFragmentComplete.Controls.codomainStore ∧
      ¬ (frames setting.levels).Solvable ContextualDependentFragmentComplete.Controls.codomainStore :=
  ⟨ContextualDependentFragmentComplete.Controls.codomain_in_fragment, codomain_unsolvable⟩

/-! ## A codomain inside a codomain -/

theorem nestedCodomain_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.sigma (.var 1) (.pi (.var 2) (.var 2)))
    (.head (.sort Tower.zero))).isSome = true := by decide +kernel

/-- `X ≐ Σ A (Π A X)` over `A X : U0`. -/
def nestedCodomainStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨universeAt twoTypes, checkedType _ self_checked⟩, ⟨universeAt twoTypes, checkedType _ nestedCodomain_checked⟩)]

theorem nestedCodomain_refuted : (run occursFullOnly nestedCodomainStore 2).readout = .refuted := by
  decide +kernel

theorem nestedCodomain_unsolvable : ¬ (frames setting.levels).Solvable nestedCodomainStore :=
  drive_refuted occursFullOnly 2 _ nestedCodomain_refuted

/-! ## A carrier -/

/-- `X : U0, x : X`. -/
abbrev pointed := ContextualDependentInversion.Controls.small

/-- A type of `X x` at `U0`, checked by the executable checker. -/
def checkedPointed (code : Tower.Tm 2)
    (accepted : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer 16 pointed.raw code (.head (.sort Tower.zero))).isSome = true) :
    Term pointed (universeAt pointed) :=
  ⟨code, CheckingAlgorithm.sound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed
    ((ExecutableChecking.check setting.R ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer
      16 pointed.raw code (.head (.sort Tower.zero))).get accepted).down pointed.formed (universeAt pointed).isType⟩

theorem pointedSelf_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 pointed.raw (.var 1) (.head (.sort Tower.zero))).isSome = true := by
  decide +kernel

theorem carrier_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 pointed.raw (.id (.var 1) (.var 0) (.var 0))
    (.head (.sort Tower.zero))).isSome = true := by decide +kernel

/-- `X ≐ Id X x x` over `X : U0, x : X`. -/
def carrierStore : EquationStore (TotalTerm pointed) :=
  [(⟨universeAt pointed, checkedPointed _ pointedSelf_checked⟩, ⟨universeAt pointed, checkedPointed _ carrier_checked⟩)]

theorem carrier_refuted : (run occursFullOnly carrierStore 2).readout = .refuted := by decide +kernel

theorem carrier_unsolvable : ¬ (frames setting.levels).Solvable carrierStore :=
  drive_refuted occursFullOnly 2 _ carrier_refuted

/-! ## A flexible occurrence -/

/-- **The full occurs rule does not fire on `X ≐ Π (G X) A`.** -/
theorem flexible_not_refused : (search flexibleStore).isNone = true := by decide +kernel

/-- **And the full occurs solver does not refute it.** -/
theorem flexible_run_not_refuted : (run occursFullOnly flexibleStore 4).readout ≠ .refuted := by decide +kernel

/-! ## The earlier witnesses -/

theorem id_refuted : (run occursFullOnly idStore 2).readout = .refuted := by decide +kernel

theorem blocked_solved : (run occursFullOnly blockedStore 2).readout = .commit := by decide +kernel

theorem pi_solved : (run occursFullOnly piStore 2).readout = .commit := by decide +kernel

theorem crossed_solved : (run occursFullOnly crossedStore 2).readout = .commit := by decide +kernel

theorem domain_refuted : (run occursFullOnly domainStore 2).readout = .refuted := by decide +kernel

theorem repeated_suspended : (run occursFullOnly repeatedStore 4).readout = .suspended := by decide +kernel

end ContextualDependentOccursFull.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
