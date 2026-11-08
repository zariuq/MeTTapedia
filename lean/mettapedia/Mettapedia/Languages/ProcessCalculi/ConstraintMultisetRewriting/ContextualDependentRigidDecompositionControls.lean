import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecomposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolverControls

/-!
# Distinct rigid locals on a concrete store

Over `T : U0, F : (a b : T) → U0`, under the telescope `x y : T`:

* `λ x y. x ≐ λ x y. y` is refuted by the rigid round, with a certificate valid in every future
  context. The full solver alone only suspends it: no clash, conversion, pattern, prune or
  exchange rule applies.
* `λ x y. x ≐ λ x y. x` is not refuted; it is discharged by conversion and the run commits.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidDecomposition.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver.Controls

/-- The rigid solver in the cumulative tower, with the full solver's parameters. -/
def rigidOnly : Solver setting.levels :=
  rigidSolver (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique 16

/-- `T` in the telescope `T, F, x, y`. -/
def carrier : TypeOver scope.target := ⟨(.var 3 : Tower.Tm 4), .sort Tower.zero, .sort _, .var (3 : Fin 4)⟩

/-- The local `x`. -/
def firstLocal : Term scope.target carrier := ⟨(.var 1 : Tower.Tm 4), .var (1 : Fin 4)⟩

/-- The local `y`. -/
def secondLocal : Term scope.target carrier := ⟨(.var 0 : Tower.Tm 4), .var (0 : Fin 4)⟩

/-- `λ x y. x ≐ λ x y. y`. -/
def distinctStore := closeStore (scope.toScoped ⟨carrier, firstLocal, secondLocal⟩)

/-- `λ x y. x ≐ λ x y. x`. -/
def sameStore := closeStore (scope.toScoped ⟨carrier, firstLocal, firstLocal⟩)

theorem distinct_store_length : distinctStore.length = 1 := by decide +kernel

theorem distinct_refuted : (run rigidOnly distinctStore 1).readout = .refuted := by decide +kernel

theorem distinct_full_suspended : (run full distinctStore 4).readout = .suspended := by decide +kernel

theorem distinct_unsolvable : ¬ (frames setting.levels).Solvable distinctStore :=
  drive_refuted rigidOnly 1 _ distinct_refuted

theorem same_store_length : sameStore.length = 1 := by decide +kernel

theorem same_committed : (run rigidOnly sameStore 2).readout = .commit := by decide +kernel

theorem same_not_refuted (rounds : Nat) : (run rigidOnly sameStore rounds).readout ≠ .refuted := by
  intro refuted
  have absent := drive_refuted rigidOnly rounds _ refuted
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit same_committed
  exact absent ⟨_, state.answer, (drive_solved_principal rigidOnly solved).1⟩

end ContextualDependentRigidDecomposition.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
