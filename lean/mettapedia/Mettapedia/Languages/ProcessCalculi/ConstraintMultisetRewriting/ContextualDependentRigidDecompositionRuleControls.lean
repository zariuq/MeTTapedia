import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolverOccursControls

/-!
# Rigid–rigid decomposition on a concrete store

The metavariable is `F : (A : U0) (c : A → A) (x : A) → A`; the telescope is `A : U0, c : A → A, x : A`.

* `λ A c x. c (F A c x) ≐ λ A c x. c x` is decomposed at the rigid local `c`, at the rigid base type
  `A`, into `F A c x ≐ x`, which the pattern rule solves. The run commits with a principal answer.
* The full solver alone only suspends the same store: neither side is a pattern, the heads do not
  clash, and the sides are not convertible.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidDecomposition.RuleControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver.Controls ContextualDependentPatternSolver.OccursControls

/-- The decomposition solver in the cumulative tower, with the full solver's parameters. -/
def decomposeOnly : Solver setting.levels :=
  decomposeSolver (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.facts TowerModel.complete
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique 16

/-- `λ A c x. c (F A c x) ≐ λ A c x. c x`. -/
def decomposedStore := closeStore (selfScope.toScoped ⟨_, occurring, applied⟩)

theorem decomposed_store_length : decomposedStore.length = 1 := by decide +kernel

/-- **Decomposition solves the store**: the run commits. -/
theorem decomposed_solved : (run decomposeOnly decomposedStore 2).readout = .commit := by decide +kernel

theorem decomposed_principal :
    ∃ state finished, run decomposeOnly decomposedStore 2 = .solved state finished ∧
      (frames setting.levels).Principal decomposedStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit decomposed_solved
  exact ⟨state, finished, solved, drive_solved_principal decomposeOnly solved⟩

/-- The full solver alone only suspends it. -/
theorem decomposed_full_suspended : (run full decomposedStore 4).readout = .suspended := by decide +kernel

end ContextualDependentRigidDecomposition.RuleControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
