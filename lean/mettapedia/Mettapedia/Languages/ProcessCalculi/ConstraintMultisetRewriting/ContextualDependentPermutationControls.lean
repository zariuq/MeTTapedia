import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPermutation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecompositionControls

/-!
# Reaching a metavariable below the two newest declarations

Over `T : U0, F : (a b : T) → U0, G : U0, H : U0`, the only equation is the crossed pattern
`λ x y. F y x ≐ λ x y. Id T x y` for `F`, two declarations below the newest. `G` and `H` do not
mention `F`.

* The rigid solver and the full solver only suspend the store: the pattern rule sees `H`, and
  adjacent exchange reaches `G`, never `F`.
* The permuting solver rotates `F` to the newest position, past `G` and `H`, along a checked
  renaming isomorphism, and the pattern rule solves it: the run commits with a principal answer.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPermutation.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentRigidDecomposition.Controls

/-- The permuting solver in the cumulative tower, with the rigid solver's parameters. -/
def permutingOnly : Solver setting.levels :=
  permutingSolver (S := setting) ContextualDependentPiSpine.Controls.rigid TowerModel.complete TowerModel.facts
    TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed
    ExecutableTowerChoices.choices ContextualDependentInversion.Controls.reducer (fun _ => none)
    DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique 16

/-- `T : U0, F : (a b : T) → U0`. -/
abbrev outer := extend types outerWhole

/-- `G : U0`. -/
def gType : TypeOver outer := universeAt outer

abbrev withG := extend outer gType

/-- `H : U0`. -/
def hType : TypeOver withG := universeAt withG

abbrev withGH := extend withG hType

/-- The crossed pattern for `F`, weakened past `G` and `H`. -/
def deepStore : EquationStore (TotalTerm withGH) :=
  (frames setting.levels).applyStore (projectionHom withG hType)
    ((frames setting.levels).applyStore (projectionHom outer gType) crossedStore)

theorem deep_store_length : deepStore.length = 1 := by decide +kernel

/-- **The rigid solver only suspends the store.** -/
theorem deep_rigid_suspended : (run rigidOnly deepStore 4).readout = .suspended := by decide +kernel

/-- **The full solver only suspends the store.** -/
theorem deep_full_suspended : (run full deepStore 4).readout = .suspended := by decide +kernel

/-- **The permuting solver commits on it.** -/
theorem deep_permuting_solved : (run permutingOnly deepStore 2).readout = .commit := by decide +kernel

theorem deep_permuting_principal :
    ∃ state finished, run permutingOnly deepStore 2 = .solved state finished ∧
      (frames setting.levels).Principal deepStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit deep_permuting_solved
  exact ⟨state, finished, solved, drive_solved_principal permutingOnly solved⟩

/-- The rotation itself: `F` moves to the newest position past `G` and `H`. -/
theorem deep_rotation :
    rotateRaw withGH.raw 2 = some (.snoc (.snoc (.snoc (.snoc .nil (.head (.sort Tower.zero))) (.head (.sort Tower.zero)))
      (.head (.sort Tower.zero))) (Presentation.rename wk (Presentation.rename wk outerWhole.code))) := by
  decide +kernel

end ContextualDependentPermutation.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
