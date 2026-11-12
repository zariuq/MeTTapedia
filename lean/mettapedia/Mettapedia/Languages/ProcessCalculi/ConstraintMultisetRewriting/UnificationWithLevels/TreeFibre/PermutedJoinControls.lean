import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PermutedJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.WideMixControls

/-!
# Controls: the glb join under a permutation, in one rank

Every run is driven by the common rank, evaluated by the kernel.

* **Two unknowns with wider domains each, related by a permutation** (`crossedWideStore` of `WideMixControls`), where
  every earlier solver of the tree is stuck: the solver with the permuted join commits (`crossedWide_committed`), with a
  principal answer (`crossedWide_principal`): `G` is declared again with its arguments swapped, then joined with `F`.
* **Everything the mixed wide solver decides, it decides**: the crossed mix, the obstruction store, the residual of a
  join, a Miller permutation, a store pruned on both sides, the glb group with level variables (`earlier_committed`).
* **Negative control**: the cross store, solvable and without a principal answer, is not committed (`cross_stuck`); no
  solver can commit it, since a committed run carries a principal answer (`cross_no_commit`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace PermutedControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses
open TreeFibre.AuditControls (principal_of_rankCommit)

/-- **The solver with the glb join under a permutation**, at the tower's facts. -/
def towerMixPerm : ContextualDependentWorklist.Solver setting.levels :=
  Miller.mixPermSolver (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes Miller.Controls.towerInh
    ContextualDependentNormalCheckingTower.head_typing_unique Controls.towerJoin Controls.towerJoin_sound
    LevelGlb.towerGlb (fun found => LevelGlb.towerGlb_isGlb found)

/-- **The crossed permutation of two wide unknowns commits.** -/
theorem crossedWide_committed : (runRank towerMixPerm WideControls.crossedWideStore).readout = .commit := by
  decide +kernel

theorem crossedWide_principal :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ WideControls.ctxCw),
      (frames setting.levels).Principal WideControls.crossedWideStore answer :=
  principal_of_rankCommit crossedWide_committed

/-- **The stores the mixed wide solver decides, it decides.** -/
theorem earlier_committed : (runRank towerMixPerm AuditControls.cxStore).readout = .commit ∧
    (runRank towerMixPerm Controls.mjStore).readout = .commit ∧
    (runRank towerMixPerm WideControls.residualStore).readout = .commit ∧
    (runRank towerMixPerm Miller.Controls.permStore).readout = .commit ∧
    (runRank towerMixPerm Miller.Controls.bothStore).readout = .commit ∧
    (runRank towerMixPerm Controls.levelStore).readout = .commit := by decide +kernel

/-- **The cross store is not committed.** -/
theorem cross_stuck : (runRank towerMixPerm crossStore).readout = .suspended := by decide +kernel

/-- **No run commits the cross store**: a committed run carries a principal answer, and it has none. -/
theorem cross_no_commit (solver : ContextualDependentWorklist.Solver setting.levels) :
    (runRank solver crossStore).readout ≠ .commit := by
  intro committed
  obtain ⟨_, answer, principal⟩ := principal_of_rankCommit committed
  exact fragment_without_principal_answer.2.2 answer principal

end PermutedControls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
