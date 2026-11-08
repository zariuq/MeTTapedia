import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRankRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursFullControls

/-!
# The ranked solver on concrete stores

* **Decomposition commits on its own.** Over `A X : U0`, `Π X A ≐ Π (Π A X) A` has no solution: its
  domains would give `X ≐ Π A X`. R94's decomposition commits only if the clash test, the pattern,
  prune and exchange rules or the in-place rule decide the pieces, and none of them reads
  `X ≐ Π A X`; so the full occurs solver leaves the store suspended. The ranked solver commits the
  decomposition, which lowers the normal weight, and the full occurs rule refutes the pieces in the
  next round.
* **The earlier witnesses keep their readouts.**

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRank.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls
open ContextualDependentFragment ContextualDependentGeneralPattern

/-- The ranked solver of the tower controls, as a fuel-indexed family. -/
noncomputable def rankedTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  rankedFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none) DispatchControls.tower_normalizes
    DispatchControls.certifyNormal ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The ranked solver at budget 16. -/
noncomputable def rankedOnly : Solver setting.levels := rankedTower.solver 16

/-! ## Decomposition commits on its own -/

/-- `Π X A ≐ Π (Π A X) A` over `A X : U0`. -/
def crossedDomainsStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨universeAt twoTypes, checkedType _ domain_checked⟩,
    ⟨universeAt twoTypes, checkedType _ ContextualDependentRigidFormers.DeepControls.twisted_checked⟩)]

/-- **The full occurs solver leaves it suspended**: no rule after its decomposition decides. -/
theorem crossedDomains_occursFull_suspended :
    (run ContextualDependentOccursFull.Controls.occursFullOnly crossedDomainsStore 4).readout = .suspended := by
  decide +kernel

/-- **The ranked solver's first round commits the decomposition.** -/
theorem crossedDomains_ranked_progress :
    (roundView (rankedTower.round 16 crossedDomainsStore)).isSome = true := by
  decide +kernel

/-- **The ranked solver refutes it**, in the round after the decomposition. -/
theorem crossedDomains_ranked_refuted : (run rankedOnly crossedDomainsStore 3).readout = .refuted := by
  decide +kernel

/-- **`Π X A ≐ Π (Π A X) A` has no solution**: the refutation is certified. -/
theorem crossedDomains_unsolvable : ¬ (frames setting.levels).Solvable crossedDomainsStore :=
  drive_refuted rankedOnly 3 _ crossedDomains_ranked_refuted

/-! ## The earlier witnesses -/

theorem codomain_refuted :
    (run rankedOnly ContextualDependentFragmentComplete.Controls.codomainStore 2).readout = .refuted := by
  decide +kernel

theorem id_refuted : (run rankedOnly idStore 2).readout = .refuted := by decide +kernel

theorem blocked_solved : (run rankedOnly blockedStore 2).readout = .commit := by decide +kernel

theorem blocked_principal :
    ∃ state finished, run rankedOnly blockedStore 2 = .solved state finished ∧
      (frames setting.levels).Principal blockedStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit blocked_solved
  exact ⟨state, finished, solved, drive_solved_principal rankedOnly solved⟩

theorem pi_solved : (run rankedOnly piStore 2).readout = .commit := by decide +kernel

theorem crossed_solved : (run rankedOnly crossedStore 2).readout = .commit := by decide +kernel

theorem flexible_run_not_refuted : (run rankedOnly flexibleStore 4).readout ≠ .refuted := by decide +kernel

theorem repeated_suspended : (run rankedOnly repeatedStore 4).readout = .suspended := by decide +kernel

end ContextualDependentRank.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
