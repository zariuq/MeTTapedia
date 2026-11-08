import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneSolveRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionControls

/-!
# Controls for the prune-and-solve round

Over `A : U0, G : U0 → U0 → U0, F : U0 → U0`, at `U0 → U0 → U0`, budget 16 and eight rounds:

| Store | Intersection solver | Prune-and-solve solver |
|---|---|---|
| `λ x y. F x ≐ λ x y. Π A (G x y)` (R107's `prunableStore`) | stuck | commit |
| `λ x y. F x ≐ λ x y. Σ A (G x y)` | stuck | commit |
| `λ x y. F x ≐ λ x y. Π A (Π A (G x y))` | stuck | commit |
| `λ x y. F x ≐ λ x y. Π (G x y) A` | stuck | commit |
| the Π and Σ equations together | stuck | refuted |

The first store is in the fragment and solvable (R107's `prunable_in_fragment`, `prunable_solvable`). In the last, the
rule prunes `G` to `H` over `x` and solves `F`; the other equation becomes `Π A (H x) ≐ Σ A (H x)`, a clash of formers,
so the store has no solution, certified by the refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPruneSolve.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersection.Controls

/-- The prune-and-solve solver of the tower controls, as a fuel-indexed family. -/
noncomputable def pruneSolveTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  pruneSolveFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The prune-and-solve solver at budget 16. -/
noncomputable def pruneSolveOnly : Solver setting.levels := pruneSolveTower.solver 16

/-! ## Pruning under a function type -/

theorem prunable_intersect_stuck : isStuck (run intersectOnly prunableStore 8) = true := by decide +kernel

/-- **The prune-and-solve solver commits on `λ x y. F x ≐ λ x y. Π A (G x y)`.** -/
theorem prunable_committed : (run pruneSolveOnly prunableStore 8).readout = .commit := by decide +kernel

/-- **The prune-and-solve rule fires on the store**, at budget 16. -/
theorem prunable_rule_fires :
    (pruneSolveRule (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique 16 prunableStore).isSome := by decide +kernel

/-- **The prune-and-solve round is not stuck on the store**, by the general lemma. -/
theorem prunable_round_not_stuck :
    pruneSolveRound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) 16 prunableStore ≠ .stuck :=
  pruneSolveRound_not_stuck_of_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ 16 prunable_rule_fires

/-! ## Pruning under a dependent pair type -/

/-- `λ x y. F x ≐ λ x y. Σ A (G x y)`. -/
def sigmaStore : EquationStore (TotalTerm withPrunable) :=
  [(termIn withPrunable twoLocalsPrunable (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withPrunable twoLocalsPrunable (.lam (.lam (.sigma (.var 4) (.app (.app (.var 4) (.var 2)) (.var 1)))))
      (by decide +kernel))]

theorem sigma_intersect_stuck : isStuck (run intersectOnly sigmaStore 8) = true := by decide +kernel

/-- **The prune-and-solve solver commits on `λ x y. F x ≐ λ x y. Σ A (G x y)`.** -/
theorem sigma_committed : (run pruneSolveOnly sigmaStore 8).readout = .commit := by decide +kernel

/-! ## Pruning in nested codomains and in a domain -/

/-- `λ x y. F x ≐ λ x y. Π A (Π A (G x y))`. -/
def nestedStore : EquationStore (TotalTerm withPrunable) :=
  [(termIn withPrunable twoLocalsPrunable (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withPrunable twoLocalsPrunable
      (.lam (.lam (.pi (.var 4) (.pi (.var 5) (.app (.app (.var 5) (.var 3)) (.var 2)))))) (by decide +kernel))]

theorem nested_intersect_stuck : isStuck (run intersectOnly nestedStore 8) = true := by decide +kernel

/-- **The prune-and-solve solver commits on a pattern in nested codomains.** -/
theorem nested_committed : (run pruneSolveOnly nestedStore 8).readout = .commit := by decide +kernel

/-- `λ x y. F x ≐ λ x y. Π (G x y) A`. -/
def domainStore : EquationStore (TotalTerm withPrunable) :=
  [(termIn withPrunable twoLocalsPrunable (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withPrunable twoLocalsPrunable (.lam (.lam (.pi (.app (.app (.var 3) (.var 1)) (.var 0)) (.var 5))))
      (by decide +kernel))]

theorem domain_intersect_stuck : isStuck (run intersectOnly domainStore 8) = true := by decide +kernel

/-- **The prune-and-solve solver commits on a pattern in a domain.** -/
theorem domain_committed : (run pruneSolveOnly domainStore 8).readout = .commit := by decide +kernel

/-! ## A refutation after pruning -/

/-- `λ x y. F x ≐ λ x y. Π A (G x y)` and `λ x y. F x ≐ λ x y. Σ A (G x y)`. -/
def clashStore : EquationStore (TotalTerm withPrunable) :=
  [(termIn withPrunable twoLocalsPrunable (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withPrunable twoLocalsPrunable (.lam (.lam (.pi (.var 4) (.app (.app (.var 4) (.var 2)) (.var 1)))))
      (by decide +kernel)),
   (termIn withPrunable twoLocalsPrunable (.lam (.lam (.app (.var 2) (.var 1)))) (by decide +kernel),
    termIn withPrunable twoLocalsPrunable (.lam (.lam (.sigma (.var 4) (.app (.app (.var 4) (.var 2)) (.var 1)))))
      (by decide +kernel))]

theorem clash_intersect_stuck : isStuck (run intersectOnly clashStore 8) = true := by decide +kernel

/-- **The prune-and-solve solver refutes it.** -/
theorem clash_refuted : (run pruneSolveOnly clashStore 8).readout = .refuted := by decide +kernel

theorem clash_unsolvable : ¬ (frames setting.levels).Solvable clashStore :=
  Outcome.readout_eq_refuted clash_refuted

end ContextualDependentPruneSolve.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
