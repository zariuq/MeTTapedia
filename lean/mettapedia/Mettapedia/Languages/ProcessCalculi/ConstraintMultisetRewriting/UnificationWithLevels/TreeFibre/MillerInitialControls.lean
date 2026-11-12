import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerRunInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbRoundControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrimmingControls

/-!
# Controls: initial solutions of Miller stores, pruning in place included

In the tree's tower, with the solver without the chain (`millerGlbTower`).

* **Both sides pruned in place** (`both_initialGlb`): `λ x y z. F x y ≐ λ x y z. G y z`. The fixed-support trimming
  theorem does not apply to this answer (`both_not_fixedSupport`, U5): the pruned unknowns are declared again and
  mention themselves. The pattern trimming theorem does: the store has an initial solution.
* **Incomparable codomains** (`levelPerm_initialGlb`, `pruneGlb_initialGlb`): the permutation with incomparable
  codomains, and the store that is pruned and then lowered, have initial solutions.
* **The Miller fragment** (`perm_initialGlb`): the permutation over one universe, as before.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- **A store of the fragment on which the solver commits has an initial solution.** -/
theorem initial_of_commitGlb {Θ : Context setting.R} {original : EquationStore (TotalTerm Θ)} {fuel : Nat}
    (inside : InMillerGlb (S := setting) original)
    (committed : (run millerGlbTower original fuel).readout = .commit) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), InitialSolution (frames setting.levels) original answer := by
  cases outcome : run millerGlbTower original fuel with
  | solved state finished =>
      exact millerGlb_solved_initial TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
        ContextualDependentPiSpine.Controls.rigid TowerModel.complete
        ContextualDependentGeneralPattern.DispatchControls.tower_normalizes towerInh
        ContextualDependentNormalCheckingTower.head_typing_unique LevelGlb.towerGlb LevelGlb.towerGlb_isGlb inside
        outcome
  | stuck _ => rw [outcome] at committed; cases committed
  | refuted _ => rw [outcome] at committed; cases committed
  | cutoff _ => rw [outcome] at committed; cases committed

/-! ## Both sides pruned in place -/

theorem both_insideGlb : InMillerGlb (S := setting) bothStore := inMillerGlb_of_inMiller both_inside

theorem both_committedGlb : (run millerGlbTower bothStore 5).readout = .commit := by decide +kernel

/-- **The fixed-support trimming theorem does not apply to the Miller solver's answer on this store.** -/
theorem both_fixedSupport_fails : ¬ ∀ (i : Fin ctxBB.arity) (j : Fin TreeFibre.Controls.bothState.target.arity),
    j ∈ (TreeFibre.Controls.bothState.answer.substitution i).support →
      TreeFibre.Controls.bothState.answer.substitution (Fin.cast TreeFibre.Controls.both_same j) = .var j :=
  TreeFibre.Controls.both_not_fixedSupport

/-- **The pattern trimming theorem does: the store has an initial solution.** -/
theorem both_initialGlb :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxBB), InitialSolution (frames setting.levels) bothStore answer :=
  initial_of_commitGlb both_insideGlb both_committedGlb

/-! ## Incomparable codomains -/

theorem levelPerm_initialGlb :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAB2), InitialSolution (frames setting.levels) levelPermStore answer :=
  initial_of_commitGlb levelPerm_insideGlb levelPerm_committedGlb

theorem pruneGlb_initialGlb :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxAB1), InitialSolution (frames setting.levels) pruneGlbStore answer :=
  initial_of_commitGlb pruneGlb_insideGlb pruneGlb_committed

/-! ## The Miller fragment -/

theorem perm_initialGlb :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ ctxBB), InitialSolution (frames setting.levels) permStore answer :=
  initial_of_commitGlb perm_insideGlb perm_committedGlb

end Controls

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
