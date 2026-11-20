import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.RankRuns

/-!
# The unifier's rank: the round count is the least sufficient budget

For every solver of the tree's worklist driver, a run with a budget of rounds finishes exactly when the
budget is at least the run's own number of rounds (`drive_finished_iff`), counted by well-founded
recursion on the solver's rank (`TreeFibre.roundsWF`). So "the run with budget `n` finishes" is a
certificate relation for "the run finishes" whose **least certificate is a function of the instance
that the tree defines** (`roundsWF_least`), and every instance is certified (`every_run_finishes`, as
the tree's `ContextualDependentWorklist.drive_finishes`). This is
the unifier's region in the sense of `Regions.Bounds`: bounded by a function of the instance, which the
tree proves sufficient (`TreeFibre.drive_eq_driveWF_of_rounds`) and, here, least. The function is
defined by well-founded recursion and not proved computable in Mathlib's sense; the run itself is
computed with no budget by structural recursion on the rank (`TreeFibre.driveRank`).

Control: budget `0` never finishes (`drive_zero_not_finished`), since every run takes a round.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeUnifier

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open UnificationWithLevels.TreeFibre

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
variable (solver : ContextualDependentWorklist.Solver levels) {Γ : Context rules}
  {original : EquationStore (TotalTerm Γ)}

/-- **A run finishes exactly when its budget is at least its number of rounds.** -/
theorem drive_finished_iff (state : Update levels original) :
    ∀ fuel, (drive solver fuel state).Finished ↔ roundsWF solver state ≤ fuel := by
  refine (InvImage.wf (fun state : Update levels original => solver.rank state.remaining)
    below_wf).induction
    (C := fun state => ∀ fuel, (drive solver fuel state).Finished ↔ roundsWF solver state ≤ fuel)
    state ?_
  intro state ih fuel
  cases decided : advance solver state with
  | done outcome =>
    rw [roundsWF_done solver decided]
    cases fuel with
    | zero =>
      rw [drive_zero]
      exact ⟨fun finished => False.elim finished, fun le => absurd le (by omega)⟩
    | succ fuel =>
      rw [drive_succ, decided]
      exact ⟨fun _ => by omega, fun _ => advance_done_finished solver decided⟩
  | next next =>
    rw [roundsWF_next solver decided]
    cases fuel with
    | zero =>
      rw [drive_zero]
      exact ⟨fun finished => False.elim finished, fun le => absurd le (by omega)⟩
    | succ fuel =>
      rw [drive_succ, decided]
      show (drive solver fuel next).Finished ↔ roundsWF solver next + 1 ≤ fuel + 1
      rw [ih next (advance_next solver decided) fuel]
      omega

/-- **The round count is the least budget at which the run finishes.** -/
theorem roundsWF_least (state : Update levels original) :
    IsLeast {fuel | (drive solver fuel state).Finished} (roundsWF solver state) :=
  ⟨(drive_finished_iff solver state _).mpr le_rfl,
    fun _ finished => (drive_finished_iff solver state _).mp finished⟩

/-- **Every run is certified**: some budget finishes it. -/
theorem every_run_finishes (state : Update levels original) :
    ∃ fuel, (drive solver fuel state).Finished :=
  ⟨roundsWF solver state, (drive_finished_iff solver state _).mpr le_rfl⟩

/-- **Control: budget `0` never finishes.** -/
theorem drive_zero_not_finished (state : Update levels original) :
    ¬ (drive solver 0 state).Finished := by
  rw [drive_zero]
  exact fun finished => finished

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeUnifier

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeUnifier in
#print axioms drive_finished_iff
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeUnifier in
#print axioms roundsWF_least
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeUnifier in
#print axioms every_run_finishes
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeUnifier in
#print axioms drive_zero_not_finished
