import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepSort
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWithinFamily

/-!
# The family that reads through the components of Σ types, as a compiled program, and its sweep

The round of `withinTower` restated as a compiled program (`towerWithinRound`), equal to the round it restates
(`towerWithinRound_eq`); the compiled run read as an ending (`endingWithin`), which is the ending of the family's
run at every budget and number of rounds (`endingWithin_run`); and the verdict of a problem under the family
(`Problem.verdictWithin`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentDynamicFragment
open ContextualDependentIntersectionGeneral ContextualDependentMillerClosure ContextualDependentOpenedNormal
open ContextualDependentAcceptance4 ContextualDependentCoverageReadersHalf ContextualDependentTwinsUnder
open ContextualDependentConstantHeads ContextualDependentCumulativeClosure
open ContextualDependentSpinesMany ContextualDependentShortClosure ContextualDependentClosure ContextualDependentEtaLong
open ContextualDependentRigidFormers ContextualDependentEtaDepth
open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

section Rule

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (below belowC : (fuel : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem)
  (reading : (fuel : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Update S.levels problem)
  (readingRank : ∀ (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    weightRank facts roots heads algebra rigid complete (reading fuel problem).remaining =
      weightRank facts roots heads algebra rigid complete problem)

/-- The round of a family above a family by a reading, from a compiled round of the family below. -/
def readRoundC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElseW facts roots heads algebra rigid complete (belowC fuel problem)
    fun _ => liftCollapsed facts roots heads algebra rigid complete (reading fuel problem)
      (readingRank fuel problem) (belowC fuel (reading fuel problem).remaining)

/-- **The compiled round is the round**, where the compiled round below is the round below. -/
theorem readRoundC_eq
    (same : ∀ (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
      belowC fuel problem = below fuel problem)
    (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    readRoundC facts roots heads algebra rigid complete belowC reading readingRank fuel problem =
      readRound facts roots heads algebra rigid complete below reading readingRank fuel problem := by
  unfold readRoundC readRound
  rw [orElseW_eq, same, same]

end Rule

/-- **The round of the tower's family that reads through components, compiled.** -/
def towerWithinRound (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Round setting.levels withinTower.rank problem :=
  readRoundC (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => towerSortRound fuel problem) (fun fuel _ problem => towerWithin fuel problem)
    (fun fuel _ problem => towerWithin_rank fuel problem) fuel problem

/-- **The compiled round of the tower is the round of the family.** -/
theorem towerWithinRound_eq (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    towerWithinRound fuel problem = withinTower.round fuel problem :=
  readRoundC_eq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => sortTower.round fuel problem) (fun fuel _ problem => towerSortRound fuel problem)
    (fun fuel _ problem => towerWithin fuel problem) (fun fuel _ problem => towerWithin_rank fuel problem)
    (fun fuel _ problem => towerSortRound_eq fuel problem) fuel problem

/-- **The compiled run of the tower's family**, read as an ending. -/
def endingWithin (fuel : Nat) : Nat → (Γ : Context setting.R) → EquationStore (TotalTerm Γ) → Ending
  | 0, _, _ => .cutoff
  | rounds + 1, _, store =>
      if store.isEmpty then .committed
      else
        match towerWithinRound fuel store with
        | .progress update _ => endingWithin fuel rounds update.target update.remaining
        | .refuted _ => .refuted
        | .stuck => .stuck

theorem endingWithin_nil (fuel rounds : Nat) {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (isEmpty : store.isEmpty = true) : endingWithin fuel (rounds + 1) Γ store = .committed := by
  rw [endingWithin, if_pos isEmpty]

theorem endingWithin_cons (fuel rounds : Nat) {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (notEmpty : store.isEmpty = false) :
    endingWithin fuel (rounds + 1) Γ store =
      match towerWithinRound fuel store with
      | .progress update _ => endingWithin fuel rounds update.target update.remaining
      | .refuted _ => .refuted
      | .stuck => .stuck := by
  rw [endingWithin, if_neg (by rw [notEmpty]; exact Bool.false_ne_true)]

theorem endingWithin_drive (fuel : Nat) : ∀ (rounds : Nat) {Γ : Context setting.R}
    {original : EquationStore (TotalTerm Γ)} (state : Update setting.levels original),
    endingOf (drive (withinTower.solver fuel) rounds state) = endingWithin fuel rounds state.target state.remaining
  | 0, _, _, _ => rfl
  | rounds + 1, _, _, state => by
      rw [drive_succ]
      cases decided : advance (withinTower.solver fuel) state with
      | done outcome =>
          change endingOf outcome = _
          unfold advance at decided
          split at decided
          · rename_i finished
            cases decided
            exact (endingWithin_nil fuel rounds (by rw [finished]; rfl)).symm
          · rename_i first rest nonempty
            have notEmpty : state.remaining.isEmpty = false := by rw [nonempty]; rfl
            rw [endingWithin_cons fuel rounds notEmpty]
            split at decided
            · cases decided
            · rename_i absent isRefuted
              cases decided
              rw [(towerWithinRound_eq fuel state.remaining).trans isRefuted]
              rfl
            · rename_i isStuck
              cases decided
              rw [(towerWithinRound_eq fuel state.remaining).trans isStuck]
              rfl
      | next next =>
          change endingOf (drive (withinTower.solver fuel) rounds next) = _
          unfold advance at decided
          split at decided
          · cases decided
          · rename_i first rest nonempty
            have notEmpty : state.remaining.isEmpty = false := by rw [nonempty]; rfl
            rw [endingWithin_cons fuel rounds notEmpty]
            split at decided
            · rename_i update smaller isProgress
              cases decided
              rw [(towerWithinRound_eq fuel state.remaining).trans isProgress]
              exact endingWithin_drive fuel rounds (state.then update)
            · cases decided
            · cases decided

/-- **The compiled run reads the ending of the family's run**, at every budget and number of rounds. -/
theorem endingWithin_run (fuel rounds : Nat) {Γ : Context setting.R} (store : EquationStore (TotalTerm Γ)) :
    endingOf (run (withinTower.solver fuel) store rounds) = endingWithin fuel rounds Γ store :=
  endingWithin_drive fuel rounds (Update.pending setting.levels store)

/-- A run that the compiled run reads as committed carries a principal answer. -/
theorem committed_of_endingWithin {fuel rounds : Nat} {Γ : Context setting.R}
    {store : EquationStore (TotalTerm Γ)} (read : endingWithin fuel rounds Γ store = .committed) :
    (run (withinTower.solver fuel) store rounds).readout = .commit := by
  rw [← endingWithin_run] at read
  cases outcome : run (withinTower.solver fuel) store rounds with
  | solved _ _ => rfl
  | stuck _ => rw [outcome] at read; cases read
  | refuted _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- A run that the compiled run reads as stuck is stuck. -/
theorem stuck_of_endingWithin {fuel rounds : Nat} {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (read : endingWithin fuel rounds Γ store = .stuck) :
    isStuck (run (withinTower.solver fuel) store rounds) = true := by
  rw [← endingWithin_run] at read
  cases outcome : run (withinTower.solver fuel) store rounds with
  | stuck _ => rfl
  | solved _ _ => rw [outcome] at read; cases read
  | refuted _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- A run that the compiled run reads as refuted certifies that the store has no solution. -/
theorem unsolvable_of_endingWithin {fuel rounds : Nat} {Γ : Context setting.R}
    {store : EquationStore (TotalTerm Γ)} (read : endingWithin fuel rounds Γ store = .refuted) :
    ¬ (frames setting.levels).Solvable store := by
  rw [← endingWithin_run] at read
  cases outcome : run (withinTower.solver fuel) store rounds with
  | refuted absent => exact absent
  | solved _ _ => rw [outcome] at read; cases read
  | stuck _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- **Run the family on a problem**, at a budget and a number of rounds. -/
def Problem.verdictWithin (fuel rounds : Nat) (problem : Problem) : Verdict :=
  match problem.store? with
  | none => .illTyped
  | some ⟨Γ, store⟩ => if storeInside store then .ended (endingWithin fuel rounds Γ store) else .outside

/-- **A stuck verdict is a stuck run of the family on a store of the fragment.** -/
theorem stuck_verdictWithin {fuel rounds : Nat} {problem : Problem}
    (stuck : problem.verdictWithin fuel rounds = .ended .stuck) :
    ∃ (Γ : Context setting.R) (store : EquationStore (TotalTerm Γ)), problem.store? = some ⟨Γ, store⟩ ∧
      InFragmentStore store ∧ isStuck (run (withinTower.solver fuel) store rounds) = true := by
  unfold Problem.verdictWithin at stuck
  cases built : problem.store? with
  | none => rw [built] at stuck; cases stuck
  | some pair =>
      obtain ⟨Γ, store⟩ := pair
      rw [built] at stuck
      by_cases inside : storeInside store = true
      · simp only [inside, if_true] at stuck
        exact ⟨Γ, store, rfl, storeInside_sound inside, stuck_of_endingWithin (Verdict.ended.inj stuck)⟩
      · simp only [inside] at stuck
        cases stuck

end ContextualDependentSweep
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
