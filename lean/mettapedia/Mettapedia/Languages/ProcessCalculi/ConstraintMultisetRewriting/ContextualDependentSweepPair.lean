import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPairFamily

/-!
# The top family, as a compiled program, and its sweep

The round of `pairTower` restated as a compiled program (`towerPairRound`), equal to the round it restates
(`towerPairRound_eq`); the compiled run read as an ending (`endingPair`), which is the ending of the family's run
at every budget and number of rounds (`endingPair_run`); and the verdict of a problem under the family
(`Problem.verdictPair`).
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
  (refute : (fuel : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Option (PLift (¬ (frames S.levels).Solvable problem)))

/-- The round of a family above a family by a refutation, from a compiled round of the family below. -/
def refuteRoundC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElseW facts roots heads algebra rigid complete (belowC fuel problem)
    fun _ => refutedRoundW facts roots heads algebra rigid complete (refute fuel problem)

/-- **The compiled round is the round**, where the compiled round below is the round below. -/
theorem refuteRoundC_eq
    (same : ∀ (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
      belowC fuel problem = below fuel problem)
    (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    refuteRoundC facts roots heads algebra rigid complete belowC refute fuel problem =
      refuteRound facts roots heads algebra rigid complete below refute fuel problem := by
  unfold refuteRoundC refuteRound
  rw [orElseW_eq, refutedRoundW_eq, same]

end Rule

/-- **The round of the top family, compiled.** -/
def towerPairRound (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Round setting.levels pairTower.rank problem :=
  refuteRoundC (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => towerWithinRound fuel problem) (fun fuel _ problem => towerPairRefuted fuel problem)
    fuel problem

/-- **The compiled round of the tower is the round of the family.** -/
theorem towerPairRound_eq (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    towerPairRound fuel problem = pairTower.round fuel problem :=
  refuteRoundC_eq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => withinTower.round fuel problem) (fun fuel _ problem => towerWithinRound fuel problem)
    (fun fuel _ problem => towerPairRefuted fuel problem)
    (fun fuel _ problem => towerWithinRound_eq fuel problem) fuel problem

/-- **The compiled run of the top family**, read as an ending. -/
def endingPair (fuel : Nat) : Nat → (Γ : Context setting.R) → EquationStore (TotalTerm Γ) → Ending
  | 0, _, _ => .cutoff
  | rounds + 1, _, store =>
      if store.isEmpty then .committed
      else
        match towerPairRound fuel store with
        | .progress update _ => endingPair fuel rounds update.target update.remaining
        | .refuted _ => .refuted
        | .stuck => .stuck

theorem endingPair_nil (fuel rounds : Nat) {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (isEmpty : store.isEmpty = true) : endingPair fuel (rounds + 1) Γ store = .committed := by
  rw [endingPair, if_pos isEmpty]

theorem endingPair_cons (fuel rounds : Nat) {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (notEmpty : store.isEmpty = false) :
    endingPair fuel (rounds + 1) Γ store =
      match towerPairRound fuel store with
      | .progress update _ => endingPair fuel rounds update.target update.remaining
      | .refuted _ => .refuted
      | .stuck => .stuck := by
  rw [endingPair, if_neg (by rw [notEmpty]; exact Bool.false_ne_true)]

theorem endingPair_drive (fuel : Nat) : ∀ (rounds : Nat) {Γ : Context setting.R}
    {original : EquationStore (TotalTerm Γ)} (state : Update setting.levels original),
    endingOf (drive (pairTower.solver fuel) rounds state) = endingPair fuel rounds state.target state.remaining
  | 0, _, _, _ => rfl
  | rounds + 1, _, _, state => by
      rw [drive_succ]
      cases decided : advance (pairTower.solver fuel) state with
      | done outcome =>
          change endingOf outcome = _
          unfold advance at decided
          split at decided
          · rename_i finished
            cases decided
            exact (endingPair_nil fuel rounds (by rw [finished]; rfl)).symm
          · rename_i first rest nonempty
            have notEmpty : state.remaining.isEmpty = false := by rw [nonempty]; rfl
            rw [endingPair_cons fuel rounds notEmpty]
            split at decided
            · cases decided
            · rename_i absent isRefuted
              cases decided
              rw [(towerPairRound_eq fuel state.remaining).trans isRefuted]
              rfl
            · rename_i isStuck
              cases decided
              rw [(towerPairRound_eq fuel state.remaining).trans isStuck]
              rfl
      | next next =>
          change endingOf (drive (pairTower.solver fuel) rounds next) = _
          unfold advance at decided
          split at decided
          · cases decided
          · rename_i first rest nonempty
            have notEmpty : state.remaining.isEmpty = false := by rw [nonempty]; rfl
            rw [endingPair_cons fuel rounds notEmpty]
            split at decided
            · rename_i update smaller isProgress
              cases decided
              rw [(towerPairRound_eq fuel state.remaining).trans isProgress]
              exact endingPair_drive fuel rounds (state.then update)
            · cases decided
            · cases decided

/-- **The compiled run reads the ending of the family's run**, at every budget and number of rounds. -/
theorem endingPair_run (fuel rounds : Nat) {Γ : Context setting.R} (store : EquationStore (TotalTerm Γ)) :
    endingOf (run (pairTower.solver fuel) store rounds) = endingPair fuel rounds Γ store :=
  endingPair_drive fuel rounds (Update.pending setting.levels store)

/-- A run that the compiled run reads as committed carries a principal answer. -/
theorem committed_of_endingPair {fuel rounds : Nat} {Γ : Context setting.R}
    {store : EquationStore (TotalTerm Γ)} (read : endingPair fuel rounds Γ store = .committed) :
    (run (pairTower.solver fuel) store rounds).readout = .commit := by
  rw [← endingPair_run] at read
  cases outcome : run (pairTower.solver fuel) store rounds with
  | solved _ _ => rfl
  | stuck _ => rw [outcome] at read; cases read
  | refuted _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- A run that the compiled run reads as stuck is stuck. -/
theorem stuck_of_endingPair {fuel rounds : Nat} {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (read : endingPair fuel rounds Γ store = .stuck) :
    isStuck (run (pairTower.solver fuel) store rounds) = true := by
  rw [← endingPair_run] at read
  cases outcome : run (pairTower.solver fuel) store rounds with
  | stuck _ => rfl
  | solved _ _ => rw [outcome] at read; cases read
  | refuted _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- A run that the compiled run reads as refuted certifies that the store has no solution. -/
theorem unsolvable_of_endingPair {fuel rounds : Nat} {Γ : Context setting.R}
    {store : EquationStore (TotalTerm Γ)} (read : endingPair fuel rounds Γ store = .refuted) :
    ¬ (frames setting.levels).Solvable store := by
  rw [← endingPair_run] at read
  cases outcome : run (pairTower.solver fuel) store rounds with
  | refuted absent => exact absent
  | solved _ _ => rw [outcome] at read; cases read
  | stuck _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- **Run the top family on a problem**, at a budget and a number of rounds. -/
def Problem.verdictPair (fuel rounds : Nat) (problem : Problem) : Verdict :=
  match problem.store? with
  | none => .illTyped
  | some ⟨Γ, store⟩ => if storeInside store then .ended (endingPair fuel rounds Γ store) else .outside

/-- **A stuck verdict is a stuck run of the top family on a store of the fragment.** -/
theorem stuck_verdictPair {fuel rounds : Nat} {problem : Problem}
    (stuck : problem.verdictPair fuel rounds = .ended .stuck) :
    ∃ (Γ : Context setting.R) (store : EquationStore (TotalTerm Γ)), problem.store? = some ⟨Γ, store⟩ ∧
      InFragmentStore store ∧ isStuck (run (pairTower.solver fuel) store rounds) = true := by
  unfold Problem.verdictPair at stuck
  cases built : problem.store? with
  | none => rw [built] at stuck; cases stuck
  | some pair =>
      obtain ⟨Γ, store⟩ := pair
      rw [built] at stuck
      by_cases inside : storeInside store = true
      · simp only [inside, if_true] at stuck
        exact ⟨Γ, store, rfl, storeInside_sound inside, stuck_of_endingPair (Verdict.ended.inj stuck)⟩
      · simp only [inside] at stuck
        cases stuck

end ContextualDependentSweep
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
