import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWide
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentLeastFamily

/-!
# The family that reads every equation at its least annotation, as a compiled program, and its sweep

The round of `leastFamily` restated with the rank fixed in the types (`leastRoundC`), equal to the round it restates
(`leastRoundC_eq`); the compiled round of the tower (`towerLeastRound`); the compiled run read as an ending
(`endingLeast`), which is the ending of the family's run at every budget and number of rounds (`endingLeast_run`);
and the verdict of a problem under the family (`Problem.verdictLeast`).
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

section Rule

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)
  (strengthening : EqualStrengthening S.R)
  (candidates : List Head)

/-- The round that reads every equation at its least annotation, compiled. -/
def leastRoundC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElseW facts roots heads algebra rigid complete
    (boundRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    fun _ => liftCollapsed facts roots heads algebra rigid complete
      (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)
      (lowerUpdate_rank facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)
      (boundRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
          problem).remaining)

/-- **The compiled round is the round.** -/
theorem leastRoundC_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    leastRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening candidates fuel problem =
      leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening candidates fuel problem := by
  unfold leastRoundC
  rw [orElseW_eq, boundRoundC_eq, boundRoundC_eq]
  rfl

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- **The round of the tower's family that reads every equation at its least annotation, compiled.** -/
def towerLeastRound (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Round setting.levels leastTower.rank problem :=
  leastRoundC (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts fuel
    problem

/-- **The compiled round of the tower is the round of the family.** -/
theorem towerLeastRound_eq (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    towerLeastRound fuel problem = leastTower.round fuel problem :=
  leastRoundC_eq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts fuel
    problem

/-- **The compiled run of the tower's family**, read as an ending. -/
def endingLeast (fuel : Nat) : Nat → (Γ : Context setting.R) → EquationStore (TotalTerm Γ) → Ending
  | 0, _, _ => .cutoff
  | rounds + 1, _, store =>
      if store.isEmpty then .committed
      else
        match towerLeastRound fuel store with
        | .progress update _ => endingLeast fuel rounds update.target update.remaining
        | .refuted _ => .refuted
        | .stuck => .stuck

theorem endingLeast_nil (fuel rounds : Nat) {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (isEmpty : store.isEmpty = true) : endingLeast fuel (rounds + 1) Γ store = .committed := by
  rw [endingLeast, if_pos isEmpty]

theorem endingLeast_cons (fuel rounds : Nat) {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (notEmpty : store.isEmpty = false) :
    endingLeast fuel (rounds + 1) Γ store =
      match towerLeastRound fuel store with
      | .progress update _ => endingLeast fuel rounds update.target update.remaining
      | .refuted _ => .refuted
      | .stuck => .stuck := by
  rw [endingLeast, if_neg (by rw [notEmpty]; exact Bool.false_ne_true)]

theorem endingLeast_drive (fuel : Nat) : ∀ (rounds : Nat) {Γ : Context setting.R}
    {original : EquationStore (TotalTerm Γ)} (state : Update setting.levels original),
    endingOf (drive (leastTower.solver fuel) rounds state) = endingLeast fuel rounds state.target state.remaining
  | 0, _, _, _ => rfl
  | rounds + 1, _, _, state => by
      rw [drive_succ]
      cases decided : advance (leastTower.solver fuel) state with
      | done outcome =>
          change endingOf outcome = _
          unfold advance at decided
          split at decided
          · rename_i finished
            cases decided
            exact (endingLeast_nil fuel rounds (by rw [finished]; rfl)).symm
          · rename_i first rest nonempty
            have notEmpty : state.remaining.isEmpty = false := by rw [nonempty]; rfl
            rw [endingLeast_cons fuel rounds notEmpty]
            split at decided
            · cases decided
            · rename_i absent isRefuted
              cases decided
              rw [(towerLeastRound_eq fuel state.remaining).trans isRefuted]
              rfl
            · rename_i isStuck
              cases decided
              rw [(towerLeastRound_eq fuel state.remaining).trans isStuck]
              rfl
      | next next =>
          change endingOf (drive (leastTower.solver fuel) rounds next) = _
          unfold advance at decided
          split at decided
          · cases decided
          · rename_i first rest nonempty
            have notEmpty : state.remaining.isEmpty = false := by rw [nonempty]; rfl
            rw [endingLeast_cons fuel rounds notEmpty]
            split at decided
            · rename_i update smaller isProgress
              cases decided
              rw [(towerLeastRound_eq fuel state.remaining).trans isProgress]
              exact endingLeast_drive fuel rounds (state.then update)
            · cases decided
            · cases decided

/-- **The compiled run reads the ending of the family's run**, at every budget and number of rounds. -/
theorem endingLeast_run (fuel rounds : Nat) {Γ : Context setting.R} (store : EquationStore (TotalTerm Γ)) :
    endingOf (run (leastTower.solver fuel) store rounds) = endingLeast fuel rounds Γ store :=
  endingLeast_drive fuel rounds (Update.pending setting.levels store)

/-- A run that the compiled run reads as committed carries a principal answer. -/
theorem committed_of_endingLeast {fuel rounds : Nat} {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (read : endingLeast fuel rounds Γ store = .committed) :
    (run (leastTower.solver fuel) store rounds).readout = .commit := by
  rw [← endingLeast_run] at read
  cases outcome : run (leastTower.solver fuel) store rounds with
  | solved _ _ => rfl
  | stuck _ => rw [outcome] at read; cases read
  | refuted _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- A run that the compiled run reads as stuck is stuck. -/
theorem stuck_of_endingLeast {fuel rounds : Nat} {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (read : endingLeast fuel rounds Γ store = .stuck) :
    isStuck (run (leastTower.solver fuel) store rounds) = true := by
  rw [← endingLeast_run] at read
  cases outcome : run (leastTower.solver fuel) store rounds with
  | stuck _ => rfl
  | solved _ _ => rw [outcome] at read; cases read
  | refuted _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- A run that the compiled run reads as refuted certifies that the store has no solution. -/
theorem unsolvable_of_endingLeast {fuel rounds : Nat} {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (read : endingLeast fuel rounds Γ store = .refuted) : ¬ (frames setting.levels).Solvable store := by
  rw [← endingLeast_run] at read
  cases outcome : run (leastTower.solver fuel) store rounds with
  | refuted absent => exact absent
  | solved _ _ => rw [outcome] at read; cases read
  | stuck _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- **Run the family on a problem**, at a budget and a number of rounds. -/
def Problem.verdictLeast (fuel rounds : Nat) (problem : Problem) : Verdict :=
  match problem.store? with
  | none => .illTyped
  | some ⟨Γ, store⟩ => if storeInside store then .ended (endingLeast fuel rounds Γ store) else .outside

/-- **A stuck verdict is a stuck run of the family on a store of the fragment.** -/
theorem stuck_verdictLeast {fuel rounds : Nat} {problem : Problem}
    (stuck : problem.verdictLeast fuel rounds = .ended .stuck) :
    ∃ (Γ : Context setting.R) (store : EquationStore (TotalTerm Γ)), problem.store? = some ⟨Γ, store⟩ ∧
      InFragmentStore store ∧ isStuck (run (leastTower.solver fuel) store rounds) = true := by
  unfold Problem.verdictLeast at stuck
  cases built : problem.store? with
  | none => rw [built] at stuck; cases stuck
  | some pair =>
      obtain ⟨Γ, store⟩ := pair
      rw [built] at stuck
      by_cases inside : storeInside store = true
      · simp only [inside, if_true] at stuck
        exact ⟨Γ, store, rfl, storeInside_sound inside, stuck_of_endingLeast (Verdict.ended.inj stuck)⟩
      · simp only [inside] at stuck
        cases stuck

end ContextualDependentSweep
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
