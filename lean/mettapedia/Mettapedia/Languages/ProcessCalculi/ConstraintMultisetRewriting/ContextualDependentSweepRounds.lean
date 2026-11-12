import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseFamily

/-!
# The base round as a compiled program

The rounds above the under-binder round (`etaRound`, `skeletonRound`, `pieceRound`, `sigmaRound`, `baseRound`) are
defined through `orElse` and `refutedRound`, which take the rank of the round as an argument. The rank is the weight
rank, a noncomputable function, so those rounds have no compiled code and a run of the base family can only be
evaluated by the kernel.

This module restates the same rounds with the rank fixed in the types (`orElseW`, `refutedRoundW`), so that no rank is
passed and the rounds compile. Each restated round **is** the round it restates (`etaRoundC_eq`, …, `baseRoundC_eq`),
so the compiled round of the tower is the round of the base family (`towerRound_eq`), and the compiled run reads the
ending of the family's run at every budget and number of rounds (`ending_run`).

The second round of `orElseW` is delayed, so a compiled round stops at the first layer that moves.
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
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- The first round, or the second when the first is stuck, at the weight rank. The second round is delayed. -/
def orElseW {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (first : Round S.levels (weightRank facts roots heads algebra rigid complete) problem)
    (second : Unit → Round S.levels (weightRank facts roots heads algebra rigid complete) problem) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match first with
  | .stuck => second ()
  | .progress update smaller => .progress update smaller
  | .refuted absent => .refuted absent

theorem orElseW_eq {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (first : Round S.levels (weightRank facts roots heads algebra rigid complete) problem)
    (second : Unit → Round S.levels (weightRank facts roots heads algebra rigid complete) problem) :
    orElseW facts roots heads algebra rigid complete first second = orElse first (second ()) := by
  cases first <;> rfl

/-- A refutation, or nothing, as a round of the weight rank. -/
def refutedRoundW {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} :
    Option (PLift (¬ (frames S.levels).Solvable problem)) →
      Round S.levels (weightRank facts roots heads algebra rigid complete) problem
  | some absent => .refuted absent.down
  | none => .stuck

theorem refutedRoundW_eq {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : Option (PLift (¬ (frames S.levels).Solvable problem))) :
    refutedRoundW facts roots heads algebra rigid complete found = refutedRound found := by
  cases found <;> rfl

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R)
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

/-- The η-long prepared store, compiled. -/
def longUpdateC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Update S.levels problem :=
  (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).then
    ((Update.pending S.levels (expandStore facts
        (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining)).rephrase
      (expand_equivalent facts _))

omit [DecidableRel S.R.cumulative] in
theorem longUpdateC_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    longUpdateC facts roots heads algebra reducer root rootComplete fuel problem =
      longUpdate facts roots heads algebra reducer root rootComplete fuel problem := rfl

/-- The η-long prepared round, compiled. -/
def etaRoundC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElseW facts roots heads algebra rigid complete
    (underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem)
    fun _ => liftCollapsed facts roots heads algebra rigid complete
      (longUpdateC facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (underRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (longUpdateC facts roots heads algebra reducer root rootComplete fuel problem).remaining)

theorem etaRoundC_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    etaRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      etaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold etaRoundC
  rw [orElseW_eq]
  rfl

/-- The skeleton round, compiled. -/
def skeletonRoundC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElseW facts roots heads algebra rigid complete
    (etaRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem)
    fun _ => refutedRoundW facts roots heads algebra rigid complete
      (flexRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem)

theorem skeletonRoundC_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    skeletonRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      skeletonRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold skeletonRoundC
  rw [orElseW_eq, etaRoundC_eq, refutedRoundW_eq]
  rfl

/-- The piece round, compiled. -/
def pieceRoundC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElseW facts roots heads algebra rigid complete
    (skeletonRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    fun _ => liftCollapsed facts roots heads algebra rigid complete
      (longUpdateC facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (normalRound facts roots heads algebra rigid complete reducer declared choices fuel
        (longUpdateC facts roots heads algebra reducer root rootComplete fuel problem).remaining)

theorem pieceRoundC_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    pieceRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      pieceRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold pieceRoundC
  rw [orElseW_eq, skeletonRoundC_eq]
  rfl

/-- The η-long prepared store η-expanded at Σ bases, compiled. -/
def sigmaUpdateC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Update S.levels problem :=
  (longUpdateC facts roots heads algebra reducer root rootComplete fuel problem).then
    ((Update.pending S.levels (sigmaExpandStore facts
        (longUpdateC facts roots heads algebra reducer root rootComplete fuel problem).remaining)).rephrase
      (sigma_equivalent facts _))

omit [DecidableRel S.R.cumulative] in
theorem sigmaUpdateC_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    sigmaUpdateC facts roots heads algebra reducer root rootComplete fuel problem =
      sigmaUpdate facts roots heads algebra reducer root rootComplete fuel problem := rfl

/-- The Σ round, compiled. -/
def sigmaRoundC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElseW facts roots heads algebra rigid complete
    (pieceRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    fun _ => liftCollapsed facts roots heads algebra rigid complete
      (sigmaUpdateC facts roots heads algebra reducer root rootComplete fuel problem)
      (sigmaUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (pieceRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (sigmaUpdateC facts roots heads algebra reducer root rootComplete fuel problem).remaining)

theorem sigmaRoundC_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    sigmaRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      sigmaRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold sigmaRoundC
  rw [orElseW_eq, pieceRoundC_eq, pieceRoundC_eq]
  rfl

/-- The base round, compiled. -/
def baseRoundC (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElseW facts roots heads algebra rigid complete
    (sigmaRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    fun _ => liftCollapsed facts roots heads algebra rigid complete
      (longUpdateC facts roots heads algebra reducer root rootComplete fuel problem)
      (longUpdate_rank facts roots heads algebra rigid complete reducer root rootComplete fuel problem)
      (baseNormalRound facts roots heads algebra rigid complete reducer declared choices fuel
        (longUpdateC facts roots heads algebra reducer root rootComplete fuel problem).remaining)

/-- **The compiled base round is the base round.** -/
theorem baseRoundC_eq (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    baseRoundC facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem =
      baseRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold baseRoundC
  rw [orElseW_eq, sigmaRoundC_eq]
  rfl

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- **The base round of the tower, compiled.** -/
def towerRound (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Round setting.levels baseTower.rank problem :=
  baseRoundC (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **The compiled round of the tower is the round of the base family.** -/
theorem towerRound_eq (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    towerRound fuel problem = baseTower.round fuel problem :=
  baseRoundC_eq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **How a run ends**: with a principal answer, with a certified refutation, stuck, or out of rounds. -/
inductive Ending where
  | committed
  | refuted
  | stuck
  | cutoff
  deriving Repr, DecidableEq, Inhabited

/-- The ending of an outcome of the driver. -/
def endingOf {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)} :
    Outcome setting.levels original → Ending
  | .solved _ _ => .committed
  | .refuted _ => .refuted
  | .stuck _ => .stuck
  | .cutoff _ => .cutoff

/-- **The compiled run of the tower's base family**, read as an ending. -/
def ending (fuel : Nat) : Nat → (Γ : Context setting.R) → EquationStore (TotalTerm Γ) → Ending
  | 0, _, _ => .cutoff
  | rounds + 1, _, store =>
      if store.isEmpty then .committed
      else
        match towerRound fuel store with
        | .progress update _ => ending fuel rounds update.target update.remaining
        | .refuted _ => .refuted
        | .stuck => .stuck

theorem ending_nil (fuel rounds : Nat) {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (isEmpty : store.isEmpty = true) : ending fuel (rounds + 1) Γ store = .committed := by
  rw [ending, if_pos isEmpty]

theorem ending_cons (fuel rounds : Nat) {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (notEmpty : store.isEmpty = false) :
    ending fuel (rounds + 1) Γ store =
      match towerRound fuel store with
      | .progress update _ => ending fuel rounds update.target update.remaining
      | .refuted _ => .refuted
      | .stuck => .stuck := by
  rw [ending, if_neg (by rw [notEmpty]; exact Bool.false_ne_true)]

theorem ending_drive (fuel : Nat) : ∀ (rounds : Nat) {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    (state : Update setting.levels original),
    endingOf (drive (baseTower.solver fuel) rounds state) = ending fuel rounds state.target state.remaining
  | 0, _, _, _ => rfl
  | rounds + 1, _, _, state => by
      rw [drive_succ]
      cases decided : advance (baseTower.solver fuel) state with
      | done outcome =>
          change endingOf outcome = _
          unfold advance at decided
          split at decided
          · rename_i finished
            cases decided
            exact (ending_nil fuel rounds (by rw [finished]; rfl)).symm
          · rename_i first rest nonempty
            have notEmpty : state.remaining.isEmpty = false := by rw [nonempty]; rfl
            rw [ending_cons fuel rounds notEmpty]
            split at decided
            · cases decided
            · rename_i absent isRefuted
              cases decided
              rw [(towerRound_eq fuel state.remaining).trans isRefuted]
              rfl
            · rename_i isStuck
              cases decided
              rw [(towerRound_eq fuel state.remaining).trans isStuck]
              rfl
      | next next =>
          change endingOf (drive (baseTower.solver fuel) rounds next) = _
          unfold advance at decided
          split at decided
          · cases decided
          · rename_i first rest nonempty
            have notEmpty : state.remaining.isEmpty = false := by rw [nonempty]; rfl
            rw [ending_cons fuel rounds notEmpty]
            split at decided
            · rename_i update smaller isProgress
              cases decided
              rw [(towerRound_eq fuel state.remaining).trans isProgress]
              exact ending_drive fuel rounds (state.then update)
            · cases decided
            · cases decided

/-- **The compiled run reads the ending of the base family's run**, at every budget and number of rounds. -/
theorem ending_run (fuel rounds : Nat) {Γ : Context setting.R} (store : EquationStore (TotalTerm Γ)) :
    endingOf (run (baseTower.solver fuel) store rounds) = ending fuel rounds Γ store :=
  ending_drive fuel rounds (Update.pending setting.levels store)

/-- A run that the compiled run reads as stuck is stuck. -/
theorem stuck_of_ending {fuel rounds : Nat} {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (read : ending fuel rounds Γ store = .stuck) : isStuck (run (baseTower.solver fuel) store rounds) = true := by
  rw [← ending_run] at read
  cases outcome : run (baseTower.solver fuel) store rounds with
  | stuck _ => rfl
  | solved _ _ => rw [outcome] at read; cases read
  | refuted _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- A run that the compiled run reads as committed carries a principal answer. -/
theorem committed_of_ending {fuel rounds : Nat} {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (read : ending fuel rounds Γ store = .committed) :
    (run (baseTower.solver fuel) store rounds).readout = .commit := by
  rw [← ending_run] at read
  cases outcome : run (baseTower.solver fuel) store rounds with
  | solved _ _ => rfl
  | stuck _ => rw [outcome] at read; cases read
  | refuted _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

/-- A run that the compiled run reads as refuted refutes a store without solutions. -/
theorem unsolvable_of_ending {fuel rounds : Nat} {Γ : Context setting.R} {store : EquationStore (TotalTerm Γ)}
    (read : ending fuel rounds Γ store = .refuted) : ¬ (frames setting.levels).Solvable store := by
  rw [← ending_run] at read
  cases outcome : run (baseTower.solver fuel) store rounds with
  | refuted absent => exact absent
  | solved _ _ => rw [outcome] at read; cases read
  | stuck _ => rw [outcome] at read; cases read
  | cutoff _ => rw [outcome] at read; cases read

end ContextualDependentSweep
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
