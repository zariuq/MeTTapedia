import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpointsArguments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentClosure

/-!
# The chain of rounds, and why no decision theorem holds on the fragment at the tower

The rounds added after R97 form one chain over R97's ranked abstraction round:

`any` → `twin` (convertible twins) → `heads` (clashes of neutral heads) → `pairs` (η for Σ) →
`endpoints` (occurrences at identity endpoints) → `projections` (projection spines) →
`arguments` (occurrences at spine arguments).

Each round runs the round below it and acts only when that round is stuck, so the chain is
**conservative** (`argumentsRound_eq_of_any`): on every store where R97's round moves, the last round makes
the same move. Every run that R97's family decides, the last family decides with the same outcome
(`arguments_run_of_any`), and every store that R97's family decides at a joint budget, the last family
decides at that budget with the same outcome (`arguments_decided_of_any`).

The last family settles on every class where it fires and stays (`argumentsSettledOfConst`), and then decides
every store of the class (`ContextualDependentDecisiveDriver.Settled.decided`). No family settles on a class
containing the fragment at the tower: the fragment holds `crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), which no family decides. What holds for
every store is that runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). The stratified fragment
(`ContextualDependentClosure.Stratified`) was the candidate class; the rows below are what firing and closure on it
would need, and they are conditions of conditional decisions only.

* **Firing.** The rigid rows of the census are read by the rules: clashes, occurrences and decompositions
  (`ContextualDependentCensusReadings`), projection spines and spine arguments (`argumentsRound_not_stuck_of_…`
  here). Firing for the flexible rows is open.
* **Closure.** The stratified fragment is kept by the conversion scan (`scan_stratified`) and by making twins
  homogeneous (`collapse_stratified`); a decomposition keeps it when its pieces have fragment sides and are
  stratified among themselves (`ContextualDependentClosure.Stratified.splice`). Closure under answers and under
  the per-rule pieces is open.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentRank ContextualDependentSpinesMany ContextualDependentTwinsUnder
open ContextualDependentConstantHeads ContextualDependentCensusPairEta ContextualDependentIdEndpoints
open ContextualDependentConstantHeadsProjections ContextualDependentIdEndpointsArguments

/-! ## Conservative extension of a solver -/

section Extension

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

variable (rank : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Nat × Nat)

/-- **A conservative extension decides what the extended solver decides**, with the same outcome: when the
second round agrees with the first wherever the first moves, every decided run of the first is a run of the
second. -/
theorem drive_conservative (first second : {Γ : Context rules} → (problem : EquationStore (TotalTerm Γ)) →
      Round levels rank problem)
    (agrees : ∀ {Γ' : Context rules} (store : EquationStore (TotalTerm Γ')), first store ≠ .stuck →
      second store = first store) {Γ : Context rules} {original : EquationStore (TotalTerm Γ)} :
    ∀ (rounds : Nat) (state : Update levels original), (drive ⟨rank, first⟩ rounds state).Decided →
      drive ⟨rank, second⟩ rounds state = drive ⟨rank, first⟩ rounds state
  | 0, _, decided => absurd decided (by simp [drive, Outcome.Decided])
  | rounds + 1, state, decided => by
      by_cases empty : state.remaining = []
      · have firstDone : advance ⟨rank, first⟩ state = .done (.solved state empty) := by
          unfold advance
          split
          · rfl
          · rename_i head tail cons
            rw [empty] at cons
            cases cons
        have secondDone : advance ⟨rank, second⟩ state = .done (.solved state empty) := by
          unfold advance
          split
          · rfl
          · rename_i head tail cons
            rw [empty] at cons
            cases cons
        rw [drive_succ, drive_succ, firstDone, secondDone]
      · cases computed : first state.remaining with
        | stuck =>
            exfalso
            have stuckAdvance : advance ⟨rank, first⟩ state = .done (.stuck state) := by
              unfold advance
              split
              · rename_i nil
                exact absurd nil empty
              · simp only [computed]
            rw [drive_succ, stuckAdvance] at decided
            exact decided
        | progress update smaller =>
            have moved := agrees state.remaining (by rw [computed]; exact fun impossible => by cases impossible)
            have secondComputed : second state.remaining = .progress update smaller := moved.trans computed
            have firstNext : advance ⟨rank, first⟩ state = .next (state.then update) := by
              unfold advance
              split
              · rename_i nil
                exact absurd nil empty
              · simp only [computed]
            have secondNext : advance ⟨rank, second⟩ state = .next (state.then update) := by
              unfold advance
              split
              · rename_i nil
                exact absurd nil empty
              · simp only [secondComputed]
            rw [drive_succ, drive_succ, secondNext, firstNext]
            rw [drive_succ, firstNext] at decided
            exact drive_conservative first second agrees rounds (state.then update) decided
        | refuted absent =>
            have moved := agrees state.remaining (by rw [computed]; exact fun impossible => by cases impossible)
            have secondComputed : second state.remaining = .refuted absent := moved.trans computed
            have firstRefuted : advance ⟨rank, first⟩ state =
                .done (.refuted fun solvable => absent (state.solvable_iff.mp solvable)) := by
              unfold advance
              split
              · rename_i nil
                exact absurd nil empty
              · simp only [computed]
            have secondRefuted : advance ⟨rank, second⟩ state =
                .done (.refuted fun solvable => absent (state.solvable_iff.mp solvable)) := by
              unfold advance
              split
              · rename_i nil
                exact absurd nil empty
              · simp only [secondComputed]
            rw [drive_succ, drive_succ, secondRefuted, firstRefuted]

end Extension

/-! ## The chain is conservative over R97's round -/

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

/-- **The last round makes the move of R97's round wherever that round moves.** -/
theorem argumentsRound_eq_of_any (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck) :
    argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  have twin : twinRound facts roots heads algebra rigid complete reducer declared choices root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem =
      anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
    unfold twinRound
    cases computed : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem with
    | stuck => exact absurd computed moving
    | progress update smaller => rfl
    | refuted absent => rfl
  have headsSame : headsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem =
      anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
    unfold headsRound
    rw [twin]
    cases computed : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem with
    | stuck => exact absurd computed moving
    | progress update smaller => rfl
    | refuted absent => rfl
  have pairs : pairsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem =
      anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
    unfold pairsRound
    rw [headsSame]
    cases computed : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem with
    | stuck => exact absurd computed moving
    | progress update smaller => rfl
    | refuted absent => rfl
  have endpoints : endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem =
      anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
    unfold endpointsRound
    rw [pairs]
    cases computed : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem with
    | stuck => exact absurd computed moving
    | progress update smaller => rfl
    | refuted absent => rfl
  have projections : projectionsRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem =
      anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
    unfold projectionsRound
    rw [endpoints]
    cases computed : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem with
    | stuck => exact absurd computed moving
    | progress update smaller => rfl
    | refuted absent => rfl
  unfold argumentsRound
  rw [projections]
  cases computed : anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that R97's family decides, the last family decides with the same outcome.** -/
theorem arguments_run_of_any (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((anyFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((argumentsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((anyFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => anyRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => argumentsRound_eq_of_any facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **Every store that R97's family decides at a joint budget, the last family decides at that budget**, with
the same outcome at every larger joint budget. -/
theorem arguments_decided_of_any {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {budget : Nat}
    (decided : ∀ larger, budget ≤ larger →
      (run ((anyFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver larger) problem larger).Decided) :
    ∀ larger, budget ≤ larger →
      run ((argumentsFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((anyFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger :=
  fun larger enough => arguments_run_of_any facts roots heads algebra rigid complete declared choices reducer root
    normalizes certifyNormal headTypingUnique rootComplete larger larger problem (decided larger enough)

/-! ## The census rows read by the last round -/

/-- The last round is not stuck when the endpoints round is not. -/
theorem argumentsRound_not_stuck_of_endpoints (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  have projections : projectionsRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck := by
    unfold projectionsRound
    cases computed : endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem with
    | stuck => exact absurd computed moving
    | progress update smaller => exact fun impossible => by cases impossible
    | refuted absent => exact fun impossible => by cases impossible
  unfold argumentsRound
  cases computed : projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed projections
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **Projection-spine row.** When the decomposition of projection spines finds an equation of the prepared store
with homogeneous twins, the last round is not stuck. -/
theorem argumentsRound_not_stuck_of_projections (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (found : (decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel
      (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining).isSome) :
    argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  have projections : projectionsRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck := by
    unfold projectionsRound
    cases endpointsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem with
    | stuck =>
        unfold projectionsRest
        obtain ⟨decomposed, computed⟩ := Option.isSome_iff_exists.mp found
        simp only [computed]
        exact fun impossible => by cases impossible
    | progress update smaller => exact fun impossible => by cases impossible
    | refuted absent => exact fun impossible => by cases impossible
  unfold argumentsRound
  cases computed : projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed projections
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **Spine-argument row.** When the spine-argument occurs check reads the prepared store with homogeneous twins,
the last round is not stuck. -/
theorem argumentsRound_not_stuck_of_arguments (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (argumentsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome) :
    argumentsRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold argumentsRound
  cases projectionsRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨absent, computed⟩ := Option.isSome_iff_exists.mp read
      simp only [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-! ## Closure of the stratified fragment under making twins homogeneous -/

omit [DecidableRel S.R.cumulative] in
/-- Making a twin homogeneous keeps the codes of both sides. -/
theorem collapseOne_codes (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    (collapseOne facts roots heads algebra reducer fuel equation).1 = equation.1 ∧
      (collapseOne facts roots heads algebra reducer fuel equation).2.2.code = equation.2.2.code := by
  unfold collapseOne
  by_cases same : equation.2.1.code = equation.1.1.code
  · rw [if_pos same]
    exact ⟨rfl, rfl⟩
  · rw [if_neg same]
    cases Conversion.compareTypes facts roots heads algebra reducer fuel equation.1.1 equation.2.1 with
    | none => exact ⟨rfl, rfl⟩
    | some found => exact ⟨rfl, rfl⟩

omit [DecidableRel S.R.cumulative] in
/-- **Making the twins of a store homogeneous keeps the stratified fragment.** -/
theorem collapse_stratified (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (stratified : ContextualDependentClosure.Stratified S.levels problem) :
    ContextualDependentClosure.Stratified S.levels
      (problem.map (collapseOne facts roots heads algebra reducer fuel)) := by
  refine stratified.map _ (fun equation _ σ => collapseOne_solves facts roots heads algebra reducer fuel σ equation)
    (fun equation _ sides => ?_) (fun equation _ before atBefore => ?_)
  · obtain ⟨first, second⟩ := collapseOne_codes facts roots heads algebra reducer fuel equation
    unfold ContextualDependentClosure.FragmentSides
    rw [first, second]
    exact sides
  · unfold collapseOne
    by_cases same : equation.2.1.code = equation.1.1.code
    · rw [if_pos same]
      exact atBefore
    · rw [if_neg same]
      cases Conversion.compareTypes facts roots heads algebra reducer fuel equation.1.1 equation.2.1 with
      | none => exact atBefore
      | some found =>
          intro σ _
          exact IsType.refl (equation.1.1.reindex σ).isType

/-! ## Closure of the stratified fragment under the conversion scan -/

omit [DecidableRel S.R.cumulative] in
/-- The conversion scan keeps exactly the equations it does not certify. -/
theorem scan_eq_filter (fuel : Nat) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      Conversion.scan facts roots heads algebra reducer fuel problem =
        problem.filter fun equation =>
          (Conversion.compare facts roots heads algebra reducer fuel equation.1 equation.2).isNone
  | [] => rfl
  | equation :: rest => by
      cases computed : Conversion.compare facts roots heads algebra reducer fuel equation.1 equation.2 with
      | some same =>
          simp only [Conversion.scan, computed]
          rw [List.filter_cons_of_neg (by simp [computed]), scan_eq_filter fuel rest]
      | none =>
          simp only [Conversion.scan, computed]
          rw [List.filter_cons_of_pos (by simp [computed]), scan_eq_filter fuel rest]

omit [DecidableRel S.R.cumulative] in
/-- **The conversion scan keeps the stratified fragment**: it drops only equations that hold at every
solution. -/
theorem scan_stratified (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (stratified : ContextualDependentClosure.Stratified S.levels problem) :
    ContextualDependentClosure.Stratified S.levels (Conversion.scan facts roots heads algebra reducer fuel problem) := by
  rw [scan_eq_filter]
  refine ContextualDependentClosure.stratifiedFrom_nil.mp
    (ContextualDependentClosure.StratifiedFrom.filter_valid _ ?_ problem (fixed := []) (fun _ solved => solved)
      (ContextualDependentClosure.stratifiedFrom_nil.mpr stratified))
  intro equation dropped Δ σ
  cases computed : Conversion.compare facts roots heads algebra reducer fuel equation.1 equation.2 with
  | none => simp [computed] at dropped
  | some same => exact (frames S.levels).preserves σ same.down

end ContextualDependentAcceptance
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
