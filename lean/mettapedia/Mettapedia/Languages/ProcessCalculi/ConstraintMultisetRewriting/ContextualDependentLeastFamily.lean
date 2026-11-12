import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentLeastAnnotation

/-!
# The family that reads every equation at its least annotation

The family above the family with the occurs rule at a bound variable: its round is that family's round, and when
that round is stuck, that family's round again on the store with every equation at its least annotation
(`ContextualDependentEtaDepth.lowerUpdate`). Reading at the least annotation keeps the solutions and the weight
rank, so every committed step of the second round lowers the rank of the store as given.

* The family decides every run that the family below decides, with the same outcome (`least_run_of_bound`).
* Its round is eventually constant (`leastRound_const`) and keeps the permuted Miller class
  (`leastRound_closure`).
* A conditional decision follows from firing as for the families below (`least_decided_of_firing`). At the tower
  firing fails: the conclusion would decide `crossStore`, solvable and without principal answer
  (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
  `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).

`leastTower` is the family of the tower controls, with the candidate universes `U0`, `U1`, `U2`.

**Where the reading belongs.** A round must lower the rank; reading an equation at a smaller universe changes
neither the context nor the normal forms of the sides, so it is not a round. It is a reading of the store, as the
preparation of the sides is. In this module it is applied where the family below is stuck, which makes the family
conservative by construction; the same update placed inside the preparation gives every rule the least annotation at
once.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentDynamicFragment
open ContextualDependentMillerClosure ContextualDependentOpenedNormal
open ContextualDependentAcceptance4 ContextualDependentTwinsUnder
open ContextualDependentConstantHeads ContextualDependentCumulativeClosure ContextualDependentShortClosure
open ContextualDependentIntersectionGeneral ContextualDependentCoverageReadersHalf
open ContextualDependentOccursBound

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

section Rule

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

/-- **The round**: the round of the family below; when it is stuck, that round on the store with every equation at
its least annotation. -/
noncomputable def leastRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)
      (lowerUpdate_rank facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)
      (boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
          problem).remaining))

/-- **The family**, at the weight rank. -/
noncomputable def leastFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening candidates fuel

/-! ## Conservativity and readers -/

theorem leastRound_eq_of_bound (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem ≠ .stuck) :
    leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening candidates fuel problem =
      boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem := by
  unfold leastRound
  cases computed : boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the family below decides, this family decides with the same outcome.** -/
theorem least_run_of_bound (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((boundFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds).Decided) :
    run ((leastFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening candidates).solver fuel) problem rounds =
      run ((boundFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (fun problem => leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening candidates fuel problem)
    (fun _ moving => leastRound_eq_of_bound facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening candidates fuel moving)
    rounds _ decided

/-- **The reader**: the round moves wherever the round of the family below moves on the store at its least
annotations. -/
theorem leastRound_not_stuck_of_lowered (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel
      (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
        problem).remaining ≠ .stuck) :
    leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening candidates fuel problem ≠ .stuck := by
  unfold leastRound
  cases boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      exact liftCollapsed_not_stuck facts roots heads algebra rigid complete _
        (lowerUpdate_rank facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)
        moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The family's readers**: a reader of the family below, on the store or on the store at its least
annotations. -/
def LeastReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  BoundReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ∨
    BoundReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel
      (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
        problem).remaining

theorem leastRound_not_stuck_of_reads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : LeastReads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening candidates fuel problem) :
    leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening candidates fuel problem ≠ .stuck := by
  rcases reads with below | lowered
  · have moving := boundRound_not_stuck_of_reads facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening fuel below
    rw [leastRound_eq_of_bound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening candidates fuel moving]
    exact moving
  · exact leastRound_not_stuck_of_lowered facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening candidates fuel
      (boundRound_not_stuck_of_reads facts roots heads algebra rigid complete declared choices reducer root
        normalizes certifyNormal headTypingUnique rootComplete strengthening fuel lowered)

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

theorem leastRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening candidates fuel problem) =
      (roundView (boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening fuel problem)).or
        (liftView (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
            problem)
          (roundView (boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel
            (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
              problem).remaining))) := by
  unfold leastRound
  rw [roundView_orElse, liftCollapsed_view]

include stable in
/-- **The round is eventually constant on every store.** -/
theorem leastRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => leastRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening candidates fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => leastRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening candidates fuel
    problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (boundRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening stable problem))
      (EventuallyConst.dep (h := fun fuel => lowerUpdate facts roots heads algebra rigid complete declared choices
          reducer candidates fuel problem)
        (k := fun fuel prepared => liftView prepared
          (roundView (boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening fuel prepared.remaining)))
        (lowerUpdate_const facts roots heads algebra rigid complete declared choices reducer stable candidates
          problem)
        (fun prepared => EventuallyConst.comp (fun round => liftView prepared (roundView round))
          (boundRound_const facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening stable prepared.remaining))))

include stable in
/-- **The family settles** on every class on which, from some budget on, its round is not stuck and keeps the
class. -/
noncomputable def leastSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete strengthening candidates larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete strengthening candidates larger problem =
                .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (leastFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening candidates) :=
  Settled.ofConst _ (fun problem => leastRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening candidates stable problem)
    holds eventual

/-! ## Closure -/

variable (sn : StronglyNormalizing S.R)
  (directed : ∀ (fuel : Nat) {n : Nat} (term : Tm Head n) (result : ExecutableReduction.Result S.R term),
    reducer fuel term = some result → ContextualDependentExecutableJoin.Star (R := S.R) term result.val)

include sn directed in
/-- **Closure of the round** at every budget. -/
theorem leastRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening candidates fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete
      (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)
      (lowerUpdate_rank facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)
      (boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel
        (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel
          problem).remaining)) =
      .progress update smaller at fired
  cases computed : boundRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel problem with
  | stuck =>
      rw [computed] at fired
      exact liftCollapsed_keeps facts roots heads algebra rigid complete (fun problem => PermutedMiller S.levels problem)
        (lowerUpdate facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)
        (lowerUpdate_rank facts roots heads algebra rigid complete declared choices reducer candidates fuel problem)
        (fun first firstSmaller inner => boundRound_closure facts roots heads algebra rigid complete declared choices
          reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ first
          firstSmaller (lowerUpdate_keeps facts roots heads algebra rigid complete declared choices reducer
            candidates fuel permuted) inner) fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact boundRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete strengthening sn directed fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include sn directed stable in
/-- **Conditional decision for the family, from firing**, on every store of the dynamic pattern fragment, with a
principal answer or a certified refutation, constant at every larger budget. At the tower's setting the conclusion
fails on `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there firing fails.
For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem least_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        leastRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening candidates larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((leastFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening candidates).solver larger) problem larger =
        run ((leastFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening candidates).solver budget) problem budget ∧
      ((∃ state finished, run ((leastFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening candidates).solver larger) problem
              larger = .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((leastFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete strengthening candidates).solver larger) problem
              larger = .refuted absent)) :=
  (leastSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening candidates stable
    (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        leastRound_closure facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete strengthening candidates sn directed larger _ update smaller
          held fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Rule

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls

/-- **The candidate universes of the tower controls**: `U0`, `U1`, `U2`, least first. -/
def towerSorts : List Tower.Head :=
  [.sort Tower.zero, .sort (.succ Tower.zero), .sort (.succ (.succ Tower.zero))]

/-- The family of the tower controls. -/
noncomputable def leastTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  leastFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts

/-- The tower's store at its least annotations, at one budget. -/
abbrev towerLower (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Update setting.levels problem :=
  lowerUpdate (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer towerSorts fuel problem

/-- Readers of the tower's family at one budget. -/
abbrev TowerLeastReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  LeastReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts fuel
    problem

/-- **The tower's readers are the readers of the family below, on the store or on the store at its least
annotations.** -/
theorem towerLeastReads_iff (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    TowerLeastReads fuel problem ↔
      TowerBoundReads fuel problem ∨ TowerBoundReads fuel (towerLower fuel problem).remaining := Iff.rfl

/-- **Every run that the tower's family below decides, this family decides with the same outcome.** -/
theorem tower_least_run_of_bound (fuel rounds : Nat) {Θ : Context setting.R}
    (problem : EquationStore (TotalTerm Θ)) (decided : (run (boundTower.solver fuel) problem rounds).Decided) :
    run (leastTower.solver fuel) problem rounds = run (boundTower.solver fuel) problem rounds :=
  least_run_of_bound (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts fuel
    rounds problem decided

/-- **Conditional decision for the tower's family, from firing**, on every store of the dynamic pattern fragment. At
the tower firing fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_least_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → leastTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (leastTower.solver larger) problem larger = run (leastTower.solver budget) problem budget ∧
      ((∃ state finished, run (leastTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (leastTower.solver larger) problem larger = .refuted absent)) :=
  least_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts
    ContextualDependentDecisiveFragment.Controls.stable tower_stronglyNormalizing tower_reducer_directed firing inside

/-- **Conditional decision for the tower's family, from its readers.** At the tower the hypothesis fails: the
conclusion would decide `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). -/
theorem tower_least_decided_of_reads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerLeastReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (leastTower.solver larger) problem larger = run (leastTower.solver budget) problem budget ∧
      ((∃ state finished, run (leastTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (leastTower.solver larger) problem larger = .refuted absent)) :=
  tower_least_decided_of_firing (fun held nonempty => by
    obtain ⟨bound, read⟩ := reads held nonempty
    exact ⟨bound, fun larger enough => leastRound_not_stuck_of_reads (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts larger
      (read larger enough)⟩) inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
