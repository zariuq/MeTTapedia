import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4Final
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance2Readings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance2Cumulative

/-!
# The readers' half of coverage: the dead-binder round moves wherever a reader reads

The dead-binder round runs the anywhere round, which runs the in-place, older and general intersection rounds, which run
the cumulative round, which runs the flexible round; each acts only where the round below it is stuck, so the
dead-binder round moves wherever the flexible round does (`deadRound_not_stuck_of_flex`). R110's readers
(`ContextualDependentAcceptance2.last_reads_*`) make the flexible round move, so the dead-binder round moves wherever one
of them reads (`deadRound_not_stuck_of_reads`).

`Reads` collects R110's twelve rows as one statement about one budget: a rigid clash or an occurrence along formers
on the prepared store with homogeneous twins, a committed decomposition of the prepared store, a decomposition of
projection spines, a refutation among spine arguments, a rigid local outside the pattern, inversion at the newest
declaration, inversion in place, flex–flex across a declaration, intersection, pruning under binders, or a move at a
flexible base. `OuterReads` collects the readers of the outer rounds: R110's cumulative rule, R119's intersection at
the newest declaration, after a rotation, in place and anywhere, and the dead-binder rule
(`deadRound_not_stuck_of_outerReads`); `AllReads` is either. **The firing hypothesis follows from eventual reading**
(`firing_of_reads`, `firing_of_allReads`), and the cumulative round is closed
(`ContextualDependentAcceptance4.cumulativeRound_closure`), so the tower's decision is conditional on eventual reading
on nonempty stores of the permuted class (`tower_dead_decided_of_reads`, `tower_dead_decided_of_allReads`). That every
census kind is read, on the prepared store at a large budget, is the other half of coverage, and at the tower it fails:
the conclusion would decide `crossStore`, solvable and without principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCoverageReadersHalf

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRigidFormers ContextualDependentRank ContextualDependentSpinesMany
open ContextualDependentTwinsUnder ContextualDependentConstantHeads ContextualDependentCensusPairEta
open ContextualDependentIdEndpoints ContextualDependentFragmentDecisive ContextualDependentEtaExpansion
open ContextualDependentIdEndpointsArguments ContextualDependentCensusReadings ContextualDependentAcceptance
open ContextualDependentPatternFiring ContextualDependentEliminations ContextualDependentFlexReorder
open ContextualDependentIntersection ContextualDependentPruneSolve ContextualDependentSpineEta
open ContextualDependentConstantHeadsProjections ContextualDependentAcceptance2 ContextualDependentIntersectionGeneral
open ContextualDependentMillerClosure

section General

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

/-- **R110's twelve rows, at one budget**: one of the readers of the flexible round reads the store. -/
def Reads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  (∃ equation ∈ (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining,
      equation.2.1.code = equation.1.1.code ∧
        HeadClash S.R 0 equation.1.1.code equation.1.2.code equation.2.2.code) ∨
  (∃ equation ∈ (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining,
      equation.2.1.code = equation.1.1.code ∧
        UnderInside S.R equation.1.1.code equation.1.2.code equation.2.2.code) ∨
  (decomposeAny facts roots heads algebra rigid complete declared choices reducer fuel
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining).isSome ∨
  (decomposeProjections facts roots heads algebra rigid complete declared choices reducer fuel
      (preparedTwins facts roots heads algebra reducer root rootComplete fuel problem).remaining).isSome ∨
  (argumentsRefuted facts roots heads algebra rigid complete reducer root rootComplete fuel problem).isSome ∨
  (rigidRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      fuel problem).isSome ∨
  (ContextualDependentRecognitionConversion.patternRuleConv facts roots heads algebra declared choices reducer
      rigid complete root normalizes certifyNormal fuel problem).isSome ∨
  (placedRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      fuel problem).isSome ∨
  (reorderRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel problem).isSome ∨
  (intersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome ∨
  (pruneSolveRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem).isSome ∨
  flexRest facts roots heads algebra rigid complete declared choices reducer root rootComplete fuel problem ≠ .stuck

/-- **The flexible round moves wherever a reader reads.** -/
theorem flexRound_not_stuck_of_reads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : Reads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem) :
    flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  rcases reads with read | read | read | read | read | read | read | read | read | read | read | read
  · exact last_reads_clash facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_inside facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_decomposed facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_projections facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_arguments facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_rigid facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_pattern facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_placed facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_reorder facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_intersection facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact last_reads_pruning facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel read
  · exact flexRound_not_stuck_of_rest facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel read

/-- **The dead-binder round moves wherever the flexible round moves.** -/
theorem deadRound_not_stuck_of_flex (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : flexRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck) :
    deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  have cumulative := cumulativeRound_not_stuck_of_flex facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete fuel moving
  have general : generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck := by
    rw [generalRound_eq_of_cumulative facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel cumulative]
    exact cumulative
  have older : olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck := by
    rw [olderRound_eq_of_general facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel general]
    exact general
  have placed : ContextualDependentIntersectionGeneral.inPlaceRound facts roots heads algebra rigid complete declared
      choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck := by
    rw [inPlaceRound_eq_of_older facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel older]
    exact older
  have anywhere : anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck := by
    rw [anywhereRound_eq_of_inPlace facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel placed]
    exact placed
  rw [deadRound_eq_of_anywhere facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel anywhere]
  exact anywhere

/-- **The dead-binder round moves wherever a reader reads.** -/
theorem deadRound_not_stuck_of_reads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : Reads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem) :
    deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck :=
  deadRound_not_stuck_of_flex facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete strengthening fuel
    (flexRound_not_stuck_of_reads facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel reads)

/-- **The readers of the outer rounds, at one budget**: R110's cumulative rule, R119's intersection at the newest
declaration, after a rotation, in place and anywhere, and the dead-binder rule. -/
def OuterReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  (ContextualDependentCumulative.cumulativeRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal fuel problem).isSome ∨
  (generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome ∨
  (olderIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome ∨
  (inPlaceIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome ∨
  (anywhereRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome ∨
  (deadRule facts roots heads algebra rigid complete declared choices reducer root normalizes headTypingUnique
      strengthening fuel problem).isSome

/-- **The dead-binder round moves wherever its own rule reads.** -/
theorem deadRound_not_stuck_of_deadRule (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (deadRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique strengthening fuel problem).isSome) :
    deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  unfold deadRound
  cases anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      dsimp only
      obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
      rw [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-- **The dead-binder round moves wherever a reader of an outer round reads.** -/
theorem deadRound_not_stuck_of_outerReads (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (reads : OuterReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique strengthening fuel problem) :
    deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := by
  have lift_anywhere : anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck →
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening fuel problem ≠ .stuck := fun anywhere => by
    rw [deadRound_eq_of_anywhere facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete strengthening fuel anywhere]
    exact anywhere
  have lift_inPlace : ContextualDependentIntersectionGeneral.inPlaceRound facts roots heads algebra rigid complete
      declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck →
      anywhereRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem ≠ .stuck := fun placed => by
    rw [anywhereRound_eq_of_inPlace facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel placed]
    exact placed
  have lift_older : olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck →
      ContextualDependentIntersectionGeneral.inPlaceRound facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck := fun older => by
    rw [inPlaceRound_eq_of_older facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel older]
    exact older
  have lift_general : generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck →
      olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem ≠ .stuck := fun general => by
    rw [olderRound_eq_of_general facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel general]
    exact general
  have lift_cumulative : ContextualDependentCumulative.cumulativeRound facts roots heads algebra rigid complete
      declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck →
      generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem ≠ .stuck := fun cumulative => by
    rw [generalRound_eq_of_cumulative facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel cumulative]
    exact cumulative
  rcases reads with read | read | read | read | read | read
  · exact lift_anywhere (lift_inPlace (lift_older (lift_general (lift_cumulative
      (ContextualDependentCumulative.cumulativeRound_not_stuck_of_rule facts roots heads algebra rigid complete
        declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel read)))))
  · exact lift_anywhere (lift_inPlace (lift_older (lift_general (generalRound_not_stuck_of_rule facts roots heads
      algebra rigid complete declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel
      read))))
  · exact lift_anywhere (lift_inPlace (lift_older (olderRound_not_stuck_of_rule facts roots heads algebra rigid
      complete declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel read)))
  · exact lift_anywhere (lift_inPlace (inPlaceRound_not_stuck_of_rule facts roots heads algebra rigid complete
      declared choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel read))
  · exact lift_anywhere (anywhereRound_not_stuck_of_rule facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel read)
  · exact deadRound_not_stuck_of_deadRule facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening fuel read

/-- **Every reader of the dead-binder family, at one budget**: R110's twelve rows of the flexible round, or a reader
of an outer round. -/
def AllReads (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  Reads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ∨
    OuterReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique strengthening fuel problem

/-- **Firing from eventual reading**: if on every nonempty store of the permuted class some reader reads from some
budget on, the dead-binder round is eventually not stuck there. -/
theorem firing_of_allReads
    (reads : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        AllReads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique rootComplete strengthening larger problem)
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (permuted : PermutedMiller S.levels problem)
    (nonempty : problem ≠ []) :
    ∃ bound, ∀ larger, bound ≤ larger →
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening larger problem ≠ .stuck := by
  obtain ⟨bound, eventually⟩ := reads permuted nonempty
  refine ⟨bound, fun larger enough => ?_⟩
  rcases eventually larger enough with flexible | outer
  · exact deadRound_not_stuck_of_reads facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening larger flexible
  · exact deadRound_not_stuck_of_outerReads facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete strengthening larger outer

/-- **Firing from eventual reading of the flexible round's rows.** -/
theorem firing_of_reads
    (reads : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        Reads facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique rootComplete larger problem)
    {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (permuted : PermutedMiller S.levels problem)
    (nonempty : problem ≠ []) :
    ∃ bound, ∀ larger, bound ≤ larger →
      deadRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete strengthening larger problem ≠ .stuck := by
  obtain ⟨bound, eventually⟩ := reads permuted nonempty
  exact ⟨bound, fun larger enough => deadRound_not_stuck_of_reads facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete strengthening larger
    (eventually larger enough)⟩

end General

/-! ## The tower -/

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4 ContextualDependentConversionBudget ContextualDependentDynamicFragment
open ContextualDependentAcceptance3

/-- R110's rows for the tower controls at one budget. -/
abbrev TowerReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  Reads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) fuel problem

/-- **Conditional decision for the tower's dead-binder family, from eventual reading**, on every store of the dynamic
pattern fragment. At the tower the hypothesis fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_dead_decided_of_reads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (deadTower.solver larger) problem larger = run (deadTower.solver budget) problem budget ∧
      ((∃ state finished, run (deadTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (deadTower.solver larger) problem larger = .refuted absent)) :=
  tower_dead_decided_of_firing
    (fun permuted nonempty => firing_of_reads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening reads permuted
      nonempty)
    inside

/-- Every reader of the tower's dead-binder family at one budget. -/
abbrev TowerAllReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  AllReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Conditional decision for the tower's dead-binder family, from eventual reading by any of its readers**, on every
store of the dynamic pattern fragment. At the tower the hypothesis fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_dead_decided_of_allReads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller setting.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger → TowerAllReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (deadTower.solver larger) problem larger = run (deadTower.solver budget) problem budget ∧
      ((∃ state finished, run (deadTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (deadTower.solver larger) problem larger = .refuted absent)) :=
  tower_dead_decided_of_firing
    (fun permuted nonempty => firing_of_allReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
      ContextualDependentInversion.Controls.reducer (fun _ => none)
      ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
      ContextualDependentGeneralPattern.DispatchControls.certifyNormal
      ContextualDependentNormalCheckingTower.head_typing_unique
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening reads permuted
      nonempty)
    inside

end ContextualDependentCoverageReadersHalf
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
