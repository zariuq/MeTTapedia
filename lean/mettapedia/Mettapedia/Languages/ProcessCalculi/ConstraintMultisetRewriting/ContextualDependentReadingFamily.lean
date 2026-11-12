import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentLeastFamily

/-!
# A family above a family, by a reading of the store

A **reading** of a store is an update with exactly the store's solutions that keeps the weight rank: it is not a
step. Given the round of a family (`below`) and a reading, the round of the family above is the round below, and
when that round is stuck, the round below on the store as read (`readRound`). The construction is the one of
`ContextualDependentEtaDepth.leastRound`, with the family below and the reading as parameters.

* The family above decides every run that the family below decides, with the same outcome (`read_run_of_below`):
  it is conservative by construction.
* Its round moves wherever the round below moves on the store as read (`readRound_not_stuck_of_read`).
* It is eventually constant where the round below and the reading are (`readRound_const`), and keeps the permuted
  Miller class where they do (`readRound_closure`).
* A conditional decision follows from firing as for the families below (`read_decided_of_firing`). At the tower's
  setting firing fails: the conclusion would decide `crossStore`, solvable and without principal answer
  (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
  `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
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

section Reading

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (below : (fuel : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem)
  (reading : (fuel : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) → Update S.levels problem)
  (readingRank : ∀ (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    weightRank facts roots heads algebra rigid complete (reading fuel problem).remaining =
      weightRank facts roots heads algebra rigid complete problem)

/-- **The round**: the round below; when it is stuck, the round below on the store as read. -/
noncomputable def readRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (below fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete (reading fuel problem) (readingRank fuel problem)
      (below fuel (reading fuel problem).remaining))

/-- **The family above**, at the weight rank. -/
noncomputable def readFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := readRound facts roots heads algebra rigid complete below reading readingRank fuel

/-- The round below, as a family at the weight rank. -/
noncomputable def belowFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := below fuel

/-! ## Conservativity and readers -/

theorem readRound_eq_of_below (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : below fuel problem ≠ .stuck) :
    readRound facts roots heads algebra rigid complete below reading readingRank fuel problem =
      below fuel problem := by
  unfold readRound
  cases computed : below fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the family below decides, the family above decides with the same outcome.** -/
theorem read_run_of_below (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((belowFamily facts roots heads algebra rigid complete below).solver fuel) problem
      rounds).Decided) :
    run ((readFamily facts roots heads algebra rigid complete below reading readingRank).solver fuel) problem
        rounds =
      run ((belowFamily facts roots heads algebra rigid complete below).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => below fuel problem)
    (fun problem => readRound facts roots heads algebra rigid complete below reading readingRank fuel problem)
    (fun _ moving => readRound_eq_of_below facts roots heads algebra rigid complete below reading readingRank fuel
      moving)
    rounds _ decided

/-- **The reader**: the round moves wherever the round below moves on the store as read. -/
theorem readRound_not_stuck_of_read (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : below fuel (reading fuel problem).remaining ≠ .stuck) :
    readRound facts roots heads algebra rigid complete below reading readingRank fuel problem ≠ .stuck := by
  unfold readRound
  cases below fuel problem with
  | stuck =>
      exact liftCollapsed_not_stuck facts roots heads algebra rigid complete _ (readingRank fuel problem) moving
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-! ## Eventual constancy -/

theorem readRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (readRound facts roots heads algebra rigid complete below reading readingRank fuel problem) =
      (roundView (below fuel problem)).or
        (liftView (reading fuel problem) (roundView (below fuel (reading fuel problem).remaining))) := by
  unfold readRound
  rw [roundView_orElse, liftCollapsed_view]

variable (belowConst : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel => below fuel problem)
  (readingConst : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel => reading fuel problem)

include belowConst readingConst in
/-- **The round is eventually constant on every store.** -/
theorem readRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      readRound facts roots heads algebra rigid complete below reading readingRank fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => readRound_view facts roots heads algebra rigid complete below reading
    readingRank fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (belowConst problem))
      (EventuallyConst.dep (h := fun fuel => reading fuel problem)
        (k := fun fuel prepared => liftView prepared (roundView (below fuel prepared.remaining)))
        (readingConst problem)
        (fun prepared => EventuallyConst.comp (fun round => liftView prepared (roundView round))
          (belowConst prepared.remaining))))

/-! ## Closure -/

variable (belowClosure : ∀ fuel : Nat,
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem => below fuel problem)
  (readingKeeps : ∀ (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)},
    PermutedMiller S.levels problem → PermutedMiller S.levels (reading fuel problem).remaining)

include belowClosure readingKeeps in
/-- **Closure of the round** at every budget. -/
theorem readRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      readRound facts roots heads algebra rigid complete below reading readingRank fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (below fuel problem)
    (liftCollapsed facts roots heads algebra rigid complete (reading fuel problem) (readingRank fuel problem)
      (below fuel (reading fuel problem).remaining)) = .progress update smaller at fired
  cases computed : below fuel problem with
  | stuck =>
      rw [computed] at fired
      exact liftCollapsed_keeps facts roots heads algebra rigid complete
        (fun problem => PermutedMiller S.levels problem) (reading fuel problem) (readingRank fuel problem)
        (fun first firstSmaller inner => belowClosure fuel _ first firstSmaller (readingKeeps fuel permuted) inner)
        fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact belowClosure fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include belowConst readingConst belowClosure readingKeeps in
/-- **Conditional decision for the family above, from firing**, on every store of the dynamic pattern fragment, with
a principal answer or a certified refutation, constant at every larger budget. At the tower's setting the conclusion
fails on `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there firing fails.
For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem read_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        readRound facts roots heads algebra rigid complete below reading readingRank larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((readFamily facts roots heads algebra rigid complete below reading readingRank).solver larger) problem
          larger =
        run ((readFamily facts roots heads algebra rigid complete below reading readingRank).solver budget) problem
          budget ∧
      ((∃ state finished,
          run ((readFamily facts roots heads algebra rigid complete below reading readingRank).solver larger)
            problem larger = .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent,
          run ((readFamily facts roots heads algebra rigid complete below reading readingRank).solver larger)
            problem larger = .refuted absent)) :=
  (Settled.ofConst (readFamily facts roots heads algebra rigid complete below reading readingRank)
    (fun problem => readRound_const facts roots heads algebra rigid complete below reading readingRank belowConst
      readingConst problem)
    (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        readRound_closure facts roots heads algebra rigid complete below reading readingRank belowClosure
          readingKeeps larger _ update smaller held fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Reading

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
