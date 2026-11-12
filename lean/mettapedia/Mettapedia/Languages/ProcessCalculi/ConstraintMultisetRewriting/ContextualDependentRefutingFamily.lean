import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentReadingFamily

/-!
# A family above a family, by a refutation

Given the round of a family (`below`) and a refutation of stores (`refute`), the round of the family above is the
round below, and when that round is stuck, the refutation (`refuteRound`). The construction is the one of
`ContextualDependentEtaDepth.sortRound`, with the family below and the refutation as parameters.

* The family above decides every run that the family below decides, with the same outcome
  (`refute_run_of_below`): it is conservative by construction, and its only new outcomes are refutations.
* Its round moves wherever the refutation reads the store (`refuteRound_not_stuck_of_refuted`).
* It is eventually constant where the round below and the refutation are (`refuteRound_const`); its progress is
  the progress of the family below (`refuteRound_closure`).
* A conditional decision follows from firing as for the families below (`refute_decided_of_firing`). At the tower's
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

section Refuting

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (below : (fuel : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem)
  (refute : (fuel : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Option (PLift (¬ (frames S.levels).Solvable problem)))

/-- **The round**: the round below; when it is stuck, the refutation. -/
noncomputable def refuteRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  orElse (below fuel problem) (refutedRound (refute fuel problem))

/-- **The family above**, at the weight rank. -/
noncomputable def refuteFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := refuteRound facts roots heads algebra rigid complete below refute fuel

/-! ## Conservativity and readers -/

theorem refuteRound_eq_of_below (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : below fuel problem ≠ .stuck) :
    refuteRound facts roots heads algebra rigid complete below refute fuel problem = below fuel problem := by
  unfold refuteRound
  cases computed : below fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the family below decides, the family above decides with the same outcome.** -/
theorem refute_run_of_below (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((belowFamily facts roots heads algebra rigid complete below).solver fuel) problem
      rounds).Decided) :
    run ((refuteFamily facts roots heads algebra rigid complete below refute).solver fuel) problem rounds =
      run ((belowFamily facts roots heads algebra rigid complete below).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => below fuel problem)
    (fun problem => refuteRound facts roots heads algebra rigid complete below refute fuel problem)
    (fun _ moving => refuteRound_eq_of_below facts roots heads algebra rigid complete below refute fuel moving)
    rounds _ decided

/-- **The reader**: the round moves wherever the refutation reads the store. -/
theorem refuteRound_not_stuck_of_refuted (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (refute fuel problem).isSome) :
    refuteRound facts roots heads algebra rigid complete below refute fuel problem ≠ .stuck := by
  unfold refuteRound
  obtain ⟨absent, computed⟩ := Option.isSome_iff_exists.mp read
  cases below fuel problem with
  | stuck =>
      change refutedRound (refute fuel problem) ≠ .stuck
      rw [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-! ## Eventual constancy -/

variable (belowConst : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel => below fuel problem)
  (refuteConst : ∀ {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)),
    EventuallyConst fun fuel => refute fuel problem)

include belowConst refuteConst in
/-- **The round is eventually constant on every store.** -/
theorem refuteRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => refuteRound facts roots heads algebra rigid complete below refute fuel problem :=
  EventuallyConst.of_eq (fun _ => rfl)
    (EventuallyConst.comp (fun pair : Round S.levels (weightRank facts roots heads algebra rigid complete) problem ×
        Option (PLift (¬ (frames S.levels).Solvable problem)) => orElse pair.1 (refutedRound pair.2))
      (EventuallyConst.pair (belowConst problem) (refuteConst problem)))

/-! ## Closure -/

variable (belowClosure : ∀ fuel : Nat,
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem => below fuel problem)

include belowClosure in
/-- **Closure of the round** at every budget: its progress is the progress of the family below. -/
theorem refuteRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      refuteRound facts roots heads algebra rigid complete below refute fuel problem := by
  intro Θ problem update smaller permuted fired
  change orElse (below fuel problem) (refutedRound (refute fuel problem)) = .progress update smaller at fired
  cases computed : below fuel problem with
  | stuck =>
      rw [computed] at fired
      change refutedRound (refute fuel problem) = .progress update smaller at fired
      cases refuted : refute fuel problem with
      | none =>
          rw [refuted] at fired
          cases fired
      | some absent =>
          rw [refuted] at fired
          cases fired
  | progress first firstSmaller =>
      rw [computed] at fired
      cases fired
      exact belowClosure fuel _ _ _ permuted computed
  | refuted absent =>
      rw [computed] at fired
      cases fired

include belowConst refuteConst belowClosure in
/-- **Conditional decision for the family above, from firing**, on every store of the dynamic pattern fragment, with
a principal answer or a certified refutation, constant at every larger budget. At the tower's setting the conclusion
fails on `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`), so there firing fails.
For every store, runs are exact; on `crossStore` they stop postponed
(`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem refute_decided_of_firing
    (firing : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, PermutedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        refuteRound facts roots heads algebra rigid complete below refute larger problem ≠ .stuck)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((refuteFamily facts roots heads algebra rigid complete below refute).solver larger) problem larger =
        run ((refuteFamily facts roots heads algebra rigid complete below refute).solver budget) problem budget ∧
      ((∃ state finished,
          run ((refuteFamily facts roots heads algebra rigid complete below refute).solver larger) problem
            larger = .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent,
          run ((refuteFamily facts roots heads algebra rigid complete below refute).solver larger) problem
            larger = .refuted absent)) :=
  (Settled.ofConst (refuteFamily facts roots heads algebra rigid complete below refute)
    (fun problem => refuteRound_const facts roots heads algebra rigid complete below refute belowConst refuteConst
      problem)
    (fun problem => PermutedMiller S.levels problem)
    (fun held nonempty => by
      obtain ⟨bound, fires⟩ := firing held nonempty
      exact ⟨bound, fun larger enough => ⟨fires larger enough, fun {update} {smaller} fired =>
        refuteRound_closure facts roots heads algebra rigid complete below refute belowClosure larger _ update
          smaller held fired⟩⟩)).decided
    (permutedMiller_of_fragment inside)

end Refuting

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
