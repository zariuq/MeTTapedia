import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRefutingFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPairClash
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWithinExact

/-!
# The family with the refutation of a universe in a component of a pair

The family above the family that reads every equation at its least annotation through components
(`withinTower`): its round is that family's round, and when that round is stuck, the refutation of
`ContextualDependentEtaDepth.pairClashStore` on the store. It is an instance of
`ContextualDependentEtaDepth.refuteFamily`. The rule only refutes.

* `pairTower`: the family of the tower controls; it is the top family.
* `tower_pair_run_of_within`: it decides every run that `withinTower` decides, with the same outcome.
* `PairReached`, **`tower_pair_decided_of_uncovered_exact`**: a conditional decision for it on the stores of the
  dynamic pattern fragment with exact arguments. Its one hypothesis: on every store reached by the family from a
  store of the fragment with exact arguments, every census head of a constant preparation whose η-long opened
  sides are of a census kind and outside the rows read is read by a reader of the family from some budget on.
  A reader of the family is a reader of `withinTower` or the refutation of this module.

Not proved: the hypothesis, and that the stores of `PairReached` have exact arguments. Against the hypothesis:
`narrowStore` has exact arguments and a principal answer, and the family is stuck on it wherever its compiled run
reads `stuck`, which it does at budget 16 (`ContextualDependentSweep.Witnesses.narrow_exact_gap_of_ending`); the
missing reader is the narrowing of a declaration. For every store, runs are exact
(`ContextualDependentEtaDepth.stuck_keeps_solutions`, `UnificationWithLevels.DependentFibre.outcome_exact`).
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
open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentSpinesMany ContextualDependentSweep

/-- **The refutation of a universe in a component of a pair**, on a store of the tower, at one budget. -/
def towerPairRefuted (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (PLift (¬ (frames setting.levels).Solvable problem)) :=
  pairClashStore (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentNormalCheckingTower.head_typing_unique
    towerSorts fuel problem

/-- The refutation is eventually constant on every store. -/
theorem towerPairRefuted_const {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => towerPairRefuted fuel problem :=
  pairClashStore_const (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentNormalCheckingTower.head_typing_unique
    ContextualDependentDecisiveFragment.Controls.stable towerSorts problem

/-- **The family of the tower controls**: the top family. -/
noncomputable def pairTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  refuteFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => withinTower.round fuel problem) (fun fuel _ problem => towerPairRefuted fuel problem)

/-- **Every run that `withinTower` decides, this family decides with the same outcome.** -/
theorem tower_pair_run_of_within (fuel rounds : Nat) {Θ : Context setting.R}
    (problem : EquationStore (TotalTerm Θ)) (decided : (run (withinTower.solver fuel) problem rounds).Decided) :
    run (pairTower.solver fuel) problem rounds = run (withinTower.solver fuel) problem rounds :=
  refute_run_of_below (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => withinTower.round fuel problem) (fun fuel _ problem => towerPairRefuted fuel problem)
    fuel rounds problem decided

/-- The round is the round of `withinTower` wherever that round moves. -/
theorem tower_pairRound_eq_of_within (fuel : Nat) {Θ : Context setting.R}
    {problem : EquationStore (TotalTerm Θ)} (moving : withinTower.round fuel problem ≠ .stuck) :
    pairTower.round fuel problem = withinTower.round fuel problem :=
  refuteRound_eq_of_below (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => withinTower.round fuel problem) (fun fuel _ problem => towerPairRefuted fuel problem)
    fuel moving

/-- The round moves wherever the refutation reads the store. -/
theorem tower_pairRound_not_stuck_of_refuted (fuel : Nat) {Θ : Context setting.R}
    {problem : EquationStore (TotalTerm Θ)} (read : (towerPairRefuted fuel problem).isSome) :
    pairTower.round fuel problem ≠ .stuck :=
  refuteRound_not_stuck_of_refuted (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => withinTower.round fuel problem) (fun fuel _ problem => towerPairRefuted fuel problem)
    fuel read

/-- The round is eventually constant on every store. -/
theorem tower_pairRound_const {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => pairTower.round fuel problem :=
  refuteRound_const (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => withinTower.round fuel problem) (fun fuel _ problem => towerPairRefuted fuel problem)
    (fun problem => tower_withinRound_const problem) (fun problem => towerPairRefuted_const problem) problem

/-- The round keeps the permuted Miller class. -/
theorem tower_pairRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller setting.levels problem) fun problem =>
      pairTower.round fuel problem :=
  refuteRound_closure (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => withinTower.round fuel problem) (fun fuel _ problem => towerPairRefuted fuel problem)
    (fun fuel => tower_withinRound_closure fuel) fuel

/-- **Readers of the family at one budget**: a reader of `withinTower`, or the refutation. -/
abbrev TowerPairReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  TowerWithinReads fuel problem ∨ (towerPairRefuted fuel problem).isSome

/-- A reader of the family moves its round. -/
theorem tower_pairRound_not_stuck_of_reads (fuel : Nat) {Θ : Context setting.R}
    {problem : EquationStore (TotalTerm Θ)} (reads : TowerPairReads fuel problem) :
    pairTower.round fuel problem ≠ .stuck := by
  rcases reads with (below | lowered) | refuted
  · have moving := tower_sortRound_not_stuck_of_reads fuel below
    have within : withinTower.round fuel problem ≠ .stuck := by
      rw [tower_withinRound_eq_of_sort fuel moving]
      exact moving
    rw [tower_pairRound_eq_of_within fuel within]
    exact within
  · have within := tower_withinRound_not_stuck_of_read fuel (tower_sortRound_not_stuck_of_reads fuel lowered)
    rw [tower_pairRound_eq_of_within fuel within]
    exact within
  · exact tower_pairRound_not_stuck_of_refuted fuel refuted

/-- **A store reached by rounds of the top family from a store of the fragment with exact arguments.** -/
inductive PairReached : {Γ : Context setting.R} → EquationStore (TotalTerm Γ) → Prop where
  | start {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)} :
      InFragmentStore problem → storeExact problem = true → PairReached problem
  | step {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)} (fuel : Nat)
      {update : Update setting.levels problem}
      {smaller : ContextualDependentWorklist.Below (pairTower.rank update.remaining) (pairTower.rank problem)} :
      PairReached problem → pairTower.round fuel problem = .progress update smaller →
      PairReached update.remaining

/-- A reached store is in the permuted Miller class. -/
theorem PairReached.permuted {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}
    (reached : PairReached problem) : PermutedMiller setting.levels problem := by
  induction reached with
  | start inside _ => exact permutedMiller_of_fragment inside
  | step fuel _ fired ih => exact tower_pairRound_closure fuel _ _ _ ih fired

/-- **Conditional decision for the top family on stores of the fragment with exact arguments, from the census rows
outside the rows read**: if, on every store reached by the family from a store of the fragment with exact
arguments, every census head of a constant preparation whose η-long opened sides are of a census kind and outside
the rows read is read by a reader of the family from some budget on, then the family decides every store of the
dynamic pattern fragment with exact arguments, with a principal answer or a certified refutation, constant at every
larger budget. The hypothesis is not proved, and the narrowing witness stands against it: `narrowStore`, exact and
with a principal answer, on which the family's compiled run reads `stuck` at budget 16
(`ContextualDependentSweep.Witnesses.narrow_exact_gap_of_ending`). For every store, runs are exact
(`UnificationWithLevels.DependentFibre.outcome_exact`). -/
theorem tower_pair_decided_of_uncovered_exact
    (uncovered : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PairReached problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ContextualDependentShortClosure.FragmentSidesMiller equation →
          Kind (openedFlexible (piCount equation.1.1.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.1.2.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.2.2.code)) →
          ¬ MixedCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerPairReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem)
    (exact : storeExact problem = true) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (pairTower.solver larger) problem larger = run (pairTower.solver budget) problem budget ∧
      ((∃ state finished, run (pairTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (pairTower.solver larger) problem larger = .refuted absent)) :=
  (Settled.ofConst pairTower (fun problem => tower_pairRound_const problem)
    (fun problem => PairReached problem)
    (fun {_} {problem} held nonempty => by
      have permuted := held.permuted
      have reads : ∃ bound, ∀ larger, bound ≤ larger → TowerPairReads larger problem := by
        obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
        by_cases covered : MixedCoveredHead equation
        · obtain ⟨bound, mixed⟩ := tower_mixedReads_of_covered constant member normal head.1 covered
          exact ⟨bound, fun larger enough => .inl (.inl (.inl (.inl (.inl (.inl (mixed larger enough))))))⟩
        · have prepared := ContextualDependentCumulativeClosure.prepare_keeps (S := setting) (fun _ => none)
            (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts
            TowerModel.roots TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing
            threshold problem permuted
          have sides := PermutedMiller.sides_of_mem prepared member
          exact uncovered held nonempty threshold constant equation member normal head sides
            (eta_kind sides normal.2.1 normal.2.2.2) covered
      obtain ⟨bound, read⟩ := reads
      exact ⟨bound, fun larger enough => ⟨tower_pairRound_not_stuck_of_reads larger (read larger enough),
        fun {update} {smaller} fired => .step larger held fired⟩⟩)).decided
    (.start inside exact)

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
