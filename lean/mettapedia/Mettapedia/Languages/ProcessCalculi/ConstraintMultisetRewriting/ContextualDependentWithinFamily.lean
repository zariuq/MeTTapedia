import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentReadingFamily
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentLeastWithin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSortFamily

/-!
# The family that reads every equation at its least annotation through the components of Σ types

The family above the family with the refutation of a universe (`sortTower`): its round is that family's round, and
when that round is stuck, that family's round again on the store with every universe position of every annotation
at its least candidate, through codomains of Π types and components of Σ types
(`ContextualDependentEtaDepth.lowerWithinUpdate`). It is an instance of
`ContextualDependentEtaDepth.readFamily`.

* `withinTower`: the family of the tower controls.
* `tower_within_run_of_sort`: it decides every run that `sortTower` decides, with the same outcome.
* `tower_within_decided_of_uncovered`: a conditional decision for it. At the tower its hypothesis fails: the
  conclusion would decide `crossStore`, solvable and without principal answer
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
open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentSpinesMany

/-- **The tower's store read at its least annotations through components**, at one budget. -/
abbrev towerWithin (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    Update setting.levels problem :=
  lowerWithinUpdate (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer towerSorts fuel problem

/-- The reading keeps the weight rank. -/
theorem towerWithin_rank (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    sortTower.rank (towerWithin fuel problem).remaining = sortTower.rank problem :=
  lowerWithinUpdate_rank (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer towerSorts fuel problem

/-- **The family of the tower controls.** -/
noncomputable def withinTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  readFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => sortTower.round fuel problem) (fun fuel _ problem => towerWithin fuel problem)
    (fun fuel _ problem => towerWithin_rank fuel problem)

/-- The round of `sortTower` is eventually constant on every store. -/
theorem tower_sortRound_const {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => sortTower.round fuel problem :=
  sortRound_const (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts
    ContextualDependentDecisiveFragment.Controls.stable problem

/-- The round of `sortTower` keeps the permuted Miller class. -/
theorem tower_sortRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller setting.levels problem) fun problem => sortTower.round fuel problem :=
  sortRound_closure (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts
    tower_stronglyNormalizing tower_reducer_directed fuel

/-- The reading is eventually constant on every store. -/
theorem towerWithin_const {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => towerWithin fuel problem :=
  lowerWithinUpdate_const (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentDecisiveFragment.Controls.stable towerSorts
    problem

/-- The reading keeps the permuted Miller class. -/
theorem towerWithin_keeps (fuel : Nat) {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller setting.levels problem) :
    PermutedMiller setting.levels (towerWithin fuel problem).remaining :=
  lowerWithinUpdate_keeps (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer towerSorts fuel permuted

/-- **Every run that `sortTower` decides, this family decides with the same outcome.** -/
theorem tower_within_run_of_sort (fuel rounds : Nat) {Θ : Context setting.R}
    (problem : EquationStore (TotalTerm Θ)) (decided : (run (sortTower.solver fuel) problem rounds).Decided) :
    run (withinTower.solver fuel) problem rounds = run (sortTower.solver fuel) problem rounds :=
  read_run_of_below (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => sortTower.round fuel problem) (fun fuel _ problem => towerWithin fuel problem)
    (fun fuel _ problem => towerWithin_rank fuel problem) fuel rounds problem decided

/-- The round is the round of `sortTower` wherever that round moves. -/
theorem tower_withinRound_eq_of_sort (fuel : Nat) {Θ : Context setting.R}
    {problem : EquationStore (TotalTerm Θ)} (moving : sortTower.round fuel problem ≠ .stuck) :
    withinTower.round fuel problem = sortTower.round fuel problem :=
  readRound_eq_of_below (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => sortTower.round fuel problem) (fun fuel _ problem => towerWithin fuel problem)
    (fun fuel _ problem => towerWithin_rank fuel problem) fuel moving

/-- The round moves wherever the round of `sortTower` moves on the store as read. -/
theorem tower_withinRound_not_stuck_of_read (fuel : Nat) {Θ : Context setting.R}
    {problem : EquationStore (TotalTerm Θ)}
    (moving : sortTower.round fuel (towerWithin fuel problem).remaining ≠ .stuck) :
    withinTower.round fuel problem ≠ .stuck :=
  readRound_not_stuck_of_read (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => sortTower.round fuel problem) (fun fuel _ problem => towerWithin fuel problem)
    (fun fuel _ problem => towerWithin_rank fuel problem) fuel moving

/-- **Readers of the family at one budget**: a reader of `sortTower`, on the store or on the store as read. -/
abbrev TowerWithinReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  TowerSortReads fuel problem ∨ TowerSortReads fuel (towerWithin fuel problem).remaining

/-- A reader of `sortTower` moves its round. -/
theorem tower_sortRound_not_stuck_of_reads (fuel : Nat) {Θ : Context setting.R}
    {problem : EquationStore (TotalTerm Θ)} (reads : TowerSortReads fuel problem) :
    sortTower.round fuel problem ≠ .stuck :=
  sortRound_not_stuck_of_reads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening towerSorts fuel
    reads

/-- **Conditional decision for the family, from firing**, on every store of the dynamic pattern fragment. At the
tower firing fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_within_decided_of_firing
    (firing : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] →
        ∃ bound, ∀ larger, bound ≤ larger → withinTower.round larger problem ≠ .stuck)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (withinTower.solver larger) problem larger = run (withinTower.solver budget) problem budget ∧
      ((∃ state finished, run (withinTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (withinTower.solver larger) problem larger = .refuted absent)) :=
  read_decided_of_firing (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => sortTower.round fuel problem) (fun fuel _ problem => towerWithin fuel problem)
    (fun fuel _ problem => towerWithin_rank fuel problem) (fun problem => tower_sortRound_const problem)
    (fun problem => towerWithin_const problem) (fun fuel => tower_sortRound_closure fuel)
    (fun fuel _ _ permuted => towerWithin_keeps fuel permuted) firing inside

/-- **Conditional decision for the family, from its readers.** At the tower the hypothesis fails: the conclusion
would decide `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). -/
theorem tower_within_decided_of_reads
    (reads : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] →
        ∃ bound, ∀ larger, bound ≤ larger → TowerWithinReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (withinTower.solver larger) problem larger = run (withinTower.solver budget) problem budget ∧
      ((∃ state finished, run (withinTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (withinTower.solver larger) problem larger = .refuted absent)) :=
  tower_within_decided_of_firing (fun held nonempty => by
    obtain ⟨bound, read⟩ := reads held nonempty
    refine ⟨bound, fun larger enough => ?_⟩
    rcases read larger enough with below | lowered
    · have moving := tower_sortRound_not_stuck_of_reads larger below
      rw [tower_withinRound_eq_of_sort larger moving]
      exact moving
    · exact tower_withinRound_not_stuck_of_read larger (tower_sortRound_not_stuck_of_reads larger lowered)) inside

/-- **Conditional decision for the family, from the census rows outside the rows read**: if every census head of a
constant preparation whose η-long opened sides are of a census kind and outside the rows read is read by a reader
of the family from some budget on, the family decides every store of the dynamic pattern fragment, with a principal
answer or a certified refutation, constant at every larger budget. At the tower the hypothesis fails: the conclusion
would decide `crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).

A reader of the family is a reader of `sortTower` on the store, or on the store with every universe position of
every annotation at its least candidate. -/
theorem tower_within_decided_of_uncovered
    (uncovered : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ContextualDependentShortClosure.FragmentSidesMiller equation →
          Kind (openedFlexible (piCount equation.1.1.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.1.2.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.2.2.code)) →
          ¬ MixedCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerWithinReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (withinTower.solver larger) problem larger = run (withinTower.solver budget) problem budget ∧
      ((∃ state finished, run (withinTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (withinTower.solver larger) problem larger = .refuted absent)) :=
  tower_within_decided_of_reads (fun {_} {problem} permuted nonempty => by
      obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
      by_cases covered : MixedCoveredHead equation
      · obtain ⟨bound, mixed⟩ := tower_mixedReads_of_covered constant member normal head.1 covered
        exact ⟨bound, fun larger enough => .inl (.inl (.inl (.inl (.inl (mixed larger enough)))))⟩
      · have prepared := ContextualDependentCumulativeClosure.prepare_keeps (S := setting) (fun _ => none)
          (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
          TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing threshold problem
          permuted
        have sides := PermutedMiller.sides_of_mem prepared member
        exact uncovered permuted nonempty threshold constant equation member normal head sides
          (eta_kind sides normal.2.1 normal.2.2.2) covered)
    inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
