import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepExact
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesCumulativePrincipal

/-!
# A conditional decision on stores with exact arguments

The dynamic pattern fragment read over a cumulative tower holds stores without a principal answer
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`): an unknown is applied to a local declared
below the type the unknown declares for its argument. With the inclusion of one universe in the next written out,
that argument is not a variable. The conditional decision here is therefore stated on the stores of the fragment with
**exact arguments** (`ContextualDependentSweep.storeExact`). Outside it such stores are not refused: on `crossStore`
every run stops postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).

* `ExactReached`: a store reached by rounds of the family `withinTower` from a store of the fragment with
  exact arguments. It is in the permuted Miller class (`ExactReached.permuted`).
* **`tower_within_decided_of_uncovered_exact`**: a conditional decision for `withinTower` on stores of the
  fragment with exact arguments. Its one hypothesis is the hypothesis of
  `ContextualDependentEtaDepth.tower_within_decided_of_uncovered`, asked only of the stores of `ExactReached`.
* `cross_boundary`: `crossStore` is in the fragment, does not have exact arguments, and has no principal answer.
  So it is outside the statement, and the instance that refutes the hypothesis asked of every store of the
  permuted class (`tower_sort_uncovered_false`) is not an instance of this one.

* `stuck_keeps_solutions`: outside the statement a run may end stuck; the state it reports is an update of the
  original store, so its answer together with its remaining equations has exactly the solutions of the original
  store. This holds for every family and every store, by the definition of the driver's state.

Not proved: that every store of `ExactReached` has exact arguments (the test compares codes, and a round may
rewrite a declared type to an equal code), and the hypothesis itself. Against the hypothesis stands `narrowStore`,
exact and with a principal answer, on which the top family's compiled run reads `stuck` at budget 16
(`ContextualDependentSweep.Witnesses.narrow_exact_gap_of_ending`): the narrowing of a declaration is missing.
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

/-- The round of `withinTower` is eventually constant on every store. -/
theorem tower_withinRound_const {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => withinTower.round fuel problem :=
  readRound_const (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => sortTower.round fuel problem) (fun fuel _ problem => towerWithin fuel problem)
    (fun fuel _ problem => towerWithin_rank fuel problem) (fun problem => tower_sortRound_const problem)
    (fun problem => towerWithin_const problem) problem

/-- The round of `withinTower` keeps the permuted Miller class. -/
theorem tower_withinRound_closure (fuel : Nat) :
    RoundKeeps (fun problem => PermutedMiller setting.levels problem) fun problem =>
      withinTower.round fuel problem :=
  readRound_closure (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun fuel _ problem => sortTower.round fuel problem) (fun fuel _ problem => towerWithin fuel problem)
    (fun fuel _ problem => towerWithin_rank fuel problem) (fun fuel => tower_sortRound_closure fuel)
    (fun fuel _ _ permuted => towerWithin_keeps fuel permuted) fuel

/-- **A store reached by rounds of `withinTower` from a store of the fragment with exact arguments.** -/
inductive ExactReached : {Γ : Context setting.R} → EquationStore (TotalTerm Γ) → Prop where
  | start {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)} :
      InFragmentStore problem → storeExact problem = true → ExactReached problem
  | step {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)} (fuel : Nat)
      {update : Update setting.levels problem}
      {smaller : ContextualDependentWorklist.Below (withinTower.rank update.remaining) (withinTower.rank problem)} :
      ExactReached problem → withinTower.round fuel problem = .progress update smaller →
      ExactReached update.remaining

/-- A reached store is in the permuted Miller class. -/
theorem ExactReached.permuted {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)}
    (reached : ExactReached problem) : PermutedMiller setting.levels problem := by
  induction reached with
  | start inside _ => exact permutedMiller_of_fragment inside
  | step fuel _ fired ih => exact tower_withinRound_closure fuel _ _ _ ih fired

/-- **Conditional decision for `withinTower` on stores of the fragment with exact arguments, from the census rows
outside the rows read**: if, on every store reached by the family from a store of the fragment with exact
arguments, every census head of a constant preparation whose η-long opened sides are of a census kind and outside
the rows read is read by a reader of the family from some budget on, then the family decides every store of the
dynamic pattern fragment with exact arguments, with a principal answer or a certified refutation, constant at every
larger budget. The hypothesis is not proved; `narrowStore`, exact and with a principal answer, needs a narrowing
reader the families lack (`ContextualDependentSweep.Witnesses.narrow_exact_gap_of_ending`). For every store, runs are
exact (`stuck_keeps_solutions`, `UnificationWithLevels.DependentFibre.outcome_exact`). -/
theorem tower_within_decided_of_uncovered_exact
    (uncovered : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      ExactReached problem → problem ≠ [] → ∀ threshold,
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
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem)
    (exact : storeExact problem = true) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (withinTower.solver larger) problem larger = run (withinTower.solver budget) problem budget ∧
      ((∃ state finished, run (withinTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (withinTower.solver larger) problem larger = .refuted absent)) :=
  (Settled.ofConst withinTower (fun problem => tower_withinRound_const problem)
    (fun problem => ExactReached problem)
    (fun {_} {problem} held nonempty => by
      have permuted := held.permuted
      have reads : ∃ bound, ∀ larger, bound ≤ larger → TowerWithinReads larger problem := by
        obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
        by_cases covered : MixedCoveredHead equation
        · obtain ⟨bound, mixed⟩ := tower_mixedReads_of_covered constant member normal head.1 covered
          exact ⟨bound, fun larger enough => .inl (.inl (.inl (.inl (.inl (mixed larger enough)))))⟩
        · have prepared := ContextualDependentCumulativeClosure.prepare_keeps (S := setting) (fun _ => none)
            (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts
            TowerModel.roots TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing
            threshold problem permuted
          have sides := PermutedMiller.sides_of_mem prepared member
          exact uncovered held nonempty threshold constant equation member normal head sides
            (eta_kind sides normal.2.1 normal.2.2.2) covered
      obtain ⟨bound, read⟩ := reads
      refine ⟨bound, fun larger enough => ⟨?_, fun {update} {smaller} fired => .step larger held fired⟩⟩
      rcases read larger enough with below | lowered
      · have moving := tower_sortRound_not_stuck_of_reads larger below
        rw [tower_withinRound_eq_of_sort larger moving]
        exact moving
      · exact tower_withinRound_not_stuck_of_read larger
          (tower_sortRound_not_stuck_of_reads larger lowered))).decided
    (.start inside exact)

/-- **A stuck run keeps the knowledge of the store.** The state of a run, in particular the state a stuck run
reports, is an update of the original store: every solution of its remaining equations, composed with its answer,
solves the original store, and every solution of the original store is such a composite, up to the equality of
terms of the frame. So the answer so far together with the remaining equations has exactly the solutions of the
original store. -/
theorem stuck_keeps_solutions {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    (state : Update setting.levels original) :
    (∀ (Δ : Context setting.R) (residual : Δ ⟶ state.target),
        (frames setting.levels).Models residual state.remaining →
          (frames setting.levels).Models (residual ≫ state.answer) original) ∧
      ∀ (Δ : Context setting.R) (solution : Δ ⟶ Γ), (frames setting.levels).Models solution original →
        ∃ residual : Δ ⟶ state.target, (frames setting.levels).Models residual state.remaining ∧
          ∀ term : TotalTerm Γ,
            (frames setting.levels).E (term.reindex solution) (term.reindex (residual ≫ state.answer)) :=
  ⟨state.sound, state.complete⟩

/-- `crossStore` does not have exact arguments: `Y`, which declares `U1` for its argument, is applied to a local of
`U0`. -/
theorem cross_not_exact : storeExact ContextualDependentSweep.Witnesses.crossStore = false := by decide +kernel

/-- **The boundary**: `crossStore` is in the dynamic pattern fragment, does not have exact arguments, and has no
principal answer. -/
theorem cross_boundary :
    InFragmentStore ContextualDependentSweep.Witnesses.crossStore ∧
      storeExact ContextualDependentSweep.Witnesses.crossStore = false ∧
      ∀ {Δ : Context setting.R} (answer : Δ ⟶ ContextualDependentSweep.Witnesses.ctxCross),
        ¬ (frames setting.levels).Principal ContextualDependentSweep.Witnesses.crossStore answer :=
  ⟨ContextualDependentSweep.Witnesses.cross_in_fragment, cross_not_exact,
    fun answer => ContextualDependentSweep.Witnesses.cross_no_principal answer⟩

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
