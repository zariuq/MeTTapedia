import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimReads
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursBoundFamily

/-!
# A conditional decision for the family with the occurs rule at a bound variable, from the rows outside the rows read

The reduction of `ContextualDependentElimReads.tower_elimSigma_decided_of_uncovered`, for the family above it: the
remaining hypothesis asks a reader of **this** family, which has one reader more (the occurs rule at a bound
variable), on every census head outside the rows read (`tower_bound_decided_of_uncovered`). At the tower the
hypothesis fails: the conclusion would decide `crossStore`, solvable and without principal answer
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
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentRank ContextualDependentSpinesMany ContextualDependentCoverageReadersHalf
open ContextualDependentConstantHeads ContextualDependentMillerClosure
open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4

/-- **Conditional decision for the tower's family with the occurs rule at a bound variable, from the census rows
outside the rows read**: if every census head of a constant preparation whose η-long opened sides are of a census kind
and outside the rows read is read by a reader of the family from some budget on, the family decides every store of the
dynamic pattern fragment, with a principal answer or a certified refutation, constant at every larger budget. At the
tower the hypothesis fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_bound_decided_of_uncovered
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
          ¬ MixedCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerBoundReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (boundTower.solver larger) problem larger = run (boundTower.solver budget) problem budget ∧
      ((∃ state finished, run (boundTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (boundTower.solver larger) problem larger = .refuted absent)) :=
  tower_bound_decided_of_reads (fun {_} {problem} permuted nonempty => by
      obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
      by_cases covered : MixedCoveredHead equation
      · obtain ⟨bound, mixed⟩ := tower_mixedReads_of_covered constant member normal head.1 covered
        exact ⟨bound, fun larger enough => .inl (.inl (mixed larger enough))⟩
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
