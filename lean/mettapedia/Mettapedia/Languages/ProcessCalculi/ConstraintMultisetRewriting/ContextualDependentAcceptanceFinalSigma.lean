import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsPieces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthSigma

/-!
# Acceptance for the Σ family, reduced to the census rows not yet read

The Σ family's readers contain the piece family's (`SigmaReads`), so every census row the piece family reads is read
by the Σ family (`tower_sigmaReads_of_covered`), and **the Σ family decides every store of the dynamic pattern
fragment, with a principal answer or a certified refutation, constant at every larger budget, as soon as every census
head of a constant preparation outside the covered rows (`PieceCoveredHead`) is read** by the Σ family from some
budget on (`tower_sigma_decided_of_uncovered`, `tower_sigma_decided_of_uncovered_kinds`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentCoverageReadersHalf ContextualDependentConstantHeads ContextualDependentMillerClosure
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4

/-- **A covered census head is read** by the Σ family from some budget on. -/
theorem tower_sigmaReads_of_covered {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (covered : PieceCoveredHead equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerSigmaReads larger problem := by
  obtain ⟨bound, reads⟩ := tower_pieceReads_of_covered constant member normal types covered
  exact ⟨bound, fun larger enough => .inl (reads larger enough)⟩

/-- **Acceptance for the tower's Σ family, reduced to the census rows not yet read**: if every census head of a
constant preparation outside the covered rows is read from some budget on, the family decides every store of the
dynamic pattern fragment, with a principal answer or a certified refutation, constant at every larger budget. -/
theorem tower_sigma_decided_of_uncovered
    (uncovered : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ¬ PieceCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerSigmaReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (sigmaTower.solver larger) problem larger = run (sigmaTower.solver budget) problem budget ∧
      ((∃ state finished, run (sigmaTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (sigmaTower.solver larger) problem larger = .refuted absent)) :=
  tower_sigma_decided_of_sigmaReads (fun permuted nonempty => by
      obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
      by_cases covered : PieceCoveredHead equation
      · exact tower_sigmaReads_of_covered constant member normal head.1 covered
      · exact uncovered permuted nonempty threshold constant equation member normal head covered)
    inside

/-- **The same, with the census kind of the η-long opened sides available.** -/
theorem tower_sigma_decided_of_uncovered_kinds
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
          ¬ PieceCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerSigmaReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (sigmaTower.solver larger) problem larger = run (sigmaTower.solver budget) problem budget ∧
      ((∃ state finished, run (sigmaTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (sigmaTower.solver larger) problem larger = .refuted absent)) :=
  tower_sigma_decided_of_uncovered (fun {_} {problem} permuted nonempty threshold constant equation member normal
      head covered => by
      have prepared := ContextualDependentCumulativeClosure.prepare_keeps (S := setting) (fun _ => none)
        (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
        TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing threshold problem permuted
      have sides := PermutedMiller.sides_of_mem prepared member
      exact uncovered permuted nonempty threshold constant equation member normal head sides
        (eta_kind sides normal.2.1 normal.2.2.2) covered)
    inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
