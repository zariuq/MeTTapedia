import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsValidHead

/-!
# Acceptance for the skeleton family, reduced to the census rows not yet read

Every nonempty store of the permuted Miller class has, from some budget on, a census head on a preparation that no
longer changes, with normal codes (`ContextualDependentCoverageReadersHalf.tower_stable_census_head`). Three rows of
the census are read by the skeleton family (`CoveredHead`, `tower_skeletonReads_of_covered`):

* the census head is valid: the conversion scan drops it (`tower_underReads_of_validHead`);
* its sides, η-expanded to the annotation's Π count, clash at their heads: distinct skeletons at a rigid base, distinct
  type kinds at a universe, reflexivity against a neutral term (`tower_etaReads_of_clash`), at any depths of the two
  sides;
* its η-expanded sides have distinct skeletons, at any base type (`tower_skeletonReads_of_clash`).

So **the skeleton family decides every store of the dynamic pattern fragment, with a principal answer or a certified
refutation, constant at every larger budget, as soon as every census head outside these three rows is read**
(`tower_skeleton_decided_of_uncovered`). The hypothesis is the rest of the census half of coverage; among its rows are
the pattern rows, spines of one head with one skeleton, formers of one kind at a universe, and pairs against neutral
terms.

The census can be read at the full depth: the η-long opened sides of every equation of the class with normal sides
are of a census kind at the annotation's Π count (`eta_kind`), so the hypothesis may use that kind
(`tower_skeleton_decided_of_uncovered_kinds`).
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

/-- **The census rows read so far**, on one equation. -/
def CoveredHead {Γ : Context setting.R} (equation : Equation (TotalTerm Γ)) : Prop :=
  (frames setting.levels).E equation.1 equation.2 ∨
    HeadClash setting.R 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code) ∨
    SkeletonClash 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)

/-- **A covered census head is read** by the skeleton family from some budget on. -/
theorem tower_skeletonReads_of_covered {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (covered : CoveredHead equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerSkeletonReads larger problem := by
  rcases covered with valid | clash | skeletons
  · obtain ⟨bound, reads⟩ := tower_underReads_of_validHead member valid
    exact ⟨bound, fun larger enough => .inl (.inl (reads larger enough))⟩
  · obtain ⟨bound, reads⟩ := tower_etaReads_of_clash constant member normal types clash
    exact ⟨bound, fun larger enough => .inl (reads larger enough)⟩
  · exact tower_skeletonReads_of_clash constant member types skeletons

/-- **Acceptance for the tower's skeleton family, reduced to the census rows not yet read**: if every census head of a
constant preparation outside the covered rows is read from some budget on, the family decides every store of the
dynamic pattern fragment, with a principal answer or a certified refutation, constant at every larger budget. -/
theorem tower_skeleton_decided_of_uncovered
    (uncovered : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ¬ CoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerSkeletonReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (skeletonTower.solver larger) problem larger = run (skeletonTower.solver budget) problem budget ∧
      ((∃ state finished, run (skeletonTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (skeletonTower.solver larger) problem larger = .refuted absent)) :=
  tower_skeleton_decided_of_skeletonReads (fun permuted nonempty => by
      obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
      by_cases covered : CoveredHead equation
      · exact tower_skeletonReads_of_covered constant member normal head.1 covered
      · exact uncovered permuted nonempty threshold constant equation member normal head covered)
    inside

/-! ## The census at the full depth -/

/-- **The η-long opened sides of an equation with Miller sides are of a census kind**, at the annotation's Π
count. -/
theorem eta_kind {Γ : Context setting.R} {equation : Equation (TotalTerm Γ)}
    (sides : ContextualDependentShortClosure.FragmentSidesMiller equation)
    (normalLeft : ContextualDependentExecutableJoin.Normal Tower.rules equation.1.2.code)
    (normalRight : ContextualDependentExecutableJoin.Normal Tower.rules equation.2.2.code) :
    Kind (openedFlexible (piCount equation.1.1.code))
      (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
        (expandTo (piCount equation.1.1.code) equation.1.2.code))
      (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
        (expandTo (piCount equation.1.1.code) equation.2.2.code)) := by
  have empty := computation_empty ContextualDependentPiSpine.Controls.rigid
  obtain ⟨left, right⟩ := ContextualDependentCumulativeClosure.side_reduct ContextualDependentPiSpine.Controls.rigid
    tower_stronglyNormalizing sides
  have opened : ∀ {code : Tower.Tm Γ.arity}, ContextualDependentCumulativeClosure.MarkedReduct Tower.rules
      (fun _ => true) code → ContextualDependentExecutableJoin.Normal Tower.rules code →
      miller (openedFlexible (piCount equation.1.1.code)) (ContextualDependentCensus.openNormal
        (piCount equation.1.1.code) (expandTo (piCount equation.1.1.code) code)) = true := fun reduct normal =>
    ContextualDependentCumulativeClosure.opened_of_reduct empty (MarkedReduct.expand empty _ reduct) _ _
      (ContextualDependentCensus.openCode_star _ _)
      (ContextualDependentCensus.openNormal_normal empty (normal_expandTo empty _ normal) _)
  exact classification (opened left normalLeft) (opened right normalRight)

/-- **Acceptance for the tower's skeleton family, reduced to the census rows not yet read**, with the census kind of
the η-long opened sides available: if every census head of a constant preparation outside the covered rows, whose
η-long opened sides are of a census kind at the annotation's Π count, is read from some budget on, the family decides
every store of the dynamic pattern fragment, with a principal answer or a certified refutation, constant at every
larger budget. -/
theorem tower_skeleton_decided_of_uncovered_kinds
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
          ¬ CoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerSkeletonReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (skeletonTower.solver larger) problem larger = run (skeletonTower.solver budget) problem budget ∧
      ((∃ state finished, run (skeletonTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (skeletonTower.solver larger) problem larger = .refuted absent)) :=
  tower_skeleton_decided_of_uncovered (fun {_} {problem} permuted nonempty threshold constant equation member normal
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
