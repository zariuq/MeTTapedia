import Mettapedia.Logic.MarkovLogicInfiniteWorldModel
import Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
import Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
import Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
import Mettapedia.Logic.MarkovLogicInfiniteCylinders
import Mettapedia.Logic.MarkovLogicInfinitePositive

/-!
# Ontology Growth Stability for Infinite MLNs

This module proves the **cross-specification stability theorem**: if two
infinite MLN specifications agree on all clauses touching a neighborhood of
a query region, their DLR measures assign the same probability to every
query in that region.

This is the formal counterpart of "adding new concepts far from a query
does not change the query answer," the core guarantee needed for open-ended
knowledge bases.

The key insight is that `finiteVolumeWeight` is a product over
`regionSupport Λ`. If two specs share the same clauses on that support,
their Gibbs kernels are **identical** — not approximately equal, but exactly
equal. The DLR equations then force exact marginal agreement.

**Positive example.** An open-ended concept graph keeps growing at the
frontier. A biomedical query about a local cluster of atoms is unaffected
by new social-network concepts added far away, as long as both the old and
new specifications satisfy the Dobrushin budget.

**Negative example.** If a newly added clause touches atoms in the query
region's interaction neighborhood, the agreement breaks — the new clause
genuinely changes the local Gibbs kernel.

## References

- Weinbaum & Veitas (2015), *Open-Ended Intelligence*, for the
  philosophical motivation of ontology growth with preserved coherence.
- Georgii (2011), *Gibbs Measures and Phase Transitions*, Theorem 8.7,
  for the Dobrushin uniqueness machinery this module composes with.
-/

namespace Mettapedia.Logic.MarkovLogicOntologyGrowth

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteCylinders
open Mettapedia.Logic.MarkovLogicInfinitePositive
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Two classical infinite MLN specifications **agree on a region** Γ when
    every clause touching Γ has the same body and the same log-weight in
    both specifications. -/
structure SpecAgreesOnRegion
    (M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Γ : Region Atom) : Prop where
  regionSupport_eq : ∀ Λ ⊆ Γ, Λ.Nonempty → M₁.regionSupport Λ = M₂.regionSupport Λ
  clause_eq : ∀ j ∈ M₁.regionSupport Γ, M₁.clause j = M₂.clause j
  logWeight_eq : ∀ j ∈ M₁.regionSupport Γ, M₁.logWeight j = M₂.logWeight j

/-- A region Γ is **interaction-closed** for specification M when every
    atom in Γ has its full interaction neighborhood contained in Γ.
    This ensures that the Gibbs kernel on any subregion of Γ depends only
    on clauses touching Γ. -/
def InteractionClosed
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (Γ : Region Atom) : Prop :=
  ∀ a ∈ Γ, M.atomInteractionNeighborhood a ⊆ Γ

/-- **Kernel agreement**: if two specs agree on an interaction-closed region Γ,
    their strictly-positive clause data agrees on every clause touching any
    Λ ⊆ Γ.

    This is the load-bearing lemma: `finiteVolumeWeight` is a product over
    `regionSupport Λ`, so identical clause data ⟹ identical weights ⟹
    identical partition functions ⟹ identical Gibbs kernels. -/
theorem classicalWeightedClause_eq_of_specAgreesOnRegion
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    {j : ClauseId} (hj : j ∈ M₁.regionSupport Γ) :
    classicalWeightedClause (M₁.clause j) (M₁.logWeight j) =
    classicalWeightedClause (M₂.clause j) (M₂.logWeight j) := by
  rw [hagree.clause_eq j hj, hagree.logWeight_eq j hj]

/-- On an interaction-closed region `Γ`, the full-region kernel does not inspect
boundary atoms at all, so any two boundary conditions agree on the boundary
support vacuously. -/
theorem agreesOnBoundarySupport_of_interactionClosed
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    {Γ : Region Atom}
    (hclosed : InteractionClosed M Γ)
    (ξ₁ ξ₂ : BoundaryCondition Atom) :
    AgreesOnBoundarySupport
      M.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec Γ ξ₁ ξ₂ := by
  intro j a hj ha hnot
  have hj' : j ∈ M.regionSupport Γ := by
    simpa [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec] using hj
  have ha' : a ∈ (M.clause j).atoms := by
    simpa [ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec] using ha
  rcases M.regionSupport_sound hj' with ⟨b, hbClause, hbΓ⟩
  have htouchSingleton : clauseTouchesRegion (M.clause j) ({b} : Region Atom) := by
    exact ⟨b, hbClause, by simp⟩
  have hjb : j ∈ M.regionSupport ({b} : Region Atom) :=
    M.regionSupport_complete htouchSingleton
  have hneq : a ≠ b := by
    intro hab
    subst hab
    exact hnot hbΓ
  have haErase : a ∈ (M.clause j).atoms.erase b := by
    exact Finset.mem_erase.mpr ⟨hneq, ha'⟩
  have hneigh : a ∈ M.atomInteractionNeighborhood b := by
    exact (M.mem_atomInteractionNeighborhood_iff b a).2 ⟨j, hjb, haErase⟩
  exact False.elim (hnot (hclosed b hbΓ hneigh))

/-- If two specifications agree on all clauses touching `Γ`, then their
finite-volume query probabilities on `Γ` are exactly equal. -/
theorem finiteVolumeQueryProb_eq_of_specAgreesOnRegion
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hΓ : Γ.Nonempty)
    (ξ : BoundaryCondition Atom)
    (q : LocalConstraintQuery Atom Γ) :
    (finiteVolumeMassSemantics
      M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec Γ ξ).queryProb q =
    (finiteVolumeMassSemantics
      M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec Γ ξ).queryProb q := by
  classical
  let N₁ := M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  let N₂ := M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec
  have hsupport : N₁.regionSupport Γ = N₂.regionSupport Γ := by
    simpa [N₁, N₂] using hagree.regionSupport_eq Γ (by intro a ha; exact ha) hΓ
  have hweight :
      ∀ x : LocalAssignment Atom Γ,
        N₁.finiteVolumeWeight Γ x ξ = N₂.finiteVolumeWeight Γ x ξ := by
    intro x
    unfold InfiniteGroundMLNSpec.finiteVolumeWeight
    rw [hsupport]
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hjN₁ : j ∈ N₁.regionSupport Γ := by
      rw [hsupport]
      exact hj
    have hj' : j ∈ M₁.regionSupport Γ := by
      simpa [N₁] using hjN₁
    have hwc := classicalWeightedClause_eq_of_specAgreesOnRegion hagree hj'
    simpa [N₁, N₂, ClassicalInfiniteGroundMLNSpec.toStrictlyPositiveInfiniteGroundMLNSpec]
      using congrArg (fun wc => wc.eval (patch Γ x ξ)) hwc
  have hpartition :
      N₁.finiteVolumePartition Γ ξ = N₂.finiteVolumePartition Γ ξ := by
    unfold InfiniteGroundMLNSpec.finiteVolumePartition
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact hweight x
  have hmass :
      finiteVolumeQueryMass N₁ Γ ξ q = finiteVolumeQueryMass N₂ Γ ξ q := by
    unfold finiteVolumeQueryMass
    refine Finset.sum_congr rfl ?_
    intro x hx
    by_cases hsat : satisfiesConstraints x q
    · simp [hsat, hweight x]
    · simp [hsat]
  change
    (if N₁.finiteVolumePartition Γ ξ = 0 then 0
      else finiteVolumeQueryMass N₁ Γ ξ q / N₁.finiteVolumePartition Γ ξ) =
    (if N₂.finiteVolumePartition Γ ξ = 0 then 0
      else finiteVolumeQueryMass N₂ Γ ξ q / N₂.finiteVolumePartition Γ ξ)
  by_cases hZ : N₁.finiteVolumePartition Γ ξ = 0
  · have hZ' : N₂.finiteVolumePartition Γ ξ = 0 := by
      simpa [N₁, N₂, hpartition] using hZ
    simp [hZ, hZ']
  · have hZ' : N₂.finiteVolumePartition Γ ξ ≠ 0 := by
      simpa [N₁, N₂, hpartition] using hZ
    rw [if_neg hZ, if_neg hZ']
    simp [hmass, hpartition]

/-- **Ontology growth**: adding clauses far from a query region does not
    change the query's WM truth value.

    More precisely: if M₁ and M₂ agree on an interaction-closed region Γ
    containing the query atoms, and both satisfy the uniform Dobrushin
    budget, then the unique DLR measures for M₁ and M₂ assign the same
    probability to every query supported on Γ.

    The proof composes three ingredients:
    1. Kernel agreement (clause data identical on Γ);
    2. Dobrushin uniqueness (each spec has exactly one DLR measure);
    3. The DLR equation forces marginals on Γ to depend only on the
       local kernel, which is shared. -/
theorem queryProb_eq_of_specAgreesOnRegion
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : Region Atom}
    (hagree : SpecAgreesOnRegion M₁ M₂ Γ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (_hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (_hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ) :
    (infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q =
    (infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q := by
  classical
  by_cases hqnil : q = []
  · subst hqnil
    simp [MassSemantics.queryProb, infiniteMLNMassSemantics, infiniteQueryEvent,
      satisfiesConstraints]
  · let qΓ : LocalConstraintQuery Atom Γ := restrictQueryToRegion Γ q hq
    let ξ₀ : BoundaryCondition Atom := fun _ => false
    have hΓ : Γ.Nonempty := by
      rcases List.exists_mem_of_ne_nil q hqnil with ⟨p, hp⟩
      exact ⟨p.1, hq p hp⟩
    have hEvent :
        infiniteQueryEvent q = localQueryEvent Γ qΓ := by
      ext ω
      have hpatch : patch Γ (worldRestriction Γ ω) ω = ω := by
        funext a
        by_cases ha : a ∈ Γ
        · simp [patch, worldRestriction, ha]
        · simp [patch, ha]
      simpa [infiniteQueryEvent, qΓ, localQueryEvent, hpatch] using
        (satisfiesConstraints_restrictQueryToRegion_iff
          (Λ := Γ) (x := worldRestriction Γ ω) (q := q) hq (ξ := ω)).symm
    have hconst₁ :
        ∀ ω : InfiniteWorld Atom,
          M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ω
              (localQueryEvent Γ qΓ) =
            M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
              (localQueryEvent Γ qΓ) := by
      intro ω
      unfold StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
      simpa using
        (finiteVolumeWorldMeasure_localQueryEvent_eq_of_agreesOnBoundarySupport
          (M := M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec)
          (Λ := Γ) (q := qΓ)
          (ξ₁ := ω) (ξ₂ := ξ₀)
          (hboundary := agreesOnBoundarySupport_of_interactionClosed M₁ hclosed₁ ω ξ₀))
    have hconst₂ :
        ∀ ω : InfiniteWorld Atom,
          M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ω
              (localQueryEvent Γ qΓ) =
            M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
              (localQueryEvent Γ qΓ) := by
      intro ω
      unfold StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
      simpa using
        (finiteVolumeWorldMeasure_localQueryEvent_eq_of_agreesOnBoundarySupport
          (M := M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec)
          (Λ := Γ) (q := qΓ)
          (ξ₁ := ω) (ξ₂ := ξ₀)
          (hboundary := agreesOnBoundarySupport_of_interactionClosed M₂ hclosed₂ ω ξ₀))
    have hdlr₁ :
        ∫⁻ ω,
          M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ω
            (localQueryEvent Γ qΓ) ∂ (μ₁ : Measure (InfiniteWorld Atom)) =
          (μ₁ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ) := by
      simpa [localQueryEvent_eq_cylinder Γ qΓ] using
        hμ₁ Γ Γ (localConstraintSet Γ qΓ) (measurableSet_localConstraintSet Γ qΓ)
    have hdlr₂ :
        ∫⁻ ω,
          M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ω
            (localQueryEvent Γ qΓ) ∂ (μ₂ : Measure (InfiniteWorld Atom)) =
          (μ₂ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ) := by
      simpa [localQueryEvent_eq_cylinder Γ qΓ] using
        hμ₂ Γ Γ (localConstraintSet Γ qΓ) (measurableSet_localConstraintSet Γ qΓ)
    have hprob₁ :
        (μ₁ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ) =
          M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
            (localQueryEvent Γ qΓ) := by
      rw [← hdlr₁]
      have hfun :
          (fun ω : InfiniteWorld Atom =>
              M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ω
                (localQueryEvent Γ qΓ)) =
            fun _ =>
              M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
                (localQueryEvent Γ qΓ) := by
        funext ω
        exact hconst₁ ω
      rw [hfun]
      simp
    have hprob₂ :
        (μ₂ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ) =
          M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
            (localQueryEvent Γ qΓ) := by
      rw [← hdlr₂]
      have hfun :
          (fun ω : InfiniteWorld Atom =>
              M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ω
                (localQueryEvent Γ qΓ)) =
            fun _ =>
              M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
                (localQueryEvent Γ qΓ) := by
        funext ω
        exact hconst₂ ω
      rw [hfun]
      simp
    have hfv₁ :
        M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
            (localQueryEvent Γ qΓ) =
          (finiteVolumeMassSemantics
            M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec Γ ξ₀).queryProb qΓ := by
      unfold StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
      simpa using
        (finiteVolumeWorldMeasure_localQueryEvent
          (M := M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec)
          (Λ := Γ) (ξ := ξ₀)
          (hZ := M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Γ ξ₀)
          (q := qΓ))
    have hfv₂ :
        M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
            (localQueryEvent Γ qΓ) =
          (finiteVolumeMassSemantics
            M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec Γ ξ₀).queryProb qΓ := by
      unfold StrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure
      simpa using
        (finiteVolumeWorldMeasure_localQueryEvent
          (M := M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec)
          (Λ := Γ) (ξ := ξ₀)
          (hZ := M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumePartition_ne_zero Γ ξ₀)
          (q := qΓ))
    have hfinite :
        (finiteVolumeMassSemantics
          M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec Γ ξ₀).queryProb qΓ =
        (finiteVolumeMassSemantics
          M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec Γ ξ₀).queryProb qΓ :=
      finiteVolumeQueryProb_eq_of_specAgreesOnRegion hagree hΓ ξ₀ qΓ
    calc
      (infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q
          = (μ₁ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ) := by
              simp [MassSemantics.queryProb, infiniteMLNMassSemantics, hEvent]
      _ = M₁.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
            (localQueryEvent Γ qΓ) := hprob₁
      _ = (finiteVolumeMassSemantics
            M₁.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec Γ ξ₀).queryProb qΓ := hfv₁
      _ = (finiteVolumeMassSemantics
            M₂.toStrictlyPositiveInfiniteGroundMLNSpec.toInfiniteGroundMLNSpec Γ ξ₀).queryProb qΓ := hfinite
      _ = M₂.toStrictlyPositiveInfiniteGroundMLNSpec.finiteVolumeWorldMeasure Γ ξ₀
            (localQueryEvent Γ qΓ) := hfv₂.symm
      _ = (μ₂ : Measure (InfiniteWorld Atom)) (localQueryEvent Γ qΓ) := hprob₂.symm
      _ = (infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q := by
            simp [MassSemantics.queryProb, infiniteMLNMassSemantics, hEvent]

/-- **Developer-facing corollary**: extending a specification with new clauses
    whose atoms are disjoint from the agreement zone preserves all query
    answers in that zone. -/
theorem queryProb_stable_of_extension_outside
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {Γ : Region Atom}
    (h_clause : ∀ j, j ∈ M₁.regionSupport Γ →
      M₁.clause j = M₂.clause j ∧ M₁.logWeight j = M₂.logWeight j)
    (h_support : ∀ Λ ⊆ Γ, Λ.Nonempty → M₁.regionSupport Λ = M₂.regionSupport Λ)
    (hclosed₁ : InteractionClosed M₁ Γ)
    (hclosed₂ : InteractionClosed M₂ Γ)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ) :
    (infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q =
    (infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q := by
  exact queryProb_eq_of_specAgreesOnRegion
    ⟨h_support, fun j hj => (h_clause j hj).1, fun j hj => (h_clause j hj).2⟩
    hclosed₁ hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q hq

end Mettapedia.Logic.MarkovLogicOntologyGrowth
