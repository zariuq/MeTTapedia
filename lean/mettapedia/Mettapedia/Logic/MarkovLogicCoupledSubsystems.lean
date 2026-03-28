import Mettapedia.Logic.MarkovLogicIndividuation

/-!
# Coupled Subsystems of Infinite MLNs

This module refines the single-core notion of individuation into a
two-community picture closer to Veitas and Weinbaum's "world of views".

A `CoupledSubsystems` object consists of:
- a larger interaction-closed **carrier** region,
- two distinguished nonempty **local cores** inside the carrier,
- the two local cores are disjoint.

The left and right cores need not themselves be interaction-closed.  They
may influence one another through interface atoms living in the carrier's
remainder.  What is protected is the carrier as a whole.

The key consequence is exact semantic stability under distant ontology
growth: if a second specification agrees with the original one on the
carrier, then every left-local, right-local, or jointly supported query
has exactly the same Gibbs / WM truth value in both specifications.

**Positive example.**  Two communities connected by a small liaison layer
can still form a single protected carrier.  Each community may affect the
other through the liaison, while distant changes outside the carrier leave
their local and joint queries unchanged.

**Negative example.**  If bridge clauses from either community spill
outside the carrier's boundary, the carrier is no longer interaction-closed
and the exact invariance theorem does not apply.

## References

- V. Veitas & D. R. Weinbaum, *Living Cognitive Society*, 2015.
- D. R. Weinbaum & V. Veitas, *Open-Ended Intelligence*, 2015.
-/

namespace Mettapedia.Logic.MarkovLogicCoupledSubsystems

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicIndividuation
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Two distinguished local cores living inside one larger protected carrier.

The carrier is the actual individuated subsystem.  The left and right cores
identify the two communities whose interaction we want to study.  Their
coupling is allowed to flow through the carrier interface
`carrier.core \ (leftCore ∪ rightCore)`. -/
structure CoupledSubsystems
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  /-- The larger protected carrier. -/
  carrier : IndividuatedSubsystem M
  /-- Left local core. -/
  leftCore : Region Atom
  /-- Right local core. -/
  rightCore : Region Atom
  /-- Each local core contains at least one atom. -/
  left_nonempty : leftCore.Nonempty
  right_nonempty : rightCore.Nonempty
  /-- Both local cores sit inside the protected carrier. -/
  left_subset_carrier : leftCore ⊆ carrier.core
  right_subset_carrier : rightCore ⊆ carrier.core
  /-- The two cores are distinguished communities, not the same region twice. -/
  cores_disjoint : Disjoint leftCore rightCore

/-- The interface region mediating possible left/right interaction inside the
carrier. -/
noncomputable def CoupledSubsystems.interfaceRegion
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M) : Region Atom :=
  S.carrier.core \ (S.leftCore ∪ S.rightCore)

theorem CoupledSubsystems.leftRightUnion_subset_carrier
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M) :
    S.leftCore ∪ S.rightCore ⊆ S.carrier.core := by
  intro a ha
  rcases Finset.mem_union.mp ha with hleft | hright
  · exact S.left_subset_carrier hleft
  · exact S.right_subset_carrier hright

theorem CoupledSubsystems.interface_subset_carrier
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M) :
    S.interfaceRegion ⊆ S.carrier.core := by
  intro a ha
  exact (Finset.mem_sdiff.mp ha).1

theorem CoupledSubsystems.left_disjoint_interface
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M) :
    Disjoint S.leftCore S.interfaceRegion := by
  refine Finset.disjoint_left.2 ?_
  intro a haLeft haInterface
  have hnot : a ∉ S.leftCore ∪ S.rightCore := (Finset.mem_sdiff.mp haInterface).2
  exact hnot (Finset.mem_union.mpr (Or.inl haLeft))

theorem CoupledSubsystems.right_disjoint_interface
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M) :
    Disjoint S.rightCore S.interfaceRegion := by
  refine Finset.disjoint_left.2 ?_
  intro a haRight haInterface
  have hnot : a ∉ S.leftCore ∪ S.rightCore := (Finset.mem_sdiff.mp haInterface).2
  exact hnot (Finset.mem_union.mpr (Or.inr haRight))

theorem CoupledSubsystems.left_union_right_union_interface_eq_carrier
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M) :
    S.leftCore ∪ S.rightCore ∪ S.interfaceRegion = S.carrier.core := by
  ext a
  constructor
  · intro ha
    rcases Finset.mem_union.mp ha with hside | hint
    · exact S.leftRightUnion_subset_carrier hside
    · exact S.interface_subset_carrier hint
  · intro ha
    by_cases hside : a ∈ S.leftCore ∪ S.rightCore
    · exact Finset.mem_union.mpr (Or.inl hside)
    · refine Finset.mem_union.mpr (Or.inr ?_)
      show a ∈ S.carrier.core \ (S.leftCore ∪ S.rightCore)
      exact Finset.mem_sdiff.mpr ⟨ha, hside⟩

private theorem supported_on_left_implies_supported_on_carrier
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.leftCore) :
    ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.carrier.core := by
  intro p hp
  exact S.left_subset_carrier (hq p hp)

private theorem supported_on_right_implies_supported_on_carrier
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.rightCore) :
    ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.carrier.core := by
  intro p hp
  exact S.right_subset_carrier (hq p hp)

private theorem supported_on_union_implies_supported_on_carrier
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.leftCore ∪ S.rightCore) :
    ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.carrier.core := by
  intro p hp
  exact S.leftRightUnion_subset_carrier (hq p hp)

/-- Left-local queries are invariant under distant ontology extension that
preserves the whole carrier. -/
theorem CoupledSubsystems.left_queryProb_invariant_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂ S.carrier.core)
    (hclosed₂ : InteractionClosed M₂ S.carrier.core)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.leftCore) :
    (infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q =
    (infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q :=
  S.carrier.queryProb_invariant_under_extension hagree hclosed₂
    hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q
    (supported_on_left_implies_supported_on_carrier S hq)

/-- Right-local queries are invariant under distant ontology extension that
preserves the whole carrier. -/
theorem CoupledSubsystems.right_queryProb_invariant_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂ S.carrier.core)
    (hclosed₂ : InteractionClosed M₂ S.carrier.core)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.rightCore) :
    (infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q =
    (infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q :=
  S.carrier.queryProb_invariant_under_extension hagree hclosed₂
    hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q
    (supported_on_right_implies_supported_on_carrier S hq)

/-- Joint queries spanning the two local communities are also invariant,
provided all queried atoms stay inside the coupled pair. -/
theorem CoupledSubsystems.coupled_queryProb_invariant_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂ S.carrier.core)
    (hclosed₂ : InteractionClosed M₂ S.carrier.core)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.leftCore ∪ S.rightCore) :
    (infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q =
    (infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q :=
  S.carrier.queryProb_invariant_under_extension hagree hclosed₂
    hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q
    (supported_on_union_implies_supported_on_carrier S hq)

/-- WM truth values for left-local queries are stable under distant ontology
growth preserving the carrier. -/
theorem CoupledSubsystems.left_wmStrength_stable_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂ S.carrier.core)
    (hclosed₂ : InteractionClosed M₂ S.carrier.core)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.leftCore) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} : MassState (ConstraintQuery Atom)) q =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} : MassState (ConstraintQuery Atom)) q := by
  simp only [queryStrength_singleton_eq_queryProb]
  exact S.left_queryProb_invariant_under_extension
    hagree hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q hq

/-- WM truth values for right-local queries are stable under distant ontology
growth preserving the carrier. -/
theorem CoupledSubsystems.right_wmStrength_stable_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂ S.carrier.core)
    (hclosed₂ : InteractionClosed M₂ S.carrier.core)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.rightCore) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} : MassState (ConstraintQuery Atom)) q =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} : MassState (ConstraintQuery Atom)) q := by
  simp only [queryStrength_singleton_eq_queryProb]
  exact S.right_queryProb_invariant_under_extension
    hagree hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q hq

/-- WM truth values for joint left/right queries are stable under distant
ontology growth preserving the carrier. -/
theorem CoupledSubsystems.coupled_wmStrength_stable_under_extension
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (S : CoupledSubsystems M₁)
    (hagree : SpecAgreesOnRegion M₁ M₂ S.carrier.core)
    (hclosed₂ : InteractionClosed M₂ S.carrier.core)
    (hbudget₁ : M₁.PaperUniformSmallTotalInfluence)
    (hbudget₂ : M₂.PaperUniformSmallTotalInfluence)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ S.leftCore ∪ S.rightCore) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} : MassState (ConstraintQuery Atom)) q =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} : MassState (ConstraintQuery Atom)) q := by
  simp only [queryStrength_singleton_eq_queryProb]
  exact S.coupled_queryProb_invariant_under_extension
    hagree hclosed₂ hbudget₁ hbudget₂ μ₁ μ₂ hμ₁ hμ₂ q hq

end Mettapedia.Logic.MarkovLogicCoupledSubsystems
