import Mettapedia.Logic.MarkovLogicCoupledSubsystems
import Mettapedia.Logic.MarkovLogicDynamicTranscendence

/-!
# Dynamic Coupled Subsystems

This module combines the two-community carrier picture of
`MarkovLogicCoupledSubsystems` with the shell-rewriting bounds of
`MarkovLogicDynamicTranscendence`.

The new theorem object is a `DynamicCoupledSubsystemStep`: two
specifications may differ outside a finite shell around a protected
carrier, but they agree on that shell and both satisfy the Dobrushin
budget.  Then left-local, right-local, and joint carrier queries drift by
at most `2|Ω| · C^n`, where `Ω` is the protected carrier and `n` is the
shell depth.

The new path layer `DynamicCoupledSubsystemPath` composes multiple such
rewrites.  The cumulative discrepancy is bounded by the sum of the
step-wise carrier shell tails.

This is the formal counterpart of Weinbaum/Veitas-style resonance through a
shared boundary: two local communities may keep exchanging influence through
their protected carrier while distant rewrites remain geometrically damped.

**Positive example.**  Two local communities joined by a liaison layer may
rewrite distant external beliefs while preserving their internal and joint
truth values up to a geometric tail.

**Negative example.**  If the rewriting reaches the carrier itself, or if
the Dobrushin budget fails, this theorem does not apply.
-/

namespace Mettapedia.Logic.MarkovLogicDynamicCoupledSubsystems

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicDynamicTranscendence
open Mettapedia.Logic.MarkovLogicCoupledSubsystems
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Dynamic rewriting step for two communities living in one protected carrier.

The two specifications may differ outside the shell around the carrier, but
left, right, and joint carrier queries remain geometrically stable.

`CoupledSubsystems M₁` packages interaction-closure for the source
specification `M₁`.  For path composition, later steps must separately ensure
that the original carrier and cores remain contained in the new protected
carrier. -/
structure DynamicCoupledSubsystemStep
    (M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  coupled : CoupledSubsystems M₁
  shellDepth : ℕ
  shell_agreement : SpecAgreesOnRegion M₁ M₂
    (M₁.iterExpandRegion coupled.carrier.core shellDepth)
  budget₁ : M₁.PaperUniformSmallTotalInfluence
  budget₂ : M₂.PaperUniformSmallTotalInfluence

private noncomputable def chosenUniformConstant
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) : ℝ :=
  Classical.choose (M.finiteRegionPairwiseDobrushinConstant_le_uniform hM)

private theorem chosenUniformConstant_nonneg
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    0 ≤ chosenUniformConstant M hM :=
  (Classical.choose_spec (M.finiteRegionPairwiseDobrushinConstant_le_uniform hM)).1

private theorem chosenUniformConstant_lt_one
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    chosenUniformConstant M hM < 1 :=
  (Classical.choose_spec (M.finiteRegionPairwiseDobrushinConstant_le_uniform hM)).2.1

private theorem finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    (hM : M.PaperUniformSmallTotalInfluence) :
    ∀ Δ : Region Atom,
      M.finiteRegionPairwiseDobrushinConstant Δ ≤ chosenUniformConstant M hM :=
  (Classical.choose_spec (M.finiteRegionPairwiseDobrushinConstant_le_uniform hM)).2.2

noncomputable def DynamicCoupledSubsystemStep.contractionConstant
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂) : ℝ :=
  max (chosenUniformConstant M₁ step.budget₁) (chosenUniformConstant M₂ step.budget₂)

theorem DynamicCoupledSubsystemStep.contractionConstant_nonneg
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂) :
    0 ≤ step.contractionConstant := by
  exact le_trans
    (chosenUniformConstant_nonneg M₁ step.budget₁)
    (le_max_left _ _)

theorem DynamicCoupledSubsystemStep.contractionConstant_lt_one
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂) :
    step.contractionConstant < 1 := by
  refine max_lt_iff.mpr ?_
  exact ⟨chosenUniformConstant_lt_one M₁ step.budget₁,
    chosenUniformConstant_lt_one M₂ step.budget₂⟩

noncomputable def DynamicCoupledSubsystemStep.errorBound
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂) : ℝ :=
  2 * (step.coupled.carrier.core.card : ℝ) * step.contractionConstant ^ step.shellDepth

theorem DynamicCoupledSubsystemStep.errorBound_nonneg
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂) :
    0 ≤ step.errorBound := by
  unfold DynamicCoupledSubsystemStep.errorBound
  have hpow : 0 ≤ step.contractionConstant ^ step.shellDepth := by
    exact pow_nonneg step.contractionConstant_nonneg _
  nlinarith

private theorem supported_on_left_implies_supported_on_carrier
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.leftCore) :
    ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.carrier.core := by
  intro p hp
  exact step.coupled.left_subset_carrier (hq p hp)

private theorem supported_on_right_implies_supported_on_carrier
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.rightCore) :
    ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.carrier.core := by
  intro p hp
  exact step.coupled.right_subset_carrier (hq p hp)

private theorem supported_on_union_implies_supported_on_carrier
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q,
      (p : Sigma fun _ : Atom => Bool).1 ∈
        step.coupled.leftCore ∪ step.coupled.rightCore) :
    ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.carrier.core := by
  intro p hp
  exact step.coupled.leftRightUnion_subset_carrier (hq p hp)

private noncomputable def DynamicCoupledSubsystemStep.toDynamicTranscendenceStep
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂) :
    DynamicTranscendenceStep M₁ M₂ where
  queryRegion := step.coupled.carrier.core
  shellDepth := step.shellDepth
  shell_agreement := step.shell_agreement
  budget₁ := step.budget₁
  budget₂ := step.budget₂

/-- Left-local queries drift by at most the explicit shell error bound. -/
theorem DynamicCoupledSubsystemStep.left_queryProb_approximately_preserved_explicit
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.leftCore) :
    |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
      ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
        step.errorBound := by
  simpa [DynamicCoupledSubsystemStep.errorBound]
    using DynamicTranscendenceStep.queryProb_approximately_preserved_of_uniformConstant
      (step := step.toDynamicTranscendenceStep)
      (C := step.contractionConstant)
      (hC_nonneg := step.contractionConstant_nonneg)
      (hC_lt_one := step.contractionConstant_lt_one)
      (hC_bound₁ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant M₁ step.budget₁ Δ)
          (le_max_left _ _))
      (hC_bound₂ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant M₂ step.budget₂ Δ)
          (le_max_right _ _))
      μ₁ μ₂ hμ₁ hμ₂ q
      (supported_on_left_implies_supported_on_carrier step hq)

/-- Right-local queries drift by at most the explicit shell error bound. -/
theorem DynamicCoupledSubsystemStep.right_queryProb_approximately_preserved_explicit
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.rightCore) :
    |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
      ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
        step.errorBound := by
  simpa [DynamicCoupledSubsystemStep.errorBound]
    using DynamicTranscendenceStep.queryProb_approximately_preserved_of_uniformConstant
      (step := step.toDynamicTranscendenceStep)
      (C := step.contractionConstant)
      (hC_nonneg := step.contractionConstant_nonneg)
      (hC_lt_one := step.contractionConstant_lt_one)
      (hC_bound₁ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant M₁ step.budget₁ Δ)
          (le_max_left _ _))
      (hC_bound₂ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant M₂ step.budget₂ Δ)
          (le_max_right _ _))
      μ₁ μ₂ hμ₁ hμ₂ q
      (supported_on_right_implies_supported_on_carrier step hq)

/-- Joint left/right queries drift by at most the explicit shell error bound. -/
theorem DynamicCoupledSubsystemStep.coupled_queryProb_approximately_preserved_explicit
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q,
      (p : Sigma fun _ : Atom => Bool).1 ∈
        step.coupled.leftCore ∪ step.coupled.rightCore) :
    |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
      ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
        step.errorBound := by
  simpa [DynamicCoupledSubsystemStep.errorBound]
    using DynamicTranscendenceStep.queryProb_approximately_preserved_of_uniformConstant
      (step := step.toDynamicTranscendenceStep)
      (C := step.contractionConstant)
      (hC_nonneg := step.contractionConstant_nonneg)
      (hC_lt_one := step.contractionConstant_lt_one)
      (hC_bound₁ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant M₁ step.budget₁ Δ)
          (le_max_left _ _))
      (hC_bound₂ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant M₂ step.budget₂ Δ)
          (le_max_right _ _))
      μ₁ μ₂ hμ₁ hμ₂ q
      (supported_on_union_implies_supported_on_carrier step hq)

/-- Left-local queries drift by at most the geometric carrier shell bound. -/
theorem DynamicCoupledSubsystemStep.left_queryProb_approximately_preserved
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.leftCore) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
        ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
          2 * (step.coupled.carrier.core.card : ℝ) * C ^ step.shellDepth := by
  simpa [DynamicCoupledSubsystemStep.toDynamicTranscendenceStep]
    using DynamicTranscendenceStep.queryProb_approximately_preserved
      (step := step.toDynamicTranscendenceStep) μ₁ μ₂ hμ₁ hμ₂ q
      (supported_on_left_implies_supported_on_carrier step hq)

/-- Right-local queries drift by at most the geometric carrier shell bound. -/
theorem DynamicCoupledSubsystemStep.right_queryProb_approximately_preserved
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.rightCore) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
        ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
          2 * (step.coupled.carrier.core.card : ℝ) * C ^ step.shellDepth := by
  simpa [DynamicCoupledSubsystemStep.toDynamicTranscendenceStep]
    using DynamicTranscendenceStep.queryProb_approximately_preserved
      (step := step.toDynamicTranscendenceStep) μ₁ μ₂ hμ₁ hμ₂ q
      (supported_on_right_implies_supported_on_carrier step hq)

/-- Joint left/right queries drift by at most the geometric carrier shell bound. -/
theorem DynamicCoupledSubsystemStep.coupled_queryProb_approximately_preserved
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q,
      (p : Sigma fun _ : Atom => Bool).1 ∈
        step.coupled.leftCore ∪ step.coupled.rightCore) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |((infiniteMLNMassSemantics M₁ μ₁ hμ₁).queryProb q).toReal -
        ((infiniteMLNMassSemantics M₂ μ₂ hμ₂).queryProb q).toReal| ≤
          2 * (step.coupled.carrier.core.card : ℝ) * C ^ step.shellDepth := by
  simpa [DynamicCoupledSubsystemStep.toDynamicTranscendenceStep]
    using DynamicTranscendenceStep.queryProb_approximately_preserved
      (step := step.toDynamicTranscendenceStep) μ₁ μ₂ hμ₁ hμ₂ q
      (supported_on_union_implies_supported_on_carrier step hq)

/-- WM truth values for left-local queries are geometrically stable under
distant rewriting outside the carrier shell. -/
theorem DynamicCoupledSubsystemStep.left_wmStrength_approximately_preserved
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.leftCore) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} : MassState (ConstraintQuery Atom)) q).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} : MassState (ConstraintQuery Atom)) q).toReal| ≤
          2 * (step.coupled.carrier.core.card : ℝ) * C ^ step.shellDepth := by
  simpa [queryStrength_singleton_eq_queryProb]
    using step.left_queryProb_approximately_preserved μ₁ μ₂ hμ₁ hμ₂ q hq

/-- WM truth values for right-local queries are geometrically stable under
distant rewriting outside the carrier shell. -/
theorem DynamicCoupledSubsystemStep.right_wmStrength_approximately_preserved
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ step.coupled.rightCore) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} : MassState (ConstraintQuery Atom)) q).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} : MassState (ConstraintQuery Atom)) q).toReal| ≤
          2 * (step.coupled.carrier.core.card : ℝ) * C ^ step.shellDepth := by
  simpa [queryStrength_singleton_eq_queryProb]
    using step.right_queryProb_approximately_preserved μ₁ μ₂ hμ₁ hμ₂ q hq

/-- WM truth values for joint left/right queries are geometrically stable under
distant rewriting outside the carrier shell. -/
theorem DynamicCoupledSubsystemStep.coupled_wmStrength_approximately_preserved
    {M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (step : DynamicCoupledSubsystemStep M₁ M₂)
    (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
    (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
    (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₁ : Measure (InfiniteWorld Atom)))
    (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
      (μ₂ : Measure (InfiniteWorld Atom)))
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q,
      (p : Sigma fun _ : Atom => Bool).1 ∈
        step.coupled.leftCore ∪ step.coupled.rightCore) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics M₁ μ₁ hμ₁} : MassState (ConstraintQuery Atom)) q).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics M₂ μ₂ hμ₂} : MassState (ConstraintQuery Atom)) q).toReal| ≤
          2 * (step.coupled.carrier.core.card : ℝ) * C ^ step.shellDepth := by
  simpa [queryStrength_singleton_eq_queryProb]
    using step.coupled_queryProb_approximately_preserved μ₁ μ₂ hμ₁ hμ₂ q hq

-- ═══════════════════════════════════════════════════════════════════════════
-- DynamicCoupledSubsystemPath: repeated distant rewrites
-- ═══════════════════════════════════════════════════════════════════════════

/-- A finite sequence of distant rewrites for coupled subsystems. -/
inductive DynamicCoupledSubsystemPath :
    ClassicalInfiniteGroundMLNSpec Atom ClauseId →
    ClassicalInfiniteGroundMLNSpec Atom ClauseId → Type _ where
  | single {M₀ M₁ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      (first : DynamicCoupledSubsystemStep M₀ M₁) :
      DynamicCoupledSubsystemPath M₀ M₁
  | step {M₀ M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      (path : DynamicCoupledSubsystemPath M₀ M₁)
      (next : DynamicCoupledSubsystemStep M₁ M₂) :
      DynamicCoupledSubsystemPath M₀ M₂

/-- The original protected carrier tracked across the whole rewrite path. -/
noncomputable def DynamicCoupledSubsystemPath.originalCarrier :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    DynamicCoupledSubsystemPath M₀ M_final → Region Atom
  | _, _, .single first => first.coupled.carrier.core
  | _, _, .step path _ => path.originalCarrier

/-- The original left core tracked across the whole rewrite path. -/
noncomputable def DynamicCoupledSubsystemPath.originalLeftCore :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    DynamicCoupledSubsystemPath M₀ M_final → Region Atom
  | _, _, .single first => first.coupled.leftCore
  | _, _, .step path _ => path.originalLeftCore

/-- The original right core tracked across the whole rewrite path. -/
noncomputable def DynamicCoupledSubsystemPath.originalRightCore :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    DynamicCoupledSubsystemPath M₀ M_final → Region Atom
  | _, _, .single first => first.coupled.rightCore
  | _, _, .step path _ => path.originalRightCore

/-- Coherence means every later rewrite still protects and contains the original
carrier and local cores. -/
def DynamicCoupledSubsystemPath.Coherent :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    DynamicCoupledSubsystemPath M₀ M_final → Prop
  | _, _, .single _ => True
  | _, _, .step path next =>
      path.Coherent ∧
      path.originalCarrier ⊆ next.coupled.carrier.core ∧
      path.originalLeftCore ⊆ next.coupled.leftCore ∧
      path.originalRightCore ⊆ next.coupled.rightCore

/-- Total accumulated shell-tail bound along a dynamic coupled rewrite path. -/
noncomputable def DynamicCoupledSubsystemPath.totalErrorBound :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    DynamicCoupledSubsystemPath M₀ M_final → ℝ
  | _, _, .single first => first.errorBound
  | _, _, .step path next => path.totalErrorBound + next.errorBound

theorem DynamicCoupledSubsystemPath.totalErrorBound_nonneg
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (path : DynamicCoupledSubsystemPath M₀ M_final) :
    0 ≤ path.totalErrorBound := by
  induction path with
  | single first =>
      simpa [DynamicCoupledSubsystemPath.totalErrorBound] using first.errorBound_nonneg
  | step path next ih =>
      simp [DynamicCoupledSubsystemPath.totalErrorBound]
      nlinarith [ih, next.errorBound_nonneg]

/-- DLR witnesses for every stage of a dynamic coupled rewrite path. -/
inductive DynamicCoupledSubsystemPathDLR :
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    (path : DynamicCoupledSubsystemPath M₀ M_final) → Type _ where
  | single {M₀ M₁ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      (first : DynamicCoupledSubsystemStep M₀ M₁)
      (μ₀ : ProbabilityMeasure (InfiniteWorld Atom))
      (μ₁ : ProbabilityMeasure (InfiniteWorld Atom))
      (hμ₀ : FixedRegionCylinderDLR M₀.toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₀ : Measure (InfiniteWorld Atom)))
      (hμ₁ : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₁ : Measure (InfiniteWorld Atom))) :
      DynamicCoupledSubsystemPathDLR (.single first)
  | step {M₀ M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
      {path : DynamicCoupledSubsystemPath M₀ M₁}
      {next : DynamicCoupledSubsystemStep M₁ M₂}
      (prev : DynamicCoupledSubsystemPathDLR path)
      (μ₂ : ProbabilityMeasure (InfiniteWorld Atom))
      (hμ₂ : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
        (μ₂ : Measure (InfiniteWorld Atom))) :
      DynamicCoupledSubsystemPathDLR (.step path next)

noncomputable def DynamicCoupledSubsystemPathDLR.startMeasure
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path) :
    ProbabilityMeasure (InfiniteWorld Atom) := by
  induction measures with
  | single _ μ₀ _ _ _ => exact μ₀
  | step prev _ _ ih => exact ih

noncomputable def DynamicCoupledSubsystemPathDLR.endMeasure
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path) :
    ProbabilityMeasure (InfiniteWorld Atom) := by
  induction measures with
  | single _ _ μ₁ _ _ => exact μ₁
  | step _ μ₂ _ => exact μ₂

theorem DynamicCoupledSubsystemPathDLR.startDLR
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path) :
    FixedRegionCylinderDLR M₀.toStrictlyPositiveInfiniteGroundMLNSpec
      ((measures.startMeasure : ProbabilityMeasure (InfiniteWorld Atom)) :
        Measure (InfiniteWorld Atom)) := by
  induction measures with
  | single _ _ _ hμ₀ _ =>
      simpa [DynamicCoupledSubsystemPathDLR.startMeasure] using hμ₀
  | step prev _ _ ih =>
      simpa [DynamicCoupledSubsystemPathDLR.startMeasure] using ih

theorem DynamicCoupledSubsystemPathDLR.endDLR
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path) :
    FixedRegionCylinderDLR M_final.toStrictlyPositiveInfiniteGroundMLNSpec
      ((measures.endMeasure : ProbabilityMeasure (InfiniteWorld Atom)) :
        Measure (InfiniteWorld Atom)) := by
  induction measures with
  | single _ _ _ _ hμ₁ =>
      simpa [DynamicCoupledSubsystemPathDLR.endMeasure] using hμ₁
  | step _ _ hμ₂ =>
      simpa [DynamicCoupledSubsystemPathDLR.endMeasure] using hμ₂

private theorem supported_on_original_left_implies_supported_on_left
    {M₀ M_final M_next : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    {next : DynamicCoupledSubsystemStep M_final M_next}
    (hsubset : path.originalLeftCore ⊆ next.coupled.leftCore)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalLeftCore) :
    ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ next.coupled.leftCore := by
  intro p hp
  exact hsubset (hq p hp)

private theorem supported_on_original_right_implies_supported_on_right
    {M₀ M_final M_next : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    {next : DynamicCoupledSubsystemStep M_final M_next}
    (hsubset : path.originalRightCore ⊆ next.coupled.rightCore)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalRightCore) :
    ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ next.coupled.rightCore := by
  intro p hp
  exact hsubset (hq p hp)

private theorem supported_on_original_union_implies_supported_on_union
    {M₀ M_final M_next : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    {next : DynamicCoupledSubsystemStep M_final M_next}
    (hleft : path.originalLeftCore ⊆ next.coupled.leftCore)
    (hright : path.originalRightCore ⊆ next.coupled.rightCore)
    {q : ConstraintQuery Atom}
    (hq : ∀ p ∈ q,
      (p : Sigma fun _ : Atom => Bool).1 ∈
        path.originalLeftCore ∪ path.originalRightCore) :
    ∀ p ∈ q,
      (p : Sigma fun _ : Atom => Bool).1 ∈
        next.coupled.leftCore ∪ next.coupled.rightCore := by
  intro p hp
  rcases Finset.mem_union.mp (hq p hp) with hpl | hpr
  · exact Finset.mem_union.mpr (Or.inl (hleft hpl))
  · exact Finset.mem_union.mpr (Or.inr (hright hpr))

/-- Repeated distant rewrites perturb original left-local queries by at most the
sum of the step-wise shell tails. -/
theorem DynamicCoupledSubsystemPathDLR.left_queryProb_cumulative_drift
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path)
    (hcoh : path.Coherent)
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalLeftCore) :
    |((infiniteMLNMassSemantics M₀ measures.startMeasure measures.startDLR).queryProb q).toReal -
      ((infiniteMLNMassSemantics M_final measures.endMeasure measures.endDLR).queryProb q).toReal| ≤
        path.totalErrorBound := by
  induction path generalizing q with
  | single first =>
      cases measures with
      | single _ μ₀ μ₁ hμ₀ hμ₁ =>
          have hq' : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ first.coupled.leftCore := by
            simpa [DynamicCoupledSubsystemPath.originalLeftCore] using hq
          simpa [DynamicCoupledSubsystemPath.originalLeftCore,
            DynamicCoupledSubsystemPath.totalErrorBound,
            DynamicCoupledSubsystemPathDLR.startMeasure,
            DynamicCoupledSubsystemPathDLR.endMeasure,
            DynamicCoupledSubsystemPathDLR.startDLR,
            DynamicCoupledSubsystemPathDLR.endDLR]
            using first.left_queryProb_approximately_preserved_explicit μ₀ μ₁ hμ₀ hμ₁ q hq'
  | step path next ih =>
      cases measures with
      | step prev μ₂ hμ₂ =>
          have hcoh' :
              path.Coherent ∧
              path.originalCarrier ⊆ next.coupled.carrier.core ∧
              path.originalLeftCore ⊆ next.coupled.leftCore ∧
              path.originalRightCore ⊆ next.coupled.rightCore := by
            simpa [DynamicCoupledSubsystemPath.Coherent] using hcoh
          rcases hcoh' with ⟨hcohPrev, _hcarrier, hleft, _hright⟩
          have hqPrev : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalLeftCore := by
            simpa [DynamicCoupledSubsystemPath.originalLeftCore] using hq
          have hprev := ih prev hcohPrev q hqPrev
          have hqNext : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ next.coupled.leftCore := by
            exact supported_on_original_left_implies_supported_on_left hleft hqPrev
          have hnext :=
            next.left_queryProb_approximately_preserved_explicit
              prev.endMeasure μ₂ prev.endDLR hμ₂ q
              hqNext
          let a : ℝ :=
            ((infiniteMLNMassSemantics M₀ prev.startMeasure prev.startDLR).queryProb q).toReal
          let b : ℝ :=
            ((infiniteMLNMassSemantics _ prev.endMeasure prev.endDLR).queryProb q).toReal
          let c : ℝ :=
            ((infiniteMLNMassSemantics _ μ₂ hμ₂).queryProb q).toReal
          have htri : |a - c| ≤ |a - b| + |b - c| := by
            calc
              |a - c| = |(a - b) + (b - c)| := by ring_nf
              _ ≤ |a - b| + |b - c| := abs_add_le _ _
          have hbound : |a - c| ≤ path.totalErrorBound + next.errorBound := by
            linarith [htri, hprev, hnext]
          simpa [a, b, c, DynamicCoupledSubsystemPath.totalErrorBound,
            DynamicCoupledSubsystemPathDLR.startMeasure,
            DynamicCoupledSubsystemPathDLR.endMeasure,
            DynamicCoupledSubsystemPathDLR.startDLR,
            DynamicCoupledSubsystemPathDLR.endDLR]
            using hbound

/-- Repeated distant rewrites perturb original right-local queries by at most the
sum of the step-wise shell tails. -/
theorem DynamicCoupledSubsystemPathDLR.right_queryProb_cumulative_drift
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path)
    (hcoh : path.Coherent)
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalRightCore) :
    |((infiniteMLNMassSemantics M₀ measures.startMeasure measures.startDLR).queryProb q).toReal -
      ((infiniteMLNMassSemantics M_final measures.endMeasure measures.endDLR).queryProb q).toReal| ≤
        path.totalErrorBound := by
  induction path generalizing q with
  | single first =>
      cases measures with
      | single _ μ₀ μ₁ hμ₀ hμ₁ =>
          have hq' : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ first.coupled.rightCore := by
            simpa [DynamicCoupledSubsystemPath.originalRightCore] using hq
          simpa [DynamicCoupledSubsystemPath.originalRightCore,
            DynamicCoupledSubsystemPath.totalErrorBound,
            DynamicCoupledSubsystemPathDLR.startMeasure,
            DynamicCoupledSubsystemPathDLR.endMeasure,
            DynamicCoupledSubsystemPathDLR.startDLR,
            DynamicCoupledSubsystemPathDLR.endDLR]
            using first.right_queryProb_approximately_preserved_explicit μ₀ μ₁ hμ₀ hμ₁ q hq'
  | step path next ih =>
      cases measures with
      | step prev μ₂ hμ₂ =>
          have hcoh' :
              path.Coherent ∧
              path.originalCarrier ⊆ next.coupled.carrier.core ∧
              path.originalLeftCore ⊆ next.coupled.leftCore ∧
              path.originalRightCore ⊆ next.coupled.rightCore := by
            simpa [DynamicCoupledSubsystemPath.Coherent] using hcoh
          rcases hcoh' with ⟨hcohPrev, _hcarrier, _hleft, hright⟩
          have hqPrev : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalRightCore := by
            simpa [DynamicCoupledSubsystemPath.originalRightCore] using hq
          have hprev := ih prev hcohPrev q hqPrev
          have hqNext : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ next.coupled.rightCore := by
            exact supported_on_original_right_implies_supported_on_right hright hqPrev
          have hnext :=
            next.right_queryProb_approximately_preserved_explicit
              prev.endMeasure μ₂ prev.endDLR hμ₂ q
              hqNext
          let a : ℝ :=
            ((infiniteMLNMassSemantics M₀ prev.startMeasure prev.startDLR).queryProb q).toReal
          let b : ℝ :=
            ((infiniteMLNMassSemantics _ prev.endMeasure prev.endDLR).queryProb q).toReal
          let c : ℝ :=
            ((infiniteMLNMassSemantics _ μ₂ hμ₂).queryProb q).toReal
          have htri : |a - c| ≤ |a - b| + |b - c| := by
            calc
              |a - c| = |(a - b) + (b - c)| := by ring_nf
              _ ≤ |a - b| + |b - c| := abs_add_le _ _
          have hbound : |a - c| ≤ path.totalErrorBound + next.errorBound := by
            linarith [htri, hprev, hnext]
          simpa [a, b, c, DynamicCoupledSubsystemPath.totalErrorBound,
            DynamicCoupledSubsystemPathDLR.startMeasure,
            DynamicCoupledSubsystemPathDLR.endMeasure,
            DynamicCoupledSubsystemPathDLR.startDLR,
            DynamicCoupledSubsystemPathDLR.endDLR]
            using hbound

/-- Repeated distant rewrites perturb original joint left/right queries by at
most the sum of the step-wise shell tails. -/
theorem DynamicCoupledSubsystemPathDLR.coupled_queryProb_cumulative_drift
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path)
    (hcoh : path.Coherent)
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q,
      (p : Sigma fun _ : Atom => Bool).1 ∈
        path.originalLeftCore ∪ path.originalRightCore) :
    |((infiniteMLNMassSemantics M₀ measures.startMeasure measures.startDLR).queryProb q).toReal -
      ((infiniteMLNMassSemantics M_final measures.endMeasure measures.endDLR).queryProb q).toReal| ≤
        path.totalErrorBound := by
  induction path generalizing q with
  | single first =>
      cases measures with
      | single _ μ₀ μ₁ hμ₀ hμ₁ =>
          have hq' :
              ∀ p ∈ q,
                (p : Sigma fun _ : Atom => Bool).1 ∈
                  first.coupled.leftCore ∪ first.coupled.rightCore := by
            simpa [DynamicCoupledSubsystemPath.originalLeftCore,
              DynamicCoupledSubsystemPath.originalRightCore] using hq
          simpa [DynamicCoupledSubsystemPath.originalLeftCore,
            DynamicCoupledSubsystemPath.originalRightCore,
            DynamicCoupledSubsystemPath.totalErrorBound,
            DynamicCoupledSubsystemPathDLR.startMeasure,
            DynamicCoupledSubsystemPathDLR.endMeasure,
            DynamicCoupledSubsystemPathDLR.startDLR,
            DynamicCoupledSubsystemPathDLR.endDLR]
            using first.coupled_queryProb_approximately_preserved_explicit μ₀ μ₁ hμ₀ hμ₁ q hq'
  | step path next ih =>
      cases measures with
      | step prev μ₂ hμ₂ =>
          have hcoh' :
              path.Coherent ∧
              path.originalCarrier ⊆ next.coupled.carrier.core ∧
              path.originalLeftCore ⊆ next.coupled.leftCore ∧
              path.originalRightCore ⊆ next.coupled.rightCore := by
            simpa [DynamicCoupledSubsystemPath.Coherent] using hcoh
          rcases hcoh' with ⟨hcohPrev, _hcarrier, hleft, hright⟩
          have hqPrev :
              ∀ p ∈ q,
                (p : Sigma fun _ : Atom => Bool).1 ∈
                  path.originalLeftCore ∪ path.originalRightCore := by
            simpa [DynamicCoupledSubsystemPath.originalLeftCore,
              DynamicCoupledSubsystemPath.originalRightCore] using hq
          have hprev := ih prev hcohPrev q hqPrev
          have hqNext :
              ∀ p ∈ q,
                (p : Sigma fun _ : Atom => Bool).1 ∈
                  next.coupled.leftCore ∪ next.coupled.rightCore := by
            exact supported_on_original_union_implies_supported_on_union hleft hright hqPrev
          have hnext :=
            next.coupled_queryProb_approximately_preserved_explicit
              prev.endMeasure μ₂ prev.endDLR hμ₂ q
              hqNext
          let a : ℝ :=
            ((infiniteMLNMassSemantics M₀ prev.startMeasure prev.startDLR).queryProb q).toReal
          let b : ℝ :=
            ((infiniteMLNMassSemantics _ prev.endMeasure prev.endDLR).queryProb q).toReal
          let c : ℝ :=
            ((infiniteMLNMassSemantics _ μ₂ hμ₂).queryProb q).toReal
          have htri : |a - c| ≤ |a - b| + |b - c| := by
            calc
              |a - c| = |(a - b) + (b - c)| := by ring_nf
              _ ≤ |a - b| + |b - c| := abs_add_le _ _
          have hbound : |a - c| ≤ path.totalErrorBound + next.errorBound := by
            linarith [htri, hprev, hnext]
          simpa [a, b, c, DynamicCoupledSubsystemPath.totalErrorBound,
            DynamicCoupledSubsystemPathDLR.startMeasure,
            DynamicCoupledSubsystemPathDLR.endMeasure,
            DynamicCoupledSubsystemPathDLR.startDLR,
            DynamicCoupledSubsystemPathDLR.endDLR]
            using hbound

/-- WM truth values for original left-local queries drift by at most the
accumulated shell tail along the path. -/
theorem DynamicCoupledSubsystemPathDLR.left_wmStrength_cumulative_drift
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path)
    (hcoh : path.Coherent)
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalLeftCore) :
    |(BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M₀ measures.startMeasure measures.startDLR} :
          MassState (ConstraintQuery Atom)) q).toReal -
      (BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M_final measures.endMeasure measures.endDLR} :
          MassState (ConstraintQuery Atom)) q).toReal| ≤
        path.totalErrorBound := by
  simpa [queryStrength_singleton_eq_queryProb]
    using measures.left_queryProb_cumulative_drift hcoh q hq

/-- WM truth values for original right-local queries drift by at most the
accumulated shell tail along the path. -/
theorem DynamicCoupledSubsystemPathDLR.right_wmStrength_cumulative_drift
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path)
    (hcoh : path.Coherent)
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ path.originalRightCore) :
    |(BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M₀ measures.startMeasure measures.startDLR} :
          MassState (ConstraintQuery Atom)) q).toReal -
      (BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M_final measures.endMeasure measures.endDLR} :
          MassState (ConstraintQuery Atom)) q).toReal| ≤
        path.totalErrorBound := by
  simpa [queryStrength_singleton_eq_queryProb]
    using measures.right_queryProb_cumulative_drift hcoh q hq

/-- WM truth values for original joint queries drift by at most the accumulated
shell tail along the path. -/
theorem DynamicCoupledSubsystemPathDLR.coupled_wmStrength_cumulative_drift
    {M₀ M_final : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {path : DynamicCoupledSubsystemPath M₀ M_final}
    (measures : DynamicCoupledSubsystemPathDLR path)
    (hcoh : path.Coherent)
    (q : ConstraintQuery Atom)
    (hq : ∀ p ∈ q,
      (p : Sigma fun _ : Atom => Bool).1 ∈
        path.originalLeftCore ∪ path.originalRightCore) :
    |(BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M₀ measures.startMeasure measures.startDLR} :
          MassState (ConstraintQuery Atom)) q).toReal -
      (BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics M_final measures.endMeasure measures.endDLR} :
          MassState (ConstraintQuery Atom)) q).toReal| ≤
        path.totalErrorBound := by
  simpa [queryStrength_singleton_eq_queryProb]
    using measures.coupled_queryProb_cumulative_drift hcoh q hq

end Mettapedia.Logic.MarkovLogicDynamicCoupledSubsystems
