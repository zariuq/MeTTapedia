import Mettapedia.UniversalAI.GodelMachine.Basic
import Mettapedia.Logic.MarkovLogicIndividuation
import Mettapedia.Logic.MarkovLogicDynamicTranscendence
import Mettapedia.Logic.MarkovLogicDynamicIndividuation

/-!
# Meta-Goal Shell Preservation for Proof-Backed Self-Modification

This module is the first direct bridge between the Gödel-machine layer and the
open-ended-intelligence / WM-Markov-logic layer.

The idea is simple:

- `validModification G G'` says a Gödel-machine rewrite is proof-backed and
  improves expected utility.
- the Markov-logic side says distant rewrites preserve protected WM queries
  either exactly (outside an interaction-closed carrier) or approximately
  (outside a shell around a protected region).

Putting these together yields a rigorous notion of **meta-goal stability**:
an agent may improve its utility while preserving protected WM goals exactly or
up to a geometric shell tail.

**Positive example.**  A proof-backed rewrite of a remote planning module leaves
core medical or social-governance queries unchanged if the rewrite stays
outside an interaction-closed carrier, and changes them only by a geometric
tail if it stays outside a deep enough shell.

**Negative example.**  If the rewrite reaches the protected carrier itself,
or if the Dobrushin budget fails, this module gives no stability guarantee.

## References

- J. Schmidhuber, *Gödel Machines*, 2003.
- D. R. Weinbaum & V. Veitas, *Open-Ended Intelligence*, 2015.
- B. Goertzel, *MetaGoal Stability*, 2026.
-/

namespace Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation

open Mettapedia.UniversalAI.GodelMachine
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicIndividuation
open Mettapedia.Logic.MarkovLogicDynamicTranscendence
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- A finite family of WM-style meta-goals protected by a region `Γ`. -/
structure ProtectedWMGoals (Γ : Region Atom) where
  /-- The protected query family. -/
  goals : Finset (ConstraintQuery Atom)
  /-- Every query in the family is supported on `Γ`. -/
  supported : ∀ q ∈ goals, ∀ p ∈ q, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ

/-- DLR witnesses for a pair of cross-specification Markov-logic semantics. -/
structure CrossSpecDLR
    (M₁ M₂ : ClassicalInfiniteGroundMLNSpec Atom ClauseId) where
  /-- DLR witness for the old specification. -/
  oldMeasure : ProbabilityMeasure (InfiniteWorld Atom)
  /-- DLR witness for the new specification. -/
  newMeasure : ProbabilityMeasure (InfiniteWorld Atom)
  /-- Gibbs/DLR evidence for the old measure. -/
  oldDLR : FixedRegionCylinderDLR M₁.toStrictlyPositiveInfiniteGroundMLNSpec
    (oldMeasure : Measure (InfiniteWorld Atom))
  /-- Gibbs/DLR evidence for the new measure. -/
  newDLR : FixedRegionCylinderDLR M₂.toStrictlyPositiveInfiniteGroundMLNSpec
    (newMeasure : Measure (InfiniteWorld Atom))

/-- Exact meta-goal preservation for proof-backed rewrites that stay outside an
interaction-closed protected core. -/
structure ExactMetaGoalPreservationStep where
  /-- Gödel-machine state before modification. -/
  oldMachine : GodelMachineState
  /-- Gödel-machine state after modification. -/
  newMachine : GodelMachineState
  /-- Old Markov-logic specification. -/
  oldSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId
  /-- New Markov-logic specification. -/
  newSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId
  /-- The protected WM core. -/
  protectedCore : IndividuatedSubsystem oldSpec
  /-- The rewrite leaves the protected core unchanged. -/
  regionAgreement : SpecAgreesOnRegion oldSpec newSpec protectedCore.core
  /-- The protected core remains interaction-closed after rewriting. -/
  newInteractionClosed : InteractionClosed newSpec protectedCore.core
  /-- Dobrushin budgets for both specifications. -/
  budget₁ : oldSpec.PaperUniformSmallTotalInfluence
  budget₂ : newSpec.PaperUniformSmallTotalInfluence
  /-- Protected WM meta-goals supported on the core. -/
  protectedGoals : ProtectedWMGoals protectedCore.core
  /-- The Gödel-machine rewrite is proof-backed. -/
  proofBacked : validModification oldMachine newMachine

/-- Dynamic meta-goal preservation for proof-backed rewrites that leave an
interaction shell around the protected query region unchanged. -/
structure MetaGoalShellPreservationStep where
  /-- Gödel-machine state before modification. -/
  oldMachine : GodelMachineState
  /-- Gödel-machine state after modification. -/
  newMachine : GodelMachineState
  /-- Old Markov-logic specification. -/
  oldSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId
  /-- New Markov-logic specification. -/
  newSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId
  /-- The semantic rewrite witness controlling shell stability. -/
  semanticStep : DynamicTranscendenceStep oldSpec newSpec
  /-- Protected WM meta-goals supported on the query region. -/
  protectedGoals : ProtectedWMGoals semanticStep.queryRegion
  /-- The Gödel-machine rewrite is proof-backed. -/
  proofBacked : validModification oldMachine newMachine

theorem ExactMetaGoalPreservationStep.utility_improves
    (step : ExactMetaGoalPreservationStep (Atom := Atom) (ClauseId := ClauseId)) :
    expectedUtilityFromStart step.newMachine >
      expectedUtilityFromStart step.oldMachine :=
  valid_modification_improves _ _ step.proofBacked

theorem ExactMetaGoalPreservationStep.goal_queryProb_preserved
    (step : ExactMetaGoalPreservationStep (Atom := Atom) (ClauseId := ClauseId))
    (measures : CrossSpecDLR step.oldSpec step.newSpec)
    {q : ConstraintQuery Atom}
    (hq : q ∈ step.protectedGoals.goals) :
    (infiniteMLNMassSemantics step.oldSpec measures.oldMeasure measures.oldDLR).queryProb q =
    (infiniteMLNMassSemantics step.newSpec measures.newMeasure measures.newDLR).queryProb q :=
  step.protectedCore.queryProb_invariant_under_extension
    step.regionAgreement step.newInteractionClosed
    step.budget₁ step.budget₂
    measures.oldMeasure measures.newMeasure measures.oldDLR measures.newDLR
    q (step.protectedGoals.supported q hq)

theorem ExactMetaGoalPreservationStep.goal_wmStrength_preserved
    (step : ExactMetaGoalPreservationStep (Atom := Atom) (ClauseId := ClauseId))
    (measures : CrossSpecDLR step.oldSpec step.newSpec)
    {q : ConstraintQuery Atom}
    (hq : q ∈ step.protectedGoals.goals) :
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics step.oldSpec measures.oldMeasure measures.oldDLR} :
        MassState (ConstraintQuery Atom)) q =
    BinaryWorldModel.queryStrength
      ({infiniteMLNMassSemantics step.newSpec measures.newMeasure measures.newDLR} :
        MassState (ConstraintQuery Atom)) q := by
  simpa [queryStrength_singleton_eq_queryProb]
    using step.goal_queryProb_preserved measures hq

theorem ExactMetaGoalPreservationStep.validModification_and_goal_wmStrength_preserved
    (step : ExactMetaGoalPreservationStep (Atom := Atom) (ClauseId := ClauseId))
    (measures : CrossSpecDLR step.oldSpec step.newSpec)
    {q : ConstraintQuery Atom}
    (hq : q ∈ step.protectedGoals.goals) :
    expectedUtilityFromStart step.newMachine >
        expectedUtilityFromStart step.oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics step.oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) q =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics step.newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) q := by
  exact ⟨step.utility_improves, step.goal_wmStrength_preserved measures hq⟩

/-- Exact meta-goal bridge from a dynamic-individuation closure witness.

If closure has emerged around a seed in the old specification, and the new
specification agrees on that closed shell, then every protected seed-goal is
exactly preserved while a proof-backed rewrite improves expected utility. -/
theorem validModification_and_goal_wmStrength_preserved_of_dynamicIndividuationClosure
    {oldSpec newSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (oldMachine newMachine : GodelMachineState)
    (proofBacked : validModification oldMachine newMachine)
    (closure : DynamicIndividuationClosure oldSpec)
    (hagree : SpecAgreesOnRegion oldSpec newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hclosed₂ : InteractionClosed newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hbudget₁ : oldSpec.PaperUniformSmallTotalInfluence)
    (hbudget₂ : newSpec.PaperUniformSmallTotalInfluence)
    (protectedGoals : ProtectedWMGoals closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec)
    {q : ConstraintQuery Atom}
    (hq : q ∈ protectedGoals.goals) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) q =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) q := by
  refine ⟨valid_modification_improves _ _ proofBacked, ?_⟩
  exact closure.seed_wmStrength_exact_under_extension
    hagree hclosed₂ hbudget₁ hbudget₂
    measures.oldMeasure measures.newMeasure
    measures.oldDLR measures.newDLR
    q (protectedGoals.supported q hq)

/-- Corrigibility corollary: if "defer to operator" is protected inside a
closed shell, then a proof-backed rewrite preserves that WM truth value
exactly while improving expected utility. -/
theorem validModification_preserves_operatorDeference_of_dynamicIndividuationClosure
    {oldSpec newSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (oldMachine newMachine : GodelMachineState)
    (proofBacked : validModification oldMachine newMachine)
    (closure : DynamicIndividuationClosure oldSpec)
    (hagree : SpecAgreesOnRegion oldSpec newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hclosed₂ : InteractionClosed newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hbudget₁ : oldSpec.PaperUniformSmallTotalInfluence)
    (hbudget₂ : newSpec.PaperUniformSmallTotalInfluence)
    (protectedGoals : ProtectedWMGoals closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec)
    (operatorDeferenceQuery : ConstraintQuery Atom)
    (hq : operatorDeferenceQuery ∈ protectedGoals.goals) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) operatorDeferenceQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) operatorDeferenceQuery := by
  exact validModification_and_goal_wmStrength_preserved_of_dynamicIndividuationClosure
    (oldMachine := oldMachine) (newMachine := newMachine)
    (proofBacked := proofBacked)
    (closure := closure)
    (hagree := hagree)
    (hclosed₂ := hclosed₂)
    (hbudget₁ := hbudget₁)
    (hbudget₂ := hbudget₂)
    (protectedGoals := protectedGoals)
    (measures := measures)
    (q := operatorDeferenceQuery) hq

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

noncomputable def MetaGoalShellPreservationStep.contractionConstant
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId)) : ℝ :=
  max (chosenUniformConstant step.oldSpec step.semanticStep.budget₁)
    (chosenUniformConstant step.newSpec step.semanticStep.budget₂)

theorem MetaGoalShellPreservationStep.contractionConstant_nonneg
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId)) :
    0 ≤ step.contractionConstant := by
  exact le_trans
    (chosenUniformConstant_nonneg step.oldSpec step.semanticStep.budget₁)
    (le_max_left _ _)

theorem MetaGoalShellPreservationStep.contractionConstant_lt_one
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId)) :
    step.contractionConstant < 1 := by
  refine max_lt_iff.mpr ?_
  exact ⟨chosenUniformConstant_lt_one step.oldSpec step.semanticStep.budget₁,
    chosenUniformConstant_lt_one step.newSpec step.semanticStep.budget₂⟩

/-- Explicit shell-tail error bound for the protected WM goal family. -/
noncomputable def MetaGoalShellPreservationStep.errorBound
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId)) : ℝ :=
  2 * (step.semanticStep.queryRegion.card : ℝ) *
    step.contractionConstant ^ step.semanticStep.shellDepth

theorem MetaGoalShellPreservationStep.errorBound_nonneg
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId)) :
    0 ≤ step.errorBound := by
  unfold MetaGoalShellPreservationStep.errorBound
  have hpow : 0 ≤ step.contractionConstant ^ step.semanticStep.shellDepth := by
    exact pow_nonneg step.contractionConstant_nonneg _
  nlinarith

theorem MetaGoalShellPreservationStep.utility_improves
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId)) :
    expectedUtilityFromStart step.newMachine >
      expectedUtilityFromStart step.oldMachine :=
  valid_modification_improves _ _ step.proofBacked

theorem MetaGoalShellPreservationStep.goal_queryProb_approximately_preserved
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId))
    (measures : CrossSpecDLR step.oldSpec step.newSpec)
    {q : ConstraintQuery Atom}
    (hq : q ∈ step.protectedGoals.goals) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      |((infiniteMLNMassSemantics step.oldSpec measures.oldMeasure measures.oldDLR).queryProb q).toReal -
        ((infiniteMLNMassSemantics step.newSpec measures.newMeasure measures.newDLR).queryProb q).toReal| ≤
          2 * (step.semanticStep.queryRegion.card : ℝ) * C ^ step.semanticStep.shellDepth :=
  step.semanticStep.queryProb_approximately_preserved
    measures.oldMeasure measures.newMeasure measures.oldDLR measures.newDLR
    q (step.protectedGoals.supported q hq)

theorem MetaGoalShellPreservationStep.goal_queryProb_approximately_preserved_explicit
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId))
    (measures : CrossSpecDLR step.oldSpec step.newSpec)
    {q : ConstraintQuery Atom}
    (hq : q ∈ step.protectedGoals.goals) :
    |((infiniteMLNMassSemantics step.oldSpec measures.oldMeasure measures.oldDLR).queryProb q).toReal -
      ((infiniteMLNMassSemantics step.newSpec measures.newMeasure measures.newDLR).queryProb q).toReal| ≤
        step.errorBound := by
  simpa [MetaGoalShellPreservationStep.errorBound]
    using DynamicTranscendenceStep.queryProb_approximately_preserved_of_uniformConstant
      (step := step.semanticStep)
      (C := step.contractionConstant)
      (hC_nonneg := step.contractionConstant_nonneg)
      (hC_lt_one := step.contractionConstant_lt_one)
      (hC_bound₁ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant
            step.oldSpec step.semanticStep.budget₁ Δ)
          (le_max_left _ _))
      (hC_bound₂ := by
        intro Δ
        exact le_trans
          (finiteRegionPairwiseDobrushinConstant_le_chosenUniformConstant
            step.newSpec step.semanticStep.budget₂ Δ)
          (le_max_right _ _))
      measures.oldMeasure measures.newMeasure measures.oldDLR measures.newDLR
      q (step.protectedGoals.supported q hq)

theorem MetaGoalShellPreservationStep.goal_wmStrength_approximately_preserved_explicit
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId))
    (measures : CrossSpecDLR step.oldSpec step.newSpec)
    {q : ConstraintQuery Atom}
    (hq : q ∈ step.protectedGoals.goals) :
    |(BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics step.oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) q).toReal -
      (BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics step.newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) q).toReal| ≤
        step.errorBound := by
  simpa [queryStrength_singleton_eq_queryProb]
    using step.goal_queryProb_approximately_preserved_explicit measures hq

theorem MetaGoalShellPreservationStep.validModification_and_goal_wmStrength_approximately_preserved_explicit
    (step : MetaGoalShellPreservationStep (Atom := Atom) (ClauseId := ClauseId))
    (measures : CrossSpecDLR step.oldSpec step.newSpec)
    {q : ConstraintQuery Atom}
    (hq : q ∈ step.protectedGoals.goals) :
    expectedUtilityFromStart step.newMachine >
        expectedUtilityFromStart step.oldMachine ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics step.oldSpec measures.oldMeasure measures.oldDLR} :
            MassState (ConstraintQuery Atom)) q).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics step.newSpec measures.newMeasure measures.newDLR} :
            MassState (ConstraintQuery Atom)) q).toReal| ≤
          step.errorBound := by
  exact ⟨step.utility_improves,
    step.goal_wmStrength_approximately_preserved_explicit measures hq⟩

end Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
