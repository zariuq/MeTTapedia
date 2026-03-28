import Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationPath
import Mettapedia.Logic.UniversalPredictionConditionalWMBridge

/-!
# Meta-Goal Stability + Universal-Mixture Refinement

This file is the first lightweight conjunction layer between:

- proof-backed Gödel-machine self-modification with protected WM goals, and
- incremental universal-mixture approximation.

It does **not** claim a fully unified semantics.  Instead, it packages together
two already-proved effects:

1. protected Markov-logic / WM goals drift by at most the shell bound, and
2. universal-mixture prefix-event scores improve monotonically with the
   approximation budget and stay below the full mixture score.

Positive example:
- a proof-backed rewrite path can improve utility while a separate universal
  predictor budget increases from `n` to `m`, giving both semantic stability on
  protected goals and better prefix prediction scores.

Negative example:
- this file does not prove monotonicity for conditional approximants, nor does
  it identify universal-mixture scores with the protected Markov-logic goals.
-/

namespace Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.Logic.UniversalPrediction
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- Combined theorem: proof-backed utility improvement, bounded cumulative WM
drift on protected goals, and monotone geometric universal-mixture refinement
for a chosen prefix query. -/
theorem MetaGoalShellPreservationPathDLR.utility_improves_and_goal_wmStrength_cumulative_drift_and_geom_prefix_refines
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent)
    {q : ConstraintQuery Atom}
    (hq : q ∈ protectedGoals)
    (ν : ℕ → Semimeasure)
    {n m : ℕ} (hnm : n ≤ m)
    (x : BinString) :
    expectedUtilityFromStart path.endMachine >
        expectedUtilityFromStart path.startMachine ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) q).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) q).toReal| ≤
          path.totalErrorBound ∧
      geomApproxQueryStrength ν n x ≤ geomApproxQueryStrength ν m x ∧
      geomApproxQueryStrength ν m x ≤ geomFullQueryStrength ν x := by
  exact ⟨path.utility_improves hcoh,
    measures.goal_wmStrength_cumulative_drift hcoh hq,
    geomApproxQueryStrength_mono ν hnm x,
    geomApproxQueryStrength_le_full ν m x⟩

/-- Exact-closure variant: proof-backed utility improvement together with exact
protected-goal WM preservation from a dynamic-individuation closure witness,
plus monotone geometric universal-mixture refinement. -/
theorem validModification_and_goal_wmStrength_preserved_of_dynamicIndividuationClosure_and_geom_prefix_refines
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
    (hq : q ∈ protectedGoals.goals)
    (ν : ℕ → Semimeasure)
    {n m : ℕ} (hnm : n ≤ m)
    (x : BinString) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) q =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) q ∧
      geomApproxQueryStrength ν n x ≤ geomApproxQueryStrength ν m x ∧
      geomApproxQueryStrength ν m x ≤ geomFullQueryStrength ν x := by
  have hstable :=
    validModification_and_goal_wmStrength_preserved_of_dynamicIndividuationClosure
      (oldMachine := oldMachine) (newMachine := newMachine)
      (proofBacked := proofBacked)
      (closure := closure)
      (hagree := hagree)
      (hclosed₂ := hclosed₂)
      (hbudget₁ := hbudget₁)
      (hbudget₂ := hbudget₂)
      (protectedGoals := protectedGoals)
      (measures := measures)
      (q := q) hq
  exact ⟨hstable.1, hstable.2,
    geomApproxQueryStrength_mono ν hnm x,
    geomApproxQueryStrength_le_full ν m x⟩

/-- Corrigibility-flavored bridge: if an operator-deference query is protected
by a dynamic-individuation closure witness, then proof-backed modification
preserves that query exactly while geometric prefix scores refine. -/
theorem validModification_preserves_operatorDeference_of_dynamicIndividuationClosure_and_geom_prefix_refines
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
    (hq : operatorDeferenceQuery ∈ protectedGoals.goals)
    (ν : ℕ → Semimeasure)
    {n m : ℕ} (hnm : n ≤ m)
    (x : BinString) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) operatorDeferenceQuery =
      BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) operatorDeferenceQuery ∧
      geomApproxQueryStrength ν n x ≤ geomApproxQueryStrength ν m x ∧
      geomApproxQueryStrength ν m x ≤ geomFullQueryStrength ν x := by
  exact validModification_and_goal_wmStrength_preserved_of_dynamicIndividuationClosure_and_geom_prefix_refines
    (oldMachine := oldMachine) (newMachine := newMachine)
    (proofBacked := proofBacked)
    (closure := closure)
    (hagree := hagree)
    (hclosed₂ := hclosed₂)
    (hbudget₁ := hbudget₁)
    (hbudget₂ := hbudget₂)
    (protectedGoals := protectedGoals)
    (measures := measures)
    (q := operatorDeferenceQuery) hq ν hnm x

/-- Path-level corrigibility bridge: if an operator-deference query stays in
the protected goal family, then proof-backed rewrites keep its WM drift within
the cumulative shell budget while geometric prefix scores refine. -/
theorem MetaGoalShellPreservationPathDLR.utility_improves_and_operatorDeference_drift_bounded_and_geom_prefix_refines
    {protectedGoals : Finset (ConstraintQuery Atom)}
    {path : MetaGoalShellPreservationPath (Atom := Atom) (ClauseId := ClauseId) protectedGoals}
    (measures : MetaGoalShellPreservationPathDLR path)
    (hcoh : path.Coherent)
    (operatorDeferenceQuery : ConstraintQuery Atom)
    (hq : operatorDeferenceQuery ∈ protectedGoals)
    (ν : ℕ → Semimeasure)
    {n m : ℕ} (hnm : n ≤ m)
    (x : BinString) :
    expectedUtilityFromStart path.endMachine >
        expectedUtilityFromStart path.startMachine ∧
      |(BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.startSpec measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Atom)) operatorDeferenceQuery).toReal -
        (BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics path.endSpec measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Atom)) operatorDeferenceQuery).toReal| ≤
          path.totalErrorBound ∧
      geomApproxQueryStrength ν n x ≤ geomApproxQueryStrength ν m x ∧
      geomApproxQueryStrength ν m x ≤ geomFullQueryStrength ν x := by
  exact ⟨path.utility_improves hcoh,
    measures.goal_wmStrength_cumulative_drift hcoh hq,
    geomApproxQueryStrength_mono ν hnm x,
    geomApproxQueryStrength_le_full ν m x⟩

end Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
