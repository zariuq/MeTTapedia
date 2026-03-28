import Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample
import Mettapedia.UniversalAI.GodelMachine.MetaGoalUniversalApproximationBridge
import Mettapedia.Logic.MarkovLogicTrustTriangleExample
import Mettapedia.Logic.UniversalPrediction.Optimality
import Mettapedia.Logic.UniversalPredictionConditionalApproximation

/-!
# Concrete Example: Protected Goals + Approximate Universal Prediction

This file instantiates the abstract Gödel-machine / WM / universal-prediction
bridge with one small concrete scenario.

We reuse the two-step trust-triangle self-modification path for the protected
goal side, and pair it with a tiny deterministic predictor family on the
universal-mixture side.

Positive example:
- utility improves along the proof-backed rewrite path,
- the protected WM goal remains within the proved shell bound,
- prefix prediction refines with approximation budget,
- and a concrete conditional next-bit query has a proved approximation bound.

Negative example:
- the conditional query is only controlled because the approximant context mass
  at `[]` stays bounded below by `1/2`; without that denominator floor, the
  conditional bound would not apply.
-/

namespace Mettapedia.UniversalAI.GodelMachine.MetaGoalUniversalApproximationExample

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicTrustTriangleExample
open Mettapedia.Logic.PLNWorldModel

/-- A tiny semimeasure concentrating all first-step mass on `false`. -/
def falseFirstBitSemimeasure : Semimeasure where
  toFun
    | [] => 1
    | [false] => 1
    | _ => 0
  root_le_one' := by simp
  superadditive' := by
    intro x
    cases x with
    | nil =>
        simp
    | cons b xs =>
        cases xs with
        | nil =>
            cases b <;> simp
        | cons b' xs' =>
            simp

/-- A tiny semimeasure concentrating all first-step mass on `true`. -/
def trueFirstBitSemimeasure : Semimeasure where
  toFun
    | [] => 1
    | [true] => 1
    | _ => 0
  root_le_one' := by simp
  superadditive' := by
    intro x
    cases x with
    | nil =>
        simp
    | cons b xs =>
        cases xs with
        | nil =>
            cases b <;> simp
        | cons b' xs' =>
            simp

/-- A tiny deterministic semimeasure family:
- index `0`: first bit forced to `false`
- index `1`: first bit forced to `true`
- all later indices: first bit forced to `false` again

This makes the first two geometric approximants easy to read while keeping the
full mixture nontrivial. -/
noncomputable def toyPredictorFamily : ℕ → Semimeasure
  | 0 => falseFirstBitSemimeasure
  | 1 => trueFirstBitSemimeasure
  | _ => falseFirstBitSemimeasure

/-- Concrete conditional query: "is the next bit false given the empty
context?" -/
def nextFalseQuery : ConditionalPrefixQuery where
  context := []
  target := [false]

theorem toyPredictorFamily_root_mass_one :
    (xiGeomApproxSemimeasure toyPredictorFamily 1) [] = (1 / 2 : ENNReal) := by
  change xiApproxFun toyPredictorFamily geometricWeight 1 [] = (1 / 2 : ENNReal)
  unfold xiApproxFun
  rw [Finset.sum_range_one]
  simp [toyPredictorFamily, geometricWeight, falseFirstBitSemimeasure]
  rw [ENNReal.zpow_neg]
  simp

theorem toyPredictorFamily_root_floor_two :
    ((1 / 2 : ENNReal)) ≤ (xiGeomApproxSemimeasure toyPredictorFamily 2) [] := by
  calc
    (1 / 2 : ENNReal) = (xiGeomApproxSemimeasure toyPredictorFamily 1) [] := by
      symm
      exact toyPredictorFamily_root_mass_one
    _ ≤ (xiGeomApproxSemimeasure toyPredictorFamily 2) [] := by
      exact xiGeomApproxSemimeasure_mono toyPredictorFamily (by omega) []

theorem oneHalf_ne_zero : (1 / 2 : ENNReal) ≠ 0 := by
  norm_num

theorem oneHalf_ne_top : (1 / 2 : ENNReal) ≠ ⊤ := by
  rw [div_eq_mul_inv]
  exact ENNReal.mul_ne_top (by simp) (by simp)

/-- Concrete joint example:
- proof-backed self-modification improves utility,
- the protected trust-triangle WM goal drifts by at most `12`,
- raw prefix mass refines from budget `1` to `2`, and
- the conditional next-bit query has the explicit denominator-floor bound
  `≤ 1`. -/
theorem trustTriangle_metaGoal_and_toyPredictor_example :
    ∃ measures :
        MetaGoalShellPreservationPathDLR
          (Atom := Nat) (ClauseId := VarNClauseId) trustTriangleMetaGoalPath,
      expectedUtilityFromStart trustTriangleMetaGoalPath.endMachine >
          expectedUtilityFromStart trustTriangleMetaGoalPath.startMachine ∧
        |(BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleMetaGoalPath.startSpec
                measures.startMeasure measures.startDLR} :
              MassState (ConstraintQuery Nat)) agent1Query).toReal -
          (BinaryWorldModel.queryStrength
            ({infiniteMLNMassSemantics trustTriangleMetaGoalPath.endSpec
                measures.endMeasure measures.endDLR} :
              MassState (ConstraintQuery Nat)) agent1Query).toReal| ≤
            12 ∧
        geomApproxQueryStrength toyPredictorFamily 1 [false] ≤
          geomApproxQueryStrength toyPredictorFamily 2 [false] ∧
        geomApproxQueryStrength toyPredictorFamily 2 [false] ≤
          geomFullQueryStrength toyPredictorFamily [false] ∧
        |(BinaryWorldModel.queryStrength
            (geomApproxConditionalProfile toyPredictorFamily 2) nextFalseQuery).toReal -
          (BinaryWorldModel.queryStrength
            (geomConditionalProfile toyPredictorFamily) nextFalseQuery).toReal| ≤
            1 := by
  rcases trustTriangle_metaGoal_path_example with ⟨measures, _, _⟩
  have hbridge :=
    MetaGoalShellPreservationPathDLR.utility_improves_and_operatorDeference_drift_bounded_and_geom_prefix_refines
      (path := trustTriangleMetaGoalPath)
      measures
      trustTriangleMetaGoalPath_coherent
      agent1Query
      (by simp [trustTriangleProtectedGoals])
      toyPredictorFamily
      (n := 1)
      (m := 2)
      (by norm_num)
      [false]
  rcases hbridge with ⟨himprove, hdrift, hmono, hfull⟩
  refine ⟨measures, himprove, ?_, hmono, hfull, ?_⟩
  · simpa [trustTriangleMetaGoalPath_totalErrorBound] using hdrift
  · have hcond :=
        geomApproxConditionalQueryStrength_abs_sub_le
          toyPredictorFamily 2 nextFalseQuery
          oneHalf_ne_zero oneHalf_ne_top
          toyPredictorFamily_root_floor_two
    norm_num [nextFalseQuery, geomTailMass] at hcond ⊢
    exact hcond

/-- Exact-closure companion example:
- the first proof-backed rewrite improves utility,
- the protected trust-triangle query is preserved exactly under closed-shell
  replacement,
- raw prefix mass refines from budget `1` to `2`, and
- the same conditional next-bit query keeps the explicit denominator-floor
  bound `≤ 1`. -/
theorem trustTriangle_exact_metaGoal_closure_and_toyPredictor_example :
    ∃ measures :
        MetaGoalShellPreservationPathDLR
          (Atom := Nat) (ClauseId := VarNClauseId) trustTriangleMetaGoalPath,
      expectedUtilityFromStart (toyMachine 1) >
          expectedUtilityFromStart (toyMachine 0) ∧
        BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics trustTriangleMetaGoalPath.startSpec
              measures.startMeasure measures.startDLR} :
            MassState (ConstraintQuery Nat)) agent1Query =
        BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics trustTriangleMetaGoalPath.endSpec
              measures.endMeasure measures.endDLR} :
            MassState (ConstraintQuery Nat)) agent1Query ∧
        geomApproxQueryStrength toyPredictorFamily 1 [false] ≤
          geomApproxQueryStrength toyPredictorFamily 2 [false] ∧
        geomApproxQueryStrength toyPredictorFamily 2 [false] ≤
          geomFullQueryStrength toyPredictorFamily [false] ∧
        |(BinaryWorldModel.queryStrength
            (geomApproxConditionalProfile toyPredictorFamily 2) nextFalseQuery).toReal -
          (BinaryWorldModel.queryStrength
            (geomConditionalProfile toyPredictorFamily) nextFalseQuery).toReal| ≤
            1 := by
  rcases trustTriangle_metaGoal_path_example with ⟨measures, _, _⟩
  have hstart :
      FixedRegionCylinderDLR
        (triangleChainSpec trustWt trustChain₀).toStrictlyPositiveInfiniteGroundMLNSpec
        (measures.startMeasure : MeasureTheory.Measure (InfiniteWorld Nat)) := by
    simpa [trustTriangleMetaGoalPath, MetaGoalShellPreservationPath.startSpec,
      trustTriangleMetaStep₀₁] using measures.startDLR
  have hend :
      FixedRegionCylinderDLR
        (triangleChainSpec trustWt trustChain₂).toStrictlyPositiveInfiniteGroundMLNSpec
        (measures.endMeasure : MeasureTheory.Measure (InfiniteWorld Nat)) := by
    simpa [trustTriangleMetaGoalPath, MetaGoalShellPreservationPath.endSpec,
      trustTriangleMetaStep₁₂] using measures.endDLR
  have hexact :=
    trustTriangle_exact_metaGoal_closure_example
      trustWt trustChain₀ trustChain₂
      trustWt_small trustChain₀_small trustChain₂_small
      measures.startMeasure measures.endMeasure hstart hend
  rcases hexact with ⟨himprove, heq⟩
  refine ⟨measures, himprove, ?_, ?_, ?_, ?_⟩
  · simpa [trustTriangleMetaGoalPath, MetaGoalShellPreservationPath.startSpec,
      MetaGoalShellPreservationPath.endSpec, trustTriangleMetaStep₀₁,
      trustTriangleMetaStep₁₂] using heq
  · exact geomApproxQueryStrength_mono toyPredictorFamily (by norm_num) [false]
  · exact geomApproxQueryStrength_le_full toyPredictorFamily 2 [false]
  · have hcond :=
        geomApproxConditionalQueryStrength_abs_sub_le
          toyPredictorFamily 2 nextFalseQuery
          oneHalf_ne_zero oneHalf_ne_top
          toyPredictorFamily_root_floor_two
    norm_num [nextFalseQuery, geomTailMass] at hcond ⊢
    exact hcond

end Mettapedia.UniversalAI.GodelMachine.MetaGoalUniversalApproximationExample
