import Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample
import Mettapedia.Logic.IntensionalInheritanceApproximationBridge

/-!
# Concrete Example: Self-Improving PLN Pattern-Miner Selector

This file packages three already-proved ingredients into one small example:

1. a proof-backed Gödel-machine rewrite path with protected WM goals,
2. a tiny universal-mixture family modelling pattern continuation hypotheses,
3. the approximate intensional-inheritance bridge used as a selector score.

Positive example:
- the candidate feature `[false]` strongly supports continuation `[false]`,
- the protected WM goal stays within the proved shell bound while the machine improves,
- and the approximate selector score stays within an explicit error envelope of
  the full intensional score.

Negative example:
- if context mass or conditional floors collapse, the logarithmic selector score
  can amplify approximation error, so no uniform selector theorem is claimed.
-/

namespace Mettapedia.UniversalAI.GodelMachine.PLNPatternMinerSelectorExample

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.IntensionalInheritance
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservationExample
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.Logic.MarkovLogicInfiniteVariableNeighborhoodWorldOfViews
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicTrustTriangleExample
open Mettapedia.Logic.PLNWorldModel

abbrev BinString := Mettapedia.Logic.UniversalPrediction.BinString
abbrev Semimeasure := Mettapedia.Logic.UniversalPrediction.Semimeasure

/-- Deterministic pattern model: once `[false]` is seen, `[false]` remains the
favored continuation. -/
def falseThenFalseSemimeasure : Semimeasure where
  toFun
    | [] => 1
    | [false] => 1
    | [false, false] => 1
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

/-- Deterministic distractor model: `[false]` is followed by `[true]`. -/
def falseThenTrueSemimeasure : Semimeasure where
  toFun
    | [] => 1
    | [false] => 1
    | [false, true] => 1
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

/-- Deterministic background model: the first bit is `true`. -/
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

/-- A tiny selector family:
- index `0`: the mined feature `[false]` predicts continuation `[false]`
- index `1`: the same feature predicts continuation `[true]`
- later indices: background models preferring first bit `[true]`
-/
noncomputable def patternMinerFamily : ℕ → Semimeasure
  | 0 => falseThenFalseSemimeasure
  | 1 => falseThenTrueSemimeasure
  | _ => trueFirstBitSemimeasure

/-- Empty mining context. -/
def miningContext : BinString := []

/-- Candidate feature detected by the miner. -/
def minedFeature : BinString := [false]

/-- Candidate continuation scored by the selector. -/
def minedContinuation : BinString := [false]

/-- Approximate selector score after `n` geometric-mixture components. -/
noncomputable def approxSelectorScore (n : ℕ) : ℝ :=
  approxIntensionalFromXiGeom patternMinerFamily n miningContext minedFeature minedContinuation

/-- Full selector score under the full geometric mixture. -/
noncomputable def fullSelectorScore : ℝ :=
  intensionalFromConditional
    (xiGeomSemimeasure patternMinerFamily)
    miningContext minedFeature minedContinuation

theorem patternMinerFamily_root_mass_one :
    (xiGeomApproxSemimeasure patternMinerFamily 1) miningContext = (1 / 2 : ENNReal) := by
  change xiApproxFun patternMinerFamily geometricWeight 1 miningContext = (1 / 2 : ENNReal)
  unfold xiApproxFun
  rw [Finset.sum_range_one]
  simp [patternMinerFamily, miningContext, geometricWeight, falseThenFalseSemimeasure]
  rw [ENNReal.zpow_neg]
  simp

theorem patternMinerFamily_feature_mass_one :
    (xiGeomApproxSemimeasure patternMinerFamily 1) minedFeature = (1 / 2 : ENNReal) := by
  change xiApproxFun patternMinerFamily geometricWeight 1 minedFeature = (1 / 2 : ENNReal)
  unfold xiApproxFun
  rw [Finset.sum_range_one]
  simp [patternMinerFamily, minedFeature, geometricWeight, falseThenFalseSemimeasure]
  rw [ENNReal.zpow_neg]
  simp

theorem patternMinerFamily_continuation_mass_one :
    (xiGeomApproxSemimeasure patternMinerFamily 1) minedContinuation = (1 / 2 : ENNReal) := by
  simpa [minedContinuation] using patternMinerFamily_feature_mass_one

theorem patternMinerFamily_feature_continuation_mass_one :
    (xiGeomApproxSemimeasure patternMinerFamily 1) (minedFeature ++ minedContinuation) =
      (1 / 2 : ENNReal) := by
  change
      xiApproxFun patternMinerFamily geometricWeight 1 (minedFeature ++ minedContinuation) =
        (1 / 2 : ENNReal)
  unfold xiApproxFun
  rw [Finset.sum_range_one]
  simp [patternMinerFamily, minedFeature, minedContinuation, geometricWeight,
    falseThenFalseSemimeasure]
  rw [ENNReal.zpow_neg]
  simp

theorem patternMinerFamily_root_floor :
    (1 / 2 : ENNReal) ≤ (xiGeomApproxSemimeasure patternMinerFamily 4) miningContext := by
  calc
    (1 / 2 : ENNReal) = (xiGeomApproxSemimeasure patternMinerFamily 1) miningContext := by
      simpa using patternMinerFamily_root_mass_one.symm
    _ ≤ (xiGeomApproxSemimeasure patternMinerFamily 4) miningContext := by
      exact xiGeomApproxSemimeasure_mono patternMinerFamily (by omega) miningContext

theorem patternMinerFamily_feature_floor :
    (1 / 2 : ENNReal) ≤ (xiGeomApproxSemimeasure patternMinerFamily 4) minedFeature := by
  calc
    (1 / 2 : ENNReal) = (xiGeomApproxSemimeasure patternMinerFamily 1) minedFeature := by
      simpa using patternMinerFamily_feature_mass_one.symm
    _ ≤ (xiGeomApproxSemimeasure patternMinerFamily 4) minedFeature := by
      exact xiGeomApproxSemimeasure_mono patternMinerFamily (by omega) minedFeature

theorem patternMinerFamily_continuation_floor :
    (1 / 2 : ENNReal) ≤ (xiGeomApproxSemimeasure patternMinerFamily 4) minedContinuation := by
  simpa [minedContinuation] using patternMinerFamily_feature_floor

theorem patternMinerFamily_feature_continuation_floor :
    (1 / 2 : ENNReal) ≤
      (xiGeomApproxSemimeasure patternMinerFamily 4) (minedFeature ++ minedContinuation) := by
  calc
    (1 / 2 : ENNReal) =
        (xiGeomApproxSemimeasure patternMinerFamily 1) (minedFeature ++ minedContinuation) := by
          simpa using patternMinerFamily_feature_continuation_mass_one.symm
    _ ≤ (xiGeomApproxSemimeasure patternMinerFamily 4) (minedFeature ++ minedContinuation) := by
      exact xiGeomApproxSemimeasure_mono patternMinerFamily (by omega)
        (minedFeature ++ minedContinuation)

theorem patternMinerFamily_full_continuation_floor :
    (1 / 2 : ENNReal) ≤ (xiGeomSemimeasure patternMinerFamily) minedContinuation := by
  calc
    (1 / 2 : ENNReal) = geometricWeight 0 * falseThenFalseSemimeasure minedContinuation := by
      simp [geometricWeight, minedContinuation, falseThenFalseSemimeasure]
      rw [ENNReal.zpow_neg]
      simp
    _ ≤ (xiGeomSemimeasure patternMinerFamily) minedContinuation := by
      exact xiGeom_dominates_index patternMinerFamily 0 minedContinuation

theorem patternMinerFamily_full_feature_continuation_floor :
    (1 / 2 : ENNReal) ≤
      (xiGeomSemimeasure patternMinerFamily) (minedFeature ++ minedContinuation) := by
  calc
    (1 / 2 : ENNReal) =
        geometricWeight 0 * falseThenFalseSemimeasure (minedFeature ++ minedContinuation) := by
          simp [geometricWeight, minedFeature, minedContinuation, falseThenFalseSemimeasure]
          rw [ENNReal.zpow_neg]
          simp
    _ ≤ (xiGeomSemimeasure patternMinerFamily) (minedFeature ++ minedContinuation) := by
      exact xiGeom_dominates_index patternMinerFamily 0
        (minedFeature ++ minedContinuation)

private theorem conditionalENN_toReal_ge_of_num_lower
    (μ : Semimeasure) (x y : BinString) {c : ℝ}
    (hc_pos : 0 < c)
    (hnum : c ≤ (μ (x ++ y)).toReal) :
    c ≤ (conditionalENN μ y x).toReal := by
  let a : ℝ := (μ (x ++ y)).toReal
  let b : ℝ := (μ x).toReal
  have hab : a ≤ b := by
    dsimp [a, b]
    exact ENNReal.toReal_mono (semimeasure_ne_top μ x) (μ.mono_append x y)
  have hb_le_one : b ≤ 1 := by
    dsimp [b]
    exact ENNReal.toReal_mono (by simp) (semimeasure_le_one μ x)
  have ha_pos : 0 < a := lt_of_lt_of_le hc_pos hnum
  have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
  have ha_le_div : a ≤ a / b := by
    rw [le_div_iff₀ hb_pos]
    nlinarith
  have hcond :
      (conditionalENN μ y x).toReal = a / b := by
    dsimp [a, b, conditionalENN]
    simp [ENNReal.toReal_div]
  rw [hcond]
  exact le_trans hnum ha_le_div

theorem patternMinerFamily_prior_approx_floor :
    (1 / 2 : ℝ) ≤ approxPriorFromXiGeom patternMinerFamily 4 miningContext minedContinuation := by
  have hnumENN : (1 / 2 : ENNReal) ≤
      (xiGeomApproxSemimeasure patternMinerFamily 4) minedContinuation :=
    patternMinerFamily_continuation_floor
  have hnumReal : (1 / 2 : ℝ) ≤
      ((xiGeomApproxSemimeasure patternMinerFamily 4) minedContinuation).toReal := by
    simpa using ENNReal.toReal_mono (semimeasure_ne_top _ _) hnumENN
  simpa [approxPriorFromXiGeom, priorFromConditional, miningContext] using
    conditionalENN_toReal_ge_of_num_lower
      (μ := xiGeomApproxSemimeasure patternMinerFamily 4)
      (x := miningContext) (y := minedContinuation)
      (c := (1 / 2 : ℝ)) (hc_pos := by norm_num) hnumReal

theorem patternMinerFamily_prior_full_floor :
    (1 / 2 : ℝ) ≤ priorFromConditional (xiGeomSemimeasure patternMinerFamily)
      miningContext minedContinuation := by
  have hnumReal : (1 / 2 : ℝ) ≤
      ((xiGeomSemimeasure patternMinerFamily) minedContinuation).toReal := by
    simpa using
      ENNReal.toReal_mono (semimeasure_ne_top _ _) patternMinerFamily_full_continuation_floor
  simpa [priorFromConditional, miningContext] using
    conditionalENN_toReal_ge_of_num_lower
      (μ := xiGeomSemimeasure patternMinerFamily)
      (x := miningContext) (y := minedContinuation)
      (c := (1 / 2 : ℝ)) (hc_pos := by norm_num) hnumReal

theorem patternMinerFamily_ext_approx_floor :
    (1 / 2 : ℝ) ≤ approxExtensionalFromXiGeom patternMinerFamily 4
      miningContext minedFeature minedContinuation := by
  have hnumENN : (1 / 2 : ENNReal) ≤
      (xiGeomApproxSemimeasure patternMinerFamily 4) (minedFeature ++ minedContinuation) :=
    patternMinerFamily_feature_continuation_floor
  have hnumReal : (1 / 2 : ℝ) ≤
      ((xiGeomApproxSemimeasure patternMinerFamily 4) (minedFeature ++ minedContinuation)).toReal := by
    simpa using ENNReal.toReal_mono (semimeasure_ne_top _ _) hnumENN
  simpa [approxExtensionalFromXiGeom, extensionalFromConditional, miningContext] using
    conditionalENN_toReal_ge_of_num_lower
      (μ := xiGeomApproxSemimeasure patternMinerFamily 4)
      (x := minedFeature) (y := minedContinuation)
      (c := (1 / 2 : ℝ)) (hc_pos := by norm_num) hnumReal

theorem patternMinerFamily_ext_full_floor :
    (1 / 2 : ℝ) ≤ extensionalFromConditional (xiGeomSemimeasure patternMinerFamily)
      miningContext minedFeature minedContinuation := by
  have hnumReal : (1 / 2 : ℝ) ≤
      ((xiGeomSemimeasure patternMinerFamily) (minedFeature ++ minedContinuation)).toReal := by
    simpa using
      ENNReal.toReal_mono (semimeasure_ne_top _ _) patternMinerFamily_full_feature_continuation_floor
  simpa [extensionalFromConditional, miningContext] using
    conditionalENN_toReal_ge_of_num_lower
      (μ := xiGeomSemimeasure patternMinerFamily)
      (x := minedFeature) (y := minedContinuation)
      (c := (1 / 2 : ℝ)) (hc_pos := by norm_num) hnumReal

theorem approxSelectorScore_abs_sub_le :
    |approxSelectorScore 4 - fullSelectorScore| ≤ 1 / Real.log 2 := by
  have hmain :=
    approxIntensionalFromXiGeom_abs_sub_le
      patternMinerFamily 4 miningContext minedFeature minedContinuation
      (by norm_num : (1 / 2 : ENNReal) ≠ 0) (by norm_num : (1 / 2 : ENNReal) ≠ ⊤)
      (by norm_num : (1 / 2 : ENNReal) ≠ 0) (by norm_num : (1 / 2 : ENNReal) ≠ ⊤)
      (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : 0 < (1 / 2 : ℝ))
      patternMinerFamily_root_floor
      patternMinerFamily_feature_floor
      patternMinerFamily_prior_approx_floor
      patternMinerFamily_prior_full_floor
      patternMinerFamily_ext_approx_floor
      patternMinerFamily_ext_full_floor
  norm_num [approxSelectorScore, fullSelectorScore, geomTailMass] at hmain ⊢
  exact hmain

/-- Concrete selector example:
- the proof-backed trust-triangle path improves utility,
- the protected WM goal remains within the shell bound `12`,
- and the approximate pattern-miner selector score stays within the explicit
  intensional error envelope. -/
theorem trustTriangle_metaGoal_and_patternMiner_selector_example :
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
        |approxSelectorScore 4 - fullSelectorScore| ≤ 1 / Real.log 2 := by
  rcases trustTriangle_metaGoal_path_example with ⟨measures, himprove, hdrift⟩
  exact ⟨measures, himprove, hdrift, approxSelectorScore_abs_sub_le⟩

end Mettapedia.UniversalAI.GodelMachine.PLNPatternMinerSelectorExample
