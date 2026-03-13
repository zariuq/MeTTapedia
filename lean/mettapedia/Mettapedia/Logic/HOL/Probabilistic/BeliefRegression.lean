import Mettapedia.Logic.HOL.Probabilistic.BeliefBridge
import Mettapedia.Logic.HOL.Probabilistic.HierarchicalRegression

/-!
# Regression Surface for the Semantic-vs-Belief ProbHOL Bridge

This module packages positive and negative fixtures for the bridge between:

- semantic probabilistic HOL over measurable indexed model/model-measure spaces,
- hierarchical and infinite-order semantic `ProbHOL`, and
- the Logical-Induction-ready belief-day/process layer.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), these regression fixtures keep
belief dynamics and semantic truth distinct while proving exact agreement on
selected examples.
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WorldModel
open Mettapedia.Logic.HOL.LogicalInduction
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

local instance instBeliefRegressionEmpiricalMeasurableSpace :
    MeasurableSpace (HenkinModel FixtureBase FixtureConst) := ⊤

private theorem empiricalPair_ne_zero : empiricalPair ≠ 0 := by
  simp [empiricalPair]

noncomputable abbrev bridgeEmpiricalPairMeasure :
    MeasureTheory.Measure (HenkinModel FixtureBase FixtureConst) :=
  (PMF.ofMultiset empiricalPair empiricalPair_ne_zero).toMeasure

/-- Finite sample used to compare the empirical belief day against semantic
probability on both a nontrivial query and the always-true query. -/
noncomputable def empiricalPairBridgeSample : Finset (ClosedFormulaCode FixtureConst) :=
  { encodeClosedFormula flagSentence,
    encodeClosedFormula (.top : ClosedFormula FixtureConst) }

private theorem empiricalPair_day_strength_flag_half :
    dayQueryStrength
      (Const := FixtureConst)
      (empiricalBeliefDay (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (encodeClosedFormula flagSentence) =
      (1 / 2 : ℝ≥0∞) := by
  have htrack :=
    empiricalBeliefDay_tracks_empiricalSentenceProb
      (Base := FixtureBase) (Const := FixtureConst)
      empiricalPair empiricalPair_ne_zero flagSentence
  have hprob :
      probQueryStrength
        (empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
        bridgeEmpiricalPairMeasure
        flagSentence = (1 / 2 : ℝ≥0∞) := by
    rw [probQueryStrength_eq_sentenceProb
      (S := empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (μ := bridgeEmpiricalPairMeasure)
      (hμ := by infer_instance)]
    simpa [bridgeEmpiricalPairMeasure] using regression_empirical_pair_flag_half
  exact htrack.trans hprob

private theorem empiricalPair_day_strength_top_one :
    dayQueryStrength
      (Const := FixtureConst)
      (empiricalBeliefDay (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (encodeClosedFormula (.top : ClosedFormula FixtureConst)) =
      (1 : ℝ≥0∞) := by
  have htrack :=
    empiricalBeliefDay_tracks_empiricalSentenceProb
      (Base := FixtureBase) (Const := FixtureConst)
      empiricalPair empiricalPair_ne_zero (.top : ClosedFormula FixtureConst)
  have hprob :
      probQueryStrength
        (empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
        bridgeEmpiricalPairMeasure
        (.top : ClosedFormula FixtureConst) = 1 := by
    rw [probQueryStrength_eq_sentenceProb
      (S := empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (μ := bridgeEmpiricalPairMeasure)
      (hμ := by infer_instance)]
    exact sentenceProb_top_eq_one
      (S := empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (μ := bridgeEmpiricalPairMeasure)
      (hμ := by infer_instance)
  exact htrack.trans hprob

/-- Positive bridge canary: the empirical belief day exactly tracks semantic
sentence probability on the chosen finite sample. -/
theorem regression_empiricalBeliefDay_tracks_empiricalPair_sample :
    BeliefDayTracksSentenceProbOn
      (Const := FixtureConst)
      (empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      bridgeEmpiricalPairMeasure
      (empiricalBeliefDay (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      empiricalPairBridgeSample := by
  intro φ hφ
  rcases Finset.mem_insert.mp hφ with hflag | htop
  · subst hflag
    rw [probQueryStrength_eq_sentenceProb
      (S := empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (μ := bridgeEmpiricalPairMeasure)
      (hμ := by infer_instance)]
    rw [decode_encodeClosedFormula]
    rw [regression_empirical_pair_flag_half]
    exact empiricalPair_day_strength_flag_half
  · have htop' : φ = encodeClosedFormula (.top : ClosedFormula FixtureConst) := by
      simpa using htop
    subst htop'
    rw [probQueryStrength_eq_sentenceProb
      (S := empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (μ := bridgeEmpiricalPairMeasure)
      (hμ := by infer_instance)]
    rw [decode_encodeClosedFormula]
    rw [sentenceProb_top_eq_one
      (S := empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (μ := bridgeEmpiricalPairMeasure)
      (hμ := by infer_instance)]
    exact empiricalPair_day_strength_top_one

/-- Positive bridge canary: the same empirical belief day also tracks the
hierarchical constant-measure lift of that semantic sample. -/
theorem regression_empiricalBeliefDay_tracks_empiricalHierarchicalSample :
    BeliefDayTracksHierarchicalProbOn
      (Const := FixtureConst)
      (HierarchicalState.ofConstantMeasure
        (empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
        bridgeEmpiricalPairMeasure)
      (empiricalBeliefDay (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      empiricalPairBridgeSample := by
  intro φ hφ
  rcases Finset.mem_insert.mp hφ with hflag | htop
  · subst hflag
    rw [hierarchicalProbQueryStrength_eq_sentenceProb,
      hierarchicalSentenceProb_ofConstantMeasure_eq_sentenceProb]
    rw [decode_encodeClosedFormula]
    rw [regression_empirical_pair_flag_half]
    exact empiricalPair_day_strength_flag_half
  · have htop' : φ = encodeClosedFormula (.top : ClosedFormula FixtureConst) := by
      simpa using htop
    subst htop'
    rw [hierarchicalProbQueryStrength_eq_sentenceProb,
      hierarchicalSentenceProb_ofConstantMeasure_eq_sentenceProb]
    rw [decode_encodeClosedFormula]
    rw [sentenceProb_top_eq_one
      (S := empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (μ := bridgeEmpiricalPairMeasure)
      (hμ := by infer_instance)]
    exact empiricalPair_day_strength_top_one

/-- Negative bridge canary: the constant-half belief day does not track the
empirical semantic sample once the always-true query is included. -/
theorem regression_processHalf_not_tracks_empiricalPair_sample :
    ¬ BeliefDayTracksSentenceProbOn
      (Const := FixtureConst)
      (empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      bridgeEmpiricalPairMeasure
      (processHalf (Const := FixtureConst) 0)
      empiricalPairBridgeSample := by
  intro htrack
  have htop :=
    htrack (φ := encodeClosedFormula (.top : ClosedFormula FixtureConst))
      (by simp [empiricalPairBridgeSample])
  have hhalf :
      dayQueryStrength
        (Const := FixtureConst)
        (processHalf (Const := FixtureConst) 0)
        (encodeClosedFormula (.top : ClosedFormula FixtureConst)) =
        (1 / 2 : ℝ≥0∞) := by
    rw [dayQueryStrength_eq_price]
    simp [processHalf, constantProcess, constantDay, Price01.half]
  have hone :
      probQueryStrength
        (empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
        bridgeEmpiricalPairMeasure
        (.top : ClosedFormula FixtureConst) = 1 := by
    rw [probQueryStrength_eq_sentenceProb
      (S := empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (μ := bridgeEmpiricalPairMeasure)
      (hμ := by infer_instance)]
    exact sentenceProb_top_eq_one
      (S := empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
      (μ := bridgeEmpiricalPairMeasure)
      (hμ := by infer_instance)
  have hcontra : (1 / 2 : ℝ≥0∞) = 1 := by
    calc
      (1 / 2 : ℝ≥0∞) =
          dayQueryStrength
            (Const := FixtureConst)
            (processHalf (Const := FixtureConst) 0)
            (encodeClosedFormula (.top : ClosedFormula FixtureConst)) := hhalf.symm
      _ =
          probQueryStrength
            (empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
            bridgeEmpiricalPairMeasure
            (decodeClosedFormula (encodeClosedFormula (.top : ClosedFormula FixtureConst))) := htop
      _ = 1 := by simpa using hone
  norm_num at hcontra

/-- Singleton sample used for the top-sentence process-level bridge. -/
def topBridgeSample (Const : Ty Base → Type v) : Finset (ClosedFormulaCode Const) :=
  { encodeClosedFormula (.top : ClosedFormula Const) }

/-- Positive process-level bridge: the constant-one process eventually tracks
semantic probability on the top-sentence sample, for every probabilistic HOL
model space. -/
theorem regression_processOne_eventuallyTracksSentenceProbOn_top
    (S : ModelSpace Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (hμ : MeasureTheory.IsProbabilityMeasure μ) :
    BeliefProcessEventuallyTracksSentenceProbOn
      (Const := Const)
      S μ (topBridgeSample Const) (processOne (Const := Const)) := by
  refine eventuallyExactOnFiniteSample_implies_eventuallyTracksSentenceProbOn
    (S := S) (μ := μ)
    (target := constantDay (Const := Const) Price01.one)
    (sample := topBridgeSample Const)
    (P := processOne (Const := Const))
    ?_ ?_
  · exact processOne_eventuallyExactOnFiniteSample_one
      (Const := Const) (topBridgeSample Const)
  · intro φ hφ
    have htop : φ = encodeClosedFormula (.top : ClosedFormula Const) := by
      simpa [topBridgeSample] using hφ
    subst htop
    simpa [topBridgeSample] using constantOne_tracks_sentenceProb_top
      (Const := Const) S μ hμ

/-- Negative day-level bridge canary: the constant-half day does not track
semantic probability on `⊤`. -/
theorem regression_constantHalf_not_tracksSentenceProb_top
    (S : ModelSpace Base Const)
    (μ : MeasureTheory.Measure S.Idx)
    (hμ : MeasureTheory.IsProbabilityMeasure μ) :
    ¬ BeliefDayTracksSentenceProb
      (Const := Const)
      S μ
      (constantDay (Const := Const) Price01.half)
      (.top : ClosedFormula Const) := by
  intro htrack
  unfold BeliefDayTracksSentenceProb at htrack
  have hhalf :
      dayQueryStrength
        (Const := Const)
        (constantDay (Const := Const) Price01.half)
        (encodeClosedFormula (.top : ClosedFormula Const)) =
        (1 / 2 : ℝ≥0∞) := by
    rw [dayQueryStrength_eq_price]
    simp [constantDay, Price01.half]
  have hone :
      probQueryStrength S μ (.top : ClosedFormula Const) = 1 := by
    rw [probQueryStrength_eq_sentenceProb S μ hμ]
    exact sentenceProb_top_eq_one (S := S) (μ := μ) (hμ := hμ)
  have hcontra : (1 / 2 : ℝ≥0∞) = 1 := by
    calc
      (1 / 2 : ℝ≥0∞) =
          dayQueryStrength
            (Const := Const)
            (constantDay (Const := Const) Price01.half)
            (encodeClosedFormula (.top : ClosedFormula Const)) := hhalf.symm
      _ = probQueryStrength S μ (.top : ClosedFormula Const) := htrack
      _ = 1 := hone
  norm_num at hcontra

end Mettapedia.Logic.HOL.Probabilistic
