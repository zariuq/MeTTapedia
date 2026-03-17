import Mathlib.Probability.Distributions.Geometric
import Mettapedia.Logic.HOL.Probabilistic.EmpiricalSpecialCase
import Mettapedia.Logic.HOL.Probabilistic.IndexedSpaces

/-!
# Regression Surface for Probabilistic HOL Semantics

This module packages the main positive and negative regression fixtures for the
infinitary-first `ProbHOL` semantics.

The semantic reading follows the higher-order probability/Kyburg line already
present elsewhere in the repository: closed HOL formulas receive probabilities
relative to measurable index spaces of pointed Henkin models.  The empirical
multiset HOL↔WM semantics is then recovered as a theorem-proved special case.

This semantic layer remains distinct from the dynamic belief-process overlay
motivated by Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020).
-/

namespace Mettapedia.Logic.HOL.Probabilistic

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WorldModel
open scoped ENNReal

abbrev FixtureBase := PUnit

inductive FixtureConst : Ty FixtureBase → Type
  | flag : FixtureConst .prop
deriving DecidableEq, Repr

/-- Closed HOL formula represented by the single propositional constant `flag`. -/
def flagSentence : ClosedFormula FixtureConst :=
  .const FixtureConst.flag

/-- Tiny standard model family whose only varying datum is the truth value of
the closed proposition `flag`. -/
def flagModel (n : Nat) : HenkinModel FixtureBase FixtureConst :=
  HenkinModel.standard
    (Carrier := fun _ => PUnit)
    (constDen := by
      intro τ c
      cases c with
      | flag => exact ULift.up (n = 0))

@[simp] theorem flagModel_models_flag_iff (n : Nat) :
    holSatisfies (flagModel n) flagSentence ↔ n = 0 := by
  change (ULift.up (n = 0)).down ↔ n = 0
  simp

/-- Infinitary model space indexed by the genuinely infinite type `Nat`. -/
noncomputable def natFlagSpace : ModelSpace FixtureBase FixtureConst where
  Idx := Nat
  instMeasurableSpace := inferInstance
  model := flagModel
  measurable_sentence_event := by
    intro φ
    exact Set.Countable.measurableSet (Set.to_countable _)

@[simp] theorem natFlagSpace_sentenceEvent_flag :
    (natFlagSpace.sentenceEvent flagSentence : Set Nat) = ({(0 : Nat)} : Set Nat) := by
  change ({n : Nat | holSatisfies (flagModel n) flagSentence} : Set Nat) = ({(0 : Nat)} : Set Nat)
  ext n
  simp [flagModel_models_flag_iff]

private theorem half_pos : (0 : ℝ) < 1 / 2 := by
  norm_num

private theorem half_le_one : (1 / 2 : ℝ) ≤ 1 := by
  norm_num

/-- Positive infinitary canary: under a geometric measure on the genuinely
infinite index type `Nat`, the sentence probability of `flag` is `1/2`. -/
theorem regression_nat_geometric_flag_half :
    sentenceProb natFlagSpace
      ((ProbabilityTheory.geometricMeasure (p := (1 / 2 : ℝ)) half_pos half_le_one) :
        MeasureTheory.Measure natFlagSpace.Idx)
      flagSentence =
      (1 / 2 : ℝ≥0∞) := by
  rw [sentenceProb, natFlagSpace_sentenceEvent_flag]
  rw [ProbabilityTheory.geometricMeasure]
  have hsingleton :
      (ProbabilityTheory.geometricPMF half_pos half_le_one).toMeasure ({0} : Set Nat) =
        ProbabilityTheory.geometricPMF half_pos half_le_one 0 := by
    simpa using
      (PMF.toMeasure_apply_singleton
        (p := ProbabilityTheory.geometricPMF half_pos half_le_one)
        (a := 0) (h := by simp))
  have hpmf0 :
      ProbabilityTheory.geometricPMF half_pos half_le_one 0 = (1 / 2 : ℝ≥0∞) := by
    change ENNReal.ofReal (((1 - (1 / 2 : ℝ)) ^ (0 : ℕ)) * (1 / 2 : ℝ)) =
      (1 / 2 : ℝ≥0∞)
    rw [show (((1 - (1 / 2 : ℝ)) ^ (0 : ℕ)) * (1 / 2 : ℝ)) = (1 / 2 : ℝ) by norm_num]
    rw [show (1 / 2 : ℝ) = ((2 : ℝ)⁻¹) by norm_num]
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  calc
    (ProbabilityTheory.geometricPMF half_pos half_le_one).toMeasure ({0} : Set Nat)
        = ProbabilityTheory.geometricPMF half_pos half_le_one 0 := hsingleton
    _ = (1 / 2 : ℝ≥0∞) := hpmf0

/-- Negative infinitary canary: the same sentence does not have probability `1`
under the geometric-indexed model space. -/
theorem regression_nat_geometric_flag_ne_one :
    sentenceProb natFlagSpace
      ((ProbabilityTheory.geometricMeasure (p := (1 / 2 : ℝ)) half_pos half_le_one) :
        MeasureTheory.Measure natFlagSpace.Idx)
      flagSentence ≠ 1 := by
  rw [regression_nat_geometric_flag_half]
  norm_num

/-- Equality/rewrite canary: pointwise equivalence on the indexed model family
forces equality of sentence probabilities. -/
theorem regression_nat_geometric_and_top_eq_flag :
    sentenceProb natFlagSpace
      ((ProbabilityTheory.geometricMeasure (p := (1 / 2 : ℝ)) half_pos half_le_one) :
        MeasureTheory.Measure natFlagSpace.Idx)
      (.and flagSentence .top) =
      sentenceProb natFlagSpace
        ((ProbabilityTheory.geometricMeasure (p := (1 / 2 : ℝ)) half_pos half_le_one) :
          MeasureTheory.Measure natFlagSpace.Idx)
        flagSentence := by
  exact sentenceProb_eq_of_pointwiseIff
    (S := natFlagSpace)
    (μ := ((ProbabilityTheory.geometricMeasure (p := (1 / 2 : ℝ)) half_pos half_le_one) :
      MeasureTheory.Measure natFlagSpace.Idx))
    (φ := (.and flagSentence .top))
    (ψ := flagSentence) <| by
      intro n
      constructor
      · intro h
        exact (HenkinModel.models_and (natFlagSpace.model n)).1 h |>.1
      · intro h
        exact (HenkinModel.models_and (natFlagSpace.model n)).2 ⟨h, HenkinModel.models_top _⟩

/-- Two-point empirical sample with one satisfying and one non-satisfying
occurrence of `flag`. -/
abbrev flagTrueModel : HenkinModel FixtureBase FixtureConst := flagModel 0

abbrev flagFalseModel : HenkinModel FixtureBase FixtureConst := flagModel 1

@[simp] theorem holSatisfies_flagTrueModel :
    holSatisfies flagTrueModel flagSentence := by
  exact (flagModel_models_flag_iff 0).2 rfl

@[simp] theorem holNotSatisfies_flagFalseModel :
    ¬ holSatisfies flagFalseModel flagSentence := by
  intro h
  exact Nat.one_ne_zero ((flagModel_models_flag_iff 1).1 h)

def empiricalPair : Multiset (HenkinModel FixtureBase FixtureConst) :=
  ({flagTrueModel, flagFalseModel} : Multiset (HenkinModel FixtureBase FixtureConst))

local instance instRegressionEmpiricalMeasurableSpace :
    MeasurableSpace (HenkinModel FixtureBase FixtureConst) := ⊤

private theorem empiricalPair_ne_zero : empiricalPair ≠ 0 := by
  simp [empiricalPair]

/-- Positive finitary canary: the empirical special-case theorem recovers the
expected half/half sentence probability on a two-point sample. -/
theorem regression_empirical_pair_flag_half :
    sentenceProb
        (empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
        (PMF.ofMultiset empiricalPair empiricalPair_ne_zero).toMeasure
        flagSentence =
      (1 / 2 : ℝ≥0∞) := by
  classical
  have hcount :
      Multiset.countP
          (fun M : HenkinModel FixtureBase FixtureConst => holSatisfies M flagSentence)
          empiricalPair = 1 := by
    rw [Multiset.countP_eq_card_filter]
    simp [empiricalPair]
  rw [empiricalSentenceProb_eq_count_ratio
      (Base := FixtureBase) (Const := FixtureConst)
      empiricalPair empiricalPair_ne_zero flagSentence]
  rw [hcount]
  norm_num [empiricalPair]

/-- Regression-facing restatement of the theorem that the empirical
probabilistic query strength coincides with the existing static HOL-WM
query-strength semantics. -/
theorem regression_empirical_probStrength_eq_static :
    probQueryStrength
        (empiricalModelSpace (Base := FixtureBase) (Const := FixtureConst) empiricalPair)
        (PMF.ofMultiset empiricalPair empiricalPair_ne_zero).toMeasure
        flagSentence =
      Mettapedia.Logic.PLNWorldModel.BinaryWorldModel.queryStrength
        (State := Multiset (HenkinModel FixtureBase FixtureConst))
        (Query := HOLQuery FixtureConst)
        empiricalPair
        flagSentence :=
  empiricalProbQueryStrength_eq_staticQueryStrength
    (Base := FixtureBase) (Const := FixtureConst)
    empiricalPair empiricalPair_ne_zero flagSentence

end Mettapedia.Logic.HOL.Probabilistic
