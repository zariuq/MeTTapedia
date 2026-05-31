import Mettapedia.Logic.IntensionalInheritance
import Mettapedia.InformationTheory.MutualInformation

/-!
# Empirical Intensional Information for Concept-Membership Events

This file gives a concrete finite model for Chapter-12-style reasoning over a
binary membership table:

- feature absent / present
- witness absent / present

It deliberately keeps two different objects side by side:

1. the **pointwise log-ratio score** for the update `P(W | F)` versus `P(W)`
2. the **Shannon mutual information** of the whole 2×2 joint table
-/

namespace Mettapedia.Logic.IntensionalInheritance

open Mettapedia.InformationTheory

/-- Counts for a binary feature/witness contingency table.

We use the convention:
- `neither`: neither `F` nor `W`
- `witnessOnly`: `W` but not `F`
- `featureOnly`: `F` but not `W`
- `both`: both `F` and `W`
-/
structure MembershipCounts where
  neither : ℕ
  witnessOnly : ℕ
  featureOnly : ℕ
  both : ℕ
  total_pos : 0 < neither + witnessOnly + featureOnly + both

namespace MembershipCounts

/-- Total number of observations. -/
def total (c : MembershipCounts) : ℕ :=
  c.neither + c.witnessOnly + c.featureOnly + c.both

/-- Number of observations where the witness concept holds. -/
def witnessSupport (c : MembershipCounts) : ℕ :=
  c.witnessOnly + c.both

/-- Number of observations where the feature concept holds. -/
def featureSupport (c : MembershipCounts) : ℕ :=
  c.featureOnly + c.both

/-- Prior probability `P(W)`. -/
noncomputable def priorProbWitness (c : MembershipCounts) : ℝ :=
  (c.witnessSupport : ℝ) / c.total

/-- Prior probability `P(F)`. -/
noncomputable def priorProbFeature (c : MembershipCounts) : ℝ :=
  (c.featureSupport : ℝ) / c.total

/-- Extensional inheritance `P(W | F)` extracted from the 2×2 table. -/
noncomputable def extensionalInheritance (c : MembershipCounts) : ℝ :=
  if c.featureSupport = 0 then
    0
  else
    (c.both : ℝ) / c.featureSupport

/-- Chapter-12 pointwise intensional score in bits, read from the empirical table. -/
noncomputable def pointwiseIntensionalScoreBits (c : MembershipCounts) : ℝ :=
  logRatioInformationGainFromEvidence (extensionalInheritance c) (priorProbWitness c)

/-- Fin-2 encoding of the empirical joint distribution.

Index convention:
- `0` = false / absent
- `1` = true / present
-/
noncomputable def jointMembershipDist (c : MembershipCounts) : JointProb 2 2 :=
  ⟨fun ij =>
      match ij with
      | (0, 0) => (c.neither : ℝ) / c.total
      | (0, 1) => (c.witnessOnly : ℝ) / c.total
      | (1, 0) => (c.featureOnly : ℝ) / c.total
      | (1, 1) => (c.both : ℝ) / c.total,
    by
      constructor
      · intro ij
        rcases ij with ⟨i, j⟩
        fin_cases i <;> fin_cases j <;> positivity
      ·
        have hTotalNe : (c.total : ℝ) ≠ 0 := by
          exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt c.total_pos)
        have hTotalCast :
            (c.total : ℝ) = (c.neither : ℝ) + c.witnessOnly + c.featureOnly + c.both := by
          norm_num [MembershipCounts.total]
        simp [MembershipCounts.total, Fintype.sum_prod_type]
        calc
          (c.neither : ℝ) / (c.neither + c.witnessOnly + c.featureOnly + c.both) +
                c.witnessOnly / (c.neither + c.witnessOnly + c.featureOnly + c.both) +
              (c.featureOnly / (c.neither + c.witnessOnly + c.featureOnly + c.both) +
                c.both / (c.neither + c.witnessOnly + c.featureOnly + c.both))
              = ((c.neither : ℝ) + c.witnessOnly + c.featureOnly + c.both) /
                  ((c.neither : ℝ) + c.witnessOnly + c.featureOnly + c.both) := by
                  ring_nf
          _ = (c.total : ℝ) / c.total := by simp [hTotalCast]
          _ = 1 := by field_simp [hTotalNe]⟩

/-- The witness prior read from the empirical joint distribution. -/
theorem marginalRight_true_eq_priorProbWitness (c : MembershipCounts) :
    (JointProb.marginalRight (jointMembershipDist c)).1 1 = priorProbWitness c := by
  have hTotalNe : (c.total : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt c.total_pos)
  simp [JointProb.marginalRight, jointMembershipDist, priorProbWitness, witnessSupport]
  field_simp [MembershipCounts.total, hTotalNe]

/-- The feature prior read from the empirical joint distribution. -/
theorem marginalLeft_true_eq_priorProbFeature (c : MembershipCounts) :
    (JointProb.marginalLeft (jointMembershipDist c)).1 1 = priorProbFeature c := by
  have hTotalNe : (c.total : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt c.total_pos)
  simp [JointProb.marginalLeft, jointMembershipDist, priorProbFeature, featureSupport]
  field_simp [MembershipCounts.total, hTotalNe]

/-- Shannon mutual information of the empirical 2×2 table, in nats. -/
noncomputable def shannonMutualInformationNats (c : MembershipCounts) : ℝ :=
  JointProb.shannonMutualInformationNats (jointMembershipDist c)

/-- Shannon mutual information of the empirical 2×2 table, in bits. -/
noncomputable def shannonMutualInformationBits (c : MembershipCounts) : ℝ :=
  JointProb.shannonMutualInformationBits (jointMembershipDist c)

/-- Expected log-ratio information gain of the empirical 2×2 table, in bits. -/
noncomputable def expectedLogRatioToProductBits (c : MembershipCounts) : ℝ :=
  JointProb.expectedLogRatioToProductBits (jointMembershipDist c)

theorem shannonMutualInformationBits_eq_expectedLogRatioToProductBits
    (c : MembershipCounts) :
    shannonMutualInformationBits c = expectedLogRatioToProductBits c := by
  unfold shannonMutualInformationBits expectedLogRatioToProductBits
  exact JointProb.shannonMutualInformationBits_eq_expectedLogRatioToProductBits _

theorem extensionalInheritance_eq_prior_mul_two_rpow_pointwiseIntensionalScoreBits
    (c : MembershipCounts)
    (hExt : 0 < extensionalInheritance c)
    (hPrior : 0 < priorProbWitness c) :
    extensionalInheritance c =
      priorProbWitness c * (2 : ℝ).rpow (pointwiseIntensionalScoreBits c) := by
  unfold pointwiseIntensionalScoreBits
  exact strength_eq_prior_mul_two_rpow_logRatioInformationGainFromEvidence hExt hPrior

/-! ## Positive and negative examples -/

def positiveExample : MembershipCounts where
  neither := 2
  witnessOnly := 1
  featureOnly := 1
  both := 6
  total_pos := by decide

def zeroFeatureSupportExample : MembershipCounts where
  neither := 3
  witnessOnly := 2
  featureOnly := 0
  both := 0
  total_pos := by decide

example : priorProbWitness positiveExample = (7 : ℝ) / 10 := by
  norm_num [priorProbWitness, witnessSupport, total, positiveExample]

example : 0 < extensionalInheritance positiveExample := by
  norm_num [extensionalInheritance, featureSupport, positiveExample]

example : extensionalInheritance zeroFeatureSupportExample = 0 := by
  simp [extensionalInheritance, featureSupport, zeroFeatureSupportExample]

example : pointwiseIntensionalScoreBits zeroFeatureSupportExample = 0 := by
  unfold pointwiseIntensionalScoreBits logRatioInformationGainFromEvidence
    Mettapedia.InformationTheory.logRatioInformationGainBits
  simp [extensionalInheritance, featureSupport,
    zeroFeatureSupportExample]

end MembershipCounts

end Mettapedia.Logic.IntensionalInheritance
