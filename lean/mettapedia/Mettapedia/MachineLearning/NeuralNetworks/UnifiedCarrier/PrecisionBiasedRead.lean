import Mettapedia.MachineLearning.NeuralNetworks.Architecture.LogitPriorAdjustment
import Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier.Core

/-!
# Precision-biased softmax reads

This module closes the normalized-read algebra for the unified carrier.  A
nonnegative precision coordinate reweights the ordinary softmax mass by the
real power `(1 + precision) ^ readBeta root`.  Consequently, normalized
weights are exactly proportional to those powered masses, paired read odds
increase strictly with one precision coordinate when the bias root is
nonzero, and zero or spatially uniform bias recovers the ordinary read.

The identities are deterministic softmax algebra.  They do not by themselves
give the precision coordinates a posterior-predictive interpretation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier

open Mettapedia.MachineLearning.NeuralNetworks.Architecture

noncomputable section

variable {Slot : Type*}

/-- The normalized softmax weight after applying the carrier's precision
logit correction. -/
def precisionBiasedReadWeight [Fintype Slot]
    (base precision : Slot → ℝ) (root : ℝ) (slot : Slot) : ℝ :=
  categoricalSoftmaxProbability
    (fun item ↦ precisionBiasedLogit (base item) root (precision item)) slot

/-- The corrected exponential mass is the ordinary exponential mass times a
real power of one plus precision. -/
theorem exp_precisionBiasedLogit_eq_poweredMass
    (base root precision : ℝ) (hprecision : 0 ≤ precision) :
    Real.exp (precisionBiasedLogit base root precision) =
      Real.exp base * (1 + precision) ^ readBeta root := by
  have hpositive : 0 < 1 + precision := by linarith
  rw [precisionBiasedLogit, Real.exp_add,
    Real.rpow_def_of_pos hpositive]
  congr 1
  ring_nf

/-- Exact normalized form of the precision-biased read.  This is the
softmax-proportionality identity: every mass is reweighted by
`(1 + precision) ^ readBeta root`, including in the common normalizer. -/
theorem precisionBiasedReadWeight_eq_poweredMass_div_sum
    [Fintype Slot]
    (base precision : Slot → ℝ) (root : ℝ)
    (hprecision : ∀ slot, 0 ≤ precision slot) (slot : Slot) :
    precisionBiasedReadWeight base precision root slot =
      (Real.exp (base slot) * (1 + precision slot) ^ readBeta root) /
        ∑ item, Real.exp (base item) *
          (1 + precision item) ^ readBeta root := by
  classical
  simp only [precisionBiasedReadWeight, categoricalSoftmaxProbability,
    attentionWeight, attentionMass]
  rw [exp_precisionBiasedLogit_eq_poweredMass
    (base slot) root (precision slot) (hprecision slot)]
  congr 1
  apply Finset.sum_congr rfl
  intro item _
  exact exp_precisionBiasedLogit_eq_poweredMass
    (base item) root (precision item) (hprecision item)

/-- Softmax normalization cancels from the odds of two precision-biased
slots. -/
theorem precisionBiasedReadWeight_div
    [Fintype Slot] [Nonempty Slot]
    (base precision : Slot → ℝ) (root : ℝ) (left right : Slot) :
    precisionBiasedReadWeight base precision root left /
        precisionBiasedReadWeight base precision root right =
      Real.exp
        (precisionBiasedLogit (base left) root (precision left) -
          precisionBiasedLogit (base right) root (precision right)) := by
  exact categoricalSoftmaxProbability_div
    (fun item ↦ precisionBiasedLogit (base item) root (precision item))
    left right

/-- Pairwise read odds are exactly the ratio of the two powered masses. -/
theorem precisionBiasedReadWeight_odds_eq_poweredMassRatio
    [Fintype Slot] [Nonempty Slot]
    (base precision : Slot → ℝ) (root : ℝ)
    (hprecision : ∀ slot, 0 ≤ precision slot) (left right : Slot) :
    precisionBiasedReadWeight base precision root left /
        precisionBiasedReadWeight base precision root right =
      (Real.exp (base left) *
          (1 + precision left) ^ readBeta root) /
        (Real.exp (base right) *
          (1 + precision right) ^ readBeta root) := by
  rw [precisionBiasedReadWeight_div, Real.exp_sub,
    exp_precisionBiasedLogit_eq_poweredMass
      (base left) root (precision left) (hprecision left),
    exp_precisionBiasedLogit_eq_poweredMass
      (base right) root (precision right) (hprecision right)]

/-- Holding the comparison slot fixed, increasing one nonnegative precision
coordinate strictly increases its read odds whenever the squared bias root is
nonzero. -/
theorem precisionBiasedReadOdds_strictMono_leftPrecision
    [Fintype Slot] [Nonempty Slot]
    (base firstPrecision secondPrecision : Slot → ℝ)
    (root : ℝ) (left right : Slot)
    (hroot : root ≠ 0)
    (hleftNonnegative : 0 ≤ firstPrecision left)
    (hleft : firstPrecision left < secondPrecision left)
    (hright : firstPrecision right = secondPrecision right) :
    precisionBiasedReadWeight base firstPrecision root left /
        precisionBiasedReadWeight base firstPrecision root right <
      precisionBiasedReadWeight base secondPrecision root left /
        precisionBiasedReadWeight base secondPrecision root right := by
  rw [precisionBiasedReadWeight_div, precisionBiasedReadWeight_div]
  apply Real.exp_lt_exp.mpr
  calc
    precisionBiasedLogit (base left) root (firstPrecision left) -
          precisionBiasedLogit (base right) root (firstPrecision right) <
        precisionBiasedLogit (base left) root (secondPrecision left) -
          precisionBiasedLogit (base right) root (firstPrecision right) :=
      sub_lt_sub_right
        (precisionBiasedLogit_strictMono_precision
          (base left) root (firstPrecision left) (secondPrecision left)
          hroot hleftNonnegative hleft) _
    _ = precisionBiasedLogit (base left) root (secondPrecision left) -
          precisionBiasedLogit (base right) root (secondPrecision right) := by
      rw [hright]

/-- Zero bias root recovers the ordinary workspace softmax weight. -/
@[simp]
theorem precisionBiasedReadWeight_zeroRoot
    [Fintype Slot]
    (base precision : Slot → ℝ) (slot : Slot) :
    precisionBiasedReadWeight base precision 0 slot =
      categoricalSoftmaxProbability base slot := by
  simp [precisionBiasedReadWeight]

/-- A spatially uniform precision adds one common logit offset and therefore
cannot change the normalized read, even when the bias root is nonzero. -/
theorem constantPrecision_preserves_readWeight
    [Fintype Slot] [Nonempty Slot]
    (base : Slot → ℝ) (precision root : ℝ) (slot : Slot) :
    precisionBiasedReadWeight base (fun _ ↦ precision) root slot =
      categoricalSoftmaxProbability base slot := by
  change attentionWeight
      (fun item ↦ base item +
        readBeta root * Real.log (1 + precision)) slot =
    attentionWeight base slot
  exact attentionWeight_add_const base
    (readBeta root * Real.log (1 + precision)) slot

def binaryBaseLogit : Bool → ℝ := fun _ ↦ 0

def binaryOneSidedPrecision : Bool → ℝ :=
  fun slot ↦ if slot then 1 else 0

/-- With unit bias, equal base logits, and precisions one versus zero, the
precision-biased read odds are exactly two to one. -/
theorem binaryOneSidedPrecision_readOdds :
    precisionBiasedReadWeight binaryBaseLogit binaryOneSidedPrecision 1 true /
        precisionBiasedReadWeight binaryBaseLogit binaryOneSidedPrecision 1 false =
      2 := by
  rw [precisionBiasedReadWeight_odds_eq_poweredMassRatio]
  · norm_num [binaryBaseLogit, binaryOneSidedPrecision, readBeta]
  · intro slot
    cases slot <;> simp [binaryOneSidedPrecision]

#print axioms exp_precisionBiasedLogit_eq_poweredMass
#print axioms precisionBiasedReadWeight_eq_poweredMass_div_sum
#print axioms precisionBiasedReadWeight_odds_eq_poweredMassRatio
#print axioms precisionBiasedReadOdds_strictMono_leftPrecision
#print axioms precisionBiasedReadWeight_zeroRoot
#print axioms constantPrecision_preserves_readWeight
#print axioms binaryOneSidedPrecision_readOdds

end

end Mettapedia.MachineLearning.NeuralNetworks.UnifiedCarrier
