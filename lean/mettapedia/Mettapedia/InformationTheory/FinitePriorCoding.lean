import Mettapedia.InformationTheory.CodebookRelativity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Finite positive priors as prefix-code priors within a factor of two

This module formalizes Proposition A.5 of Michael Timothy Bennett's *The Wrong
Razor* complete-proofs appendix.  Every strictly positive probability mass on a
nonempty finite hypothesis type induces an explicit binary prefix codebook
whose normalized dyadic code prior lies between one half and twice the original
mass, pointwise.

The proof is constructive at the level needed by the theorem and avoids
assuming a Kraft-converse axiom.  Each hypothesis receives:

1. an injective one-hot tag of common length `Fintype.card Hypothesis`;
2. a dyadic depth chosen minimally so that `2⁻ⁿ ≤ Q(h)`.

The common tag makes the resulting words prefix-free.  Its weight is the same
for every hypothesis and therefore cancels from the normalized prior.  Minimal
dyadic rounding gives

`Q(h) / 2 < 2⁻ˡ⁽ʰ⁾ ≤ Q(h)`,

which yields Bennett's factor-two bounds after normalization.

The construction is deliberately finite.  Codebook ranking reversal on a
countably infinite class and the impossibility of finite-string codebooks for
uncountable classes are proved separately in `CodebookRelativity`.

Reference: M. T. Bennett, *The Wrong Razor*, Proposition A.5 in the
complete-proofs appendix (2026).  Bennett invokes Kraft–McMillan after rounding;
the equal-tag construction here proves the same stated conclusion directly.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.FinitePriorCoding

open scoped BigOperators
open Mettapedia.InformationTheory.CodebookRelativity

universe uHypothesis

/-! ## Minimal dyadic rounding -/

/-- Some dyadic power is at most every positive real number. -/
theorem exists_dyadic_le {q : ℝ} (positive : 0 < q) :
    ∃ depth : Nat, (1 / 2 : ℝ) ^ depth ≤ q := by
  obtain ⟨depth, less⟩ :=
    exists_pow_lt_of_lt_one positive (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨depth, less.le⟩

/-- Least depth whose dyadic weight lies below `q`. -/
noncomputable def dyadicDepth (q : ℝ) (positive : 0 < q) : Nat :=
  Nat.find (exists_dyadic_le positive)

/-- Rounded dyadic weight at the least admissible depth. -/
noncomputable def dyadicWeight (q : ℝ) (positive : 0 < q) : ℝ :=
  (1 / 2 : ℝ) ^ dyadicDepth q positive

theorem dyadicWeight_le (q : ℝ) (positive : 0 < q) :
    dyadicWeight q positive ≤ q :=
  Nat.find_spec (exists_dyadic_le positive)

theorem dyadicWeight_pos (q : ℝ) (positive : 0 < q) :
    0 < dyadicWeight q positive := by
  exact pow_pos (by norm_num) _

/-- Minimality supplies the strict lower half-bound used in Bennett A.5 for a
mass bounded by one. -/
theorem half_lt_dyadicWeight (q : ℝ) (positive : 0 < q) (upper : q ≤ 1) :
    q / 2 < dyadicWeight q positive := by
  rw [dyadicWeight]
  generalize depthEq : dyadicDepth q positive = depth
  cases depth with
  | zero =>
      simp
      linarith
  | succ depth =>
      have previousNot : ¬ (1 / 2 : ℝ) ^ depth ≤ q := by
        have depth_lt : depth < dyadicDepth q positive := by omega
        exact Nat.find_min (exists_dyadic_le positive) depth_lt
      have q_lt_previous : q < (1 / 2 : ℝ) ^ depth :=
        lt_of_not_ge previousNot
      rw [pow_succ]
      norm_num
      linarith

/-! ## Positive finite priors -/

/-- A strictly positive probability mass on a finite hypothesis type. -/
structure PositivePrior (Hypothesis : Type uHypothesis)
    [Fintype Hypothesis] where
  mass : Hypothesis → ℝ
  positive : ∀ hypothesis, 0 < mass hypothesis
  sum_one : ∑ hypothesis, mass hypothesis = 1

namespace PositivePrior

variable {Hypothesis : Type uHypothesis}
variable [Fintype Hypothesis]

theorem mass_le_one (prior : PositivePrior Hypothesis)
    (hypothesis : Hypothesis) : prior.mass hypothesis ≤ 1 := by
  calc
    prior.mass hypothesis ≤ ∑ other, prior.mass other := by
      exact Finset.single_le_sum
        (fun other _ ↦ (prior.positive other).le)
        (Finset.mem_univ hypothesis)
    _ = 1 := prior.sum_one

/-- Rounded raw weight before normalization. -/
noncomputable def rawWeight (prior : PositivePrior Hypothesis)
    (hypothesis : Hypothesis) : ℝ :=
  dyadicWeight (prior.mass hypothesis) (prior.positive hypothesis)

/-- Sum of rounded raw weights. -/
noncomputable def rawNormalizer (prior : PositivePrior Hypothesis) : ℝ :=
  ∑ hypothesis, prior.rawWeight hypothesis

theorem rawWeight_le_mass (prior : PositivePrior Hypothesis)
    (hypothesis : Hypothesis) :
    prior.rawWeight hypothesis ≤ prior.mass hypothesis :=
  dyadicWeight_le _ _

theorem half_mass_lt_rawWeight (prior : PositivePrior Hypothesis)
    (hypothesis : Hypothesis) :
    prior.mass hypothesis / 2 < prior.rawWeight hypothesis :=
  half_lt_dyadicWeight _ _ (prior.mass_le_one hypothesis)

theorem rawNormalizer_le_one (prior : PositivePrior Hypothesis) :
    prior.rawNormalizer ≤ 1 := by
  calc
    prior.rawNormalizer ≤ ∑ hypothesis, prior.mass hypothesis := by
      exact Finset.sum_le_sum fun hypothesis _ ↦
        prior.rawWeight_le_mass hypothesis
    _ = 1 := prior.sum_one

theorem half_lt_rawNormalizer [Nonempty Hypothesis]
    (prior : PositivePrior Hypothesis) :
    (1 : ℝ) / 2 < prior.rawNormalizer := by
  calc
    (1 : ℝ) / 2 = ∑ hypothesis, prior.mass hypothesis / 2 := by
      rw [← Finset.sum_div, prior.sum_one]
    _ < ∑ hypothesis, prior.rawWeight hypothesis := by
      exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        fun hypothesis _ ↦ prior.half_mass_lt_rawWeight hypothesis
    _ = prior.rawNormalizer := rfl

theorem rawNormalizer_pos [Nonempty Hypothesis]
    (prior : PositivePrior Hypothesis) :
    0 < prior.rawNormalizer :=
  (by norm_num : (0 : ℝ) < 1 / 2).trans prior.half_lt_rawNormalizer

/-! ## An explicit equal-tag prefix code -/

/-- A one-hot code of common length `Fintype.card Hypothesis`. -/
noncomputable def fixedTag (hypothesis : Hypothesis) : List Bool :=
  List.ofFn fun index : Fin (Fintype.card Hypothesis) ↦
    decide (index = Fintype.equivFin Hypothesis hypothesis)

@[simp]
theorem fixedTag_length (hypothesis : Hypothesis) :
    (fixedTag hypothesis).length = Fintype.card Hypothesis := by
  simp [fixedTag]

theorem fixedTag_injective :
    Function.Injective (fixedTag : Hypothesis → List Bool) := by
  classical
  intro left right equalTags
  have equalFunctions :
      (fun index : Fin (Fintype.card Hypothesis) ↦
          decide (index = Fintype.equivFin Hypothesis left)) =
        (fun index : Fin (Fintype.card Hypothesis) ↦
          decide (index = Fintype.equivFin Hypothesis right)) :=
    List.ofFn_injective equalTags
  have atLeft := congrFun equalFunctions (Fintype.equivFin Hypothesis left)
  have encodedEqual :
      Fintype.equivFin Hypothesis left =
        Fintype.equivFin Hypothesis right := by
    simpa using atLeft
  exact (Fintype.equivFin Hypothesis).injective encodedEqual

/-- One-hot tag followed by the probability-adaptive dyadic depth. -/
noncomputable def roundedCode (prior : PositivePrior Hypothesis)
    (hypothesis : Hypothesis) : List Bool :=
  fixedTag hypothesis ++
    List.replicate
      (dyadicDepth (prior.mass hypothesis) (prior.positive hypothesis)) false

@[simp]
theorem roundedCode_length (prior : PositivePrior Hypothesis)
    (hypothesis : Hypothesis) :
    (prior.roundedCode hypothesis).length =
      Fintype.card Hypothesis +
        dyadicDepth (prior.mass hypothesis) (prior.positive hypothesis) := by
  simp [roundedCode]

/-- The equal-length injective tags make the complete variable-depth code
prefix-free. -/
noncomputable def prefixCodebook
    (prior : PositivePrior Hypothesis) : PrefixCodebook Hypothesis where
  encode := prior.roundedCode
  prefixFree := by
    intro left right different isPrefix
    obtain ⟨suffix, codeEqual⟩ := isPrefix
    have tagEqual := congrArg (List.take (Fintype.card Hypothesis)) codeEqual
    have : fixedTag left = fixedTag right := by
      simpa [roundedCode, List.take_append_of_le_length] using tagEqual
    exact different (fixedTag_injective this)

/-! ## The induced normalized Occam prior -/

/-- Dyadic weight of the explicit prefix codeword. -/
noncomputable def codeWeight (prior : PositivePrior Hypothesis)
    (hypothesis : Hypothesis) : ℝ :=
  (1 / 2 : ℝ) ^ (prior.prefixCodebook.length hypothesis)

/-- Normalization constant of the explicit codebook. -/
noncomputable def codeNormalizer (prior : PositivePrior Hypothesis) : ℝ :=
  ∑ hypothesis, prior.codeWeight hypothesis

/-- The normalized Occam prior induced by the explicit prefix code. -/
noncomputable def inducedOccamPrior (prior : PositivePrior Hypothesis)
    (hypothesis : Hypothesis) : ℝ :=
  prior.codeWeight hypothesis / prior.codeNormalizer

theorem codeWeight_eq_common_mul_rawWeight
    (prior : PositivePrior Hypothesis) (hypothesis : Hypothesis) :
    prior.codeWeight hypothesis =
      (1 / 2 : ℝ) ^ Fintype.card Hypothesis * prior.rawWeight hypothesis := by
  rw [codeWeight, PrefixCodebook.length, prefixCodebook,
    roundedCode_length, pow_add]
  rfl

theorem codeNormalizer_eq_common_mul_rawNormalizer
    (prior : PositivePrior Hypothesis) :
    prior.codeNormalizer =
      (1 / 2 : ℝ) ^ Fintype.card Hypothesis * prior.rawNormalizer := by
  simp_rw [codeNormalizer, codeWeight_eq_common_mul_rawWeight,
    rawNormalizer, Finset.mul_sum]

theorem codeNormalizer_pos [Nonempty Hypothesis]
    (prior : PositivePrior Hypothesis) :
    0 < prior.codeNormalizer := by
  rw [codeNormalizer_eq_common_mul_rawNormalizer]
  exact mul_pos (pow_pos (by norm_num) _) prior.rawNormalizer_pos

/-- The normalized code weights really form a probability mass. -/
theorem sum_inducedOccamPrior [Nonempty Hypothesis]
    (prior : PositivePrior Hypothesis) :
    ∑ hypothesis, prior.inducedOccamPrior hypothesis = 1 := by
  simp_rw [inducedOccamPrior]
  rw [← Finset.sum_div, show (∑ hypothesis, prior.codeWeight hypothesis) =
    prior.codeNormalizer from rfl]
  exact div_self (ne_of_gt prior.codeNormalizer_pos)

theorem inducedOccamPrior_eq_raw
    (prior : PositivePrior Hypothesis) (hypothesis : Hypothesis) :
    prior.inducedOccamPrior hypothesis =
      prior.rawWeight hypothesis / prior.rawNormalizer := by
  rw [inducedOccamPrior, codeWeight_eq_common_mul_rawWeight,
    codeNormalizer_eq_common_mul_rawNormalizer]
  exact mul_div_mul_left _ _ (ne_of_gt (pow_pos (by norm_num) _))

/-- Bennett A.5, lower factor-two bound. -/
theorem half_mass_le_inducedOccamPrior
    [Nonempty Hypothesis]
    (prior : PositivePrior Hypothesis) (hypothesis : Hypothesis) :
    prior.mass hypothesis / 2 ≤ prior.inducedOccamPrior hypothesis := by
  rw [inducedOccamPrior_eq_raw, le_div_iff₀ prior.rawNormalizer_pos]
  have normalizerLe := prior.rawNormalizer_le_one
  have roundedGt := prior.half_mass_lt_rawWeight hypothesis
  have massPos := prior.positive hypothesis
  nlinarith

/-- Bennett A.5, upper factor-two bound. -/
theorem inducedOccamPrior_le_twice_mass
    [Nonempty Hypothesis]
    (prior : PositivePrior Hypothesis) (hypothesis : Hypothesis) :
    prior.inducedOccamPrior hypothesis ≤ 2 * prior.mass hypothesis := by
  rw [inducedOccamPrior_eq_raw, div_le_iff₀ prior.rawNormalizer_pos]
  have roundedLe := prior.rawWeight_le_mass hypothesis
  have normalizerGt := prior.half_lt_rawNormalizer
  have massPos := prior.positive hypothesis
  nlinarith

/-- Complete formal statement of Bennett A.5 for a nonempty finite hypothesis
type. -/
theorem exists_prefixCodebook_factor_two
    [Nonempty Hypothesis]
    (prior : PositivePrior Hypothesis) :
    ∃ codebook : PrefixCodebook Hypothesis,
      ∀ hypothesis,
        prior.mass hypothesis / 2 ≤
            ((1 / 2 : ℝ) ^ codebook.length hypothesis) /
              (∑ other, (1 / 2 : ℝ) ^ codebook.length other) ∧
          ((1 / 2 : ℝ) ^ codebook.length hypothesis) /
              (∑ other, (1 / 2 : ℝ) ^ codebook.length other) ≤
            2 * prior.mass hypothesis := by
  refine ⟨prior.prefixCodebook, fun hypothesis ↦ ?_⟩
  change prior.mass hypothesis / 2 ≤ prior.inducedOccamPrior hypothesis ∧
    prior.inducedOccamPrior hypothesis ≤ 2 * prior.mass hypothesis
  exact ⟨prior.half_mass_le_inducedOccamPrior hypothesis,
    prior.inducedOccamPrior_le_twice_mass hypothesis⟩

end PositivePrior

end Mettapedia.InformationTheory.FinitePriorCoding

#print axioms Mettapedia.InformationTheory.FinitePriorCoding.PositivePrior.prefixCodebook
#print axioms Mettapedia.InformationTheory.FinitePriorCoding.PositivePrior.sum_inducedOccamPrior
#print axioms Mettapedia.InformationTheory.FinitePriorCoding.PositivePrior.inducedOccamPrior_eq_raw
#print axioms Mettapedia.InformationTheory.FinitePriorCoding.PositivePrior.exists_prefixCodebook_factor_two
