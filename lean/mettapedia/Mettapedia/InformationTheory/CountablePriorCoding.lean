import Mettapedia.InformationTheory.CodebookRelativity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# An exact countably infinite prefix-code prior

Finite factor-two approximation does not exhaust the relation between priors
and prefix codes.  This module first isolates the general object: a strictly
positive probability mass is a family with total mass one, and a prefix
codebook is dyadically complete when its code weights themselves have total
mass one.  Every complete codebook therefore induces a positive probability
mass without further normalization.

The concrete unary codebook on `Nat` then gives an actually infinite positive
prior exactly, not as a finite truncation:

`mass n = 2⁻⁽ⁿ⁺¹⁾`.

Every natural-number hypothesis has positive mass and the complete infinite
sum is one.  A negative control proves that no strictly positive uniform real
mass can be summable on `Nat`.  Together with the uncountable codebook
obstruction in `CodebookRelativity`, this identifies the genuine boundary:
finite binary descriptions support at most countably many individually
positive hypotheses, and the infinite mass must decay.

The geometric construction is standard.  Its use here is an infinite-primary
extension of the finite recoding analysis in M. T. Bennett, *The Wrong Razor*
(2026); it is not attributed to Bennett's finite Proposition A.5.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.CountablePriorCoding

open Mettapedia.InformationTheory.CodebookRelativity

universe uHypothesis

/-! ## General positive masses and complete codebooks -/

/-- A strictly positive probability mass, with no finiteness assumption on
the hypothesis type. -/
structure PositiveProbabilityMass (Hypothesis : Type uHypothesis) where
  mass : Hypothesis → ℝ
  positive : ∀ hypothesis, 0 < mass hypothesis
  hasSum_one : HasSum mass 1

variable {Hypothesis : Type uHypothesis}

/-- Unnormalized dyadic mass assigned by a binary codebook. -/
noncomputable def dyadicMass (codebook : PrefixCodebook Hypothesis)
    (hypothesis : Hypothesis) : ℝ :=
  (1 / 2 : ℝ) ^ codebook.length hypothesis

theorem dyadicMass_pos (codebook : PrefixCodebook Hypothesis)
    (hypothesis : Hypothesis) :
    0 < dyadicMass codebook hypothesis := by
  exact pow_pos (by norm_num) _

/-- Completeness means that the codewords exhaust dyadic mass one.  Ordinary
prefix-freeness alone only supplies a subprobability mass. -/
def IsDyadicallyComplete (codebook : PrefixCodebook Hypothesis) : Prop :=
  HasSum (dyadicMass codebook) 1

/-- A complete prefix codebook induces a positive probability mass directly,
without a finite normalizer. -/
noncomputable def toPositiveProbabilityMass
    (codebook : PrefixCodebook Hypothesis)
    (complete : IsDyadicallyComplete codebook) :
    PositiveProbabilityMass Hypothesis where
  mass := dyadicMass codebook
  positive := dyadicMass_pos codebook
  hasSum_one := complete

/-! ## Exact unary/geometric instance -/

/-- The full-support geometric mass on natural-number hypotheses. -/
noncomputable def geometricMass (index : Nat) : ℝ :=
  (1 : ℝ) / 2 / 2 ^ index

theorem geometricMass_pos (index : Nat) : 0 < geometricMass index := by
  exact div_pos (by norm_num) (pow_pos (by norm_num) _)

theorem hasSum_geometricMass : HasSum geometricMass 1 := by
  exact hasSum_geometric_two' (a := (1 : ℝ))

theorem tsum_geometricMass : (∑' index : Nat, geometricMass index) = 1 :=
  hasSum_geometricMass.tsum_eq

/-- The unary code length `n+1` induces exactly the geometric mass, pointwise. -/
theorem natCodebook_dyadicMass_eq (index : Nat) :
    dyadicMass natCodebook index = geometricMass index := by
  simp [dyadicMass, natCodebook_length, geometricMass, pow_succ,
    div_eq_mul_inv, mul_comm]

/-- The countably infinite unary prefix code is dyadically complete. -/
theorem natCodebook_isDyadicallyComplete :
    IsDyadicallyComplete natCodebook := by
  refine hasSum_geometricMass.congr_fun (fun index ↦ ?_)
  exact natCodebook_dyadicMass_eq index

/-- An exact, full-support, countably infinite code-induced prior. -/
noncomputable def geometricPrior : PositiveProbabilityMass Nat :=
  toPositiveProbabilityMass natCodebook natCodebook_isDyadicallyComplete

@[simp]
theorem geometricPrior_mass (index : Nat) :
    geometricPrior.mass index = geometricMass index :=
  natCodebook_dyadicMass_eq index

theorem geometricPrior_hasSum_one : HasSum geometricPrior.mass 1 :=
  geometricPrior.hasSum_one

/-- Positive uniform weights cannot form a probability mass on a countably
infinite class.  Infinite-primary priors must allocate diminishing mass rather
than silently reuse a finite uniform premise. -/
theorem no_strictlyPositive_uniform_summable_mass :
    ¬ ∃ constant : ℝ, 0 < constant ∧
      Summable (fun _ : Nat ↦ constant) := by
  rintro ⟨constant, positive, summable⟩
  have zero : constant = 0 := (summable_const_iff constant).mp summable
  linarith

end Mettapedia.InformationTheory.CountablePriorCoding

#print axioms Mettapedia.InformationTheory.CountablePriorCoding.natCodebook_isDyadicallyComplete
#print axioms Mettapedia.InformationTheory.CountablePriorCoding.geometricPrior_hasSum_one
#print axioms Mettapedia.InformationTheory.CountablePriorCoding.no_strictlyPositive_uniform_summable_mass
