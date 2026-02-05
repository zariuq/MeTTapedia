/-
# Evidence Interval Bounds

This file connects PLN Evidence incomparability to probability interval bounds,
creating a bridge between the Evidence quantale and Heyting K&S interval theory.

## The Key Insight

When two Evidence values are **incomparable** in the partial order (neither ≤ the other),
this represents **epistemic uncertainty**: we don't know the exact state of the world.

This maps to **interval-valued probability**:
- Lower bound: minimum possible strength
- Upper bound: maximum possible strength

## Connection to Heyting K&S

In Heyting algebra-based probability:
- `lowerBound ν a = ν(a)` (direct evidence)
- `upperBound ν a = 1 - ν(¬a)` (absence of counter-evidence)

For Evidence counts, we derive similar bounds from the partial order structure.

## References

- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
- Augustin et al., "Introduction to Imprecise Probabilities" (2014)
- Heyting bounds from HeytingBounds.lean
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.HeytingIntervalRepresentation

namespace Mettapedia.Logic.EvidenceIntervalBounds

open scoped ENNReal
open Mettapedia.Logic.EvidenceQuantale
open Evidence

/-! ## Strength Bounds from Evidence -/

/-- The strength of evidence: s = n⁺ / (n⁺ + n⁻).
    Returns 0 if total evidence is 0 (undefined case handled as zero). -/
noncomputable def strength (e : Evidence) : ℝ≥0∞ :=
  e.pos / (e.pos + e.neg)

/-- Strength is at most 1. -/
theorem strength_le_one (e : Evidence) : strength e ≤ 1 := by
  unfold strength
  by_cases h₀ : e.pos + e.neg = 0
  · -- When sum is 0, both components are 0 (since ℝ≥0∞ is nonneg), so 0/0 = 0 ≤ 1
    have hp : e.pos = 0 := by
      by_contra hp'
      have hpos : 0 < e.pos := pos_iff_ne_zero.mpr hp'
      have : 0 < e.pos + e.neg := add_pos_of_pos_of_nonneg hpos (zero_le _)
      exact (ne_of_gt this) h₀
    simp [hp, ENNReal.zero_div]
  · by_cases h_top : e.pos + e.neg = ⊤
    · -- When sum is ⊤, division by ⊤ gives 0
      simp [h_top, ENNReal.div_top]
    · -- Normal case: 0 < sum < ⊤
      rw [ENNReal.div_le_iff h₀ h_top, one_mul]
      exact le_self_add

/-- Strength is non-negative (trivially true for ℝ≥0∞). -/
theorem strength_nonneg (e : Evidence) : 0 ≤ strength e := zero_le _

/-- Strength of zero evidence is zero. -/
theorem strength_zero : strength ⟨0, 0⟩ = 0 := by simp [strength]

/-- Strength of pure positive evidence is 1. -/
theorem strength_pure_pos (p : ℝ≥0∞) (hp : p ≠ 0) (hpt : p ≠ ⊤) : strength ⟨p, 0⟩ = 1 := by
  simp only [strength, add_zero]
  exact ENNReal.div_self hp hpt

/-- Strength of pure negative evidence is 0. -/
theorem strength_pure_neg (n : ℝ≥0∞) : strength ⟨0, n⟩ = 0 := by
  simp [strength]

/-! ## Evidence Incomparability

Uses the general `Incomparable` definition from `HeytingIntervalRepresentation.lean`
which applies to any Preorder. Evidence inherits this via its PartialOrder instance.
-/

open Mettapedia.ProbabilityTheory.KnuthSkilling.Heyting (Incomparable)

/-- Incomparability is symmetric (specialization to Evidence of the general theorem). -/
theorem incomparable_symm (e₁ e₂ : Evidence) :
    Incomparable e₁ e₂ ↔ Incomparable e₂ e₁ := by
  simp only [Incomparable, and_comm]

/-- Incomparable evidence requires at least one dimension to "cross". -/
theorem incomparable_characterization (e₁ e₂ : Evidence) :
    Incomparable e₁ e₂ ↔
    (e₁.pos < e₂.pos ∧ e₂.neg < e₁.neg) ∨ (e₂.pos < e₁.pos ∧ e₁.neg < e₂.neg) := by
  simp only [Incomparable, le_def, not_and_or, not_le]
  constructor
  · intro ⟨h1, h2⟩
    rcases h1 with h1p | h1n <;> rcases h2 with h2p | h2n
    · exact absurd (lt_trans h1p h2p) (lt_irrefl _)
    · right; exact ⟨h1p, h2n⟩
    · left; exact ⟨h2p, h1n⟩
    · exact absurd (lt_trans h1n h2n) (lt_irrefl _)
  · intro h
    rcases h with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · -- e₁.pos < e₂.pos and e₂.neg < e₁.neg
      -- Need: ¬(e₁ ≤ e₂) and ¬(e₂ ≤ e₁)
      -- e₁ ≤ e₂ means e₁.pos ≤ e₂.pos AND e₁.neg ≤ e₂.neg
      -- ¬(e₁ ≤ e₂) means e₁.pos > e₂.pos OR e₁.neg > e₂.neg
      -- We have e₂.neg < e₁.neg, so e₁.neg > e₂.neg
      -- ¬(e₂ ≤ e₁) means e₂.pos > e₁.pos OR e₂.neg > e₁.neg
      -- We have e₁.pos < e₂.pos, so e₂.pos > e₁.pos
      exact ⟨Or.inr hn, Or.inl hp⟩
    · -- e₂.pos < e₁.pos and e₁.neg < e₂.neg
      exact ⟨Or.inl hp, Or.inr hn⟩

/-! ## Interval Representation -/

/-- The strength interval for evidence e: a single point [s, s].
    For a single evidence value, the interval is trivial. -/
noncomputable def strengthInterval (e : Evidence) : Set ℝ :=
  Set.Icc (strength e).toReal (strength e).toReal

/-- The strength interval is a single point. -/
theorem strengthInterval_singleton (e : Evidence) :
    strengthInterval e = {(strength e).toReal} := by
  simp [strengthInterval, Set.Icc_self]

/-- For uncertain evidence (represented as a set of possibilities),
    the strength interval spans from minimum to maximum strength. -/
noncomputable def strengthIntervalOfSet (S : Set Evidence) : Set ℝ :=
  Set.Icc (⨅ e ∈ S, (strength e).toReal) (⨆ e ∈ S, (strength e).toReal)

/-! ## Fréchet-Style Bounds for Evidence Combination -/

/-- Meet of two evidence values (coordinatewise minimum).
    This is a lower bound in the partial order. -/
def evidenceMeet (e₁ e₂ : Evidence) : Evidence :=
  ⟨min e₁.pos e₂.pos, min e₁.neg e₂.neg⟩

/-- Join of two evidence values (coordinatewise maximum).
    This is an upper bound in the partial order. -/
def evidenceJoin (e₁ e₂ : Evidence) : Evidence :=
  ⟨max e₁.pos e₂.pos, max e₁.neg e₂.neg⟩

/-- Meet is below both inputs. -/
theorem evidenceMeet_le_left (e₁ e₂ : Evidence) : evidenceMeet e₁ e₂ ≤ e₁ := by
  simp only [evidenceMeet, le_def]
  exact ⟨min_le_left _ _, min_le_left _ _⟩

theorem evidenceMeet_le_right (e₁ e₂ : Evidence) : evidenceMeet e₁ e₂ ≤ e₂ := by
  simp only [evidenceMeet, le_def]
  exact ⟨min_le_right _ _, min_le_right _ _⟩

/-- Join is above both inputs. -/
theorem le_evidenceJoin_left (e₁ e₂ : Evidence) : e₁ ≤ evidenceJoin e₁ e₂ := by
  simp only [evidenceJoin, le_def]
  exact ⟨le_max_left _ _, le_max_left _ _⟩

theorem le_evidenceJoin_right (e₁ e₂ : Evidence) : e₂ ≤ evidenceJoin e₁ e₂ := by
  simp only [evidenceJoin, le_def]
  exact ⟨le_max_right _ _, le_max_right _ _⟩

/-- Meet is below Join. -/
theorem evidenceMeet_le_evidenceJoin (e₁ e₂ : Evidence) :
    evidenceMeet e₁ e₂ ≤ evidenceJoin e₁ e₂ := by
  simp only [evidenceMeet, evidenceJoin, le_def]
  exact ⟨min_le_max, min_le_max⟩

/-! ## The "Evidence Gap" -/

/-- The evidence gap measures the uncertainty between a lower and upper bound.
    This is analogous to the Heyting excluded middle gap. -/
noncomputable def evidenceGap (eLower eUpper : Evidence) : ℝ :=
  (strength eUpper).toReal - (strength eLower).toReal

/-- The gap between meet and join measures incomparability. -/
noncomputable def meetJoinGap (e₁ e₂ : Evidence) : ℝ :=
  evidenceGap (evidenceMeet e₁ e₂) (evidenceJoin e₁ e₂)

/-- The meet-join gap is non-negative when join has higher strength than meet. -/
theorem meetJoinGap_nonneg_of_le (e₁ e₂ : Evidence)
    (h : strength (evidenceMeet e₁ e₂) ≤ strength (evidenceJoin e₁ e₂)) :
    0 ≤ meetJoinGap e₁ e₂ := by
  unfold meetJoinGap evidenceGap
  have := ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (strength_le_one _)) h
  linarith

/-! ## Incomparability and Uncertainty -/

/-- When evidence values are incomparable, they represent different possible states. -/
theorem incomparable_implies_ne (e₁ e₂ : Evidence)
    (h : Incomparable e₁ e₂) : e₁ ≠ e₂ := by
  intro heq
  rw [heq] at h
  simp [Incomparable] at h

/-- The set of evidence values comparable to a given evidence. -/
def comparableSet (e : Evidence) : Set Evidence :=
  { e' | e ≤ e' ∨ e' ≤ e }

/-- Any evidence is comparable to itself. -/
theorem self_mem_comparableSet (e : Evidence) : e ∈ comparableSet e := by
  simp [comparableSet]

/-- If e' is above e and e' ≤ e'', then e'' is above e (transitivity). -/
theorem comparableSet_closed_above (e e' e'' : Evidence)
    (h : e ≤ e') (hle : e' ≤ e'') : e ≤ e'' :=
  le_trans h hle

/-! ## Bridge to Heyting K&S -/

/-- When we have uncertainty about which evidence is "true", represented by
    a pair (lower, upper) with a strength ordering, the lower strength lies in the interval.

    NOTE: The hypothesis is `strength eLower ≤ strength eUpper`, NOT `eLower ≤ eUpper`.
    The Evidence partial order does NOT induce a strength ordering:
    increasing both pos and neg can change the ratio either way.

    This is analogous to Heyting bounds where:
    - lower corresponds to ν(a)
    - upper corresponds to 1 - ν(¬a)
-/
theorem strength_in_interval (eLower eUpper : Evidence)
    (h_strength : strength eLower ≤ strength eUpper) :
    (strength eLower).toReal ∈ Set.Icc (strength eLower).toReal (strength eUpper).toReal := by
  constructor
  · exact le_refl _
  · exact ENNReal.toReal_mono (ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      (strength_le_one _)) h_strength

/-! ## Summary

This file establishes:

1. **Strength function**: Maps Evidence to [0,1] via s = n⁺ / (n⁺ + n⁻)

2. **Incomparability**: Two Evidence values may be incomparable in the partial order,
   representing epistemic uncertainty.

3. **Meet and Join**: The meet (coordinatewise min) and join (coordinatewise max)
   provide bounds on uncertain evidence.

4. **Gap measures**: The difference between join and meet strengths quantifies
   uncertainty, analogous to the Heyting excluded middle gap.

5. **Bridge to Heyting K&S**: Evidence incomparability → strength uncertainty →
   interval-valued probability.

## Key Observation

The Evidence partial order does NOT directly induce a strength ordering:
- e₁ ≤ e₂ does NOT imply strength e₁ ≤ strength e₂

This is because strength depends on the RATIO of pos to total, and increasing
both components can change the ratio either way.

The proper connection to Heyting bounds requires a different construction,
working through the complement structure rather than the partial order directly.
-/

end Mettapedia.Logic.EvidenceIntervalBounds
