import Mettapedia.Logic.PLNEvidence

/-!
# PLN Revision Rule

This file formalizes the PLN **Revision Rule** which combines evidence from
independent sources.

## Key Insight

The Revision Rule is the PLN mechanism for combining two estimates of the
same relationship. It is mathematically equivalent to the `hplus` operation
on Evidence:

    D₁ ⊕ D₂ = (n⁺₁ + n⁺₂, n⁻₁ + n⁻₂)

## Properties

- **Commutative**: D₁ ⊕ D₂ = D₂ ⊕ D₁
- **Associative**: (D₁ ⊕ D₂) ⊕ D₃ = D₁ ⊕ (D₂ ⊕ D₃)
- **Weighted Averaging**: The strength of the combined evidence is a weighted
  average of the input strengths, weighted by total evidence counts.

## Connection to Bayesian Updating

The Revision Rule corresponds to Beta conjugate updating:
- Prior: Beta(α₀, β₀)
- Observation 1: n⁺₁ successes, n⁻₁ failures → Posterior: Beta(α₀+n⁺₁, β₀+n⁻₁)
- Observation 2: n⁺₂ successes, n⁻₂ failures → Final: Beta(α₀+n⁺₁+n⁺₂, β₀+n⁻₁+n⁻₂)

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Section 5.10
-/

namespace Mettapedia.Logic.PLNRevision

open scoped ENNReal
open Mettapedia.Logic.PLNEvidence
open Evidence

/-! ## Revision as hplus -/

/-- The PLN Revision Rule: combine independent evidence sources.
    This is an alias for `hplus` (parallel aggregation). -/
noncomputable abbrev revision (e₁ e₂ : Evidence) : Evidence := e₁ + e₂

/-! ## Basic Properties (inherited from hplus) -/

/-- Revision is commutative -/
theorem revision_comm (e₁ e₂ : Evidence) : revision e₁ e₂ = revision e₂ e₁ :=
  hplus_comm e₁ e₂

/-- Revision is associative -/
theorem revision_assoc (e₁ e₂ e₃ : Evidence) :
    revision (revision e₁ e₂) e₃ = revision e₁ (revision e₂ e₃) :=
  hplus_assoc e₁ e₂ e₃

/-- Revision with zero evidence -/
theorem revision_zero (e : Evidence) : revision e 0 = e := hplus_zero e

/-- Zero evidence revised with e -/
theorem zero_revision (e : Evidence) : revision 0 e = e := zero_hplus e

/-! ## Strength as Weighted Average

The key property: when combining two evidence sources, the resulting strength
is a weighted average of the input strengths.
-/

/-- Revision strength is weighted average of input strengths.
    This is exactly PLN's revision formula from Section 5.10 of the book.

    s_combined = (n₁ * s₁ + n₂ * s₂) / (n₁ + n₂)

    where n₁ = total₁, n₂ = total₂, s₁ = strength₁, s₂ = strength₂
-/
theorem revision_strength_weighted_avg (e₁ e₂ : Evidence)
    (h₁ : e₁.total ≠ 0) (h₂ : e₂.total ≠ 0) (h₁₂ : (e₁ + e₂).total ≠ 0)
    (h₁_top : e₁.total ≠ ⊤) (h₂_top : e₂.total ≠ ⊤) :
    toStrength (revision e₁ e₂) =
      (e₁.total / (e₁ + e₂).total) * toStrength e₁ +
      (e₂.total / (e₁ + e₂).total) * toStrength e₂ :=
  toStrength_hplus e₁ e₂ h₁ h₂ h₁₂ h₁_top h₂_top

/-! ## Confidence Increase

More evidence leads to higher confidence.
-/

/-- Revision increases total evidence -/
theorem revision_total (e₁ e₂ : Evidence) :
    (revision e₁ e₂).total = e₁.total + e₂.total := by
  simp only [revision, hplus_def, total]
  ring

/-! ## Revision preserves Evidence structure -/

/-- Revision of finite evidence is finite -/
theorem revision_total_ne_top (e₁ e₂ : Evidence)
    (h₁ : e₁.total ≠ ⊤) (h₂ : e₂.total ≠ ⊤) :
    (revision e₁ e₂).total ≠ ⊤ := by
  rw [revision_total]
  simp only [total] at h₁ h₂ ⊢
  exact ENNReal.add_ne_top.mpr ⟨h₁, h₂⟩

/-! ## Distribution with tensor -/

/-- Tensor distributes over revision.
    (e₁ + e₂) * e₃ = (e₁ * e₃) + (e₂ * e₃)

    This is because both operations are coordinatewise:
    - revision/hplus: adds coordinates
    - tensor: multiplies coordinates
    So multiplication distributes over addition coordinatewise.
-/
theorem tensor_distrib_revision (e₁ e₂ e₃ : Evidence) :
    (revision e₁ e₂) * e₃ = revision (e₁ * e₃) (e₂ * e₃) := by
  simp only [revision, hplus_def, tensor_def]
  ext
  · simp only [add_mul]
  · simp only [add_mul]

/-- Right distribution -/
theorem tensor_distrib_revision_right (e₁ e₂ e₃ : Evidence) :
    e₁ * (revision e₂ e₃) = revision (e₁ * e₂) (e₁ * e₃) := by
  rw [tensor_comm, tensor_distrib_revision, tensor_comm e₂, tensor_comm e₃]

end Mettapedia.Logic.PLNRevision
