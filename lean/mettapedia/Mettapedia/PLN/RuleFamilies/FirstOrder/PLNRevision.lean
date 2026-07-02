import Mettapedia.PLN.Evidence.EvidenceQuantale

/-!
# PLN Revision Rule

This file formalizes the PLN **Revision Rule** which combines evidence from
independent sources.

## Key Insight

The Revision Rule is the PLN mechanism for combining two estimates of the
same relationship. It is mathematically equivalent to the `hplus` operation
on BinaryEvidence:

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

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceQuantale
open BinaryEvidence

/-! ## Revision as hplus -/

/-- The PLN Revision Rule: combine independent evidence sources.
    This is an alias for `hplus` (parallel aggregation). -/
noncomputable abbrev revision (e₁ e₂ : BinaryEvidence) : BinaryEvidence := e₁ + e₂

/-! ## Basic Properties (inherited from hplus) -/

/-- Revision is commutative -/
theorem revision_comm (e₁ e₂ : BinaryEvidence) : revision e₁ e₂ = revision e₂ e₁ :=
  hplus_comm e₁ e₂

/-- Revision is associative -/
theorem revision_assoc (e₁ e₂ e₃ : BinaryEvidence) :
    revision (revision e₁ e₂) e₃ = revision e₁ (revision e₂ e₃) :=
  hplus_assoc e₁ e₂ e₃

/-- Revision with zero evidence -/
theorem revision_zero (e : BinaryEvidence) : revision e 0 = e := hplus_zero e

/-- Zero evidence revised with e -/
theorem zero_revision (e : BinaryEvidence) : revision 0 e = e := zero_hplus e

/-! ## Finite Multi-Source Revision -/

/-- Finite-source PLN Revision: revise a finite list of independent evidence
packets by summing their underlying binary evidence counts. -/
noncomputable def revisionMany (xs : List BinaryEvidence) : BinaryEvidence :=
  xs.sum

@[simp] theorem revisionMany_nil :
    revisionMany [] = (0 : BinaryEvidence) := rfl

@[simp] theorem revisionMany_cons (x : BinaryEvidence) (xs : List BinaryEvidence) :
    revisionMany (x :: xs) = revision x (revisionMany xs) := rfl

theorem revisionMany_eq_sum (xs : List BinaryEvidence) :
    revisionMany xs = xs.sum := rfl

/-- Revising two packets through the finite-source interface is the binary
Revision rule. -/
@[simp] theorem revisionMany_pair (e₁ e₂ : BinaryEvidence) :
    revisionMany [e₁, e₂] = revision e₁ e₂ := by
  simp [revisionMany, revision, hplus_def]

/-- Appending independent batches corresponds to binary Revision of their
already-aggregated evidence. -/
theorem revisionMany_append (xs ys : List BinaryEvidence) :
    revisionMany (xs ++ ys) = revision (revisionMany xs) (revisionMany ys) := by
  simp [revisionMany, revision, List.sum_append]

/-- Finite-source Revision is insensitive to source order.  The only finite
structure retained by the raw rule is the summed positive/negative evidence
count, so any provenance-sensitive duplicate suppression must happen before
calling `revisionMany`. -/
theorem revisionMany_perm {xs ys : List BinaryEvidence} (h : xs.Perm ys) :
    revisionMany xs = revisionMany ys := by
  simpa [revisionMany] using h.sum_eq

@[simp] theorem revisionMany_pos (xs : List BinaryEvidence) :
    (revisionMany xs).pos = (xs.map (fun e => e.pos)).sum := by
  induction xs with
  | nil => simp [revisionMany]
  | cons x xs ih => simp [revisionMany_cons, revision, hplus_def, ih]

@[simp] theorem revisionMany_neg (xs : List BinaryEvidence) :
    (revisionMany xs).neg = (xs.map (fun e => e.neg)).sum := by
  induction xs with
  | nil => simp [revisionMany]
  | cons x xs ih => simp [revisionMany_cons, revision, hplus_def, ih]

/-- Finite-source Revision adds total evidence counts. -/
@[simp] theorem revisionMany_total (xs : List BinaryEvidence) :
    (revisionMany xs).total = (xs.map (fun e => e.total)).sum := by
  induction xs with
  | nil => simp [revisionMany]
  | cons x xs _ih =>
      simp [revisionMany_cons, revision, hplus_def, total, revisionMany_pos,
        revisionMany_neg, add_assoc, add_left_comm]

/-! ### Concrete finite-source canaries -/

/-- One unit of positive evidence and no negative evidence. -/
def positiveUnitEvidence : BinaryEvidence where
  pos := 1
  neg := 0

@[simp] theorem positiveUnitEvidence_pos : positiveUnitEvidence.pos = 1 := rfl

@[simp] theorem positiveUnitEvidence_neg : positiveUnitEvidence.neg = 0 := rfl

/-- Negative canary: unguarded finite-source Revision double-counts duplicate
evidence packets.  Provenance-aware callers must guard duplicates before using
the additive rule. -/
theorem revisionMany_duplicate_positiveUnitEvidence_ne_singleton :
    revisionMany [positiveUnitEvidence, positiveUnitEvidence] ≠
      positiveUnitEvidence := by
  intro h
  have hp := congrArg BinaryEvidence.pos h
  norm_num [revisionMany, revision, hplus_def, positiveUnitEvidence] at hp

/-! ## Strength as Weighted Average

The key property: when combining two evidence sources, the resulting strength
is a weighted average of the input strengths.
-/

/-- Revision strength is weighted average of input strengths.
    This is exactly PLN's revision formula from Section 5.10 of the book.

    s_combined = (n₁ * s₁ + n₂ * s₂) / (n₁ + n₂)

    where n₁ = total₁, n₂ = total₂, s₁ = strength₁, s₂ = strength₂
-/
theorem revision_strength_weighted_avg (e₁ e₂ : BinaryEvidence)
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
theorem revision_total (e₁ e₂ : BinaryEvidence) :
    (revision e₁ e₂).total = e₁.total + e₂.total := by
  simp only [revision, hplus_def, total]
  ring

/-! ## Revision preserves BinaryEvidence structure -/

/-- Revision of finite evidence is finite -/
theorem revision_total_ne_top (e₁ e₂ : BinaryEvidence)
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
theorem tensor_distrib_revision (e₁ e₂ e₃ : BinaryEvidence) :
    (revision e₁ e₂) * e₃ = revision (e₁ * e₃) (e₂ * e₃) := by
  simp only [revision, hplus_def, tensor_def]
  ext
  · simp only [add_mul]
  · simp only [add_mul]

/-- Right distribution -/
theorem tensor_distrib_revision_right (e₁ e₂ e₃ : BinaryEvidence) :
    e₁ * (revision e₂ e₃) = revision (e₁ * e₂) (e₁ * e₃) := by
  rw [tensor_comm, tensor_distrib_revision, tensor_comm e₂, tensor_comm e₃]

end Mettapedia.PLN.RuleFamilies.FirstOrder.PLNRevision
