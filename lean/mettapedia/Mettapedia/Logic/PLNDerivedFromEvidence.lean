import Mettapedia.Logic.EvidenceQuantale

namespace Mettapedia.Logic.EvidenceQuantale

open Classical

/-!
# Derived PLN Rules from Evidence

This file collects small, semantics-first facts:
- which PLN/NARS truth rules correspond directly to operations on the Evidence carrier, and
- the exact algebraic statements we have proven in Lean.

It is intentionally lightweight and does not depend on the probability-derivation files.
-/

namespace Evidence

/-! ## Negation-as-polarity-swap

PLN/NARS "negation" at the STV level typically maps `(s,c)` to `(1-s,c)`.
On Evidence counts `(n⁺, n⁻)`, the corresponding operation is swapping the components.

This is *not* Heyting negation `compl`; it is a polarity swap preserving total evidence.
-/

/-- Swap positive and negative evidence. -/
def flip (e : Evidence) : Evidence :=
  ⟨e.neg, e.pos⟩

theorem flip_total (e : Evidence) : (flip e).total = e.total := by
  -- total is `pos + neg`, and addition is commutative.
  simp [flip, Evidence.total, add_comm]

theorem toStrength_flip (e : Evidence) (ht0 : e.total ≠ 0) (htT : e.total ≠ ⊤) :
    toStrength (flip e) = 1 - toStrength e := by
  -- Unfold `toStrength` and compute in `ℝ≥0∞`.
  unfold toStrength
  have hflip0 : (flip e).total ≠ 0 := by simpa [flip_total] using ht0
  -- Remove the `if` branches.
  simp only [ht0, hflip0, ↓reduceIte]
  -- Rewrite the flipped strength denominator to `e.total` and unfold the numerator.
  rw [flip_total]
  simp [flip]
  have hposT : e.pos ≠ (⊤ : ENNReal) := by
    intro h
    apply htT
    simp [Evidence.total, h]
  have h_total_sub : e.total - e.pos = e.neg := by
    -- `total = pos + neg`, and `pos` is finite, so we can cancel it.
    -- This is the `ENNReal`-specialized cancellation lemma.
    exact ENNReal.sub_eq_of_eq_add_rev hposT (by rfl)
  -- Push subtraction through division: (a - b)/c = a/c - b/c.
  have hsub : (e.total - e.pos) / e.total = e.total / e.total - e.pos / e.total := by
    simpa using (ENNReal.sub_div (a := e.total) (b := e.pos) (c := e.total) (h := fun _ _ => ht0))
  -- `neg/total = (total - pos)/total = 1 - pos/total`.
  rw [← h_total_sub, hsub, ENNReal.div_self ht0 htT]

end Evidence

end Mettapedia.Logic.EvidenceQuantale
