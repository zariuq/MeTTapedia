import Mettapedia.Computability.PNP.FiniteIIDRecovery
import Mettapedia.Computability.PNP.HypothesisClass

/-!
# P vs NP background theory: the same-route interface

This file packages the exact positive interface that counts as "the same route"
for the current switching/ERM program.

If a proposed rescue still intends to pass through:

* a visible input surface,
* a small encoded family of per-bit predictors, and
* finite-class ERM / deceptive-sample recovery bounds,

then it must instantiate the objects below.  In particular, a bit-budgeted
family over an available input surface automatically inherits the weighted exact
recovery lower bound from `FiniteIIDRecovery.lean`.

So a weakness/GSLT argument that does *not* produce such an encoded family is no
longer a repair of the current route.  It is a different route.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v w

/-- A "same-route" family is a bit-encoded boolean predictor family over one
Hyperseed available input surface. -/
abbrev SameRouteFamily
    {World : Type u} {Signal : Type v} {Cost : Type w} [Preorder Cost]
    (P : Mettapedia.Hyperseed.Perspective World Signal Cost) (B : Cost) (guard : Set World)
    (s : ℕ) :=
  BitEncodedClassifierFamily (AvailableInput P B guard) s

namespace BitEncodedClassifierFamily

section Recovery

variable {Input : Type u} [Fintype Input]
variable {s : ℕ}

/-- Exact recovery mass for a bit-encoded family, with the nonempty-code witness
spelled out directly. -/
noncomputable def bitExactRecoverySampleMass
    (F : BitEncodedClassifierFamily Input s)
    (μ : PMF Input) (target : Input → Bool) (m : ℕ) : ℝ≥0∞ :=
  @EncodedFamily.exactRecoverySampleMass _ _ _ _ F.toEncodedFamily
    (by
      change Nonempty (BitCode s)
      exact ⟨fun _ => false⟩)
    μ target m

/-- The finite weighted ERM recovery theorem specialized to an `s`-bit encoded
family.  This is the exact certificate that a same-route rescue must provide to
reuse the current learning-theoretic backbone. -/
theorem exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    (F : BitEncodedClassifierFamily Input s)
    (μ : PMF Input) (target : Input → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    {q : ℝ≥0∞}
    (hq : ∀ c : F.toEncodedFamily.BadCodes target, agreementMass μ target (F.decode c.1) ≤ q) :
    1 - (2 ^ s : ℝ≥0∞) * q ^ m ≤
      F.bitExactRecoverySampleMass μ target m := by
  have hmain := @EncodedFamily.exactRecoverySampleMass_ge_one_sub_codeCard_mul_pow_of_agreementMass_le
    _ _ _ _ F.toEncodedFamily
    (by
      change Nonempty (BitCode s)
      exact ⟨Classical.choose htarget⟩)
    μ target m htarget q hq
  simpa [bitExactRecoverySampleMass, BitEncodedClassifierFamily.toEncodedFamily, card_bitCode] using
    hmain

end Recovery

end BitEncodedClassifierFamily

end Mettapedia.Computability.PNP
