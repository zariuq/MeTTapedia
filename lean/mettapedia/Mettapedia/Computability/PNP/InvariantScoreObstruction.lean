import Mathlib.Tactic

/-!
# P vs NP crux: invariant soft scores have zero signed signal

The previous symmetry obstructions ruled out hard classifiers, conditional
means, and even small symmetry-breaking repairs on large unresolved slices.

This file isolates a still more general statement: any soft score computed only
from involution-invariant local features has zero weighted signed correlation
with the target under involution-symmetric weights.  So no downstream nonlinear
use of such a score can create signal unless some genuinely non-invariant mass
is present.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α]

/-- Encode a Boolean target as a signed label. -/
def targetSign (b : Bool) : ℤ :=
  if b then 1 else -1

lemma targetSign_flip (b : Bool) : targetSign (!b) = - targetSign b := by
  cases b <;> simp [targetSign]

/-- The weighted signed correlation of an invariant soft score with the target
vanishes under an involution that preserves the score inputs and weights and
flips the target bit. -/
theorem weighted_signedScore_sum_eq_zero
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ∑ x : α, (w x : ℤ) * score (u x) * targetSign (y x) = 0 := by
  let f : α → ℤ := fun x => (w x : ℤ) * score (u x) * targetSign (y x)
  have hbij : Function.Bijective τ := by
    refine ⟨hτ.injective, ?_⟩
    intro x
    exact ⟨τ x, hτ x⟩
  have hsum :
      ∑ x : α, f x = ∑ x : α, f (τ x) := by
    refine Fintype.sum_equiv (Equiv.ofBijective τ hbij) f (fun x : α => f (τ x)) ?_
    intro x
    simp [hτ x]
  have hflip : ∀ x : α, f (τ x) = -f x := by
    intro x
    simp [f, hu x, hy x, hw x, targetSign_flip, mul_assoc, mul_comm]
  have hneg : ∑ x : α, f x = - ∑ x : α, f x := by
    calc
      ∑ x : α, f x = ∑ x : α, f (τ x) := hsum
      _ = ∑ x : α, -f x := by
        refine Fintype.sum_congr (fun x : α => f (τ x)) (fun x : α => -f x) ?_
        intro x
        exact hflip x
      _ = - ∑ x : α, f x := by
        simp [f]
  have : ∑ x : α, f x = 0 := by
    have hneg' := hneg
    omega
  simpa [f] using this

end

end Mettapedia.Computability.PNP
