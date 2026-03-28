import Mettapedia.Computability.PNP.InvariantScoreObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: invariant-score signal comes only from weight asymmetry

If the retained score inputs are involution-invariant and the target flips under
the involution, then any signed correlation carried by an invariant soft score
must come entirely from the antisymmetric part of the weighting.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [Fintype α]

/-- The contribution of one sample point to an invariant signed-score sum. -/
def signedScoreContribution
    (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ) (x : α) : ℤ :=
  (w x : ℤ) * score (u x) * targetSign (y x)

/-- The antisymmetric part of the weight contribution along one involution pair. -/
def antisymmetricWeightContribution
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ) (x : α) : ℤ :=
  ((w x : ℤ) - (w (τ x) : ℤ)) * score (u x) * targetSign (y x)

/-- For invariant score inputs and target-flipping involution, twice the total
signed score equals the total contribution of the antisymmetric weight part. -/
theorem two_mul_signedScore_sum_eq_antisymmetricWeight_sum
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → ℕ) (score : U → ℤ)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x)) :
    2 * ∑ x : α, signedScoreContribution u y w score x
      = ∑ x : α, antisymmetricWeightContribution τ u y w score x := by
  let f : α → ℤ := signedScoreContribution u y w score
  have hbij : Function.Bijective τ := by
    refine ⟨hτ.injective, ?_⟩
    intro x
    exact ⟨τ x, hτ x⟩
  have hsum :
      ∑ x : α, f x = ∑ x : α, f (τ x) := by
    refine Fintype.sum_equiv (Equiv.ofBijective τ hbij) f (fun x : α => f (τ x)) ?_
    intro x
    simp [hτ x]
  have hadd :
      ∑ x : α, (f x + f (τ x)) = ∑ x : α, f x + ∑ x : α, f (τ x) := by
    simpa using
      (Finset.sum_add_distrib (s := (Finset.univ : Finset α))
        (f := f) (g := fun x => f (τ x)))
  calc
    2 * ∑ x : α, f x = ∑ x : α, f x + ∑ x : α, f x := by ring
    _ = ∑ x : α, f x + ∑ x : α, f (τ x) := by rw [hsum]
    _ = ∑ x : α, (f x + f (τ x)) := by
      simpa using hadd.symm
    _ = ∑ x : α, antisymmetricWeightContribution τ u y w score x := by
      refine Fintype.sum_congr (fun x : α => f x + f (τ x))
        (fun x : α => antisymmetricWeightContribution τ u y w score x) ?_
      intro x
      dsimp [f, signedScoreContribution, antisymmetricWeightContribution]
      rw [hu x, hy x, targetSign_flip]
      ring

end

end Mettapedia.Computability.PNP
