import Mettapedia.Computability.PNP.SideChannelResolutionObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: domination advantage forces orbit-resolving mass

The side-channel resolution obstruction shows that total success is bounded by
the mass where a retained side channel actually separates involution partners.

This file packages the converse quantitative reading: any claimed global
advantage over chance forces at least that much orbit-resolving mass.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U V : Type*} [Fintype α]

/-- Twice the success advantage over chance for a weighted classifier. -/
def doubledAdvantage
    (u : α → U) (y : α → Bool) (w : α → ℕ) (h : U → Bool) : ℕ :=
  2 * weightedCorrectMass u y w h - weightedTotalMass w

/-- Any doubled success advantage achieved using an invariant feature map plus
side channel is bounded by the mass where the side channel resolves involution
pairs. -/
theorem doubledAdvantage_pair_le_resolvedMass
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    doubledAdvantage (fun x => (u x, v x)) y w h ≤ resolvedMass τ v w := by
  unfold doubledAdvantage
  have hbound :
      2 * weightedCorrectMass (fun x => (u x, v x)) y w h
        ≤ weightedTotalMass w + resolvedMass τ v w :=
    two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
      τ u v y w h hτ hu hy hw
  omega

end

end Mettapedia.Computability.PNP
