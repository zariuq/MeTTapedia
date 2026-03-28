import Mettapedia.Computability.PNP.AsymmetryBudgetObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: side channels help only on orbit-resolving mass

One natural repair route is to keep a controlled amount of involution-sensitive
local information.  This file packages the earlier residual-symmetry and
asymmetry-budget obstructions into the right direct statement for that move:
if the retained invariant features are augmented by a side channel `v`, then any
global advantage can come only from the mass where `v` actually separates an
orbit point from its involution partner.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U V : Type*} [Fintype α]

/-- The slice on which a side channel fails to distinguish an involution pair. -/
def unresolvedBySideChannel
    (τ : α → α) (v : α → V) : α → Prop :=
  fun x => v (τ x) = v x

/-- The total weight of the points whose side-channel value changes under the
involution.  This is exactly the mass where the side channel resolves the orbit
pair. -/
noncomputable def resolvedMass
    (τ : α → α) (v : α → V) (w : α → ℕ) : ℕ :=
  by
    classical
    exact outsideMass (unresolvedBySideChannel τ v) w

/-- For classifiers that use an invariant feature map `u` together with a side
channel `v`, any advantage over chance is bounded by the mass where `v`
actually distinguishes involution partners. -/
theorem two_mul_weightedCorrectMass_pair_le_total_plus_resolvedMass
    (τ : α → α) (u : α → U) (v : α → V) (y : α → Bool) (w : α → ℕ)
    (h : U × V → Bool)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    2 * weightedCorrectMass (fun x => (u x, v x)) y w h
      ≤ weightedTotalMass w + resolvedMass τ v w := by
  classical
  let p : α → Prop := unresolvedBySideChannel τ v
  have hp : ∀ x, p x → p (τ x) := by
    intro x hx
    dsimp [p, unresolvedBySideChannel] at hx ⊢
    simpa [hτ x] using hx.symm
  have huv : ∀ x, p x → (u (τ x), v (τ x)) = (u x, v x) := by
    intro x hx
    exact Prod.ext (hu x) hx
  simpa [resolvedMass, p, unresolvedBySideChannel] using
    (two_mul_weightedCorrectMass_le_total_plus_outside
      (α := α) (U := U × V)
      τ p (fun x => (u x, v x)) y w h
      hτ hp huv
      (fun x _ => hy x)
      (fun x _ => hw x))

end

end Mettapedia.Computability.PNP
