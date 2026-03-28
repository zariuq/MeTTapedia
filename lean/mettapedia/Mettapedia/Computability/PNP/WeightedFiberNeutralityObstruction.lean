import Mettapedia.Computability.PNP.FiberNeutralityObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: orbit-symmetric weights still force zero conditional margin

The previous fiber-neutrality obstruction showed that if an involution preserves
the retained feature map and flips the target bit, then every invariant feature
fiber has exactly as many `true` labels as `false` labels.

This file extends that obstruction from uniform counting to arbitrary
involution-invariant weights.  So the same zero-margin conclusion holds not only
for the raw finite orbit space, but also for any weighted empirical sample or
finite distribution that respects the involution symmetry.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U β : Type*} [DecidableEq U] [Fintype α] [AddCommMonoid β]

/-- The total weight of the `true` points in one retained feature fiber. -/
def weightedFeatureFiberTrueMass
    (u : α → U) (y : α → Bool) (w : α → β) (v : U) : β :=
  ∑ x : FeatureFiberTrue u y v, w x.1.1

/-- The total weight of the `false` points in one retained feature fiber. -/
def weightedFeatureFiberFalseMass
    (u : α → U) (y : α → Bool) (w : α → β) (v : U) : β :=
  ∑ x : FeatureFiberFalse u y v, w x.1.1

/-- Any involution-invariant weight assigns the same total mass to the `true`
and `false` parts of each invariant feature fiber. -/
theorem weightedFeatureFiberTrueMass_eq_weightedFeatureFiberFalseMass
    (τ : α → α) (u : α → U) (y : α → Bool) (w : α → β) (v : U)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    weightedFeatureFiberTrueMass u y w v =
      weightedFeatureFiberFalseMass u y w v := by
  classical
  unfold weightedFeatureFiberTrueMass weightedFeatureFiberFalseMass
  refine Fintype.sum_equiv
    (featureFiberTrueEquivFalse τ u y v hτ hu hy)
    (fun x : FeatureFiberTrue u y v => w x.1.1)
    (fun x : FeatureFiberFalse u y v => w x.1.1) ?_
  intro x
  simpa [featureFiberTrueEquivFalse] using (hw x.1.1).symm

end

end Mettapedia.Computability.PNP
