import Mettapedia.Computability.PNP.OrbitNeutralityObstruction
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# P vs NP crux: invariant feature fibers have exact zero margin

The previous orbit-neutrality obstruction showed that if an involution preserves
the retained feature map and flips the target bit, then every classifier using
only those features has exactly `1/2` average accuracy.

This file strengthens that statement to the soft-score setting.  Under the same
hypotheses, every *individual feature fiber* already has exact half `true` and
half `false` labels.  So the conditional mean of the target on any retained
feature value is exactly `1/2`, and no margin can be extracted from those
features alone.
-/

namespace Mettapedia.Computability.PNP

section

variable {α U : Type*} [DecidableEq U]

/-- The fiber of a feature map over one retained feature value. -/
abbrev FeatureFiber (u : α → U) (v : U) := {x : α // u x = v}

/-- Points in one feature fiber whose target bit is `true`. -/
abbrev FeatureFiberTrue (u : α → U) (y : α → Bool) (v : U) :=
  {x : FeatureFiber u v // y x.1 = true}

/-- Points in one feature fiber whose target bit is `false`. -/
abbrev FeatureFiberFalse (u : α → U) (y : α → Bool) (v : U) :=
  {x : FeatureFiber u v // y x.1 = false}

/-- On each retained feature fiber, the involution pairs every `true` label with
one `false` label. -/
def featureFiberTrueEquivFalse
    (τ : α → α) (u : α → U) (y : α → Bool) (v : U)
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x)) :
    FeatureFiberTrue u y v ≃ FeatureFiberFalse u y v where
  toFun x := ⟨
    ⟨τ x.1.1, by simpa [x.1.2] using hu x.1.1⟩,
    by simp [hy x.1.1, x.2]⟩
  invFun x := ⟨
    ⟨τ x.1.1, by simpa [x.1.2] using hu x.1.1⟩,
    by
      have hflip : y (τ (τ x.1.1)) = !(y (τ x.1.1)) := hy (τ x.1.1)
      simpa [hτ x.1.1, x.2] using hflip⟩
  left_inv x := by
    ext
    simp [hτ x.1.1]
  right_inv x := by
    ext
    simp [hτ x.1.1]

/-- Therefore each retained feature fiber has exactly as many `true` labels as
`false` labels. -/
theorem card_featureFiberTrue_eq_card_featureFiberFalse
    (τ : α → α) (u : α → U) (y : α → Bool) (v : U)
    [Fintype α]
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x)) :
    Fintype.card (FeatureFiberTrue u y v) =
      Fintype.card (FeatureFiberFalse u y v) := by
  classical
  exact Fintype.card_congr (featureFiberTrueEquivFalse τ u y v hτ hu hy)

/-- Equivalently, the conditional mean on every retained feature value is
exactly `1/2`: the `true` part occupies half the fiber. -/
theorem two_mul_card_featureFiberTrue_eq_card_featureFiber
    (τ : α → α) (u : α → U) (y : α → Bool) (v : U)
    [Fintype α]
    (hτ : Function.Involutive τ)
    (hu : ∀ x, u (τ x) = u x)
    (hy : ∀ x, y (τ x) = !(y x)) :
    2 * Fintype.card (FeatureFiberTrue u y v) = Fintype.card (FeatureFiber u v) := by
  classical
  set a : ℕ := Fintype.card (FeatureFiberTrue u y v)
  have hcomp :
      Fintype.card (FeatureFiberFalse u y v) =
        Fintype.card (FeatureFiber u v) - a := by
    simpa [a, FeatureFiberTrue, FeatureFiberFalse] using
      (Fintype.card_subtype_compl fun x : FeatureFiber u v => y x.1 = true)
  have heq : a = Fintype.card (FeatureFiberFalse u y v) := by
    simpa [a] using card_featureFiberTrue_eq_card_featureFiberFalse τ u y v hτ hu hy
  have hsub : Fintype.card (FeatureFiber u v) - a = a := by
    simpa [heq] using hcomp.symm
  have hle : a ≤ Fintype.card (FeatureFiber u v) := by
    simpa [a, FeatureFiberTrue] using
      Fintype.card_subtype_le (fun x : FeatureFiber u v => y x.1 = true)
  have hsum : Fintype.card (FeatureFiber u v) = a + a := Nat.eq_add_of_sub_eq hle hsub
  simpa [a, two_mul, Nat.add_comm] using hsum.symm

end

end Mettapedia.Computability.PNP
