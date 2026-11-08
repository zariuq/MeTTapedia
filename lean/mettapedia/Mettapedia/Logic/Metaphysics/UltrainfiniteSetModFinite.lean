import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Nat.Nth
import Mettapedia.Logic.StoneGunkDuality

/-!
# The bridge model `P(ℕ)/fin`

Germs along a filter of functions into a Boolean algebra form a Boolean algebra
(`instBooleanAlgebraGerm`), computed pointwise. For the cofinite filter on `ℕ` and `Prop` this is
`P(ℕ)/fin` (`SetModFinite`): subsets of `ℕ` with finite differences ignored.

* **Its zero is the class of all finite sets** (`coe_eq_bot_iff`): infinitely many empties, one
  class.
* **It has no atoms** (`isGunky_setModFinite`): every infinite set splits into two infinite sets
  (the members of even and of odd rank, `Nat.nth`).
* **Its Stone space is perfect** (`perfectSpace_stoneSpace_setModFinite`), by
  `StoneGunkDuality.isGunky_iff_perfect_stoneSpace`: no point is isolated.

This is a bridge model, not a foundation: it is built from the subsets of `ℕ`, so from the finite,
and its zero is the finite sets. The identification of its Stone points with the free ultrafilters
on `ℕ` is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Filter Mettapedia.Foundations.Gunk

universe u v

/-- **Germs into a Boolean algebra form a Boolean algebra**, pointwise. -/
instance instBooleanAlgebraGerm {α : Type u} {β : Type v} {l : Filter α} [BooleanAlgebra β] :
    BooleanAlgebra (Germ l β) where
  __ := Germ.instDistribLattice
  compl := Germ.map compl
  top := ⊤
  bot := ⊥
  inf_compl_le_bot f := Germ.inductionOn f fun f =>
    (Germ.coe_le (f := fun x => f x ⊓ (f x)ᶜ) (g := fun _ => ⊥)).mpr
      (Eventually.of_forall fun x => (inf_compl_self (f x)).le)
  top_le_sup_compl f := Germ.inductionOn f fun f =>
    (Germ.coe_le (f := fun _ => ⊤) (g := fun x => f x ⊔ (f x)ᶜ)).mpr
      (Eventually.of_forall fun x => (sup_compl_eq_top (x := f x)).ge)
  le_top _ := le_top
  bot_le _ := bot_le
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl

/-- **`P(ℕ)/fin`**: subsets of `ℕ`, as predicates, with finite differences ignored. -/
abbrev SetModFinite := Germ (cofinite : Filter ℕ) Prop

/-- **The zero of `P(ℕ)/fin` is the class of all finite sets.** -/
theorem coe_eq_bot_iff (S : ℕ → Prop) : (S : SetModFinite) = ⊥ ↔ {n | S n}.Finite := by
  rw [show (⊥ : SetModFinite) = ((fun _ => False : ℕ → Prop) : SetModFinite) from rfl, Germ.coe_eq,
    EventuallyEq, eventually_cofinite]
  simp

/-- **`P(ℕ)/fin` has no atoms**: every infinite set splits into two infinite sets. -/
theorem isGunky_setModFinite : IsGunky SetModFinite := by
  intro a
  refine Germ.inductionOn a fun S nonzero => ?_
  have infinite : {n | S n}.Infinite := fun finite => nonzero ((coe_eq_bot_iff S).mpr finite)
  have injective : Function.Injective (Nat.nth S) := Nat.nth_injective infinite
  let T : ℕ → Prop := fun n => ∃ k, Nat.nth S (2 * k) = n
  have evenRanks : {n | T n}.Infinite :=
    Set.infinite_range_of_injective (f := fun k => Nat.nth S (2 * k))
      fun j k same => by have := injective same; omega
  have oddRanks : (Set.range fun k => Nat.nth S (2 * k + 1)).Infinite :=
    Set.infinite_range_of_injective fun j k same => by have := injective same; omega
  have below : (T : SetModFinite) ≤ S :=
    Germ.coe_le.mpr (Eventually.of_forall fun n ⟨k, hk⟩ => hk ▸ Nat.nth_mem_of_infinite infinite _)
  refine ⟨(T : SetModFinite), fun zero => evenRanks ((coe_eq_bot_iff T).mp zero),
    lt_of_le_of_ne below fun same => ?_⟩
  have differ := Germ.coe_eq.mp same
  rw [EventuallyEq, eventually_cofinite] at differ
  refine oddRanks (differ.subset ?_)
  rintro _ ⟨k, rfl⟩ agree
  have member : S (Nat.nth S (2 * k + 1)) := Nat.nth_mem_of_infinite infinite _
  rw [← agree] at member
  obtain ⟨j, hj⟩ := member
  have := injective hj
  omega

/-- **The Stone space of `P(ℕ)/fin` is perfect**: no point is isolated. -/
theorem perfectSpace_stoneSpace_setModFinite : PerfectSpace (StoneSpace SetModFinite) :=
  isGunky_iff_perfect_stoneSpace.mp isGunky_setModFinite

end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms instBooleanAlgebraGerm
#print axioms coe_eq_bot_iff
#print axioms isGunky_setModFinite
#print axioms perfectSpace_stoneSpace_setModFinite

end Mettapedia.Logic.Metaphysics.Ultrainfinite
