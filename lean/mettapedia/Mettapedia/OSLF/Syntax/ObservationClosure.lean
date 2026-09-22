import Mathlib.Logic.Relation

/-!
# From a raw distinction to an equation theory, and what survives the climb

A theory of observation starts from something weaker than an equivalence.  The
primitive is a *policy* saying which pairs an observer declines to tell apart:
an arbitrary relation, with no reflexivity, symmetry or transitivity assumed.
Three rungs sit above it, and they are genuinely different objects:

* **rung 0** an arbitrary relation `R` -- a raw indistinction policy;
* **rung 1** `Tolerance R`, its reflexive-symmetric closure -- what "cannot
  tell apart" means when the observer is at least consistent with itself and
  does not care about the order in which it is handed a pair;
* **rung 2** `Relation.EqvGen R`, the equivalence it generates -- what an
  equational theory means.

Only rung 2 lets indistinguishability be *composed*, and composing it is not
free.  This module proves both halves of that.

**What survives the climb.**  A predicate that cannot separate raw-related
things cannot separate anything the closure relates either: stability is the
same condition at all three rungs (`stable_tolerance_iff`, `stable_eqvGen_iff`).
So working with an equation theory rather than with the raw policy loses
nothing *about observations*.

**What does not.**  The relation itself changes, and the change can be total.
Adjacency on the numbers is a tolerance that is not transitive, and its
equivalence closure relates everything; so a predicate that cannot separate
adjacent numbers cannot separate any two numbers at all
(`stable_adjacent_is_constant`).  That is the sorites, as a theorem, and it is
the reason the rungs must stay distinct: passing to the closure is sound for
observations and catastrophic for the relation.

Both controls -- the collapse and a policy whose closure is *not* total -- are
in `ObservationClosureWitness`, kept apart so that this module needs nothing but
the relation library and can be imported wherever the ladder is used.

**Where OSLF's equations sit, precisely.**  A presentation's `EqClosure` is not
the rung-2 relation of its axiom instances: it adjoins `cong` as well, so it is
a *congruence* closure and sits a rung above.  `eqvGen_axInstance_le_eqClosure`
in the binding-signature development records the inclusion that does hold --
rung 2 of the bare axiom instances lands inside the congruence closure -- so
stability checked against the congruence closure descends to the ladder, while
the converse needs the contextual step and is not claimed here.  Getting this
the wrong way round is easy and was got wrong once: the theorems below reach the
equivalence rung, and a presentation's quotient is above it.
-/

namespace Mettapedia.OSLF.Syntax.ObservationClosure

open Relation

set_option autoImplicit false

universe u

variable {α : Type u}

/-! ## Rung 1: the tolerance a policy generates -/

/-- The reflexive-symmetric closure of a raw indistinction policy.  Transitivity
is deliberately absent: an observer that cannot separate `x` from `y`, nor `y`
from `z`, may still separate `x` from `z`. -/
def Tolerance (R : α → α → Prop) : α → α → Prop :=
  fun x y => x = y ∨ R x y ∨ R y x

theorem tolerance_refl (R : α → α → Prop) (x : α) : Tolerance R x x := Or.inl rfl

theorem tolerance_symm {R : α → α → Prop} {x y : α} (h : Tolerance R x y) :
    Tolerance R y x := by
  rcases h with rfl | h | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem le_tolerance (R : α → α → Prop) (x y : α) (h : R x y) : Tolerance R x y :=
  Or.inr (Or.inl h)

/-- **The tolerance is the least reflexive symmetric relation containing the
policy.**  This is the universal property that makes rung 1 canonical rather
than one construction among several. -/
theorem tolerance_least {R S : α → α → Prop} (hrefl : ∀ x, S x x)
    (hsymm : ∀ {x y : α}, S x y → S y x) (h : ∀ x y, R x y → S x y) :
    ∀ x y, Tolerance R x y → S x y := by
  rintro x y (rfl | hxy | hyx)
  · exact hrefl x
  · exact h x y hxy
  · exact hsymm (h y x hyx)

/-! ## Rung 2: the equation theory

`Relation.EqvGen` is Mathlib's equivalence closure, and it is reused rather
than rebuilt.  Its universal property is recorded here in the form the rungs
below need. -/

theorem tolerance_le_eqvGen (R : α → α → Prop) (x y : α) (h : Tolerance R x y) :
    EqvGen R x y := by
  rcases h with rfl | hxy | hyx
  · exact EqvGen.refl x
  · exact EqvGen.rel x y hxy
  · exact EqvGen.symm y x (EqvGen.rel y x hyx)

/-- **The closure is the least equivalence containing the policy.** -/
theorem eqvGen_least {R S : α → α → Prop} (hS : Equivalence S)
    (h : ∀ x y, R x y → S x y) : ∀ x y, EqvGen R x y → S x y := by
  intro x y hxy
  induction hxy with
  | rel a b hab => exact h a b hab
  | refl a => exact hS.refl a
  | symm a b _ ih => exact hS.symm ih
  | trans a b c _ _ ih₁ ih₂ => exact hS.trans ih₁ ih₂

/-! ## Observations, and why the rungs agree about them -/

/-- An **observation** at a relation: a predicate that cannot tell related
things apart. -/
def Stable (S : α → α → Prop) (P : α → Prop) : Prop :=
  ∀ x y, S x y → (P x ↔ P y)

/-- Stability at the policy and at its tolerance are the same condition. -/
theorem stable_tolerance_iff {R : α → α → Prop} {P : α → Prop} :
    Stable R P ↔ Stable (Tolerance R) P := by
  constructor
  · rintro h x y (rfl | hxy | hyx)
    · exact Iff.rfl
    · exact h x y hxy
    · exact (h y x hyx).symm
  · intro h x y hxy
    exact h x y (le_tolerance R x y hxy)

/-- **And so is stability at the equation theory.**  Climbing the ladder does
not change which predicates count as observations, which is what licenses
working with an equational quotient instead of the raw policy. -/
theorem stable_eqvGen_iff {R : α → α → Prop} {P : α → Prop} :
    Stable R P ↔ Stable (EqvGen R) P := by
  constructor
  · intro h x y hxy
    induction hxy with
    | rel a b hab => exact h a b hab
    | refl _ => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h x y hxy
    exact h x y (EqvGen.rel x y hxy)

/-- The three rungs therefore have exactly the same observations. -/
theorem stable_iff_stable_of_rungs {R : α → α → Prop} {P : α → Prop} :
    (Stable R P ↔ Stable (Tolerance R) P) ∧ (Stable R P ↔ Stable (EqvGen R) P) :=
  ⟨stable_tolerance_iff, stable_eqvGen_iff⟩

end Mettapedia.OSLF.Syntax.ObservationClosure
