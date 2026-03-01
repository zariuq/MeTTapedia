/-!
# Structural Congruence Infrastructure for Process Calculi

Shared typeclass and theorems for structural congruence (SC) across
π-calculus, ρ-calculus, and MQ-calculus.

All three calculi define SC as an equivalence relation with:
- reflexivity, symmetry, transitivity
- congruence rules for parallel composition and restriction
- a "reduction modulo SC" constructor in their one-step reduction

This module provides the shared infrastructure.
-/

universe u

namespace ProcessCalculi

/-- Typeclass for process types with structural congruence.

    All three process calculi (π, ρ, MQ) define structural congruence
    as a Prop-valued equivalence relation. -/
class HasSC (α : Type u) where
  /-- Structural congruence relation -/
  sc : α → α → Prop
  sc_refl : ∀ x, sc x x
  sc_symm : ∀ x y, sc x y → sc y x
  sc_trans : ∀ x y z, sc x y → sc y z → sc x z

namespace HasSC

variable {α : Type u} [HasSC α]

/-- Structural congruence forms an equivalence relation. -/
theorem equivalence : Equivalence (sc (α := α)) where
  refl := sc_refl
  symm := sc_symm _ _
  trans := sc_trans _ _ _

/-- SC is reflexive. -/
theorem refl' (x : α) : sc x x := sc_refl x

/-- SC is symmetric. -/
theorem symm' {x y : α} (h : sc x y) : sc y x := sc_symm x y h

/-- SC is transitive. -/
theorem trans' {x y z : α} (h₁ : sc x y) (h₂ : sc y z) : sc x z :=
  sc_trans x y z h₁ h₂

end HasSC

/-- Reduction modulo structural congruence.

    All three process calculi have a constructor of the form:
    `sc p p' → reduces p' q' → sc q' q → reduces p q`

    This theorem captures the shared pattern. -/
theorem reduces_modulo_sc {α : Type u} [HasSC α] {R : α → α → Prop}
    (sc_close : ∀ {p p' q' q : α}, HasSC.sc p p' → R p' q' → HasSC.sc q' q → R p q)
    {p p' q' q : α} (hp : HasSC.sc p p') (hr : R p' q') (hq : HasSC.sc q' q) :
    R p q :=
  sc_close hp hr hq

end ProcessCalculi
