import Mettapedia.OSLF.Formula
import Mathlib.Order.FixedPoints

/-!
# Least fixpoints over the predicate frame

The generated logic's predicates at a sort form a frame, hence a complete
lattice, so every monotone predicate transformer has a least fixed point by
Knaster–Tarski.  That is what a scope needs: a region that is finitely
described and unboundedly large, given by a generator rather than a list.

This layer sits beside the formula language and is *not* where the project's
generator lives.  `OSLFFormula` carries a `µ` binder of its own, with a symbol
count, a fixed point law under positivity, and an executable descent; the
theorem at the foot of this file is the argument that made that migration
necessary, and it is kept here because it is a statement about what this layer
cannot do.  What remains useful here is Knaster--Tarski itself, stated once for
the ambient predicate lattice.

The choice of *least* rather than greatest is not neutral, and the reason is
economic.  A scope whose membership test terminates is one an agent can survey;
a greatest fixed point admits members witnessed only by an infinite descent,
which is a cost with no receipt.

Two limitations of this layer, both of which the formula-language binder now
answers.  `Pred` is the lattice of *all* predicates on patterns: it is neither
sorted nor equation-invariant, where the project's own notion of a predicate of
the generated logic is `EquationPredicate`, a subtype carrying that invariance —
so a fixed point taken here is taken in a lattice the generated logic does not
have.  And a transformer has no symbols, so generator length — the number of
symbols in a generator, set against the size of its extension — is not a
function of an object of this type at all.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FormulaFixpoint

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula

/-- Predicates on patterns, ordered by implication. -/
abbrev Pred := Pattern → Prop

/-- The least fixed point of a monotone predicate transformer. -/
def lfp (f : Pred →o Pred) : Pred := OrderHom.lfp f

/-- **Knaster–Tarski, unfolding.**  The least fixed point is a fixed point. -/
theorem lfp_unfold (f : Pred →o Pred) : f (lfp f) = lfp f :=
  (OrderHom.map_lfp f)

/-- **Knaster–Tarski, induction.**  Any pre-fixed point is above the least
fixed point: this is the induction principle a scope is surveyed by. -/
theorem lfp_le {f : Pred →o Pred} {p : Pred} (pre : f p ≤ p) : lfp f ≤ p :=
  OrderHom.lfp_le f pre

/-- The least fixed point is below every fixed point. -/
theorem lfp_le_of_eq {f : Pred →o Pred} {p : Pred} (fixed : f p = p) : lfp f ≤ p :=
  lfp_le (le_of_eq fixed)

/-- Membership in the least fixed point is preserved by the transformer. -/
theorem mem_lfp_of_mem_apply {f : Pred →o Pred} {term : Pattern}
    (member : f (lfp f) term) : lfp f term := by
  rw [lfp_unfold f] at member
  exact member

/-- And conversely. -/
theorem mem_apply_of_mem_lfp {f : Pred →o Pred} {term : Pattern}
    (member : lfp f term) : f (lfp f) term := by
  rw [lfp_unfold f]
  exact member

/-! ## Transformers from the connectives

A generator is built from the logic's own connectives, so the transformers that
matter are the ones those connectives induce.  Each is monotone, so each has a
least fixed point; none of this is vacuous. -/

/-- Disjunction with a fixed predicate is monotone. -/
def orWith (fixedPart : Pred) : Pred →o Pred where
  toFun := fun variablePart term => fixedPart term ∨ variablePart term
  monotone' := by
    intro first second inclusion term
    rintro (hfixed | hvar)
    · exact Or.inl hfixed
    · exact Or.inr (inclusion term hvar)

/-- Conjunction with a fixed predicate is monotone. -/
def andWith (fixedPart : Pred) : Pred →o Pred where
  toFun := fun variablePart term => fixedPart term ∧ variablePart term
  monotone' := by
    intro first second inclusion term
    rintro ⟨hfixed, hvar⟩
    exact ⟨hfixed, inclusion term hvar⟩

/-- The step-future modality is monotone. -/
def diaOf (step : Pattern → Pattern → Prop) : Pred →o Pred where
  toFun := fun variablePart term =>
    ∃ successor, step term successor ∧ variablePart successor
  monotone' := by
    intro first second inclusion term
    rintro ⟨successor, hstep, hvar⟩
    exact ⟨successor, hstep, inclusion successor hvar⟩

/-- Composition of monotone transformers is monotone, so generators built by
nesting connectives have least fixed points too. -/
def comp (outer inner : Pred →o Pred) : Pred →o Pred :=
  outer.comp inner

theorem comp_apply (outer inner : Pred →o Pred) (p : Pred) :
    comp outer inner p = outer (inner p) := rfl

/-- A transformer that ignores its argument has the fixed part as its least
fixed point: the degenerate generator describes exactly its atoms. -/
theorem lfp_const (fixedPart : Pred) :
    lfp ⟨fun _ => fixedPart, by intro _ _ _; exact le_refl _⟩ = fixedPart := by
  apply le_antisymm
  · exact lfp_le (le_refl _)
  · intro term member
    have := lfp_unfold ⟨fun _ => fixedPart, by intro _ _ _; exact le_refl _⟩
    rw [← this]
    exact member

/-! ## Why this layer cannot be the destination

The source material makes the *generator length* of a scope the number of
symbols in its generator, and the substance of that chapter is that generator
length and extension size are different quantities which do not move together —
a compact description of an enormous structure is cheap in the description, not
in the structure.

That quantity is not available here, and the reason is not that it is awkward to
define.  A transformer forgets the generator that produced it: the two
generators below differ as syntax — one is the scope variable alone, the other
disjoins it with the empty predicate — and are *equal* as transformers.  Any
function of a transformer therefore assigns them the same value, while generator
length must assign them different ones.  So generator length is not a function
of an object of this type at all.

This is the justification for carrying a fixpoint binder in the formula language
rather than only here.  It is a statement about what this layer cannot do, not a
preference, and it is why `OSLFFormula.mu` exists. -/

/-- Disjoining the scope variable with the empty predicate changes the
generator and not the transformer. -/
theorem transformer_forgets_generator :
    orWith (fun _ => False) = (OrderHom.id : Pred →o Pred) := by
  apply OrderHom.ext
  funext variablePart
  funext term
  exact propext ⟨fun h => h.elim (fun absurd => absurd.elim) id, fun h => Or.inr h⟩

/-- Hence the two generators have the same least fixed point, as they must. -/
theorem lfp_orWith_bot :
    lfp (orWith (fun _ => False)) = lfp (OrderHom.id : Pred →o Pred) := by
  rw [transformer_forgets_generator]

end Mettapedia.OSLF.Framework.FormulaFixpoint
