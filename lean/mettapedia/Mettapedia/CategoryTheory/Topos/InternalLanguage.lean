import Mathlib.Order.Heyting.Basic
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Internal Language Theory for OSLF

This file documents the internal language concepts needed to understand
WHY OSLF and Native Type Theory work semantically.

## The Key Insight

**Without internal language theory:**
- Modal types are just "things we define"
- No explanation of WHY rely-possibly formulas have their meaning

**With internal language theory:**
- Modal types ARE comprehensions (subobjects classified by χ : X → Ω)
- Rely-possibly IS the logical formula defining them via Kripke-Joyal semantics
- Reduction semantics provides the existential witness
- Everything has categorical/logical meaning!

## Kripke-Joyal Semantics (Conceptual)

In a topos E with subobject classifier Ω and truth morphism ⊤ : 1 → Ω,
a formula φ : A → Ω is interpreted via **Kripke-Joyal semantics**:

For f : X → A (a "generalized element of A at stage X"):

- f ⊨ ⊤  always holds
- f ⊨ φ ∧ ψ  iff  f ⊨ φ and f ⊨ ψ
- f ⊨ φ → ψ  iff  for all g : Y → X, (f ∘ g ⊨ φ implies f ∘ g ⊨ ψ)
- f ⊨ ∀x:B. φ(x)  iff  for all g : Y → X and h : Y → B, (f ∘ g, h) ⊨ φ
- f ⊨ ∃x:B. φ(x)  iff  there exists a cover (gᵢ : Yᵢ → X) and hᵢ : Yᵢ → B
                        such that (f ∘ gᵢ, hᵢ) ⊨ φ

## Connection to OSLF Modal Types

The rely-possibly formula for modal types:

  ⟨Cⱼ⟩_{xₖ::Aₖ} B = { t : context | ∀xₖ. (∧ xₖ::Aₖ) → ∃p. Cⱼ[t]⇝p ∧ p::B }

In Kripke-Joyal terms:
- "∀xₖ" means: for all stages and parameter choices (universal quantifier)
- "xₖ::Aₖ" means: parameters satisfying rely predicates (comprehension)
- "∃p" means: there exists a cover (reduction provides covers!)
- "Cⱼ[t]⇝p" means: reduction is possible (the cover condition)
- "p::B" means: the result satisfies predicate B (comprehension)

**This is WHY OSLF works:** modal types are comprehensions in a topos,
and their semantics follows from the internal logic interpretation!

## References

- MacLane & Moerdijk, "Sheaves in Geometry and Logic" Ch. VI §6
- Bell, "Toposes and Local Set Theories" Ch. 3
- Pitts, "Categorical Logic" in Handbook of Logic in Computer Science
-/

set_option linter.dupNamespace false

namespace Mettapedia.CategoryTheory.Topos.InternalLanguage

/-! ## Abstract Internal Language

We model the internal language abstractly. The key structure is:

1. A type of "truth values" Ω with Frame (complete Heyting algebra) structure
2. Predicates as functions A → Ω
3. Satisfaction defined via the algebra structure
-/

/-- An abstract internal language consists of truth values with Frame structure -/
structure IntLang where
  /-- The type of truth values (subobject classifier) -/
  Ω : Type*
  /-- Truth values form a Frame (complete Heyting algebra) -/
  [frame : Order.Frame Ω]

namespace IntLang

attribute [instance] IntLang.frame

variable (L : IntLang)

/-- A predicate on type A is a function to truth values -/
def Pred (A : Type*) := A → L.Ω

/-- The constantly-true predicate -/
def truePred (A : Type*) : Pred L A := fun _ => ⊤

/-- The constantly-false predicate -/
def falsePred (A : Type*) : Pred L A := fun _ => ⊥

/-- Conjunction of predicates -/
def andPred {A : Type*} (φ ψ : Pred L A) : Pred L A :=
  fun a => φ a ⊓ ψ a

/-- Disjunction of predicates -/
def orPred {A : Type*} (φ ψ : Pred L A) : Pred L A :=
  fun a => φ a ⊔ ψ a

/-- Implication of predicates (Heyting) -/
def implPred {A : Type*} (φ ψ : Pred L A) : Pred L A :=
  fun a => φ a ⇨ ψ a

/-- Comprehension: elements satisfying a predicate -/
def comprehension {A : Type*} (φ : Pred L A) : Set A :=
  { a | φ a = ⊤ }

/-- Satisfaction: a ⊨ φ means φ(a) = ⊤ -/
def sat {A : Type*} (a : A) (φ : Pred L A) : Prop :=
  φ a = ⊤

/-- True is always satisfied -/
theorem sat_true {A : Type*} (a : A) : sat L a (truePred L A) := rfl

/-- Conjunction semantics -/
theorem sat_and {A : Type*} (a : A) (φ ψ : Pred L A) :
    sat L a (andPred L φ ψ) ↔ (sat L a φ ∧ sat L a ψ) := by
  unfold sat andPred
  constructor
  · intro h
    constructor
    · exact le_antisymm le_top (h ▸ inf_le_left)
    · exact le_antisymm le_top (h ▸ inf_le_right)
  · intro ⟨hφ, hψ⟩
    simp [hφ, hψ]

end IntLang

/-! ## Key Theorem: Frame Structure Enables Modal Reasoning

The Frame (complete Heyting algebra) structure on truth values is
essential because:

1. **Arbitrary joins** (sSup) model the existential quantifier
2. **Arbitrary meets** (sInf) model the universal quantifier
3. **Meet distributes over joins** - this is the quantale law!
4. **Heyting implication** models logical implication

The modal composition (tensor product in the quantale) arises from
this structure via:

  (φ ⊗ ψ)(a) = ⨆ { φ(b) ⊓ ψ(c) | b, c reduce from a }

This is exactly what LambdaTheory.lean proves with `modalCompose_sSup`!
-/

theorem frame_enables_modality (L : IntLang) (a : L.Ω) (S : Set L.Ω) :
    a ⊓ sSup S = sSup ((a ⊓ ·) '' S) := by
  rw [inf_sSup_eq, sSup_image]

end Mettapedia.CategoryTheory.Topos.InternalLanguage

/-! ## Summary

This file establishes the semantic foundation for OSLF:

1. ✅ **IntLang**: Abstract structure with Frame Ω
2. ✅ **Pred**: Functions A → Ω (the internal logic)
3. ✅ **comprehension**: { a | φ(a) = ⊤ }
4. ✅ **sat**: a ⊨ φ iff φ(a) = ⊤
5. ✅ **Frame law**: Meet distributes over joins (quantale property)

**Why this matters for OSLF:**

The modal types in OSLF are comprehensions of rely-possibly formulas.
The Frame structure provides:
- Existential quantification via sSup (for "∃p. reduction to p")
- Universal quantification via sInf (for "∀xₖ. relies")
- The quantale law (meet distributes over join)

This connects to LambdaTheory.lean where we proved:
- `modalCompose_sSup`: composition distributes over joins
- This IS the quantale law in disguise!

**Future work:**
- Connect to Mathlib's `HasClassifier` for specific toposes
- Prove the full Kripke-Joyal semantics
- Show presheaf toposes satisfy these properties
-/
