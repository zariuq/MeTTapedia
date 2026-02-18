import Mathlib.Order.GaloisConnection.Defs
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Derived Modalities from Change-of-Base Adjunctions

The OSLF paper (Meredith & Stay) derives modal operators from the reduction span
of a rewrite system via change-of-base functors. This file formalizes that
construction at the Set level and proves the key results:

1. **Set-level change-of-base**: For any function `f : E → X`, the triple
   `∃_f ⊣ f* ⊣ ∀_f` on `(· → Prop)` fibers
2. **Derived modalities**: For a span `E --src--> X <--tgt-- E`:
   - `◇ = ∃_src ∘ tgt*` (step-future)
   - `□ = ∀_tgt ∘ src*` (step-past)
3. **Generic Galois connection**: `◇ ⊣ □` by composing `∃_src ⊣ src*` and `tgt* ⊣ ∀_tgt`
4. **ρ-calculus**: The derived operators equal `possiblyProp`/`relyProp`,
   making the existing Galois connection a corollary of the general construction.

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §4, §6
- Williams & Stay, "Native Type Theory" (ACT 2021) §3
- Jacobs, "Categorical Logic and Type Theory" Ch. 1
-/

namespace Mettapedia.OSLF.Framework.DerivedModalities

/-! ## Reduction Spans -/

/-- A reduction span: the graph of a reduction relation as a diagram `E --src--> X <--tgt-- E`.

    For a rewrite system with reduction `⇝` on terms of type `X`:
    - `Edge` is the type of reduction steps (e.g., `{ (p,q) | p ⇝ q }`)
    - `source` maps each step to its input term
    - `target` maps each step to its output term

    This captures the reduction relation as a span in **Set**, which is the
    input needed for change-of-base to derive modal operators.
-/
structure ReductionSpan (X : Type*) where
  /-- The type of reduction steps (edges of the reduction graph) -/
  Edge : Type*
  /-- Source of a reduction step -/
  source : Edge → X
  /-- Target of a reduction step -/
  target : Edge → X

/-! ## Set-Level Change-of-Base Functors

For any function `f : E → X`, we get three operations on predicate fibers:
- `pb f` (pullback / inverse image): `(X → Prop) → (E → Prop)`
- `di f` (direct image / ∃): `(E → Prop) → (X → Prop)`
- `ui f` (universal image / ∀): `(E → Prop) → (X → Prop)`

These satisfy the adjoint triple: `∃_f ⊣ f* ⊣ ∀_f`.
-/

section SetLevelChangeOfBase

variable {X : Type*} {E : Type*}

/-- Pullback (inverse image): `f*(φ)(e) = φ(f(e))`.

    Pulls back a predicate on `X` to a predicate on `E` along `f`. -/
def pb (f : E → X) (φ : X → Prop) : E → Prop := φ ∘ f

/-- Direct image (existential image): `∃_f(ψ)(x) = ∃ e, f(e) = x ∧ ψ(e)`.

    Pushes forward a predicate on `E` to a predicate on `X`:
    `x` satisfies the result iff some `e` mapping to `x` satisfies `ψ`. -/
def di (f : E → X) (ψ : E → Prop) : X → Prop :=
  fun x => ∃ e, f e = x ∧ ψ e

/-- Universal image: `∀_f(ψ)(x) = ∀ e, f(e) = x → ψ(e)`.

    Pushes forward a predicate on `E` to a predicate on `X`:
    `x` satisfies the result iff ALL `e` mapping to `x` satisfy `ψ`. -/
def ui (f : E → X) (ψ : E → Prop) : X → Prop :=
  fun x => ∀ e, f e = x → ψ e

/-- `∃_f ⊣ f*`: Direct image is left adjoint to pullback.

    `∃_f(α) ≤ β  ↔  α ≤ f*(β)`
    i.e., `(∀x, (∃e, f e = x ∧ α e) → β x)  ↔  (∀e, α e → β (f e))` -/
theorem di_pb_adj (f : E → X) : GaloisConnection (di f) (pb f) := by
  intro α β
  simp only [Pi.le_def]
  constructor
  · -- Forward: ∃_f(α) ≤ β implies α ≤ f*(β)
    intro h e hα
    exact h (f e) ⟨e, rfl, hα⟩
  · -- Backward: α ≤ f*(β) implies ∃_f(α) ≤ β
    intro h x ⟨e, hfe, hα⟩
    subst hfe
    exact h e hα

/-- `f* ⊣ ∀_f`: Pullback is left adjoint to universal image.

    `f*(α) ≤ β  ↔  α ≤ ∀_f(β)`
    i.e., `(∀e, α(f e) → β e)  ↔  (∀x, α x → ∀e, f e = x → β e)` -/
theorem pb_ui_adj (f : E → X) : GaloisConnection (pb f) (ui f) := by
  intro α β
  simp only [Pi.le_def]
  constructor
  · -- Forward: f*(α) ≤ β implies α ≤ ∀_f(β)
    intro h x hα e hfe
    subst hfe
    exact h e hα
  · -- Backward: α ≤ ∀_f(β) implies f*(α) ≤ β
    intro h e hα
    exact h (f e) hα e rfl

end SetLevelChangeOfBase

/-! ## Derived Modal Operators

Given a reduction span `E --src--> X <--tgt-- E`, the OSLF modal operators are:

- **◇ (step-future)**: `◇(φ)(p) = ∃q. p ⇝ q ∧ φ(q)` = `∃_src(tgt*(φ))`
  "p can step to some q satisfying φ"

- **□ (step-past)**: `□(φ)(p) = ∀q. q ⇝ p → φ(q)` = `∀_tgt(src*(φ))`
  "all predecessors of p satisfy φ"

The Galois connection `◇ ⊣ □` follows from composing adjunctions:

```
◇(φ) ≤ ψ  ↔  ∃_src(tgt*(φ)) ≤ ψ     (def of ◇)
           ↔  tgt*(φ) ≤ src*(ψ)        (∃_src ⊣ src*)
           ↔  φ ≤ ∀_tgt(src*(ψ))       (tgt* ⊣ ∀_tgt)
           ↔  φ ≤ □(ψ)                 (def of □)
```
-/

variable {X : Type*}

/-- Step-future modal operator derived from change-of-base: `◇ = ∃_src ∘ tgt*`.

    `derivedDiamond(span)(φ)(p) = ∃ e, src(e) = p ∧ φ(tgt(e))`
    = "there is a reduction step from p whose target satisfies φ"
    = "p can step to some q satisfying φ" -/
def derivedDiamond (span : ReductionSpan X) (φ : X → Prop) : X → Prop :=
  di span.source (pb span.target φ)

/-- Step-past modal operator derived from change-of-base: `□ = ∀_tgt ∘ src*`.

    `derivedBox(span)(φ)(p) = ∀ e, tgt(e) = p → φ(src(e))`
    = "for every reduction step ending at p, its source satisfies φ"
    = "all predecessors of p satisfy φ" -/
def derivedBox (span : ReductionSpan X) (φ : X → Prop) : X → Prop :=
  ui span.target (pb span.source φ)

/-- The Galois connection `◇ ⊣ □` from composing adjunctions.

    Per OSLF §4 + §6: the modal operators form an adjoint pair.
    This is proven generically for ANY reduction span, by composing:
    - `∃_src ⊣ src*` (from `di_pb_adj`)
    - `tgt* ⊣ ∀_tgt` (from `pb_ui_adj`)
-/
theorem derived_galois (span : ReductionSpan X) :
    GaloisConnection (derivedDiamond span) (derivedBox span) := by
  intro φ ψ
  -- ◇(φ) ≤ ψ ↔ ∃_src(tgt*(φ)) ≤ ψ ↔ tgt*(φ) ≤ src*(ψ) ↔ φ ≤ ∀_tgt(src*(ψ)) ↔ φ ≤ □(ψ)
  exact Iff.trans (di_pb_adj span.source _ _) (pb_ui_adj span.target _ _)

/-! ## ρ-Calculus Instantiation

We instantiate the generic construction for the ρ-calculus and prove that the
derived operators equal the hand-written `possiblyProp` and `relyProp` from
`Reduction.lean`. This makes the existing Galois connection a **corollary** of
the general adjoint-composition argument.
-/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-- The ρ-calculus reduction span.

    Edges are pairs `(p, q)` with a witness that `p ⇝ q`.
    - `source`: the process before reduction
    - `target`: the process after reduction -/
def rhoSpan : ReductionSpan Pattern where
  Edge := { pair : Pattern × Pattern // Nonempty (pair.1 ⇝ pair.2) }
  source := fun e => e.val.1
  target := fun e => e.val.2

/-- The derived ◇ equals `possiblyProp`.

    Both compute `fun p => ∃ q, Nonempty (p ⇝ q) ∧ φ q`. -/
theorem derived_diamond_eq_possiblyProp (φ : Pattern → Prop) :
    derivedDiamond rhoSpan φ = possiblyProp φ := by
  ext p
  simp only [derivedDiamond, di, pb, Function.comp, rhoSpan, possiblyProp]
  constructor
  · rintro ⟨⟨⟨p', q⟩, hred⟩, hp_eq, hφ⟩
    simp at hp_eq
    subst hp_eq
    exact ⟨q, hred, hφ⟩
  · rintro ⟨q, hred, hφ⟩
    exact ⟨⟨⟨p, q⟩, hred⟩, rfl, hφ⟩

/-- The derived □ equals `relyProp`.

    Both compute `fun p => ∀ q, Nonempty (q ⇝ p) → φ q`. -/
theorem derived_box_eq_relyProp (φ : Pattern → Prop) :
    derivedBox rhoSpan φ = relyProp φ := by
  ext p
  simp only [derivedBox, ui, pb, Function.comp, rhoSpan, relyProp]
  constructor
  · intro h q hred
    exact h ⟨⟨q, p⟩, hred⟩ rfl
  · rintro h ⟨⟨q, p'⟩, hred⟩ hp_eq
    simp at hp_eq
    subst hp_eq
    exact h q hred

/-- The ρ-calculus Galois connection `possiblyProp ⊣ relyProp` as a
    **corollary** of the generic `derived_galois` construction.

    This demonstrates that the OSLF paper's claim — modal operators arise
    from adjoint triples along the reduction span — is not just a slogan
    but a formally verified derivation. -/
theorem rho_galois_from_span : GaloisConnection possiblyProp relyProp := by
  have h := derived_galois rhoSpan
  intro φ ψ
  rw [← derived_diamond_eq_possiblyProp φ, ← derived_box_eq_relyProp ψ]
  exact h φ ψ

/-! ## Summary

**0 sorries. 0 axioms.**

This file establishes:

1. `di_pb_adj` / `pb_ui_adj` — the adjoint triple `∃_f ⊣ f* ⊣ ∀_f` at the Set level
2. `derived_galois` — generic `◇ ⊣ □` for any reduction span
3. `derived_diamond_eq_possiblyProp` / `derived_box_eq_relyProp` — ρ-calculus operators
   are instances of the general construction
4. `rho_galois_from_span` — the ρ-calculus Galois connection as a corollary

**Connection to other files:**
- `Reduction.lean`: provides `possiblyProp`, `relyProp`, `Reduces` (the hand-written versions)
- `RhoInstance.lean`: uses the hand-written versions in `OSLFTypeSystem`; could be refactored
  to use the derived versions via this file
- `GSLT/Core/ChangeOfBase.lean`: the same adjoint triple at the categorical level;
  this file is the concrete Set-level realization
-/

end Mettapedia.OSLF.Framework.DerivedModalities
