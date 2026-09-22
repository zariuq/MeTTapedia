import Mettapedia.GSLT.GraphTheory.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Weak-product source obligations and projection coding

The projection-only `WeakProduct` below is not a lawful graph model: its
coding has collisions, and its injectivity field remains admitted. The exact
coding obstruction is proved independently in `WeakProductControls`.
`PartialPair` constructs the source's injective partial disjoint union, and
`PartialPairCompletion` constructs its actual canonical graph model.
`FactorFlattening` supplies the source factor-comparison map and its coding
laws. `FactorInterpretation` proves actual interpretation comparison for any
factor satisfying the primitive coding laws, and actual theory lower bounds
for both disjoint-union factors. Indexed families and source stratification
remain separate obligations.

## Main Definitions

* `WeakProduct` - Unfinished projection-only model packaging
* `StratifiedModel` - A rank condition not identified with source stratification

## Source results, not established by this packaging

The source's completed weak product satisfies:
- Th(D₁ ◇ D₂) ⊆ Th(D₁) ∩ Th(D₂)

For models stratified in the source's proper-partial-pair completion sense:
- Every stratified model is semisensible

## References

- Bucciarelli & Salibra, "Graph Lambda Theories" (2008), §3
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

/-! ## Weak Product Construction

The source first combines the webs as an injective partial pair, then adds
fresh tokens for missing full finite-support/output pairs by canonical
completion. Its later i-flattening is a semantic comparison map, not the
construction of injective coding. The total projection map below omits that
completion and cannot satisfy its injectivity obligation.
-/

/-- Project a finite subset of Sum to its left component -/
def projectLeft {α β : Type*} [DecidableEq α] (s : Finset (α ⊕ β)) : Finset α :=
  s.filterMap (fun x => match x with | .inl a => some a | .inr _ => none)
    (by intro a b; cases a <;> cases b <;> simp [eq_comm])

/-- Project a finite subset of Sum to its right component -/
def projectRight {α β : Type*} [DecidableEq β] (s : Finset (α ⊕ β)) : Finset β :=
  s.filterMap (fun x => match x with | .inl _ => none | .inr b => some b)
    (by intro a b; cases a <;> cases b <;> simp [eq_comm])

/-- Unfinished projection-only packaging. Opposite-component support is
discarded, so distinct inputs have the same code. The admitted field below
is false for this definition; source completion requires a different carrier
and coding map, not an injectivity proof for this one. -/
def WeakProduct (D₁ D₂ : GraphModel) : GraphModel where
  web := {
    carrier := D₁.Carrier ⊕ D₂.Carrier
    decEq := instDecidableEqSum
    infinite := Sum.infinite_of_left
  }
  coding := {
    code := fun ⟨a, d⟩ =>
      match d with
      | .inl d₁ => .inl (D₁.coding.code (projectLeft a, d₁))
      | .inr d₂ => .inr (D₂.coding.code (projectRight a, d₂))
    -- False for this coding map: opposite-component supports are erased.
    -- The source's partial-pair completion must replace the construction.
    injective := by
      intro ⟨a₁, d₁⟩ ⟨a₂, d₂⟩ h
      cases d₁ with
      | inl x₁ =>
        cases d₂ with
        | inl x₂ =>
          simp at h
          have hc := D₁.coding.injective h
          -- Equality of these projections does not imply equality of supports.
          sorry
        | inr _ => simp at h
      | inr y₁ =>
        cases d₂ with
        | inl _ => simp at h
        | inr y₂ =>
          simp at h
          have hc := D₂.coding.injective h
          sorry
  }

notation:70 D₁ " ◇ " D₂ => WeakProduct D₁ D₂

/-! ## Theory Inclusion

The key property of weak products: the theory of the product
is contained in the intersection of the component theories.
-/

/-- The theory of a weak product is contained in the intersection of theories.

    Th(D₁ ◇ D₂) ⊆ Th(D₁) ∩ Th(D₂)

    This means any equation valid in the weak product is valid in both components.

    Proof sketch (Bucciarelli-Salibra):
    - There are natural embeddings D₁ → D₁ ◇ D₂ and D₂ → D₁ ◇ D₂
    - These embeddings preserve the interpretation of terms
    - If eq is valid in D₁ ◇ D₂, restricting to D₁ (or D₂) gives validity there

    See: Bucciarelli & Salibra, "Graph Lambda Theories" (2008), §3
-/
theorem WeakProduct.theory_inclusion (D₁ D₂ : GraphModel) :
    theoryOf (D₁ ◇ D₂) ⊆ theoryOf D₁ ∩ theoryOf D₂ := by
  sorry

/-! ## Stratified Models

The rank record below is not the source's definition of stratification as a
proper-partial-pair completion. No identification or semisensibility result
for this record is currently established.
-/

/-- A stratification of a web is a function assigning natural number levels. -/
structure Stratification (W : Web) where
  /-- Level function -/
  level : W.carrier → Nat
  /-- Non-degenerate: unbounded levels -/
  unbounded : ∀ n, ∃ x, level x > n

/-- A graph model is stratified if its web has a stratification
    compatible with the coding function.

    The key property is that coding INCREASES levels:
    the result of coding has level strictly greater than all inputs.
    This rank condition is separate from source stratification. -/
structure StratifiedModel where
  /-- The underlying graph model -/
  model : GraphModel
  /-- The stratification of the underlying web -/
  stratification : Stratification model.web
  /-- Coding respects levels: code(a, d) has level > max levels in a -/
  coding_increases_level : ∀ (a : Finset model.web.carrier) (d : model.web.carrier),
    ∀ x ∈ a, stratification.level (model.coding.code (a, d)) > stratification.level x

/-- Unproved semisensibility obligation for the rank record below.
The source's Theorem 29 concerns proper-partial-pair completions; it does not
establish this statement without connecting the definitions.

    The key insight: in a stratified model, solvable and unsolvable terms
    have different "complexity" in terms of level structure, so they
    cannot be identified.

    More precisely:
    - Solvable terms have finite approximations at each level
    - Unsolvable terms have infinite behavior at all levels
    - These cannot be equal in a stratified model

    The proof requires showing that the level structure of a stratified model
    distinguishes between terms based on their computational behavior.

-/
theorem stratified_semisensible (D : StratifiedModel) :
    ∀ T : LambdaTheory, T.equations = theoryOf D.model → T.Semisensible := by
  sorry

/-! ## Summary

The weak-product record and source claims remain unqualified. The projection
helpers are independent of its admitted fields. The lawful partial pair and
collision controls live in `PartialPair` and `WeakProductControls`. The actual
canonical completion, generic factor-flattening primitives, and actual
interpretation comparison are separate qualified constructions.
`FactorInterpretation` proves the existing `graphTheory_inter` lower-bound
statement from the actual completed model, not this projection-only record.
`IndexedPartialPair` supplies nonempty indexed families and their actual
completed-model theory lower bounds. Exact intersection realization and
source stratification remain open.

**Next Steps**:
- Exact intersection realization and source stratification
- Connection to Böhm trees
- Characterization of maximal graph theory (B)
-/

end Mettapedia.GSLT.GraphTheory
