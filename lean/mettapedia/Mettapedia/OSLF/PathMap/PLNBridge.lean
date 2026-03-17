import Mettapedia.OSLF.PathMap.Core
import Mettapedia.Logic.EvidenceQuantale
import Mathlib.Data.Finset.Card

/-!
# PathMap ↔ PLN BinaryEvidence Bridge

This module proves the formal connection between PathMap's algebraic operations
(`pjoin`, `pmeet`, `psubtract`, `prestrict` on `Finset α`) and PLN's BinaryEvidence
type (`(n⁺, n⁻) : ℝ≥0∞ × ℝ≥0∞`).

## Core Insight

For a PathMap store `W : Finset α` and a query `q : Finset α`, define:

```
finsetPathEvidence W q = ⟨|W ∩ q|, |W \ q|⟩
```

- `n⁺ = |W ∩ q|` — store paths that match query (positive evidence)
- `n⁻ = |W \ q|` — store paths that do NOT match (negative evidence)
- `n⁺ + n⁻ = |W|` — K&S sum rule: all store paths are classified

This definition (with `n⁻ = |W \ q|` rather than `|q \ W|`) makes BinaryEvidence
additivity hold cleanly for disjoint stores, proving the World-Model Calculus
paper's key claim:

  `ev(W₁ ⊕ W₂, q) = ev(W₁, q) ⊕ ev(W₂, q)` for disjoint W₁, W₂

## K&S Grounding

The function satisfies the Knuth–Skilling valuation axioms on the lattice
`Finset α`:
- Empty store → zero evidence
- Self-query → all positive
- Monotone in store size
- Sum rule: n⁺ + n⁻ = |W|

## Connection to AlgebraicResult

Each PathMap operation corresponds to an BinaryEvidence relationship:
- `pjoin`  (union)        : additive for disjoint stores (independence)
- `pmeet`  (intersection) : sub-infimum (conjunction weakens evidence)
- `prestrict` (prefix-filter) : partition of evidence by context
- `psubtract` (difference): evidence-decreasing (monotone)

## Relationship to `BinaryWorldModel` (PLNWorldModel.lean)

The `BinaryWorldModel` typeclass (`PLNWorldModel.lean`) requires `evidence_add` to hold for
**all** store combinations: `ev(W₁ + W₂, q) = ev(W₁, q) ⊕ ev(W₂, q)`.

`PathMapWorldModel` only requires additivity for **disjoint** stores (`pmeet = .none`).
This is the correct restriction because `Finset α` union (`W₁ ∪ W₂`) is *idempotent*
(`W ∪ W = W`), so it does not form a free additive monoid.  In particular,
`ev(W ∪ W, q) = ev(W, q) ≠ 2 · ev(W, q)` in general — the full `BinaryWorldModel` law fails.

To obtain a true `BinaryWorldModel` instance, replace `Finset α` with `Multiset α` (allowing
duplicates), where `+` is genuine multiset sum and disjoint-union coincides with `+`.
This extension is left for future work.
-/

namespace Mettapedia.OSLF.PathMap.PLNBridge

open Mettapedia.PathMap
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

/-! ## Section 1: BinaryEvidence Extraction -/

/-- Extract PLN BinaryEvidence from a PathMap store `W` for query `q`.

    - `pos = |W ∩ q|` : store paths that match the query
    - `neg = |W \ q|` : store paths that refute the query (in store, not in query)

    The key design choice: `neg = |W \ q|` (not `|q \ W|`) gives `pos + neg = |W|`,
    the K&S sum rule. Strength `= |W∩q|/|W|` is the empirical hit rate. -/
noncomputable def finsetPathEvidence {α : Type*} [DecidableEq α] (W q : Finset α) : BinaryEvidence :=
  ⟨(W ∩ q).card, (W \ q).card⟩

/-! ### Boundary conditions (K&S valuation axioms) -/

@[simp]
theorem finsetPathEvidence_empty_store {α : Type*} [DecidableEq α] (q : Finset α) :
    finsetPathEvidence (∅ : Finset α) q = 0 := by
  simp [finsetPathEvidence]; rfl

@[simp]
theorem finsetPathEvidence_empty_query {α : Type*} [DecidableEq α] (W : Finset α) :
    finsetPathEvidence W (∅ : Finset α) = ⟨0, W.card⟩ := by
  simp [finsetPathEvidence]

@[simp]
theorem finsetPathEvidence_self {α : Type*} [DecidableEq α] (W : Finset α) :
    finsetPathEvidence W W = ⟨W.card, 0⟩ := by
  simp [finsetPathEvidence]

/-! ## Section 2: K&S Valuation Properties -/

/-- K&S sum rule: positive and negative evidence together account for all store paths.
    Discrete analogue of P(q|W) + P(¬q|W) = 1. -/
theorem finsetPathEvidence_total {α : Type*} [DecidableEq α] (W q : Finset α) :
    (finsetPathEvidence W q).pos + (finsetPathEvidence W q).neg = W.card := by
  simp only [finsetPathEvidence]
  exact_mod_cast Finset.card_inter_add_card_sdiff W q

/-- BinaryEvidence extraction is monotone: larger store yields more evidence (coordinatewise).
    K&S valuation axiom: adding observations cannot decrease evidence. -/
theorem finsetPathEvidence_lattice_monotone {α : Type*} [DecidableEq α]
    {W₁ W₂ : Finset α} (h : W₁ ⊆ W₂) (q : Finset α) :
    finsetPathEvidence W₁ q ≤ finsetPathEvidence W₂ q := by
  simp only [finsetPathEvidence, BinaryEvidence.le_def]
  constructor
  · exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right h)
  · exact_mod_cast Finset.card_le_card (Finset.sdiff_subset_sdiff h (le_refl q))

/-! ## Section 3: pjoin Additivity — Main Bridge Theorem -/

/-- For **disjoint** PathMap stores, pjoin (set union) produces additive BinaryEvidence.

    This is the Lean formalization of the World-Model Calculus paper's semantic spine:
      `ev(W₁ ⊕ W₂, q) = ev(W₁, q) ⊕ ev(W₂, q)`
    for independent (disjoint) world-model states W₁ and W₂.

    Proof: both `(W₁∪W₂)∩q = (W₁∩q)∪(W₂∩q)` and `(W₁∪W₂)\q = (W₁\q)∪(W₂\q)`
    are disjoint unions when W₁ ⊥ W₂, so cardinalities add. -/
theorem pjoin_evidence_additive {α : Type*} [DecidableEq α]
    (W₁ W₂ q : Finset α) (hDisj : Disjoint W₁ W₂) :
    finsetPathEvidence (W₁ ∪ W₂) q =
    finsetPathEvidence W₁ q + finsetPathEvidence W₂ q := by
  simp only [finsetPathEvidence, BinaryEvidence.hplus_def, BinaryEvidence.mk.injEq]
  constructor
  · -- pos: |(W₁∪W₂)∩q| = |W₁∩q| + |W₂∩q|
    rw [Finset.union_inter_distrib_right]
    exact_mod_cast Finset.card_union_of_disjoint (hDisj.mono Finset.inter_subset_left Finset.inter_subset_left)
  · -- neg: |(W₁∪W₂)\q| = |W₁\q| + |W₂\q|
    rw [Finset.union_sdiff_distrib]
    exact_mod_cast Finset.card_union_of_disjoint (hDisj.mono Finset.sdiff_subset Finset.sdiff_subset)

/-! ## Section 4: pmeet — Sub-Infimum Theorem -/

/-- pmeet (intersection) gives evidence at most the coordinatewise infimum.

    Conditioning on two stores simultaneously gives evidence no stronger
    than either store alone. This reflects that conjunction is weaker
    than either conjunct in the BinaryEvidence lattice. -/
theorem pmeet_evidence_le_inf {α : Type*} [DecidableEq α]
    (W₁ W₂ q : Finset α) :
    finsetPathEvidence (W₁ ∩ W₂) q ≤
    finsetPathEvidence W₁ q ⊓ finsetPathEvidence W₂ q := by
  apply le_inf
  · exact finsetPathEvidence_lattice_monotone Finset.inter_subset_left q
  · exact finsetPathEvidence_lattice_monotone Finset.inter_subset_right q

/-! ## Section 5: prestrict — Bayesian Conditioning Partition -/

/-- BinaryEvidence from a full store partitions along any context boundary:
      `ev(W, q) = ev(W ∩ ctx, q) + ev(W \ ctx, q)`

    K&S interpretation: restricting to context `ctx` partitions the store into
    within-context paths (`W ∩ ctx`, where prestrict operates) and out-of-context
    paths (`W \ ctx`). Together they account for all evidence.

    This is the discrete version of the K&S law of total probability:
      P(q) = P(q | ctx) · P(ctx) + P(q | ¬ctx) · P(¬ctx)
    expressed as count additivity rather than probability multiplication. -/
theorem prestrict_evidence_partition {α : Type*} [DecidableEq α]
    (W ctx q : Finset α) :
    finsetPathEvidence W q =
    finsetPathEvidence (W ∩ ctx) q + finsetPathEvidence (W \ ctx) q := by
  have hW : W ∩ ctx ∪ W \ ctx = W := by rw [Finset.union_comm, Finset.sdiff_union_inter]
  conv_lhs => rw [← hW]
  exact pjoin_evidence_additive (W ∩ ctx) (W \ ctx) q
    (disjoint_sdiff_self_right.mono_left Finset.inter_subset_right)

/-- When a store is already within context, restricting to context preserves evidence.

    Corresponds to `prestrict W ctx = W` (Identity SELF case) in the AlgebraicResult
    semantics: if `W ⊆ ctx`, then `prestrict W ctx = .identity true false`. -/
theorem prestrict_evidence_identity {α : Type*} [DecidableEq α]
    (W ctx q : Finset α) (h : W ⊆ ctx) :
    finsetPathEvidence (W ∩ ctx) q = finsetPathEvidence W q := by
  rw [Finset.inter_eq_left.mpr h]

/-- prestrict (prefix restriction) is evidence-monotone in the store argument.
    Restricting the store can only decrease evidence. -/
theorem prestrict_evidence_le {α : Type*} [DecidableEq α]
    (W ctx q : Finset α) :
    finsetPathEvidence (W ∩ ctx) q ≤ finsetPathEvidence W q :=
  finsetPathEvidence_lattice_monotone Finset.inter_subset_left q

/-! ## Section 6: psubtract — BinaryEvidence Monotone -/

/-- psubtract (set difference) decreases evidence: removing paths from a store
    can only reduce the evidence it provides. -/
theorem psubtract_evidence_le {α : Type*} [DecidableEq α]
    (W₁ W₂ q : Finset α) :
    finsetPathEvidence (W₁ \ W₂) q ≤ finsetPathEvidence W₁ q :=
  finsetPathEvidence_lattice_monotone Finset.sdiff_subset q

/-! ## Section 7: PathMapWorldModel Typeclass -/

open Mettapedia.PathMap in
/-- A PathMap store `α` with queries `Q` acts as a World-Model when equipped with
    an evidence extraction function satisfying:
    - pjoin of disjoint stores gives additive BinaryEvidence (independence law)

    This mirrors the World-Model Calculus typeclass `BinaryWorldModel.evidence_add`,
    restricted to the disjoint case (which is the PathMap notion of independent
    observations). -/
class PathMapWorldModel (α : Type*) (Q : Type*)
    [PathMapDistributiveLattice α] where
  /-- Extract BinaryEvidence for query q from store W. -/
  extract : α → Q → BinaryEvidence
  /-- pjoin of disjoint stores (pmeet = .none) gives additive evidence. -/
  pjoin_disjoint_additive : ∀ (W₁ W₂ : α) (q : Q),
    PathMapLattice.pmeet W₁ W₂ = .none →
    ∃ union, (PathMapLattice.pjoin W₁ W₂).resolve W₁ W₂ = some union ∧
             extract union q = extract W₁ q + extract W₂ q

/-- `Finset α` PathMap stores form a `PathMapWorldModel` via `finsetPathEvidence`.

    The disjointness condition `pmeet W₁ W₂ = .none` (in the `Finset α` instance,
    this means `W₁ ∩ W₂ = ∅`) directly gives `Disjoint W₁ W₂`, enabling
    `pjoin_evidence_additive`. -/
noncomputable instance {α : Type*} [DecidableEq α] :
    PathMapWorldModel (Finset α) (Finset α) where
  extract := finsetPathEvidence
  pjoin_disjoint_additive W₁ W₂ q hMeetNone := by
    -- Extract disjointness from pmeet = .none
    -- pmeet = .none iff (W₁ ∩ W₂).card = 0 (first branch of the Finset α instance)
    have hDisj : Disjoint W₁ W₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exfalso
      -- x ∈ W₁ ∩ W₂ → card > 0 → first pmeet branch is false → pmeet ≠ .none
      have hcard0 : ¬(W₁ ∩ W₂).card = 0 := by
        have := Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hx1, hx2⟩⟩; omega
      simp only [PathMapLattice.pmeet] at hMeetNone
      rw [if_neg hcard0] at hMeetNone
      split_ifs at hMeetNone
    -- pjoin resolves to W₁ ∪ W₂ in all cases (each subset case degenerates)
    have hResolve : (PathMapLattice.pjoin W₁ W₂ : AlgebraicResult (Finset α)).resolve W₁ W₂ =
        some (W₁ ∪ W₂) := by
      simp only [PathMapLattice.pjoin]
      split_ifs with h₁ h₂ h₃
      · -- h₁ : W₁ = W₂; .identity true true → resolve = some W₁
        show some W₁ = some (W₁ ∪ W₂)
        simp [h₁]
      · -- h₂ : W₁ ⊆ W₂; .identity false true → resolve = some W₂
        show some W₂ = some (W₁ ∪ W₂)
        congr 1; exact (Finset.union_eq_right.mpr h₂).symm
      · -- h₃ : W₂ ⊆ W₁; .identity true false → resolve = some W₁
        show some W₁ = some (W₁ ∪ W₂)
        congr 1; exact (Finset.union_eq_left.mpr h₃).symm
      · rfl  -- .element (W₁ ∪ W₂) → some (W₁ ∪ W₂) directly
    exact ⟨W₁ ∪ W₂, hResolve, pjoin_evidence_additive W₁ W₂ q hDisj⟩

/-! ## Section 8: Connection to PLN STV -/

/-- The PLN strength (truth value) derived from a PathMap store equals
    the empirical hit rate: the fraction of store paths matching the query.

      `strength = |W ∩ q| / |W|`

    This is the Bayesian reading Skilling identified: strength is the
    maximum-likelihood estimate of P(q | W) from evidence counts. -/
theorem finsetPathEvidence_strength {α : Type*} [DecidableEq α] (W q : Finset α)
    (hW : (W.card : ℝ≥0∞) ≠ 0) :
    (finsetPathEvidence W q).toStrength = (W ∩ q).card / W.card := by
  simp only [BinaryEvidence.toStrength, finsetPathEvidence, BinaryEvidence.total]
  have hTotal : ((W ∩ q).card : ℝ≥0∞) + (W \ q).card = W.card := by
    exact_mod_cast Finset.card_inter_add_card_sdiff W q
  rw [if_neg (by rw [hTotal]; exact hW), hTotal]

end Mettapedia.OSLF.PathMap.PLNBridge
