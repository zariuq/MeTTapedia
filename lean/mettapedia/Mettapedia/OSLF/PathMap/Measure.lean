import Mettapedia.OSLF.PathMap.SolomonoffBridge

/-!
# PathMapValuation: K&S-Style Valuations on PathMap Stores

This module defines `PathMapValuation`, a typeclass for **K&S-style real-valued
valuations** on `Finset α` PathMap stores.  A valuation assigns a non-negative
extended-real weight to each store, respecting:

1. **Zero** on the empty store
2. **Disjoint additivity** (the K&S independence axiom)
3. **Monotonicity** (adding observations cannot decrease weight)

## Main definitions

- `PathMapValuation α` — the typeclass
- `countingPathMapValuation` — `weight W = |W|` (cardinality)
- `mkWeightedValuation w` — `weight W = ∑_{p∈W} w p`
- `solomonoffValuation sm` — Solomonoff semimeasure instance

## Main theorems

- `pathMapValuation_evidence_split` — `weight W = ev(W,q).pos + ev(W,q).neg`
- `counting_valuation_eq_evidence_total` — counting valuation = `finsetPathEvidence` total
- `weighted_valuation_eq_evidence_total` — weighted valuation = `weightedPathEvidence` total
-/

namespace Mettapedia.OSLF.PathMap.Measure

open Mettapedia.PathMap
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.OSLF.PathMap.PLNBridge
open Mettapedia.OSLF.PathMap.SolomonoffBridge
open Mettapedia.Logic.SolomonoffPrior
open scoped ENNReal
open Finset BigOperators

/-! ## Section 1: PathMapValuation Typeclass -/

/-- A K&S-style valuation on `Finset α` PathMap stores.

    `weight : Finset α → ℝ≥0∞` satisfies two independent axioms:
    - **Zero** at empty store
    - **Disjoint additivity**: `weight (W₁ ∪ W₂) = weight W₁ + weight W₂` for `W₁ ⊥ W₂`

    **Note on minimality**: monotonicity (`W₁ ⊆ W₂ → weight W₁ ≤ weight W₂`) is *not* an
    independent axiom — it is provable from the two above via the decomposition
    `W₂ = W₁ ∪ (W₂ \ W₁)` (see `pathMapValuation_weight_monotone`).  The typeclass
    is therefore minimal.

    These are exactly the K&S valuation axioms restricted to the discrete PathMap
    setting.  Specialised to `Finset α` to avoid needing `LE` on the abstract
    `PathMapLattice`. -/
class PathMapValuation (α : Type*) [DecidableEq α] where
  weight : Finset α → ℝ≥0∞
  weight_empty : weight ∅ = 0
  weight_additive : ∀ W₁ W₂ : Finset α, Disjoint W₁ W₂ →
    weight (W₁ ∪ W₂) = weight W₁ + weight W₂

/-! ## Section 2: Counting Instance -/

/-- Cardinality valuation: `weight W = |W|`.

    The fundamental uniform K&S valuation on PathMap stores. -/
noncomputable instance countingPathMapValuation {α : Type*} [DecidableEq α] :
    PathMapValuation α where
  weight W := W.card
  weight_empty := by simp
  weight_additive W₁ W₂ h := by exact_mod_cast Finset.card_union_of_disjoint h

/-! ## Section 3: Weighted Instance Constructor -/

/-- Construct a `PathMapValuation` from any weight function `w : α → ℝ≥0∞`.

    `weight W = ∑_{p ∈ W} w p` satisfies all three valuation axioms. -/
noncomputable def mkWeightedValuation {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) : PathMapValuation α where
  weight W := ∑ p ∈ W, w p
  weight_empty := by simp
  weight_additive W₁ W₂ h := Finset.sum_union h

/-! ## Section 4: Connection to BinaryEvidence -/

/-- K&S sum rule for weighted valuations: the weight of a store equals the sum
    of positive and negative evidence for any query.

      `(∑_{p ∈ W} w p) = ev_w(W, q).pos + ev_w(W, q).neg` -/
theorem weighted_valuation_eq_evidence_total {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) (W q : Finset α) :
    (mkWeightedValuation w).weight W =
    (weightedPathEvidence w W q).pos + (weightedPathEvidence w W q).neg :=
  (weightedPathEvidence_total w W q).symm

/-- The counting valuation's weight equals the total `finsetPathEvidence` for any query. -/
theorem counting_valuation_eq_evidence_total {α : Type*} [DecidableEq α]
    (W q : Finset α) :
    (countingPathMapValuation (α := α)).weight W =
    (finsetPathEvidence W q).pos + (finsetPathEvidence W q).neg := by
  exact_mod_cast (finsetPathEvidence_total W q).symm

/-- Any valuation weight equals the total of any compatible weighted evidence. -/
theorem pathMapValuation_evidence_split {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) (W q : Finset α) :
    ∑ p ∈ W, w p =
    (weightedPathEvidence w W q).pos + (weightedPathEvidence w W q).neg :=
  (weightedPathEvidence_total w W q).symm

/-! ## Section 5: Solomonoff Instance -/

/-- The Solomonoff semimeasure gives a `PathMapValuation` on `BinString` stores.

    `weight W = ∑_{p ∈ W} M(p)` — total Solomonoff weight of programs in the store. -/
noncomputable def solomonoffValuation (sm : Semimeasure) : PathMapValuation BinString :=
  mkWeightedValuation (fun p => ENNReal.ofReal (sm.μ p))

/-- The Solomonoff valuation weight equals the Solomonoff evidence total. -/
theorem solomonoffValuation_eq_evidence_total (sm : Semimeasure)
    (W q : Finset BinString) :
    (solomonoffValuation sm).weight W =
    (solomonoffPathEvidence sm W q).pos +
    (solomonoffPathEvidence sm W q).neg :=
  weighted_valuation_eq_evidence_total _ W q

/-! ## Section 6: Derived Monotonicity -/

/-- Monotonicity of the valuation weight: `W₁ ⊆ W₂ → weight W₁ ≤ weight W₂`.

    **This is a theorem, not an axiom.**  It follows from `weight_additive` and the
    identity `W₂ = W₁ ∪ (W₂ \ W₁)` (disjoint decomposition):

      `weight W₂ = weight W₁ + weight (W₂ \ W₁) ≥ weight W₁`

    since all `ℝ≥0∞` summands are non-negative.  This confirms that `PathMapValuation`
    has a minimal two-axiom basis. -/
theorem pathMapValuation_weight_monotone {α : Type*} [DecidableEq α]
    (pv : PathMapValuation α) {W₁ W₂ : Finset α} (h : W₁ ⊆ W₂) :
    pv.weight W₁ ≤ pv.weight W₂ := by
  have hSplit : pv.weight W₂ = pv.weight W₁ + pv.weight (W₂ \ W₁) := by
    have h' := pv.weight_additive W₁ (W₂ \ W₁) disjoint_sdiff_self_right
    rw [Finset.union_sdiff_of_subset h] at h'; exact h'
  rw [hSplit]; exact le_add_right le_rfl

end Mettapedia.OSLF.PathMap.Measure
