import Mettapedia.OSLF.PathMap.PLNBridge
import Mettapedia.Logic.SolomonoffPrior
import Mathlib.Data.Finset.Basic

/-!
# SolomonoffBridge: Weighted PathMap Evidence

This module generalises `finsetPathEvidence` (uniform counting weights) to
**arbitrary weight functions** `w : α → ℝ≥0∞` and instantiates the result
for the **Solomonoff semimeasure** `sm.μ : BinString → ℝ`.

## Main definitions

- `weightedPathEvidence w W q` — `⟨∑_{p∈W∩q} w p, ∑_{p∈W\q} w p⟩`
- `solomonoffPathEvidence sm W q` — same, with `w p = ENNReal.ofReal (sm.μ p)`
- `weightedPathMapWorldModel w` — `PathMapWorldModel` instance for weighted evidence

## Main theorems

- `weightedPathEvidence_total` — `pos + neg = ∑_{p∈W} w p`  (K&S sum rule)
- `weightedPathEvidence_additive` — disjoint additivity (semantic spine)
- `weightedPathEvidence_partition` — Bayesian conditioning partition
- `finsetPathEvidence_eq_uniform` — uniform weight recovers counting evidence
- `solomonoffPathEvidence_additive` — Solomonoff posterior additivity
- `solomonoffPathEvidence_strength` — strength = Solomonoff hit-rate P(q|W)

## Reference

See `PLNBridge.lean` for the uniform (`Finset.card`) version and the
World-Model Calculus paper for the semantic motivation.
-/

namespace Mettapedia.OSLF.PathMap.SolomonoffBridge

open Mettapedia.PathMap
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.OSLF.PathMap.PLNBridge
open scoped ENNReal
open Finset BigOperators

/-! ## Section 1: Weighted Evidence -/

/-- Extract PLN Evidence from a PathMap store `W` for query `q` using weight `w`.

    - `pos = ∑_{p ∈ W ∩ q} w p`  — total weight of matching store paths
    - `neg = ∑_{p ∈ W \ q} w p`  — total weight of refuting store paths

    Choosing `w = fun _ => 1` recovers `finsetPathEvidence` (uniform counting).
    Choosing `w = ENNReal.ofReal ∘ sm.μ` yields the Solomonoff posterior. -/
noncomputable def weightedPathEvidence {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) (W q : Finset α) : Evidence :=
  ⟨∑ p ∈ W ∩ q, w p, ∑ p ∈ W \ q, w p⟩

/-! ### Boundary conditions -/

@[simp]
theorem weightedPathEvidence_empty_store {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) (q : Finset α) :
    weightedPathEvidence w (∅ : Finset α) q = 0 := by
  simp [weightedPathEvidence]; rfl

@[simp]
theorem weightedPathEvidence_empty_query {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) (W : Finset α) :
    weightedPathEvidence w W (∅ : Finset α) = ⟨0, ∑ p ∈ W, w p⟩ := by
  simp [weightedPathEvidence]

@[simp]
theorem weightedPathEvidence_self {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) (W : Finset α) :
    weightedPathEvidence w W W = ⟨∑ p ∈ W, w p, 0⟩ := by
  simp [weightedPathEvidence]

/-! ### K&S sum rule -/

/-- K&S sum rule for weighted evidence: positive and negative weights together
    account for all store weight.  Discrete analogue of P(q|W) + P(¬q|W) = 1. -/
theorem weightedPathEvidence_total {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) (W q : Finset α) :
    (weightedPathEvidence w W q).pos + (weightedPathEvidence w W q).neg =
    ∑ p ∈ W, w p := by
  simp only [weightedPathEvidence]
  rw [← Finset.sum_union (disjoint_sdiff_self_right.mono_left inter_subset_right)]
  congr 1
  rw [Finset.union_comm, Finset.sdiff_union_inter]

/-! ### Monotonicity -/

/-- Weighted evidence is monotone in the store: larger store → more evidence. -/
theorem weightedPathEvidence_monotone {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) {W₁ W₂ : Finset α} (h : W₁ ⊆ W₂) (q : Finset α) :
    weightedPathEvidence w W₁ q ≤ weightedPathEvidence w W₂ q := by
  simp only [weightedPathEvidence, Evidence.le_def]
  constructor
  · apply Finset.sum_le_sum_of_subset
    exact Finset.inter_subset_inter_right h
  · apply Finset.sum_le_sum_of_subset
    exact Finset.sdiff_subset_sdiff h (le_refl q)

/-! ## Section 2: Main Bridge Theorems -/

/-- For **disjoint** stores, weighted pjoin (union) gives additive Evidence.

    Weighted generalisation of `pjoin_evidence_additive`:
      `ev_w(W₁ ∪ W₂, q) = ev_w(W₁, q) ⊕ ev_w(W₂, q)` for W₁ ⊥ W₂.

    Proof uses `Finset.sum_union` for both intersection and sdiff components,
    exploiting that disjointness of W₁, W₂ implies disjointness of the
    derived families `W₁∩q` & `W₂∩q` and `W₁\q` & `W₂\q`. -/
theorem weightedPathEvidence_additive {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) (W₁ W₂ q : Finset α) (hDisj : Disjoint W₁ W₂) :
    weightedPathEvidence w (W₁ ∪ W₂) q =
    weightedPathEvidence w W₁ q + weightedPathEvidence w W₂ q := by
  simp only [weightedPathEvidence, Evidence.hplus_def, Evidence.mk.injEq]
  constructor
  · rw [Finset.union_inter_distrib_right]
    exact Finset.sum_union (hDisj.mono inter_subset_left inter_subset_left)
  · rw [Finset.union_sdiff_distrib]
    exact Finset.sum_union (hDisj.mono sdiff_subset sdiff_subset)

/-- Weighted evidence partitions along any context boundary:
      `ev_w(W, q) = ev_w(W ∩ ctx, q) + ev_w(W \ ctx, q)` -/
theorem weightedPathEvidence_partition {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) (W ctx q : Finset α) :
    weightedPathEvidence w W q =
    weightedPathEvidence w (W ∩ ctx) q + weightedPathEvidence w (W \ ctx) q := by
  have hW : W ∩ ctx ∪ W \ ctx = W := by rw [Finset.union_comm, Finset.sdiff_union_inter]
  conv_lhs => rw [← hW]
  exact weightedPathEvidence_additive w (W ∩ ctx) (W \ ctx) q
    (disjoint_sdiff_self_right.mono_left inter_subset_right)

/-! ## Section 3: Uniform Weight = Counting Evidence -/

/-- Setting `w = fun _ => 1` recovers the uniform counting evidence of `PLNBridge`. -/
theorem finsetPathEvidence_eq_uniform {α : Type*} [DecidableEq α] (W q : Finset α) :
    (finsetPathEvidence W q : Evidence) =
    weightedPathEvidence (fun _ => (1 : ℝ≥0∞)) W q := by
  simp only [finsetPathEvidence, weightedPathEvidence, Evidence.mk.injEq]
  exact ⟨by exact_mod_cast Finset.card_eq_sum_ones _,
         by exact_mod_cast Finset.card_eq_sum_ones _⟩

/-! ## Section 4: Solomonoff Evidence -/

open Mettapedia.Logic.SolomonoffPrior

/-- Evidence from a PathMap store weighted by Solomonoff semimeasure `sm`.

    - `pos = ∑_{p ∈ W ∩ q} M(p)` — Solomonoff weight of matching programs
    - `neg = ∑_{p ∈ W \ q} M(p)` — Solomonoff weight of refuting programs

    The weight function `ENNReal.ofReal (sm.μ p)` is well-defined since
    `sm.nonneg p : 0 ≤ sm.μ p` ensures non-negativity. -/
noncomputable def solomonoffPathEvidence (sm : Semimeasure)
    (W q : Finset BinString) : Evidence :=
  weightedPathEvidence (fun p => ENNReal.ofReal (sm.μ p)) W q

/-- K&S sum rule for Solomonoff evidence. -/
theorem solomonoffPathEvidence_total (sm : Semimeasure)
    (W q : Finset BinString) :
    (solomonoffPathEvidence sm W q).pos +
    (solomonoffPathEvidence sm W q).neg =
    ∑ p ∈ W, ENNReal.ofReal (sm.μ p) :=
  weightedPathEvidence_total _ W q

/-- Solomonoff evidence is disjointly additive (semantic spine for Solomonoff weights).

    `ev_M(W₁ ∪ W₂, q) = ev_M(W₁, q) ⊕ ev_M(W₂, q)` for disjoint stores. -/
theorem solomonoffPathEvidence_additive (sm : Semimeasure)
    (W₁ W₂ q : Finset BinString) (hDisj : Disjoint W₁ W₂) :
    solomonoffPathEvidence sm (W₁ ∪ W₂) q =
    solomonoffPathEvidence sm W₁ q + solomonoffPathEvidence sm W₂ q :=
  weightedPathEvidence_additive _ W₁ W₂ q hDisj

/-- Solomonoff evidence partitions along any context boundary. -/
theorem solomonoffPathEvidence_partition (sm : Semimeasure)
    (W ctx q : Finset BinString) :
    solomonoffPathEvidence sm W q =
    solomonoffPathEvidence sm (W ∩ ctx) q +
    solomonoffPathEvidence sm (W \ ctx) q :=
  weightedPathEvidence_partition _ W ctx q

/-- The PLN strength derived from Solomonoff evidence equals the empirical Solomonoff
    posterior hit-rate:

      `strength = (∑_{p ∈ W ∩ q} M(p)) / (∑_{p ∈ W} M(p))`

    This is the Bayesian estimate P(q | W) under the Solomonoff prior. -/
theorem solomonoffPathEvidence_strength (sm : Semimeasure)
    (W q : Finset BinString)
    (hW : ∑ p ∈ W, ENNReal.ofReal (sm.μ p) ≠ 0) :
    (solomonoffPathEvidence sm W q).toStrength =
    (∑ p ∈ W ∩ q, ENNReal.ofReal (sm.μ p)) /
    (∑ p ∈ W, ENNReal.ofReal (sm.μ p)) := by
  simp only [Evidence.toStrength, solomonoffPathEvidence, weightedPathEvidence,
             Evidence.total]
  -- Connect the unfolded sum (pos + neg) back to W-sum via weightedPathEvidence_total
  have hTotal : ∑ x ∈ W ∩ q, ENNReal.ofReal (sm.μ x) +
      ∑ x ∈ W \ q, ENNReal.ofReal (sm.μ x) =
      ∑ p ∈ W, ENNReal.ofReal (sm.μ p) := by
    have := weightedPathEvidence_total (fun p => ENNReal.ofReal (sm.μ p)) W q
    simp only [weightedPathEvidence] at this
    exact this
  rw [if_neg (by rw [hTotal]; exact hW), hTotal]

/-! ## Section 5: Weighted PathMapWorldModel Instance -/

/-- Any weight function `w : α → ℝ≥0∞` makes `Finset α` a `PathMapWorldModel`.

    **Note on `def` vs `instance`**: This is a `def`, not an `instance`, because `w`
    is a free parameter that Lean cannot infer from the types alone — there is no
    canonical weight function for `Finset α`.  The uniform case (`w = fun _ => 1`) is
    the canonical instance and is registered in `PLNBridge` via
    `instance {α} [DecidableEq α] : PathMapWorldModel (Finset α) (Finset α)`.
    To use a specific weight, call `weightedPathMapWorldModel w` explicitly
    (e.g. `haveI := weightedPathMapWorldModel w`). -/
noncomputable def weightedPathMapWorldModel {α : Type*} [DecidableEq α]
    (w : α → ℝ≥0∞) : PathMapWorldModel (Finset α) (Finset α) where
  extract W q := weightedPathEvidence w W q
  pjoin_disjoint_additive W₁ W₂ q hMeetNone := by
    -- Extract disjointness from pmeet = .none (same structure as PLNBridge)
    have hDisj : Disjoint W₁ W₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2; exfalso
      have hcard0 : ¬(W₁ ∩ W₂).card = 0 := by
        have := Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hx1, hx2⟩⟩; omega
      simp only [PathMapLattice.pmeet] at hMeetNone
      rw [if_neg hcard0] at hMeetNone
      split_ifs at hMeetNone
    have hResolve : (PathMapLattice.pjoin W₁ W₂ : AlgebraicResult (Finset α)).resolve W₁ W₂ =
        some (W₁ ∪ W₂) := by
      simp only [PathMapLattice.pjoin]
      split_ifs with h₁ h₂ h₃
      · show some W₁ = some (W₁ ∪ W₂); simp [h₁]
      · show some W₂ = some (W₁ ∪ W₂); congr 1; exact (Finset.union_eq_right.mpr h₂).symm
      · show some W₁ = some (W₁ ∪ W₂); congr 1; exact (Finset.union_eq_left.mpr h₃).symm
      · rfl
    exact ⟨W₁ ∪ W₂, hResolve, weightedPathEvidence_additive w W₁ W₂ q hDisj⟩

end Mettapedia.OSLF.PathMap.SolomonoffBridge
