-- FourColor/Kempe/Guardrails.lean
-- Canonical theorems about when Kempe swaps free colors
--
-- This module contains:
-- 1. The precise iff theorem for color-freeing (frees_α_at_v_iff)
-- 2. A counterexample showing the naive claim "swap always frees α" is FALSE
-- 3. Helper lemmas for working with kempeSwitch
--
-- These are guardrails to prevent regressions back to incorrect simplifications.

import FourColor.Tait
import FourColor.Kempe.Vertex

namespace FourColor.Kempe.Guardrails

open Relation
open FourColor.VertexKempe

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Helper Lemmas for kempeSwitch -/

/-- Vertices outside the Kempe chain are unchanged by swap. -/
lemma swap_outside (color : V → VertexColor) (K : Set V) (α β : VertexColor)
    (w : V) (hw : w ∉ K) :
    kempeSwitch color K α β w = color w := by
  simp [kempeSwitch, hw]

/-- Vertices in the chain colored α become β after swap. -/
lemma swap_inside_α (color : V → VertexColor) (K : Set V) (α β : VertexColor)
    (w : V) (hwK : w ∈ K) (hα : color w = α) :
    kempeSwitch color K α β w = β := by
  simp [kempeSwitch, hwK, hα]

/-- Vertices in the chain colored β become α after swap. -/
lemma swap_inside_β (color : V → VertexColor) (K : Set V) (α β : VertexColor)
    (w : V) (hwK : w ∈ K) (hβ : color w = β) :
    kempeSwitch color K α β w = α := by
  simp [kempeSwitch, hwK, hβ]

/-- Vertices in an αβ-Kempe chain are colored either α or β. -/
lemma color_mem_αβ_of_in_K (adj : V → V → Prop) (color : V → VertexColor)
    (α β w₁ w : V)
    (hwK : w ∈ VertexKempeChain adj color α β w₁)
    (hbase : color w₁ = α ∨ color w₁ = β) :
    color w = α ∨ color w = β :=
  kempe_chain_colors adj color α β w₁ w hbase hwK

/-! ### The Canonical Iff Theorem -/

/-- **CANONICAL THEOREM**: Swapping on the αβ-component from `w₁` frees α at `v`
    if and only if:
    - (i) all α-neighbors of `v` lie in that component, AND
    - (ii) no β-neighbor of `v` lies in that component.

    This is the precise graph-theoretic characterization of Kempe color-freeing.
    It works for ANY graph (no planarity or degree assumptions needed).

    **IMPORTANT**: The naive claim "swapping always frees α" is FALSE.
    See the counterexample below for a formal proof. -/
theorem frees_α_at_v_iff
    (adj : V → V → Prop) (color : V → VertexColor)
    (v w₁ : V) (α β : VertexColor)
    (hw₁_color : color w₁ = α ∨ color w₁ = β) :
    let K := VertexKempeChain adj color α β w₁
    let color' := kempeSwitch color K α β
    ((∀ w, adj v w → color' w ≠ α)
     ↔
     ((∀ w, adj v w → color w = α → w ∈ K)     -- all α-neighbors flip off α
      ∧
      (∀ w, adj v w → color w = β → w ∉ K)))   -- no β-neighbor flips to α
    := by
  classical
  intro K color'
  constructor
  · -- (→) If α is absent after swap, deduce the two side conditions
    intro h
    constructor
    · -- (i) All α-neighbors must be in K
      intro w hv hαw
      -- If w were outside K, it would stay α after swap
      by_contra hw_notK
      have : color' w = α := by
        simp [color', kempeSwitch, hw_notK, hαw]
      exact h w hv this
    · -- (ii) No β-neighbor is in K
      intro w hv hβw hwK
      -- If a β-neighbor is in K, it becomes α after swap
      have : color' w = α := by
        simp [color', kempeSwitch, hwK, hβw]
      exact h w hv this
  · -- (←) Use the two side conditions to show α is absent after swap
    rintro ⟨hαall, hβnone⟩ w hv
    by_cases hwK : w ∈ K
    · -- Case 1: w ∈ K
      -- Vertices in K have color α or β
      have hαβ : color w = α ∨ color w = β := by
        apply color_mem_αβ_of_in_K adj color α β w₁ w hwK hw₁_color
      cases hαβ with
      | inl hα =>
        -- If w has α and is in K, it becomes β
        intro h'
        have : color' w = β := by
          simp [color', kempeSwitch, hwK, hα]
        rw [this] at h'
        cases h'
      | inr hβ =>
        -- If w has β and is in K, this contradicts hβnone
        exact False.elim (hβnone w hv hβ hwK)
    · -- Case 2: w ∉ K
      -- Outside K means color unchanged
      intro h'
      have hαw : color w = α := by
        simp [color', kempeSwitch, hwK] at h'
        exact h'
      -- But then hαall says w must be in K
      have : w ∈ K := hαall w hv hαw
      exact (hwK this).elim

/-! ### General Failure Lemma

The naive claim "swapping on (α,β) chain K from w₁ always frees α" is FALSE.
This is the reusable API lemma showing the failure mechanism.
-/

/-- **Kempe swap does NOT always free α**: If v has two α-neighbors w₁ and w₃,
    where w₁ ∈ K (the αβ-Kempe chain) but w₃ ∉ K, then after swapping on K,
    w₃ remains α, hence α is NOT freed at v.

    This is the minimal obstruction to the naive claim. No planarity or degree
    assumptions needed - it's a pure property of component-wise Kempe swaps. -/
lemma kempeSwap_does_not_free_if_other_alpha_outside
    (adj : V → V → Prop) (coloring : V → VertexColor)
    (K : Set V) (α β : VertexColor) (v w₁ w₃ : V)
    (hadj₁ : adj v w₁) (hadj₃ : adj v w₃)
    (hα₁ : coloring w₁ = α) (hα₃ : coloring w₃ = α)
    (hK₁ : w₁ ∈ K) (hK₃ : w₃ ∉ K) :
    let coloring' := kempeSwitch coloring K α β
    coloring' w₃ = α := by
  -- The swap doesn't touch w₃ (not in K), so its color remains α
  simp [kempeSwitch, hK₃, hα₃]

/-! ### Guardrails / Counterexamples -/

section Counterexample

/-- The naive claim fails on this star graph.
    These are not used by the main proof, but protect against regressions. -/

-- Construct a small star graph with specific coloring
inductive CounterVertex : Type
  | v : CounterVertex      -- center vertex
  | w₁ : CounterVertex     -- neighbor colored α
  | w₂ : CounterVertex     -- neighbor colored β
  | w₃ : CounterVertex     -- neighbor colored α (NOT in chain!)
  | w₄ : CounterVertex     -- neighbor colored γ
  deriving DecidableEq, Fintype

open CounterVertex

-- Define adjacency: v is adjacent to all four neighbors
def counter_adj : CounterVertex → CounterVertex → Prop
  | v, w₁ => True
  | w₁, v => True
  | v, w₂ => True
  | w₂, v => True
  | v, w₃ => True
  | w₃, v => True
  | v, w₄ => True
  | w₄, v => True
  | _, _ => False

-- FIXED coloring: v ∉ {α,β}; also make the star proper
def counter_coloring : CounterVertex → VertexColor
  | v   => VertexColor.green     -- center NOT in {red, blue}
  | w₁  => VertexColor.red
  | w₂  => VertexColor.blue
  | w₃  => VertexColor.red
  | w₄  => VertexColor.yellow    -- avoid same color as v

-- The Kempe chain from w₁ using red-blue
def K : Set CounterVertex :=
  VertexKempeChain counter_adj counter_coloring
    VertexColor.red VertexColor.blue w₁

-- Key lemma: with v=green, there is NO αβ-edge in the star,
-- so w₃ is not reachable from w₁ in the αβ-subgraph.
lemma w₃_not_in_K : w₃ ∉ K := by
  -- K-membership: ReflTransGen of twoColorSubgraph (red/blue) from w₁ to w₃
  unfold K VertexKempeChain
  -- Goal: ¬ ReflTransGen R w₁ w₃
  intro h
  -- twoColor edges must go through v in this star, but v ∉ {red, blue}
  -- so R has no edges at all
  -- Induct on the path proof:
  induction h with
  | @refl =>
    -- base case would force w₁ = w₃ (not true)
    have : w₁ ≠ w₃ := by decide
    exact this rfl
  | @tail u _ h₁ h_step ih =>
    -- show the final step R u w₃ is impossible by computation
    -- (every possible (u,w₃) adjacency uses v; but v is green)
    simpa [twoColorSubgraph, counter_adj, counter_coloring] using h_step

-- Apply Kempe swap
def swapped_coloring : CounterVertex → VertexColor :=
  kempeSwitch counter_coloring K VertexColor.red VertexColor.blue

-- After swap, w₃ is untouched; still red
theorem w₃_still_red_after_swap :
    swapped_coloring w₃ = VertexColor.red := by
  unfold swapped_coloring kempeSwitch
  -- off the chain ⇒ unchanged
  simp [w₃_not_in_K]

-- Therefore α is not free at v
theorem red_not_free_after_swap :
    ∃ w, counter_adj v w ∧ swapped_coloring w = VertexColor.red := by
  refine ⟨w₃, ?_, w₃_still_red_after_swap⟩
  -- (v,w₃) are adjacent in the star
  simpa [counter_adj]

/-- **COUNTEREXAMPLE**: The naive claim "swapping always frees α" is FALSE.
    This formal proof shows that swapping on the αβ-chain from an α-neighbor
    does NOT always free color α at the center vertex. -/
theorem naive_kempe_claim_is_false :
    ¬(∀ (adj : CounterVertex → CounterVertex → Prop)
       (coloring : CounterVertex → VertexColor)
       (v w₁ : CounterVertex)
       (α β : VertexColor),
      let K := VertexKempeChain adj coloring α β w₁
      let coloring' := kempeSwitch coloring K α β
      (∀ w, adj v w → coloring' w ≠ α)) := by
  intro h
  -- Apply h to our counterexample
  have := h counter_adj counter_coloring v w₁
    VertexColor.red VertexColor.blue
  -- This says all neighbors have color ≠ red after swap
  -- But we proved w₃ still has red
  have : swapped_coloring w₃ ≠ VertexColor.red :=
    this w₃ (by unfold counter_adj; trivial)
  -- Contradiction with w₃_still_red_after_swap
  exact this w₃_still_red_after_swap

end Counterexample

end FourColor.Kempe.Guardrails
