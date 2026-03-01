/-
# Bridge: Bool Checker → Mathlib's SimpleGraph

Connects the `hasIndepSet` computation to Mathlib's `SimpleGraph`,
`NoKIndepSet`, and `TriangleFree`.

The algorithm and structural decomposition lemmas live in the `algorithms` package
(`Algorithms.Graph.IndepSetFunc`, `Algorithms.Graph.IndepSetChecker`).
This file provides:
- `hasIndepSetAux_complete`: the Finset-based completeness theorem (needs Mathlib)
- Bridge theorems connecting Bool results to Mathlib's SimpleGraph types

## LLM Notes
- `decide` proofs on closed `∀`-statements work; open `(v w : Fin n) : ... := by decide` fails.
- `adj17Bool_spec` / `adj17NotBool_spec` use the closed form.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Ramsey36.RamseyDef
import Algorithms.Graph.IndepSetChecker

open SimpleGraph Finset

/-! ## Completeness Theorem -/

/-- If a valid independent set exists, the backtracking search finds it. -/
theorem hasIndepSetAux_complete
    {n : ℕ} {adj : Fin n → Fin n → Bool}
    {remaining start : ℕ} {chosen : List (Fin n)}
    {fuel : ℕ} {s : Finset (Fin n)}
    (h_fuel : n ≤ start + fuel)
    (h_card : s.card = remaining)
    (h_ge : ∀ v ∈ s, start ≤ v.val)
    (h_indep : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → adj v w = false)
    (h_compat : ∀ v ∈ s, ∀ w ∈ chosen, adj v w = false) :
    hasIndepSetAux n adj remaining start chosen fuel = true := by
  induction fuel generalizing remaining start chosen s with
  | zero =>
    simp only [hasIndepSetAux]
    suffices remaining = 0 by simp [this]
    by_contra h_rem
    have ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
    exact absurd v.isLt (Nat.not_lt.mpr (by have := h_ge v hv; omega))
  | succ fuel ih =>
    simp only [hasIndepSetAux]
    by_cases h_rem : remaining = 0
    · simp [h_rem]
    · simp only [h_rem, ↓reduceIte]
      by_cases h_start : start < n
      · rw [dif_pos h_start]
        have h_pig : ¬(n - start < remaining) := by
          intro h_lt
          have h_inj : Function.Injective (fun v : s => (⟨v.1.val - start,
            by have := h_ge v.1 v.2; have := v.1.isLt; omega⟩ : Fin (n - start))) := by
            intro a b h_eq
            have ha_ge := h_ge a.1 a.2
            have hb_ge := h_ge b.1 b.2
            have : a.1.val - start = b.1.val - start := congrArg Fin.val h_eq
            have : a.1.val = b.1.val := by omega
            exact Subtype.ext (Fin.ext this)
          have := Fintype.card_le_of_injective _ h_inj
          simp [Fintype.card_coe, Fintype.card_fin] at this
          omega
        simp only [h_pig, ↓reduceIte]
        let v : Fin n := ⟨start, h_start⟩
        by_cases h_in : v ∈ s
        · have h_cv : (chosen.all fun w => !adj ⟨start, h_start⟩ w) = true := by
            rw [List.all_eq_true]; intro w hw
            simp only [Bool.not_eq_true']; exact h_compat v h_in w hw
          simp only [h_cv, ↓reduceIte]
          have h_inc := ih (s := s.erase v) (start := start + 1) (remaining := remaining - 1)
            (h_fuel := by omega)
            (h_card := by rw [Finset.card_erase_of_mem h_in, h_card])
            (h_ge := by
              intro u hu; rw [Finset.mem_erase] at hu
              have := h_ge u hu.2
              have : u.val ≠ start := fun h_eq => hu.1 (Fin.ext h_eq)
              omega)
            (h_indep := by
              intro u hu w hw huv
              rw [Finset.mem_erase] at hu hw
              exact h_indep u hu.2 w hw.2 huv)
            (h_compat := by
              intro u hu w hw; rw [Finset.mem_erase] at hu
              rcases List.mem_cons.mp hw with rfl | hw'
              · exact h_indep u hu.2 v h_in hu.1
              · exact h_compat u hu.2 w hw')
          suffices hasIndepSetAux n adj (remaining - 1) (start + 1) (⟨start, h_start⟩ :: chosen) fuel = true by
            simp [this]
          exact h_inc
        · have h_ge' : ∀ u ∈ s, start + 1 ≤ u.val := by
            intro u hu; have := h_ge u hu
            have : u.val ≠ start := fun h_eq => h_in ((Fin.ext h_eq : u = v) ▸ hu)
            omega
          have h_skip := ih (s := s) (start := start + 1) (h_fuel := by omega) h_card h_ge' h_indep h_compat
          split <;> simp [h_skip]
      · rw [dif_neg h_start]; push_neg at h_start; exfalso
        have : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
          fun u hu => absurd u.isLt (Nat.not_lt.mpr (by have := h_ge u hu; omega))
        rw [this, Finset.card_empty] at h_card; omega

/-! ## Bridge to SimpleGraph.IndepSetFree -/

/-- If the checker says no k-independent set, then `G.IndepSetFree k`. -/
private theorem indepSetFree_of_hasIndepSet_false
    {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h : hasIndepSet n (fun v w => decide (G.Adj v w)) k = false) :
    G.IndepSetFree k := by
  intro t ht
  have h_indep := ht.isIndepSet
  have h_card := ht.card_eq
  have h_bool : ∀ v ∈ t, ∀ w ∈ t, v ≠ w → decide (G.Adj v w) = false :=
    fun v hv w hw hne => decide_eq_false_iff_not.mpr
      (h_indep (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw) hne)
  have h_true : hasIndepSetAux n (fun v w => decide (G.Adj v w)) k 0 [] (n + 1) = true :=
    hasIndepSetAux_complete (fuel := n + 1) (by omega) h_card
      (fun _ _ => Nat.zero_le _) h_bool (by intro _ _ _ hw; simp at hw)
  simp only [hasIndepSet] at h; rw [h_true] at h; simp at h

/-- Convenience wrapper. Usage: `noKIndepSet_of_checker_false (by decide)` -/
theorem noKIndepSet_of_checker_false
    {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h : hasIndepSet n (fun v w => decide (G.Adj v w)) k = false) :
    NoKIndepSet k G :=
  indepSetFree_of_hasIndepSet_false h

/-! ## Bridge to CliqueFree / TriangleFree

A k-clique in G is a k-independent set in the complement adjacency
`fun v w => !decide (G.Adj v w)`. So `hasIndepSet n adjNot k = false`
proves `CliqueFree k G`. -/

/-- If the complement checker says no k-independent set, then `G.CliqueFree k`. -/
theorem cliqueFree_of_checker_false
    {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h : hasIndepSet n (fun v w => !decide (G.Adj v w)) k = false) :
    G.CliqueFree k := by
  intro s ⟨h_clique, h_card⟩
  have h_bool : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → (!decide (G.Adj v w)) = false := by
    intro v hv w hw hne
    simp only [Bool.not_eq_false']
    exact decide_eq_true_eq.mpr
      (h_clique (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw) hne)
  have h_true : hasIndepSetAux n (fun v w => !decide (G.Adj v w)) k 0 [] (n + 1) = true :=
    hasIndepSetAux_complete (fuel := n + 1) (by omega) h_card
      (fun _ _ => Nat.zero_le _) h_bool (by intro _ _ _ hw; simp at hw)
  simp only [hasIndepSet] at h; rw [h_true] at h; simp at h

/-- Triangle-free via complement checker. -/
theorem triangleFree_of_checker_false
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h : hasIndepSet n (fun v w => !decide (G.Adj v w)) 3 = false) :
    TriangleFree G :=
  cliqueFree_of_checker_false h

/-- Version that accepts any `adj` extensionally equal to `decide (G.Adj · ·)`. -/
theorem noKIndepSet_of_adj_checker_false
    {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {adj : Fin n → Fin n → Bool}
    (hadj : ∀ v w : Fin n, adj v w = decide (G.Adj v w))
    (h : hasIndepSet n adj k = false) :
    NoKIndepSet k G := by
  apply noKIndepSet_of_checker_false
  have heq : adj = fun v w => decide (G.Adj v w) :=
    funext (fun v => funext (fun w => hadj v w))
  rwa [← heq]

/-- Version that accepts any `adjNot` extensionally equal to `!decide (G.Adj · ·)`. -/
theorem triangleFree_of_adj_checker_false
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {adjNot : Fin n → Fin n → Bool}
    (hadj : ∀ v w : Fin n, adjNot v w = !decide (G.Adj v w))
    (h : hasIndepSet n adjNot 3 = false) :
    TriangleFree G := by
  apply triangleFree_of_checker_false
  have heq : adjNot = fun v w => !decide (G.Adj v w) :=
    funext (fun v => funext (fun w => hadj v w))
  rwa [← heq]
