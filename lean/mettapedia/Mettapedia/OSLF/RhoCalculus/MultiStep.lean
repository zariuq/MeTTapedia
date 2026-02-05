import Mettapedia.OSLF.RhoCalculus.Reduction

/-!
# Multi-Step Reduction for ρ-Calculus

Defines reflexive-transitive closure and n-step reduction for the ρ-calculus.
This is the foundation for the spice calculus (n-step lookahead).

## Main Definitions

* `ReducesStar` - Reflexive-transitive closure of `Reduces`
* `ReducesN n` - Exactly n reduction steps
* `reducesN_zero_iff_eq` - n=0 gives reflexivity
* `reducesN_to_star` - n-step implies star closure

## References

- Meredith & Radestock (2005): "A Reflective Higher-Order Calculus"
- Meredith (2026): "How the Agents Got Their Present Moment"
-/

namespace Mettapedia.OSLF.RhoCalculus

open Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Reflexive-transitive closure of reduction.
    `p ⇝* q` means p reduces to q in zero or more steps.

    Type-valued (like Reduces) to enable extraction of reduction sequences.
-/
inductive ReducesStar : Pattern → Pattern → Type where
  | refl (p : Pattern) : ReducesStar p p
  | step {p q r : Pattern} : Reduces p q → ReducesStar q r → ReducesStar p r

notation:20 p " ⇝* " q => ReducesStar p q

namespace ReducesStar

/-- Star closure is transitive (def since returns Type-valued data) -/
noncomputable def trans {p q r : Pattern} (h1 : p ⇝* q) (h2 : q ⇝* r) : p ⇝* r := by
  induction h1 with
  | refl => exact h2
  | step h_pq _ ih => exact step h_pq (ih h2)

/-- Single step gives star closure (def since returns Type-valued data) -/
def single {p q : Pattern} (h : Reduces p q) : p ⇝* q :=
  step h (refl q)

end ReducesStar

/-- n-step reduction.
    `p ⇝[n] q` means p reduces to q in exactly n steps.

    Type-valued to enable counting reduction steps computationally.
-/
inductive ReducesN : ℕ → Pattern → Pattern → Type where
  | zero (p : Pattern) : ReducesN 0 p p
  | succ {n : ℕ} {p q r : Pattern} : Reduces p q → ReducesN n q r → ReducesN (n+1) p r

notation:20 p " ⇝[" n "]" q => ReducesN n p q

namespace ReducesN

/-- n=0 gives reflexivity -/
theorem zero_iff_eq (p q : Pattern) :
    Nonempty (p ⇝[0] q) ↔ (p = q) := by
  constructor
  · intro ⟨h⟩; cases h; rfl
  · intro h; rw [h]; exact ⟨zero q⟩

/-- 1-step equals single reduction -/
theorem one_iff_reduces (p q : Pattern) :
    Nonempty (p ⇝[1] q) ↔ Nonempty (Reduces p q) := by
  constructor
  · intro ⟨h⟩
    cases h with
    | succ h_red h_zero =>
      cases h_zero
      exact ⟨h_red⟩
  · intro ⟨h⟩
    exact ⟨succ h (zero q)⟩

end ReducesN

/-- Star closure includes n-step for all n (def since returns Type-valued data) -/
noncomputable def reducesN_to_star {n : ℕ} {p q : Pattern} (h : p ⇝[n] q) :
    p ⇝* q := by
  induction h with
  | zero => exact ReducesStar.refl _
  | succ h_step _ ih => exact ReducesStar.step h_step ih

/-- If p reduces to q in some number of steps, it reduces via star -/
noncomputable def star_of_reducesN_exists (p q : Pattern) :
    (Σ n, p ⇝[n] q) → (p ⇝* q) := by
  intro ⟨n, h⟩
  exact reducesN_to_star h

/-- Concatenation of n-step reductions (def since returns Type-valued data) -/
noncomputable def reducesN_concat {n m : ℕ} {p q r : Pattern}
    (h1 : p ⇝[n] q) (h2 : q ⇝[m] r) : p ⇝[n + m] r := by
  induction h1 generalizing r with
  | zero =>
      -- Goal: p ⇝[0 + m] r, have: p ⇝[m] r
      convert h2
      simp
  | @succ k p' q' _ h_step h_rest ih =>
      -- Goal: p' ⇝[(k + 1) + m] r
      -- Apply succ to get: p' ⇝[(k + m) + 1] r
      -- Then convert (k + m) + 1 to (k + 1) + m
      show p' ⇝[(k + 1) + m] r
      have step_km : q' ⇝[k + m] r := ih h2
      rw [Nat.add_right_comm k 1 m]
      exact ReducesN.succ h_step step_km

/-- Transitivity of star closure (alternative proof) -/
noncomputable def reducesN_trans_via_concat {p q r : Pattern}
    (h1 : Σ n, p ⇝[n] q) (h2 : Σ m, q ⇝[m] r) :
    Σ k, p ⇝[k] r := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, reducesN_concat hn hm⟩

/-- Decomposition: n+1 step reduction = 1 step + n steps -/
theorem reducesN_succ_iff {n : ℕ} {p r : Pattern} :
    Nonempty (p ⇝[n + 1] r) ↔ Nonempty (Σ q, (p ⇝[1] q) × (q ⇝[n] r)) := by
  constructor
  · -- Forward: decompose n+1 step into 1 + n
    intro ⟨h⟩  -- Unwrap Nonempty (LHS)
    constructor  -- Wrap in Nonempty (RHS)
    cases h with
    | succ h_step h_rest =>
      -- h_step : p ⇝ q✝, h_rest : q✝ ⇝[n] r
      -- Need to show: Σ q, (p ⇝[1] q) × (q ⇝[n] r)
      -- Take q = the middle pattern from the reduction
      exact ⟨_, ⟨ReducesN.succ h_step (ReducesN.zero _), h_rest⟩⟩
  · -- Backward: build n+1 step from 1 + n
    intro ⟨⟨q, ⟨h1, hn⟩⟩⟩  -- Unwrap Nonempty, then destructure Σ and ×
    constructor  -- Wrap in Nonempty
    -- h1 : p ⇝[1] q means p ⇝ q' ∧ q' ⇝[0] q for some q'
    cases h1 with
    | succ h_step h_zero =>
      cases h_zero  -- h_zero : q' ⇝[0] q means q' = q
      exact ReducesN.succ h_step hn

end Mettapedia.OSLF.RhoCalculus
