import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.Induction.ThetaPrime

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

open Classical KnuthSkillingAlgebra
open SandwichSeparation.SeparationToArchimedean

variable {α : Type*} [KnuthSkillingAlgebra α] [KSSeparation α]

/-!
# Hypercube boundary-collision argument (made explicit)

Several “refutation” or “gap proof” attempts try to rule out the B-empty boundary case
`Θx - Θy = Δ·δ` by observing that it forces a collision:

`Theta'_raw R d δ x 0 = Theta'_raw R d δ y Δ`.

This collision *does* contradict a **strictly monotone** extended evaluator `Θ'` that agrees with
`Theta'_raw` on join-multiplicity witnesses.

However, in the Appendix-A induction, strict monotonicity in the mixed-`t` cases is **exactly**
the point where the B-empty strict relative gap lemmas are needed. So using “strictMono ⇒ no
boundary” as the proof of strictMono is circular.

This file keeps the argument in a non-circular form: it is a lemma schema showing that
*once you already have* a strictly monotone extension, the strict relative gap follows immediately.
-/

structure BoundaryConfig
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (r_x r_y : Multi k) (δ : ℝ) (Δ : ℕ) : Prop where
  gap_exact :
    R.Θ_grid ⟨mu F r_x, mu_mem_kGrid F r_x⟩ -
        R.Θ_grid ⟨mu F r_y, mu_mem_kGrid F r_y⟩ = (Δ : ℝ) * δ

lemma boundary_implies_Theta'_raw_eq
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F) (d : α) (δ : ℝ)
    (r_x r_y : Multi k) (Δ : ℕ) (hB : BoundaryConfig (R := R) r_x r_y δ Δ) :
    Theta'_raw R d δ r_x 0 = Theta'_raw R d δ r_y Δ := by
  classical
  unfold Theta'_raw
  have : R.Θ_grid ⟨mu F r_x, mu_mem_kGrid F r_x⟩ =
      R.Θ_grid ⟨mu F r_y, mu_mem_kGrid F r_y⟩ + (Δ : ℝ) * δ := by
    linarith [hB.gap_exact]
  simp [this]

/-- If an extension evaluator `Θ'` is already strictly monotone and agrees with `Theta'_raw`,
then any boundary configuration contradicts strict monotonicity (via the obvious collision). -/
theorem boundary_contradiction_of_strictMono_extension
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (_IH : GridBridge F) (_H : GridComm F)
    (d : α) (hd : ident < d) (δ : ℝ)
    (Θ' : {x // x ∈ kGrid (extendAtomFamily F d hd)} → ℝ)
    (h_on_join :
      ∀ (r_old : Multi k) (t : ℕ),
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩ =
          Theta'_raw R d δ r_old t)
    (h_strict : StrictMono Θ')
    (r_x r_y : Multi k) (Δ : ℕ)
    (h_between : mu F r_x < op (mu F r_y) (iterate_op d Δ))
    (hB : BoundaryConfig (R := R) r_x r_y δ Δ) :
    False := by
  classical
  have hμx : mu (extendAtomFamily F d hd) (joinMulti r_x 0) = mu F r_x := by
    simpa [iterate_op_zero, op_ident_right] using (mu_extend_last F d hd r_x 0)
  have hμy :
      mu (extendAtomFamily F d hd) (joinMulti r_y Δ) = op (mu F r_y) (iterate_op d Δ) := by
    simpa using (mu_extend_last F d hd r_y Δ)
  have hμ_lt' :
      mu (extendAtomFamily F d hd) (joinMulti r_x 0) <
        mu (extendAtomFamily F d hd) (joinMulti r_y Δ) := by
    simpa [hμx, hμy] using h_between
  have hΘ_lt :
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_x 0),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_x 0)⟩ <
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_y Δ),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_y Δ)⟩ :=
    h_strict hμ_lt'
  have hraw_lt : Theta'_raw R d δ r_x 0 < Theta'_raw R d δ r_y Δ := by
    simpa [h_on_join] using hΘ_lt
  have hraw_eq : Theta'_raw R d δ r_x 0 = Theta'_raw R d δ r_y Δ :=
    boundary_implies_Theta'_raw_eq (R := R) (d := d) (δ := δ) (r_x := r_x) (r_y := r_y) (Δ := Δ) hB
  exact (ne_of_lt hraw_lt) hraw_eq

/-- The hypercube “boundary collision” argument yields the strict A-side gap inequality,
but only assuming a *prior* strictly monotone extension `Θ'` agreeing with `Theta'_raw`.

This makes the circularity explicit: in Appendix A, this strict gap is needed to establish
strict monotonicity in the mixed-`t` cases. -/
theorem theta_gap_lt_of_strictMono_extension_hypercube
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (_IH : GridBridge F) (_H : GridComm F)
    (d : α) (hd : ident < d) (δ : ℝ)
    (Θ' : {x // x ∈ kGrid (extendAtomFamily F d hd)} → ℝ)
    (h_on_join :
      ∀ (r_old : Multi k) (t : ℕ),
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩ =
          Theta'_raw R d δ r_old t)
    (h_strict : StrictMono Θ')
    (r_x r_y : Multi k) (Δ : ℕ)
    (h_between : mu F r_x < op (mu F r_y) (iterate_op d Δ)) :
    R.Θ_grid ⟨mu F r_x, mu_mem_kGrid F r_x⟩ -
        R.Θ_grid ⟨mu F r_y, mu_mem_kGrid F r_y⟩ < (Δ : ℝ) * δ := by
  classical
  have hμx : mu (extendAtomFamily F d hd) (joinMulti r_x 0) = mu F r_x := by
    simpa [iterate_op_zero, op_ident_right] using (mu_extend_last F d hd r_x 0)
  have hμy :
      mu (extendAtomFamily F d hd) (joinMulti r_y Δ) = op (mu F r_y) (iterate_op d Δ) := by
    simpa using (mu_extend_last F d hd r_y Δ)
  have hμ_lt' :
      mu (extendAtomFamily F d hd) (joinMulti r_x 0) <
        mu (extendAtomFamily F d hd) (joinMulti r_y Δ) := by
    simpa [hμx, hμy] using h_between
  have hΘ_lt :
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_x 0),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_x 0)⟩ <
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_y Δ),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_y Δ)⟩ :=
    h_strict hμ_lt'
  have hraw_lt : Theta'_raw R d δ r_x 0 < Theta'_raw R d δ r_y Δ := by
    simpa [h_on_join] using hΘ_lt
  exact (theta_gap_lt_iff_Theta'_raw_lt (R := R) (d := d) (δ := δ)
      (r_old_x := r_x) (r_old_y := r_y) (Δ := Δ)).2 hraw_lt

/-!
## Ben's Lemma 7: Algebraic Order-Invariance via Cancellation

From Ben Goertzel's "A Categorical Repackaging of the Knuth-Skilling Appendix Proofs" (Dec 2025):

**Lemma 7 (Order-invariance inside the admissible gap)**: In the B = ∅ case, the truth value
of V_d < W_d is independent of the choice of d in the admissible interval.

**Key Insight**: If μ(r_x) ⊕ d^u = μ(r_y) ⊕ d^v with u < v, then by cancellation we can derive
μ(r_x) = μ(r_y) ⊕ d^{v-u}. When μ(r_y) = ident (the zero multi), this gives μ(r_x) = d^{v-u},
creating a B-witness and contradicting B-emptiness.
-/

/-- Powers of the same element commute: d^m ⊕ d^n = d^n ⊕ d^m.
This follows from iterate_op_add: d^m ⊕ d^n = d^{m+n} = d^{n+m} = d^n ⊕ d^m. -/
lemma iterate_op_powers_comm (d : α) (m n : ℕ) :
    op (iterate_op d m) (iterate_op d n) = op (iterate_op d n) (iterate_op d m) := by
  rw [iterate_op_add, iterate_op_add]
  simp only [Nat.add_comm]

/-- Cancellation lemma for equality: if A ⊕ z = B ⊕ z, then A = B.
Uses cancellative_left in both directions. -/
lemma cancel_right_eq {x y z : α} (h : op x z = op y z) : x = y := by
  have h1 : x ≤ y := cancellative_left (le_of_eq h)
  have h2 : y ≤ x := cancellative_left (le_of_eq h.symm)
  exact le_antisymm h1 h2

/-- **Ben's Lemma 7 (Special Case)**: When μ(r_y) = ident, the equality
μ(r_x) ⊕ d^u = μ(r_y) ⊕ d^v with u < v forces μ(r_x) = d^{v-u}, creating a B-witness.

This is the cleanly provable case of the order-invariance lemma. -/
lemma equality_implies_B_witness_of_ident
    {k : ℕ} {F : AtomFamily α k} (d : α) (_hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (r_x r_y : Multi k) (u v : ℕ) (huv : u < v)
    (h_eq : op (mu F r_x) (iterate_op d u) = op (mu F r_y) (iterate_op d v))
    (hr_y_ident : mu F r_y = ident) :
    False := by
  -- Step 1: Rewrite d^v = d^u ⊕ d^{v-u}
  have hv_eq : v = u + (v - u) := by omega
  have hv_split : iterate_op d v = op (iterate_op d u) (iterate_op d (v - u)) := by
    conv_lhs => rw [hv_eq]
    exact (iterate_op_add d u (v - u)).symm
  rw [hv_split] at h_eq
  -- Step 2: Use μ(r_y) = ident to simplify RHS
  rw [hr_y_ident, op_ident_left] at h_eq
  -- Now h_eq : μ(r_x) ⊕ d^u = d^u ⊕ d^{v-u}
  -- Step 3: Use commutativity of d-powers to rearrange RHS
  have h_comm : op (iterate_op d u) (iterate_op d (v - u)) =
                op (iterate_op d (v - u)) (iterate_op d u) :=
    iterate_op_powers_comm d u (v - u)
  rw [h_comm] at h_eq
  -- Now h_eq : μ(r_x) ⊕ d^u = d^{v-u} ⊕ d^u
  -- Step 4: Cancel d^u from the right using cancel_right_eq
  have h_cancel : mu F r_x = iterate_op d (v - u) := cancel_right_eq h_eq
  -- Step 5: This means r_x ∈ B(v-u), contradicting B_empty
  have hvu_pos : 0 < v - u := Nat.sub_pos_of_lt huv
  have hrx_in_B : r_x ∈ extensionSetB F d (v - u) := by
    simp only [extensionSetB, Set.mem_setOf_eq, h_cancel]
  exact hB_empty r_x (v - u) hvu_pos hrx_in_B

/-- **Ben's Lemma 7 (General Form)**: The equality μ(r_x) ⊕ d^u = μ(r_y) ⊕ d^v with u < v
implies μ(r_x) = μ(r_y) ⊕ d^{v-u} via cancellation.

This is the core algebraic step. The contradiction with B_empty follows when μ(r_y) = ident.
For general μ(r_y), the equation shows that μ(r_x) "exceeds" μ(r_y) by exactly d^{v-u}. -/
lemma equality_implies_cancel
    (d : α) (μ_x μ_y : α) (u v : ℕ) (huv : u < v)
    (h_eq : op μ_x (iterate_op d u) = op μ_y (iterate_op d v)) :
    μ_x = op μ_y (iterate_op d (v - u)) := by
  -- Step 1: Rewrite d^v = d^u ⊕ d^{v-u}
  have hv_eq : v = u + (v - u) := by omega
  have hv_split : iterate_op d v = op (iterate_op d u) (iterate_op d (v - u)) := by
    conv_lhs => rw [hv_eq]
    exact (iterate_op_add d u (v - u)).symm
  rw [hv_split] at h_eq
  -- Step 2: Rearrange RHS using associativity and commutativity of d-powers
  -- μ_y ⊕ (d^u ⊕ d^{v-u}) = (μ_y ⊕ d^u) ⊕ d^{v-u}  (by assoc)
  --                       = (μ_y ⊕ d^{v-u}) ⊕ d^u  (swap inner)
  have h_rhs_rearrange : op μ_y (op (iterate_op d u) (iterate_op d (v - u))) =
                         op (op μ_y (iterate_op d (v - u))) (iterate_op d u) := by
    -- First, use commutativity of d-powers
    have h_comm : op (iterate_op d u) (iterate_op d (v - u)) =
                  op (iterate_op d (v - u)) (iterate_op d u) :=
      iterate_op_powers_comm d u (v - u)
    rw [h_comm]
    -- Now: μ_y ⊕ (d^{v-u} ⊕ d^u) = (μ_y ⊕ d^{v-u}) ⊕ d^u by associativity
    exact (op_assoc μ_y (iterate_op d (v - u)) (iterate_op d u)).symm
  rw [h_rhs_rearrange] at h_eq
  -- Now h_eq : μ_x ⊕ d^u = (μ_y ⊕ d^{v-u}) ⊕ d^u
  exact cancel_right_eq h_eq

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

/-!
The remainder of this file was an earlier draft attempt to prove the B-empty strict relative gaps
directly, but it relied (implicitly) on the existence of a strictly monotone extension and did not
typecheck. It is retained here only as historical context.
-/

/- BEGIN ARCHIVED (broken) DRAFT
/-!
# Hypercube/Reverse-Mathematics Proof of B-Empty Strict Gap

This file proves `theta_gap_lt_of_mu_lt_op_B_empty_strict` using the insight from
the TOGL/Hypercube framework: the boundary case (gap = Δ·δ exactly) would cause the
extended Θ' to assign the same value to two distinct μ'-values, contradicting strict
monotonicity.

## Main Results

* `theta_gap_strict_of_boundary_impossible` - If boundary implies Θ' non-strict-mono,
  and Θ' must be strictly monotonic, then boundary is impossible.

* `theta_gap_lt_hypercube` - The strict gap inequality via the hypercube argument.

## The Hypercube Insight

From the TOGL/Hypercube framework (Stay & Wells 2024):
- The extension operation generates a modality ⟨C_extend⟩
- This modality must preserve strict monotonicity (a semantic requirement)
- Boundary configurations violate this requirement
- Therefore, boundary configurations are inadmissible in the "equational center"

Concretely: If Θ(μ_x) - Θ(μ_y) = Δ·δ exactly, then:
- Θ'(μ_x, 0) = Θ(μ_x) + 0·δ = Θ(μ_x)
- Θ'(μ_y, Δ) = Θ(μ_y) + Δ·δ = Θ(μ_y) + (Θ(μ_x) - Θ(μ_y)) = Θ(μ_x)

So Θ'(μ_x, 0) = Θ'(μ_y, Δ). But:
- μ'(x,0) = μ_x and μ'(y,Δ) = μ_y ⊕ d^Δ
- Given h_lt: μ_x < μ_y ⊕ d^Δ, we have μ'(x,0) < μ'(y,Δ)

Two distinct μ'-values with the same Θ'-value contradicts strict monotonicity!
-/

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

open Classical KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-! ### The Boundary Configuration -/

/-- A boundary configuration is one where the Θ-gap equals Δ·δ exactly.
This is the forbidden configuration that the hypercube analysis identifies. -/
structure BoundaryConfig {k : ℕ} (F : AtomFamily α k) (R : MultiGridRep F)
    (d : α) (δ : ℝ) (r_x r_y : Multi k) (Δ : ℕ) : Prop where
  /-- The gap equals Δ·δ exactly -/
  gap_exact : R.Θ_grid ⟨mu F r_x, mu_mem_kGrid F r_x⟩ -
              R.Θ_grid ⟨mu F r_y, mu_mem_kGrid F r_y⟩ = (Δ : ℝ) * δ
  /-- μ_y < μ_x (order condition) -/
  mu_order : mu F r_y < mu F r_x
  /-- μ_x < μ_y ⊕ d^Δ (upper bound) -/
  mu_upper : mu F r_x < op (mu F r_y) (iterate_op d Δ)
  /-- Δ > 0 -/
  delta_pos : 0 < Δ

/-! ### Key Lemma: Boundary Implies Θ' Collision -/

/-- If a boundary configuration holds, then the raw Θ' evaluator assigns the same value
to two distinct extended grid points: (r_x, 0) and (r_y, Δ).

This is the key step: boundary ⟹ Θ' collision. -/
lemma boundary_implies_Theta'_collision
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (δ : ℝ) (r_x r_y : Multi k) (Δ : ℕ)
    (hB : BoundaryConfig F R d δ r_x r_y Δ) :
    Theta'_raw R d δ r_x 0 = Theta'_raw R d δ r_y Δ := by
  unfold Theta'_raw
  -- LHS = Θ(μ_x) + 0·δ = Θ(μ_x)
  -- RHS = Θ(μ_y) + Δ·δ
  -- By gap_exact: Θ(μ_x) - Θ(μ_y) = Δ·δ
  -- So: Θ(μ_y) + Δ·δ = Θ(μ_y) + (Θ(μ_x) - Θ(μ_y)) = Θ(μ_x)
  simp only [Nat.cast_zero, zero_mul, add_zero]
  linarith [hB.gap_exact]

/-- The extended μ-values for (r_x, 0) and (r_y, Δ) are distinct, with a strict ordering. -/
lemma boundary_mu_extended_distinct
    {k : ℕ} {F : AtomFamily α k} {R : MultiGridRep F}
    {d : α} (hd : ident < d) {δ : ℝ} {r_x r_y : Multi k} {Δ : ℕ}
    (hB : BoundaryConfig F R d δ r_x r_y Δ) :
    mu (extendAtomFamily F d hd) (joinMulti r_x 0) <
    mu (extendAtomFamily F d hd) (joinMulti r_y Δ) := by
  -- μ'(x,0) = μ_x ⊕ d^0 = μ_x
  have hμx : mu (extendAtomFamily F d hd) (joinMulti r_x 0) = mu F r_x := by
    have := mu_extend_last F d hd r_x 0
    simpa [iterate_op_zero, op_ident_right] using this
  -- μ'(y,Δ) = μ_y ⊕ d^Δ
  have hμy : mu (extendAtomFamily F d hd) (joinMulti r_y Δ) = op (mu F r_y) (iterate_op d Δ) := by
    exact mu_extend_last F d hd r_y Δ
  -- By h_lt: μ_x < μ_y ⊕ d^Δ
  simpa [hμx, hμy] using hB.mu_upper

/-! ### The Contradiction: Boundary vs Strict Monotonicity -/

/-- **Main Lemma (Hypercube Insight)**: If any strictly monotonic extension Θ' exists
that agrees with Theta'_raw on joinMulti witnesses, then boundary configurations
cannot occur.

This is the reverse-mathematics insight: the EXISTENCE of a valid extension
IMPLIES the boundary is impossible. -/
theorem no_boundary_if_strictMono_extension_exists
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d) (δ : ℝ) (r_x r_y : Multi k) (Δ : ℕ)
    -- Existence of a valid strictly monotonic extension
    (Θ' : {x // x ∈ kGrid (extendAtomFamily F d hd)} → ℝ)
    (h_on_join : ∀ (r_old : Multi k) (t : ℕ),
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩ =
        Theta'_raw R d δ r_old t)
    (h_strict : StrictMono Θ')
    -- Boundary configuration hypothesis
    (hB : BoundaryConfig F R d δ r_x r_y Δ) :
    False := by
  -- Step 1: By boundary_implies_Theta'_collision, the raw evaluator gives same value
  have h_collision : Theta'_raw R d δ r_x 0 = Theta'_raw R d δ r_y Δ :=
    boundary_implies_Theta'_collision R d δ r_x r_y Δ hB

  -- Step 2: Therefore Θ' gives the same value on these extended points
  have h_Θ'_eq :
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_x 0),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_x 0)⟩ =
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_y Δ),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_y Δ)⟩ := by
    rw [h_on_join r_x 0, h_on_join r_y Δ, h_collision]

  -- Step 3: But the μ'-values are strictly ordered
  have h_μ'_lt : mu (extendAtomFamily F d hd) (joinMulti r_x 0) <
                 mu (extendAtomFamily F d hd) (joinMulti r_y Δ) :=
    boundary_mu_extended_distinct hd hB

  -- Step 4: Strict monotonicity of Θ' gives Θ'(μ'_x) < Θ'(μ'_y)
  have h_Θ'_lt :
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_x 0),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_x 0)⟩ <
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_y Δ),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_y Δ)⟩ :=
    h_strict h_μ'_lt

  -- Step 5: Contradiction: Θ'_x = Θ'_y but Θ'_x < Θ'_y
  linarith

/-! ### Strict Gap from Non-Strict + Boundary Impossible -/

/-- The strict gap inequality via the hypercube approach: given
1. The non-strict bound (Θ_x - Θ_y ≤ Δ·δ)
2. The existence of a valid strictly monotonic extension

Use (2) to rule out equality in (1) via the boundary-implies-collision argument. -/
theorem theta_gap_lt_via_hypercube
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d) (δ : ℝ) (r_x r_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ)
    (h_mu : mu F r_y < mu F r_x)
    (h_lt : mu F r_x < op (mu F r_y) (iterate_op d Δ))
    -- Non-strict bound (from crossing index analysis)
    (h_nonstrict : R.Θ_grid ⟨mu F r_x, mu_mem_kGrid F r_x⟩ -
                   R.Θ_grid ⟨mu F r_y, mu_mem_kGrid F r_y⟩ ≤ (Δ : ℝ) * δ)
    -- Existence of a valid strictly monotonic extension
    (Θ' : {x // x ∈ kGrid (extendAtomFamily F d hd)} → ℝ)
    (h_on_join : ∀ (r_old : Multi k) (t : ℕ),
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩ =
        Theta'_raw R d δ r_old t)
    (h_strict : StrictMono Θ') :
    R.Θ_grid ⟨mu F r_x, mu_mem_kGrid F r_x⟩ -
        R.Θ_grid ⟨mu F r_y, mu_mem_kGrid F r_y⟩ < (Δ : ℝ) * δ := by
  -- Use lt_of_le_of_ne: we have ≤, need to show ≠
  apply lt_of_le_of_ne h_nonstrict
  -- Assume for contradiction that equality holds
  intro h_eq
  -- Then we have a boundary configuration
  have hB : BoundaryConfig F R d δ r_x r_y Δ := {
    gap_exact := h_eq
    mu_order := h_mu
    mu_upper := h_lt
    delta_pos := hΔ
  }
  -- But this contradicts the existence of a strictly monotonic extension
  exact no_boundary_if_strictMono_extension_exists R d hd δ r_x r_y Δ Θ' h_on_join h_strict hB

/-! ### The Inaccessible δ Property (Key to Breaking Circularity)

**Theorem (Inaccessible δ in B-Empty)**: When B is globally empty, no separation
statistic equals δ exactly. This is because:

1. δ = sup(A-stats) = inf(C-stats) by the Dedekind cut property
2. If some A-stat = δ, that would be a maximum A-stat
3. If some C-stat = δ, that would be a minimum C-stat
4. The separation property says all A-stats < all C-stats (strictly)
5. If A-stat = δ = C-stat for some pair, this violates strict separation

Therefore, δ is strictly between all A-stats and all C-stats:
  ∀ (r, u) ∈ A, stat(r,u) < δ    (strictly)
  ∀ (r, u) ∈ C, δ < stat(r,u)    (strictly)

**Consequence for Floor-Bracket**:
Let K be the crossing index for μ (least n with μ < d^n). Then:
  (K-1)·δ < Θ(μ) < K·δ    (BOTH bounds strict!)

The lower bound is strict because:
  μ > d^(K-1) (by B-empty, μ ≠ d^(K-1))
  ⟹ μ ∈ C(K-1)
  ⟹ C-stat for (μ, K-1) = Θ(μ)/(K-1) > δ  (by inaccessibility)
  ⟹ Θ(μ) > (K-1)·δ

**Boundary Elimination**:
At boundary θ_x - θ_y = Δ·δ with K_x = K_y + Δ:
  - Parameterize: θ_x = (K_x - 1)·δ + ε_x, θ_y = (K_y - 1)·δ + ε_y
  - Strict floor-bracket: 0 < ε_x < δ and 0 < ε_y < δ
  - Boundary requires: ε_x = ε_y

The remaining step is to show ε_x = ε_y is impossible given h_lt: μ_x < μ_y ⊕ d^Δ.

**Connection to Hypercube Framework**:
The hypercube insight is that the "equational center" Z (valid type assignments)
excludes boundary configurations because they violate the strict monotonicity
modality. The inaccessible δ property is the formal mechanism that enforces this.
-/

/-! ### Formalization of Inaccessible δ -/

/-- In B-empty, no C-statistic equals δ. This is the key "inaccessibility" property.
The C-stat being > δ (not just ≥) makes the floor-bracket lower bound strict. -/
lemma C_stat_gt_chooseδ_of_B_empty
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (r : Multi k) (u : ℕ) (hu : 0 < u) (hrC : r ∈ extensionSetC F d u) :
    chooseδ hk R d hd < separationStatistic R r u hu := by
  -- δ = sup(A-stats) by B-empty
  -- All A-stats < C-stat(r, u) by separation_property
  -- Therefore δ = sup(A-stats) ≤ C-stat(r, u)
  -- To get strict: if δ = C-stat(r, u), then inf(C-stats) would be attained
  -- But by delta_cut_tight, we can find A-stats arbitrarily close to δ from below
  -- If δ = C-stat exactly, then some A-stat would equal or exceed some C-stat
  -- This contradicts strict separation A < C
  --
  -- Formalization: use delta_cut_tight to get ε-close A-witness, derive contradiction
  classical
  by_contra h_not_lt
  push_neg at h_not_lt
  -- h_not_lt : C-stat ≤ δ
  -- Combined with chooseδ_C_bound: δ ≤ C-stat
  -- This gives C-stat = δ
  have hδ_le : chooseδ hk R d hd ≤ separationStatistic R r u hu :=
    chooseδ_C_bound hk R IH H d hd r u hu hrC
  have hC_eq_δ : separationStatistic R r u hu = chooseδ hk R d hd :=
    le_antisymm h_not_lt hδ_le
  -- Now use delta_cut_tight to get an A-witness arbitrarily close to δ
  -- The A-witness has A-stat < C-stat = δ, but also A-stat > δ - ε for any ε
  -- As ε → 0, this forces A-stat → δ from below
  -- But then we'd have A-stat ≈ C-stat, contradicting strict separation A < C
  have hδ_pos : 0 < chooseδ hk R d hd := delta_pos hk R IH H d hd
  -- Get an A-witness within ε = δ/2 of δ
  have hε : 0 < chooseδ hk R d hd / 2 := by linarith
  obtain ⟨rA, uA, rC', uC', huA, huC', hrA, hrC', hC'_close, hA_close⟩ :=
    delta_cut_tight (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
      (hB_empty := hB_empty) (chooseδ hk R d hd / 2) hε
  -- A-stat(rA, uA) is within δ/2 of δ, so A-stat > δ/2
  -- C-stat(r, u) = δ
  -- But separation says A-stat(rA, uA) < C-stat(r, u) = δ
  have hA_lt_C : separationStatistic R rA uA huA < separationStatistic R r u hu := by
    have := separation_property R H IH hd huA hrA hu hrC
    simpa [separationStatistic]
  -- From hA_close: |δ - A-stat| < δ/2, so A-stat > δ/2
  have hA_lower : chooseδ hk R d hd / 2 < separationStatistic R rA uA huA := by
    have h := hA_close
    rw [abs_lt] at h
    linarith [h.1]
  -- But A-stat < C-stat = δ
  have hA_lt_δ : separationStatistic R rA uA huA < chooseδ hk R d hd := by
    simpa [hC_eq_δ] using hA_lt_C
  -- A-stat > δ/2 and A-stat < δ is consistent, no immediate contradiction...
  -- The issue is we need to push ε → 0 to get a contradiction
  -- Actually, the contradiction comes from hC'_close: there's a C' with |C'-stat - δ| < δ/2
  -- Combined with hC_eq_δ (our original C-stat = δ), we have C'-stat close to C-stat
  -- But C'-stat > δ (since it's a C-stat), so C'-stat > δ = C-stat
  -- Hmm, this doesn't directly contradict anything...
  --
  -- The real argument: if C-stat = δ exactly, and δ = sup(A-stats),
  -- then the infimum of C-stats is achieved at some C-stat.
  -- But by strict separation A < C, we'd have sup(A) < inf(C).
  -- Combined with sup(A) = inf(C) = δ (Dedekind cut), this is a contradiction.
  --
  -- TODO: Complete this proof using the Dedekind cut property.
  -- PROOF_HOLE (archived sketch)

/-- Strict floor-bracket lower bound in B-empty.
If K is the crossing index (K > 1) and B is empty, then (K-1)·δ < Θ(μ) (strictly). -/
lemma theta_gt_floor_of_B_empty
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (r : Multi k) (K : ℕ)
    (hK_is_crossing : K = Nat.find (bounded_by_iterate d hd (mu F r)))
    (hK_gt_1 : 1 < K) :
    ((K - 1 : ℕ) : ℝ) * chooseδ hk R d hd < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
  classical
  set δ : ℝ := chooseδ hk R d hd with hδ_def
  have hKm1_pos : 0 < K - 1 := Nat.sub_pos_of_lt hK_gt_1
  -- r ∈ C(K-1) because μ(r) > d^(K-1) (by B-empty and K minimality)
  have h_not_lt : ¬ mu F r < iterate_op d (K - 1) := by
    intro hlt
    have hP_ex : ∃ n : ℕ, mu F r < iterate_op d n := bounded_by_iterate d hd (mu F r)
    have : Nat.find hP_ex ≤ K - 1 := Nat.find_min' hP_ex hlt
    rw [hK_is_crossing] at this
    omega
  have hne : mu F r ≠ iterate_op d (K - 1) := by
    intro hEq
    have : r ∈ extensionSetB F d (K - 1) := by
      simp [extensionSetB, Set.mem_setOf_eq, hEq]
    exact hB_empty r (K - 1) hKm1_pos this
  have hgt : iterate_op d (K - 1) < mu F r := lt_of_le_of_ne (le_of_not_gt h_not_lt) (Ne.symm hne)
  have hrC : r ∈ extensionSetC F d (K - 1) := hgt
  -- Use C_stat_gt_chooseδ_of_B_empty to get δ < C-stat
  have hC_stat_gt : δ < separationStatistic R r (K - 1) hKm1_pos :=
    C_stat_gt_chooseδ_of_B_empty hk R IH H d hd hB_empty r (K - 1) hKm1_pos hrC
  -- C-stat = Θ(μ(r)) / (K-1), so δ < Θ(μ(r)) / (K-1)
  -- Thus (K-1)·δ < Θ(μ(r))
  have hKm1_pos_real : (0 : ℝ) < ((K - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hKm1_pos
  simp only [separationStatistic] at hC_stat_gt
  have h_ineq := (lt_div_iff₀ hKm1_pos_real).mp hC_stat_gt
  ring_nf at h_ineq ⊢
  exact h_ineq

/-! ### Ben Goertzel's Algebraic Approach (Lemma 7)

From "A Categorical Repackaging of the Knuth-Skilling Appendix Proofs" (Dec 2025):

**Lemma 7 (Order-invariance inside the admissible gap)**: In B = ∅ case, the truth value
of V_d < W_d is independent of the choice of d in the admissible interval.

**Proof idea**: If order flipped between d₁ and d₂, there would be some d₀ where
V_{d₀} = W_{d₀}. By cancellation, this gives X ⊕ d^{u-v} = Y, creating a B-witness.
Contradiction with B = ∅.

**Application to strict gap**: The algebraic order μ_x < μ_y ⊕ d^Δ is an absolute fact.
Any valid representation must preserve this order. By additivity:
  Θ(μ_x) < Θ(μ_y ⊕ d^Δ) = Θ(μ_y) + Δ·δ

This is NOT circular because we use the algebraic order (h_lt) to force the Θ inequality,
not the other way around.
-/

/-- **Ben's Lemma 7 (Core insight)**: In B-empty, if two extended expressions
V = X ⊕ d^u and W = Y ⊕ d^v ever become equal, this creates a B-witness.

Specifically: V = W implies X ⊕ d^{|u-v|} = Y (assuming u > v WLOG),
which means some element of the old grid equals a power of d, contradicting B = ∅.

This is the key lemma that breaks the circularity in the strict gap proof. -/
lemma equality_implies_B_witness_of_B_empty
    {k : ℕ} {F : AtomFamily α k} (d : α) (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (r_x r_y : Multi k) (u v : ℕ) (huv : u < v)
    (h_eq : op (mu F r_x) (iterate_op d u) = op (mu F r_y) (iterate_op d v)) :
    False := by
  -- From h_eq: μ_x ⊕ d^u = μ_y ⊕ d^v
  -- Rewrite as: μ_x ⊕ d^u = μ_y ⊕ d^u ⊕ d^{v-u}
  have hv_split : iterate_op d v = op (iterate_op d u) (iterate_op d (v - u)) := by
    rw [← iterate_op_add d u (v - u)]
    congr 1
    omega
  rw [hv_split] at h_eq
  -- Now: μ_x ⊕ d^u = (μ_y ⊕ d^u) ⊕ d^{v-u}
  have h_assoc : op (mu F r_y) (op (iterate_op d u) (iterate_op d (v - u))) =
                 op (op (mu F r_y) (iterate_op d u)) (iterate_op d (v - u)) := by
    exact (op_assoc _ _ _).symm
  rw [h_assoc] at h_eq
  -- By right-cancellation: μ_x = (μ_y ⊕ d^u) ⊕ d^{v-u} with common suffix d^{v-u} on both sides
  -- Wait, that's not right. Let me redo this.
  -- h_eq: μ_x ⊕ d^u = μ_y ⊕ d^u ⊕ d^{v-u}
  -- This says μ_x ⊕ d^u is "bigger" than μ_y ⊕ d^u by d^{v-u}
  -- But actually we need to use cancellation differently.
  -- Actually, the issue is that we can't directly cancel d^u from both sides
  -- because the monoid is not necessarily a group.
  --
  -- Let's use Ben's approach: the equality creates a B-witness.
  -- If μ_x ⊕ d^u = μ_y ⊕ d^v, and u < v, then by the K&S structure,
  -- there must be some "compensation" that creates the B-witness.
  --
  -- For now, we note this needs the GridComm structure to proceed.
  -- PROOF_HOLE (archived sketch)

/-- **Algebraic Strict Gap (Ben's approach)**: The strict gap follows directly from
the algebraic order and additivity, without circularity.

Given:
  - μ_x < μ_y ⊕ d^Δ (algebraic fact from h_lt)
  - Θ is order-preserving and additive

Then: Θ(μ_x) < Θ(μ_y ⊕ d^Δ) = Θ(μ_y) + Δ·Θ(d) = Θ(μ_y) + Δ·δ

This gives Θ(μ_x) - Θ(μ_y) < Δ·δ without assuming strict monotonicity of the extension. -/
theorem theta_gap_lt_algebraic
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    (r_x r_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ)
    (h_lt : mu F r_x < op (mu F r_y) (iterate_op d Δ))
    -- Key hypothesis: δ is the Θ-value assigned to d in the extension
    (δ : ℝ) (hδ_def : δ > 0)
    -- Additivity of Θ on the extended grid (the extension formula)
    (h_additive : ∀ (μ : α) (t : ℕ),
      ∃ (Θ_ext : α → ℝ), Θ_ext (op μ (iterate_op d t)) = Θ_ext μ + (t : ℝ) * δ ∧
                          (∀ r, Θ_ext (mu F r) = R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩) ∧
                          StrictMono Θ_ext) :
    R.Θ_grid ⟨mu F r_x, mu_mem_kGrid F r_x⟩ -
        R.Θ_grid ⟨mu F r_y, mu_mem_kGrid F r_y⟩ < (Δ : ℝ) * δ := by
  -- Get the extended Θ that is strictly monotone and additive
  obtain ⟨Θ_ext, h_add, h_agrees, h_strictMono⟩ := h_additive (mu F r_y) Δ
  -- By strict monotonicity and h_lt: Θ_ext(μ_x) < Θ_ext(μ_y ⊕ d^Δ)
  have h1 : Θ_ext (mu F r_x) < Θ_ext (op (mu F r_y) (iterate_op d Δ)) :=
    h_strictMono h_lt
  -- By additivity: Θ_ext(μ_y ⊕ d^Δ) = Θ_ext(μ_y) + Δ·δ
  have h2 : Θ_ext (op (mu F r_y) (iterate_op d Δ)) = Θ_ext (mu F r_y) + (Δ : ℝ) * δ := h_add
  -- By agreement: Θ_ext(μ_x) = R.Θ_grid(μ_x) and Θ_ext(μ_y) = R.Θ_grid(μ_y)
  have h3 : Θ_ext (mu F r_x) = R.Θ_grid ⟨mu F r_x, mu_mem_kGrid F r_x⟩ := h_agrees r_x
  have h4 : Θ_ext (mu F r_y) = R.Θ_grid ⟨mu F r_y, mu_mem_kGrid F r_y⟩ := h_agrees r_y
  -- Combine: R.Θ_grid(μ_x) < R.Θ_grid(μ_y) + Δ·δ
  calc R.Θ_grid ⟨mu F r_x, mu_mem_kGrid F r_x⟩
      = Θ_ext (mu F r_x) := h3.symm
    _ < Θ_ext (op (mu F r_y) (iterate_op d Δ)) := h1
    _ = Θ_ext (mu F r_y) + (Δ : ℝ) * δ := h2
    _ = R.Θ_grid ⟨mu F r_y, mu_mem_kGrid F r_y⟩ + (Δ : ℝ) * δ := by rw [h4]

/-! ### Discussion: Resolution via Ben's Categorical Repackaging

**The Key Insight (Ben Goertzel, Dec 2025)**:
The strict gap follows from the ALGEBRAIC structure, not from assuming the extension
is strictly monotonic.

1. The algebraic order μ_x < μ_y ⊕ d^Δ is an ABSOLUTE FACT (given by h_lt)
2. Any valid representation MUST preserve this order (that's what "representation" means)
3. By additivity: Θ(μ_y ⊕ d^Δ) = Θ(μ_y) + Δ·δ
4. Combining: Θ(μ_x) < Θ(μ_y) + Δ·δ, i.e., Θ(μ_x) - Θ(μ_y) < Δ·δ

**Why This is Not Circular**:
- We're NOT assuming the extension Θ' is strictly monotonic and then deriving strict gap
- Instead, we use that the EXISTENCE of a valid extension (which is what we're constructing)
  REQUIRES the strict gap to hold
- The K&S construction proves such an extension EXISTS (via the admissible interval argument)
- Therefore the strict gap holds

**Ben's Lemma 7 (Order-Invariance)**:
The deeper algebraic fact is that in B-empty, the order between extended expressions
CANNOT flip as the parameter δ varies in the admissible interval. If it did flip,
at some point two expressions would be equal, creating a B-witness (contradiction).

**Formalization Strategy**:
The `theta_gap_lt_algebraic` theorem above shows the structure: given the existence
of a valid additive strictly-monotone extension, the strict gap follows trivially.
The remaining work is to prove such an extension exists, which is the main content
of the K&S Appendix A construction.
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

END ARCHIVED (broken) DRAFT -/
