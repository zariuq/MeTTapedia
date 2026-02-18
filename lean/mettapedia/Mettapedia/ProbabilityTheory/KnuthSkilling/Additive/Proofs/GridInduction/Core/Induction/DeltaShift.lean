import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Core.Induction.Construction


namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open SandwichSeparation.SeparationToArchimedean

variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α]

/-! ### Key Trade Lemma: δ-Shift Equivalence

This is the heart of K&S Appendix A's well-definedness argument.
When we have a "trade" equality `mu F r_old = op (mu F s_old) (d^Δ)`,
the δ bounds force the Θ-difference to equal Δ·δ.

**Mathematical proof sketch**:
1. From trade: r_old = s_old ⊕ d^Δ (in α via μ)
2. For any u > Δ with s_old ∈ A(u): r_old ∈ A(u+Δ) (shift property)
3. For any v > Δ with r_old ∈ C(v): s_old ∈ C(v-Δ) (shift property)
4. Using δ bounds + Archimedean (can choose u arbitrarily large):
   - Upper: Θ(r_old)/(u+Δ) ≤ δ and Θ(s_old)/u ≤ δ
   - These combine to bound (Θ(r_old) - Θ(s_old))/Δ from above
5. Similarly for lower bound using C comparisons
6. Taking limits as u → ∞ forces equality: (Θ(r_old) - Θ(s_old))/Δ = δ
-/

/-
**Shift property for A**: If trade holds and `s_old ∈ A(u)`, then `r_old ∈ A(u+Δ)`.

Proof sketch: `s_old ∈ A(u)` means `mu F s_old < d^u`.
-/
/-
### Deferred corollaries: relative A/C bounds

The strict **relative** A/C bounds (comparing `mu F r` against `op (mu F s) (d^u)`) are best proved
as corollaries of the constructed `(k+1)`-grid representation in `extend_grid_rep_with_atom`.

Keeping them here creates circular dependencies and forward references.
-/

/-- δ is a tight Dedekind cut: for any ε > 0, there exist A and C witnesses
    whose statistics approximate δ within ε. -/
lemma delta_cut_tight {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F)
    (d : α) (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ∀ ε > 0, ∃ (rA : Multi k) (uA : ℕ) (rC : Multi k) (uC : ℕ)
      (huA : 0 < uA) (huC : 0 < uC),
      rA ∈ extensionSetA F d uA ∧ rC ∈ extensionSetC F d uC ∧
      |separationStatistic R rC uC huC - chooseδ hk R d hd| < ε ∧
      |chooseδ hk R d hd - separationStatistic R rA uA huA| < ε := by
  intro ε hε
  -- accuracy_lemma gives rA,uA,rC,uC with (C-stat) - (A-stat) < ε
  have hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u :=
    extensionSetA_nonempty_of_B_empty F d hd hB_empty
  have hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
    extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
  obtain ⟨rA, uA, huA, hrA, rC, uC, huC, hrC, h_gap⟩ :=
    accuracy_lemma R d hd hB_empty hA_nonempty hC_nonempty ε hε

  set δ := chooseδ hk R d hd
  have hA_le_δ : separationStatistic R rA uA huA ≤ δ :=
    chooseδ_A_bound hk R IH H d hd rA uA huA hrA
  have hδ_le_C : δ ≤ separationStatistic R rC uC huC :=
    chooseδ_C_bound hk R IH H d hd rC uC huC hrC

  use rA, uA, rC, uC, huA, huC
  refine ⟨hrA, hrC, ?C_close, ?A_close⟩

  · -- |C - δ| < ε
    -- We know δ ≤ C and C - A < ε ⇒ C - δ ≤ C - A < ε
    have h_diff : separationStatistic R rC uC huC - δ ≤
                  separationStatistic R rC uC huC - separationStatistic R rA uA huA := by
      linarith [hA_le_δ]
    have hpos : 0 ≤ separationStatistic R rC uC huC - δ := by linarith [hδ_le_C]
    have := lt_of_le_of_lt h_diff h_gap
    simp [abs_of_nonneg hpos]
    exact this

  · -- |δ - A| < ε
    have h_diff : δ - separationStatistic R rA uA huA ≤
                  separationStatistic R rC uC huC - separationStatistic R rA uA huA := by
      linarith [hδ_le_C]
    have hpos : 0 ≤ δ - separationStatistic R rA uA huA := by linarith [hA_le_δ]
    have := lt_of_le_of_lt h_diff h_gap
    simp [abs_of_nonneg hpos]
    exact this

/-- `delta_cut_tight`, but with A and C witnesses at a common denominator.

Given `ε>0`, produce `u>0` and witnesses `rA ∈ A(u)`, `rC ∈ C(u)` such that both statistics are
within `ε` of `δ := chooseδ hk R d hd`.

This is a convenience lemma for the K&S Appendix A.3.4 “B-empty” arguments where we repeatedly
need denominator-matched approximants on both sides of the cut. -/
lemma delta_cut_tight_common_den {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F)
    (d : α) (hd : ident < d)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ∀ ε > 0, ∃ (u : ℕ) (hu : 0 < u) (rA rC : Multi k),
      rA ∈ extensionSetA F d u ∧ rC ∈ extensionSetC F d u ∧
      |separationStatistic R rC u hu - chooseδ hk R d hd| < ε ∧
      |chooseδ hk R d hd - separationStatistic R rA u hu| < ε := by
  classical
  intro ε hε
  obtain ⟨rA, uA, rC, uC, huA, huC, hrA, hrC, hC_close, hA_close⟩ :=
    delta_cut_tight (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
      (hB_empty := hB_empty) ε hε
  -- Scale to common denominator u := uA * uC.
  let u : ℕ := uA * uC
  have hu : 0 < u := Nat.mul_pos huA huC
  let rA' : Multi k := scaleMult uC rA
  let rC' : Multi k := scaleMult uA rC
  have hA' : rA' ∈ extensionSetA F d u := by
    -- μ(rA) < d^uA ⇒ (μ(rA))^uC < d^(uA*uC) and μ(scaleMult uC rA) = (μ(rA))^uC.
    have hμA : mu F rA < iterate_op d uA := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hrA
    have h_iter : iterate_op (mu F rA) uC < iterate_op d (uA * uC) := by
      have : iterate_op (mu F rA) (1 * uC) < iterate_op d (uA * uC) :=
        repetition_lemma_lt (mu F rA) d 1 uA uC huC (by simpa [iterate_op_one] using hμA)
      simpa [Nat.one_mul] using this
    have hbridge : mu F (scaleMult uC rA) = iterate_op (mu F rA) uC := IH.bridge rA uC
    have : mu F rA' < iterate_op d u := by
      simpa [rA', u, hbridge] using h_iter
    simpa [extensionSetA, Set.mem_setOf_eq, rA', u] using this
  have hC' : rC' ∈ extensionSetC F d u := by
    have hμC : iterate_op d uC < mu F rC := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hrC
    have h_iter : iterate_op d (uC * uA) < iterate_op (mu F rC) uA := by
      have : iterate_op d (uC * uA) < iterate_op (mu F rC) (1 * uA) :=
        repetition_lemma_lt d (mu F rC) uC 1 uA huA (by simpa [iterate_op_one] using hμC)
      simpa [Nat.one_mul] using this
    have hbridge : mu F (scaleMult uA rC) = iterate_op (mu F rC) uA := IH.bridge rC uA
    have : iterate_op d u < mu F rC' := by
      have : iterate_op d (uC * uA) < mu F (scaleMult uA rC) := by
        simpa [hbridge] using h_iter
      simpa [u, Nat.mul_comm uA uC, rC'] using this
    simpa [extensionSetC, Set.mem_setOf_eq, rC', u] using this
  have hstatA :
      separationStatistic R rA' u hu = separationStatistic R rA uA huA := by
    have hθ :
        R.Θ_grid ⟨mu F (scaleMult uC rA), mu_mem_kGrid F _⟩ =
          uC * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ :=
      Theta_scaleMult (R := R) (r := rA) uC
    have huA0 : (uA : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huA)
    have huC0 : (uC : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huC)
    have hcancel :
        (uC : ℝ) * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ /
            ((uA : ℝ) * (uC : ℝ)) =
          R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ / (uA : ℝ) := by
      field_simp [huA0, huC0]
    -- Unfold the statistic and cancel the common factor `uC`.
    simpa [separationStatistic, rA', u, hθ, Nat.cast_mul, hcancel]
  have hstatC :
      separationStatistic R rC' u hu = separationStatistic R rC uC huC := by
    have hθ :
        R.Θ_grid ⟨mu F (scaleMult uA rC), mu_mem_kGrid F _⟩ =
          uA * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ :=
      Theta_scaleMult (R := R) (r := rC) uA
    have huA0 : (uA : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huA)
    have huC0 : (uC : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huC)
    have hcancel :
        (uA : ℝ) * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ /
            ((uA : ℝ) * (uC : ℝ)) =
          R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ / (uC : ℝ) := by
      field_simp [huA0, huC0]
    simpa [separationStatistic, rC', u, hθ, Nat.cast_mul, hcancel]
  refine ⟨u, hu, rA', rC', hA', hC', ?_, ?_⟩
  · simpa [hstatC] using hC_close
  · simpa [hstatA] using hA_close

/-- Shift property for A: if trade holds and `s_old ∈ A(u)`, then `r_old ∈ A(u+Δ)`.

By trade, `mu F r_old = op (mu F s_old) (d^Δ)`.
Since `d^{u+Δ} = d^u ⊕ d^Δ` and `op` is strictly monotone:
`op (mu F s_old) (d^Δ) < op (d^u) (d^Δ) = d^{u+Δ}`.
So `r_old ∈ A(u+Δ)`. -/
lemma trade_shift_A {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {u : ℕ} (hrA : s_old ∈ extensionSetA F d u) :
    r_old ∈ extensionSetA F d (u + Δ) := by
  simp only [extensionSetA, Set.mem_setOf_eq] at *
  rw [htrade]
  have h_split : iterate_op d (u + Δ) = op (iterate_op d u) (iterate_op d Δ) :=
    (iterate_op_add d u Δ).symm
  rw [h_split]
  exact op_strictMono_left (iterate_op d Δ) hrA

/-- Backward shift property for A: if trade holds and `r_old ∈ A(u+Δ)`, then `s_old ∈ A(u)`. -/
lemma trade_shift_A_backward {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {u : ℕ} (hrA : r_old ∈ extensionSetA F d (u + Δ)) :
    s_old ∈ extensionSetA F d u := by
  simp only [extensionSetA, Set.mem_setOf_eq] at *
  have h_split : iterate_op d (u + Δ) = op (iterate_op d u) (iterate_op d Δ) :=
    (iterate_op_add d u Δ).symm
  -- Rewrite r_old ∈ A(u+Δ) using the trade and the iterate split.
  have h_lt :
      op (mu F s_old) (iterate_op d Δ) < op (iterate_op d u) (iterate_op d Δ) := by
    simpa [htrade, h_split] using hrA
  -- Cancel the common right factor by strict monotonicity.
  by_contra h_not
  have h_le : iterate_op d u ≤ mu F s_old := le_of_not_gt h_not
  have hmono := (op_strictMono_left (iterate_op d Δ)).monotone
  have : op (iterate_op d u) (iterate_op d Δ) ≤ op (mu F s_old) (iterate_op d Δ) :=
    hmono h_le
  exact (not_lt_of_ge this) h_lt

/-! ### Helper Lemmas for Cast Management and Proof Simplification -/

/-- If δ>0 and m*δ < u*δ, then m < u (as integers). -/
lemma int_lt_of_mul_lt_mul_right {δ : ℝ} (hδ : 0 < δ)
    {m u : ℤ} (h : (m:ℝ) * δ < (u:ℝ) * δ) : m < u := by
  -- cancel δ
  have : (m:ℝ) < (u:ℝ) := (mul_lt_mul_iff_left₀ hδ).1 h
  -- cast back to ℤ
  exact Int.cast_lt.mp this

/-- If δ>0 and u*δ < m*δ, then u < m (as integers). -/
lemma int_lt_of_mul_lt_mul_right' {δ : ℝ} (hδ : 0 < δ)
    {m u : ℤ} (h : (u:ℝ) * δ < (m:ℝ) * δ) : u < m := by
  have : (u:ℝ) < (m:ℝ) := (mul_lt_mul_iff_left₀ hδ).1 h
  exact Int.cast_lt.mp this

/-- If δ>0 and m*δ ≤ u*δ, then m ≤ u (as integers). -/
lemma int_le_of_mul_le_mul_right {δ : ℝ} (hδ : 0 < δ)
    {m u : ℤ} (h : (m:ℝ) * δ ≤ (u:ℝ) * δ) : m ≤ u := by
  have : (m:ℝ) ≤ (u:ℝ) := (mul_le_mul_iff_left₀ hδ).1 h
  exact Int.cast_le.mp this

/-- **Shift property for C**: If trade holds and r_old ∈ C(v) with v > Δ, then s_old ∈ C(v-Δ).

Proof sketch: r_old ∈ C(v) means d^v < mu F r_old.
By trade, mu F r_old = op (mu F s_old) (d^Δ).
Since d^v = d^{v-Δ} ⊕ d^Δ and op is strictly monotone:
  If mu F s_old ≤ d^{v-Δ}, then op (mu F s_old) (d^Δ) ≤ d^v, contradicting hrC.
So d^{v-Δ} < mu F s_old, i.e., s_old ∈ C(v-Δ). -/
lemma trade_shift_C {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {v : ℕ} (hv : Δ < v) (hrC : r_old ∈ extensionSetC F d v) :
    s_old ∈ extensionSetC F d (v - Δ) := by
  simp only [extensionSetC, Set.mem_setOf_eq] at *
  rw [htrade] at hrC
  have hv_split : v = (v - Δ) + Δ := by omega
  have h_split : iterate_op d v = op (iterate_op d (v - Δ)) (iterate_op d Δ) := by
    conv_lhs => rw [hv_split]
    exact (iterate_op_add d (v - Δ) Δ).symm
  rw [h_split] at hrC
  by_contra h_not_gt
  push_neg at h_not_gt
  rcases h_not_gt.lt_or_eq with hlt | heq
  · exact absurd hrC (not_lt.mpr (le_of_lt (op_strictMono_left (iterate_op d Δ) hlt)))
  · rw [heq] at hrC; exact lt_irrefl _ hrC

/-- **Forward shift property for C**: If trade holds and s_old ∈ C(v), then r_old ∈ C(v+Δ).

Proof sketch: s_old ∈ C(v) means d^v < mu F s_old.
By trade, mu F r_old = op (mu F s_old) (d^Δ).
Since op is strictly monotone:
  op (d^v) (d^Δ) < op (mu F s_old) (d^Δ) = mu F r_old
And op (d^v) (d^Δ) = d^{v+Δ} by iterate_op_add.
So d^{v+Δ} < mu F r_old, i.e., r_old ∈ C(v+Δ). -/
lemma trade_shift_C_forward {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {v : ℕ} (hsC : s_old ∈ extensionSetC F d v) :
    r_old ∈ extensionSetC F d (v + Δ) := by
  simp only [extensionSetC, Set.mem_setOf_eq] at *
  rw [htrade]
  have h_split : iterate_op d (v + Δ) = op (iterate_op d v) (iterate_op d Δ) :=
    (iterate_op_add d v Δ).symm
  rw [h_split]
  exact op_strictMono_left (iterate_op d Δ) hsC

/-- The trade relation shifts A-membership by `Δ` (for levels `U ≥ Δ`). -/
lemma trade_shift_A_iff {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {U : ℕ} (hU : Δ ≤ U) :
    r_old ∈ extensionSetA F d U ↔ s_old ∈ extensionSetA F d (U - Δ) := by
  constructor
  · intro hrA
    have : r_old ∈ extensionSetA F d ((U - Δ) + Δ) := by
      simpa [Nat.sub_add_cancel hU] using hrA
    exact trade_shift_A_backward (k := k) (F := F) hd hΔ htrade this
  · intro hsA
    have : r_old ∈ extensionSetA F d ((U - Δ) + Δ) :=
      trade_shift_A (k := k) (F := F) hd hΔ htrade (u := U - Δ) hsA
    simpa [Nat.sub_add_cancel hU] using this

/-- The trade relation shifts C-membership by `Δ` (for levels `U > Δ`). -/
lemma trade_shift_C_iff {k : ℕ} {F : AtomFamily α k}
    {d : α} (hd : ident < d)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    {U : ℕ} (hU : Δ < U) :
    r_old ∈ extensionSetC F d U ↔ s_old ∈ extensionSetC F d (U - Δ) := by
  constructor
  · intro hrC
    exact trade_shift_C (k := k) (F := F) hd hΔ htrade hU hrC
  · intro hsC
    have : r_old ∈ extensionSetC F d ((U - Δ) + Δ) :=
      trade_shift_C_forward (k := k) (F := F) hd hΔ htrade (v := U - Δ) hsC
    have hU' : (U - Δ) + Δ = U := Nat.sub_add_cancel (le_of_lt hU)
    simpa [hU'] using this

/-- If `x` commutes with `y`, then all iterates of `x` commute with `y`. -/
lemma iterate_op_comm_right {x y : α} (hxy : op x y = op y x) :
    ∀ n : ℕ, op (iterate_op x n) y = op y (iterate_op x n) := by
  intro n
  induction n with
  | zero =>
    simp [iterate_op_zero, op_ident_left, op_ident_right]
  | succ n ih =>
    -- (x^(n+1)) ⊕ y = x ⊕ (x^n ⊕ y) = x ⊕ (y ⊕ x^n) = (x ⊕ y) ⊕ x^n = (y ⊕ x) ⊕ x^n = y ⊕ x^(n+1)
    calc
      op (iterate_op x (n + 1)) y = op (op x (iterate_op x n)) y := by
        simp [iterate_op_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ = op x (op (iterate_op x n) y) := by
        simpa [op_assoc]
      _ = op x (op y (iterate_op x n)) := by
        simpa [ih]
      _ = op (op x y) (iterate_op x n) := by
        simpa [op_assoc]
      _ = op (op y x) (iterate_op x n) := by
        simpa [hxy]
      _ = op y (op x (iterate_op x n)) := by
        simpa [op_assoc]
      _ = op y (iterate_op x (n + 1)) := by
        simp [iterate_op_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- If `x` commutes with `y`, then iterating `x ⊕ y` distributes over iterating each term. -/
lemma iterate_op_op_of_comm {x y : α} (hxy : op x y = op y x) :
    ∀ n : ℕ, iterate_op (op x y) n = op (iterate_op x n) (iterate_op y n) := by
  intro n
  induction n with
  | zero =>
    simp [iterate_op_zero, op_ident_left, op_ident_right]
  | succ n ih =>
    have h_y_comm_xn : op y (iterate_op x n) = op (iterate_op x n) y := by
      -- Use the previous lemma and flip the equality.
      simpa using (iterate_op_comm_right (x := x) (y := y) hxy n).symm
    have h_inner :
        op y (op (iterate_op x n) (iterate_op y n)) =
          op (iterate_op x n) (op y (iterate_op y n)) := by
      calc
        op y (op (iterate_op x n) (iterate_op y n))
            = op (op y (iterate_op x n)) (iterate_op y n) := by
                simpa using (op_assoc y (iterate_op x n) (iterate_op y n)).symm
        _ = op (op (iterate_op x n) y) (iterate_op y n) := by
              simpa [h_y_comm_xn]
        _ = op (iterate_op x n) (op y (iterate_op y n)) := by
              simpa using (op_assoc (iterate_op x n) y (iterate_op y n))
    calc
      iterate_op (op x y) (n + 1)
          = op (op x y) (iterate_op (op x y) n) := by
              simp [iterate_op_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ = op (op x y) (op (iterate_op x n) (iterate_op y n)) := by
            simpa [ih]
      _ = op x (op y (op (iterate_op x n) (iterate_op y n))) := by
            simpa [op_assoc]
      _ = op x (op (iterate_op x n) (op y (iterate_op y n))) := by
            simpa [h_inner]
      _ = op (op x (iterate_op x n)) (op y (iterate_op y n)) := by
            simpa [op_assoc]
      _ = op (iterate_op x (n + 1)) (iterate_op y (n + 1)) := by
            simp [iterate_op_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Internal δ-shift when `d^Δ` already lies on the old `k`-grid (i.e. we have a B-witness). -/
private lemma delta_shift_equiv_of_B_witness {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (IH : GridBridge F) {d : α} (hd : ident < d)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδB : ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u → separationStatistic R r u hu = δ)
    {r_old s_old rΔ : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ))
    (hrΔB : rΔ ∈ extensionSetB F d Δ) :
    R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
      R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ = (Δ : ℝ) * δ := by
  have hrΔ_eq : mu F rΔ = iterate_op d Δ := by
    simpa [extensionSetB, Set.mem_setOf_eq] using hrΔB
  have hΘrΔ : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ = (Δ : ℝ) * δ := by
    have hstat : separationStatistic R rΔ Δ hΔ = δ := hδB rΔ Δ hΔ hrΔB
    unfold separationStatistic at hstat
    have hΔ_ne : (Δ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hΔ)
    have h := (div_eq_iff hΔ_ne).1 hstat
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

  have htrade' : mu F r_old = op (mu F s_old) (mu F rΔ) := by
    calc
      mu F r_old = op (mu F s_old) (iterate_op d Δ) := htrade
      _ = op (mu F s_old) (mu F rΔ) := by rw [← hrΔ_eq]

  have h_mu_eq : mu F r_old = mu F (s_old + rΔ) := by
    calc
      mu F r_old = op (mu F s_old) (mu F rΔ) := htrade'
      _ = mu F (s_old + rΔ) := by
            simpa using (mu_add_of_comm H s_old rΔ).symm

  have hθ_eq :
      R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ =
        R.Θ_grid ⟨mu F (s_old + rΔ), mu_mem_kGrid F (s_old + rΔ)⟩ := by
    congr 1
    ext
    exact h_mu_eq

  have hΘ_add := R.add s_old rΔ

  calc
    R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
        R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩
        = R.Θ_grid ⟨mu F (s_old + rΔ), mu_mem_kGrid F (s_old + rΔ)⟩ -
            R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ := by
              simpa [hθ_eq]
    _ = R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ := by
          have hΘ_add' :
              R.Θ_grid ⟨mu F (s_old + rΔ), mu_mem_kGrid F (s_old + rΔ)⟩ =
                R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ +
                  R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ := by
            simpa [Pi.add_apply] using hΘ_add
          calc
            R.Θ_grid ⟨mu F (s_old + rΔ), mu_mem_kGrid F (s_old + rΔ)⟩ -
                R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩
                = (R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ +
                    R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩) -
                      R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ := by
                    simpa [hΘ_add']
            _ = R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ := by ring
    _ = (Δ : ℝ) * δ := hΘrΔ

/-- **The δ-Shift Equivalence Lemma** (K&S trade argument core)

Given a trade equality mu F r_old = op (mu F s_old) (d^Δ) and δ bounds,
the Θ-difference must equal Δ·δ.

**Proof strategy** (GPT-5.1 Pro / K&S Appendix A):
1. The shift rules give: r_old ∈ A(U) ↔ s_old ∈ A(U-Δ) for U > Δ
2. Similarly for C-membership
3. For upper bound: Use A-bound on r at U, C-bound on s at V, get Θ(r)-Θ(s) ≤ (U-V)·δ
4. For lower bound: Use C-bound on r at V+Δ, A-bound on s at U-Δ
5. As U → ∞ with the accuracy lemma squeezing A-C gap, we get equality

This is THE key lemma for Theta'_well_defined. -/
lemma delta_shift_equiv {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (IH : GridBridge F) {d : α} (hd : ident < d)
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδA : ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u → separationStatistic R r u hu ≤ δ)
    (hδC : ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u → δ ≤ separationStatistic R r u hu)
    (hδB : ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u → separationStatistic R r u hu = δ)
    {r_old s_old : Multi k} {Δ : ℕ} (hΔ : 0 < Δ)
    (htrade : mu F r_old = op (mu F s_old) (iterate_op d Δ)) :
    R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
    R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ = (Δ : ℝ) * δ := by
  classical
  -- If d^Δ already lies on the old k-grid, the trade is internal and the result follows
  -- from additivity of Θ on the k-grid.
  by_cases hBΔ : ∃ rΔ : Multi k, rΔ ∈ extensionSetB F d Δ
  · rcases hBΔ with ⟨rΔ, hrΔB⟩
    exact delta_shift_equiv_of_B_witness R H IH hd hδ_pos hδB hΔ htrade hrΔB
  · -- External case: d^Δ is not already a μ-value on the old k-grid.
    -- If B is non-empty somewhere, scale the trade to an internal one; otherwise, this is the
    -- genuinely irrational case and needs the full K&S accuracy proof.
    set y := mu F s_old
    set z := iterate_op d Δ

    have hz_comm_y : op z y = op y z := by
      -- Use commutativity on the grid and cancel the common left factor.
      have hcomm := H.comm r_old s_old
      have h1 : op (op y z) y = op y (op y z) := by
        simpa [y, z, htrade] using hcomm
      have h2 : op y (op z y) = op y (op y z) := by
        simpa [op_assoc] using h1
      exact (op_strictMono_right y).injective h2

    by_cases hB_global : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u
    · rcases hB_global with ⟨rB, uB, huB, hrB⟩
      set n := uB
      have hn_pos : 0 < n := huB

      -- Iterate the trade n times, using commutativity between y and z.
      have htrade_iter :
          iterate_op (mu F r_old) n = op (iterate_op y n) (iterate_op z n) := by
        have h0 := congrArg (fun x : α => iterate_op x n) htrade
        -- rewrite the RHS using commutativity between y and z
        have hdist : iterate_op (op y z) n = op (iterate_op y n) (iterate_op z n) :=
          iterate_op_op_of_comm (x := y) (y := z) hz_comm_y.symm n
        simpa [y, z, hdist] using h0

      -- Move from iterates back to μ on scaled multiplicities, then reduce to the internal case.
      have hr_bridge : mu F (scaleMult n r_old) = iterate_op (mu F r_old) n := IH.bridge r_old n
      have hs_bridge : mu F (scaleMult n s_old) = iterate_op y n := by
        simpa [y] using (IH.bridge s_old n)

      have hz_iter : iterate_op z n = iterate_op d (Δ * n) := by
        simpa [z] using (iterate_op_mul d Δ n)

      have htrade_scaled :
          mu F (scaleMult n r_old) =
            op (mu F (scaleMult n s_old)) (iterate_op d (Δ * n)) := by
        -- rewrite `htrade_iter` using the bridge equations
        rw [hr_bridge, hs_bridge]
        simpa [hz_iter] using htrade_iter

      -- Build a B-witness for d^(Δ*n) by scaling the global B witness.
      have hrB_eq : mu F rB = iterate_op d n := by
        simpa [extensionSetB, Set.mem_setOf_eq, n] using hrB
      have hrΔ_eq : mu F (scaleMult Δ rB) = iterate_op d (Δ * n) := by
        have h := IH.bridge rB Δ
        -- μ(Δ·rB) = (μ rB)^Δ = (d^n)^Δ = d^(n*Δ) = d^(Δ*n)
        rw [hrB_eq] at h
        -- turn (d^n)^Δ into d^(n*Δ), then swap multiplication order
        have : iterate_op (iterate_op d n) Δ = iterate_op d (Δ * n) := by
          simpa [Nat.mul_comm] using (iterate_op_mul d n Δ)
        simpa [this] using h
      have hΔn_pos : 0 < Δ * n := Nat.mul_pos hΔ hn_pos
      have hrΔB : (scaleMult Δ rB) ∈ extensionSetB F d (Δ * n) := by
        simp [extensionSetB, Set.mem_setOf_eq, hrΔ_eq]

      have h_scaled_gap :
          R.Θ_grid ⟨mu F (scaleMult n r_old), mu_mem_kGrid F (scaleMult n r_old)⟩ -
            R.Θ_grid ⟨mu F (scaleMult n s_old), mu_mem_kGrid F (scaleMult n s_old)⟩ =
              ((Δ * n : ℕ) : ℝ) * δ :=
        delta_shift_equiv_of_B_witness R H IH hd hδ_pos hδB hΔn_pos htrade_scaled hrΔB

      -- Cancel the common scalar factor `n`.
      have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_pos)
      have hθr_scale := Theta_scaleMult R r_old n
      have hθs_scale := Theta_scaleMult R s_old n

      -- Rewrite the scaled gap in terms of θr and θs.
      have : (n : ℝ) *
            (R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
              R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩)
            = (n : ℝ) * ((Δ : ℝ) * δ) := by
        -- Expand the left using Theta_scaleMult, then simplify.
        -- First: rewrite the LHS of h_scaled_gap.
        have h_scaled_gap' :
            (n : ℝ) * R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ -
              (n : ℝ) * R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ =
                ((Δ * n : ℕ) : ℝ) * δ := by
          simpa [hθr_scale, hθs_scale] using h_scaled_gap
        -- Now factor out n on the left, and rewrite (Δ*n) on the right.
        -- `simp` turns `((Δ*n):ℕ : ℝ)` into `(Δ:ℝ) * (n:ℝ)`.
        simpa [mul_sub, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using h_scaled_gap'
      exact mul_left_cancel₀ hn_ne this

    · -- TODO(K&S Appendix A): complete the accuracy-based proof for the globally B-empty case.
        -- This is the genuinely irrational trade configuration.
        have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u := by
          intro r u hu hrB
          exact hB_global ⟨r, u, hu, hrB⟩
  
        -- k = 0 is impossible under the trade hypothesis (μ is constantly ident).
        cases k with
        | zero =>
          have hmu_r : mu F r_old = ident := by simp [mu]
          have hmu_s : mu F s_old = ident := by simp [mu]
          have hEq : ident = iterate_op d Δ := by
            simpa [y, z, hmu_r, hmu_s, op_ident_left] using htrade
          have hpos : ident < iterate_op d Δ := iterate_op_pos d hd _ hΔ
          have : False := by
            have : iterate_op d Δ < iterate_op d Δ := by simpa [hEq] using hpos
            exact (lt_irrefl _ this)
          exact False.elim this
        | succ k =>
          -- In the external B-empty case, μ(F, s_old) must be strictly above ident.
          have hy_ne : y ≠ ident := by
            intro hy_eq
            have hmu_s : mu F s_old = ident := by simpa [y] using hy_eq
            have hmu_r : mu F r_old = iterate_op d Δ := by
              simpa [y, z, hmu_s, op_ident_left] using htrade
            have hrB : r_old ∈ extensionSetB F d Δ := by
              simp [extensionSetB, Set.mem_setOf_eq, hmu_r]
            exact hBΔ ⟨r_old, hrB⟩
          have hy_pos : ident < y :=
            lt_of_le_of_ne (ident_le y) (Ne.symm hy_ne)
  
          -- Abbreviate the Θ-values on the k-grid.
          set θr := R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩
          set θs := R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩
  
          -- Show the Θ-gap is arbitrarily close to Δ·δ by scaling and bracketing within a 1-step window.
          have h_close : ∀ ε > 0, |(θr - θs) - (Δ : ℝ) * δ| < ε := by
            intro ε hε
  
            -- Choose n large enough that d < y^n and δ/ε < n.
            obtain ⟨n_d, hn_d⟩ := bounded_by_iterate y hy_pos d
            obtain ⟨N, hN⟩ := exists_nat_gt (δ / ε)
            let n1 : ℕ := Nat.succ N
            let n : ℕ := max n_d n1
            have hn_pos : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) (le_max_right _ _)
  
            have hn_ge_n1 : n1 ≤ n := le_max_right _ _
            have hn1_gt : δ / ε < (n1 : ℝ) := by
              have hle : (N : ℝ) ≤ (n1 : ℝ) := by exact_mod_cast Nat.le_succ N
              exact lt_of_lt_of_le hN hle
            have hratio : δ / ε < (n : ℝ) := by
              have hn1_le : (n1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_n1
              exact lt_of_lt_of_le hn1_gt hn1_le
            have hε_ne : (ε : ℝ) ≠ 0 := ne_of_gt hε
            have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn_pos
            have hδ_div : δ / (n : ℝ) < ε := by
              have h_mul : (δ / ε) * ε < (n : ℝ) * ε :=
                mul_lt_mul_of_pos_right hratio hε
              have hleft : (δ / ε) * ε = δ := by field_simp [hε_ne]
              have hδ_lt : δ < (n : ℝ) * ε := by simpa [hleft] using h_mul
              -- turn δ < n*ε into δ/n < ε
              exact (div_lt_iff₀ hn_real).2 (by simpa [mul_comm] using hδ_lt)
  
            have hd_lt_y_iter : d < iterate_op y n := by
              have hn_d_le : n_d ≤ n := le_max_left _ _
              have hmono : Monotone (iterate_op y) := (iterate_op_strictMono y hy_pos).monotone
              exact lt_of_lt_of_le hn_d (hmono hn_d_le)
  
            -- Scale the trade by n and rewrite it as a trade on μ-values.
            have htrade_iter :
                iterate_op (mu F r_old) n = op (iterate_op y n) (iterate_op z n) := by
              have h0 := congrArg (fun x : α => iterate_op x n) htrade
              have hdist :
                  iterate_op (op y z) n = op (iterate_op y n) (iterate_op z n) :=
                iterate_op_op_of_comm (x := y) (y := z) hz_comm_y.symm n
              simpa [y, z, hdist] using h0
            have hr_bridge : mu F (scaleMult n r_old) = iterate_op (mu F r_old) n :=
              IH.bridge r_old n
            have hs_bridge : mu F (scaleMult n s_old) = iterate_op y n := by
              simpa [y] using (IH.bridge s_old n)
            have hz_iter : iterate_op z n = iterate_op d (Δ * n) := by
              simpa [z] using (iterate_op_mul d Δ n)
            have htrade_scaled :
                mu F (scaleMult n r_old) =
                  op (mu F (scaleMult n s_old)) (iterate_op d (Δ * n)) := by
              rw [hr_bridge, hs_bridge]
              simpa [hz_iter] using htrade_iter
  
            -- Define the scaled grid points for r_old and s_old.
            set rN : Multi (k + 1) := scaleMult n r_old
            set sN : Multi (k + 1) := scaleMult n s_old
            have hmu_sN : mu F sN = iterate_op y n := by
              simpa [sN] using hs_bridge
            have hmu_rN : mu F rN = op (mu F sN) (iterate_op d (Δ * n)) := by
              simpa [rN, sN] using htrade_scaled
  
            -- Find the crossing index m such that d^m < μ(sN) < d^(m+1).
            obtain ⟨K, hK⟩ := bounded_by_iterate d hd (mu F sN)
            let P : ℕ → Prop := fun u => iterate_op d u ≤ mu F sN
            have hP0 : P 0 := by
              simp [P, iterate_op_zero]
              exact ident_le _
            have hcross := findGreatest_crossing (P := P) K hP0
            set m : ℕ := Nat.findGreatest P K
            have hmP : P m := by simpa [m] using hcross.1
            have hm_le_K : m ≤ K := by simpa [m] using hcross.2.1
            have hmax : ∀ k, m < k → k ≤ K → ¬ P k := by
              simpa [m] using hcross.2.2
            have hPK_false : ¬ P K := by
              -- From μ(sN) < d^K, we get ¬(d^K ≤ μ(sN)).
              have : mu F sN < iterate_op d K := by simpa [P] using hK
              exact not_le_of_gt this
            have hm_lt_K : m < K :=
              lt_of_le_of_ne hm_le_K (by
                intro hm_eq
                apply hPK_false
                simpa [hm_eq] using hmP)
            have hm1_le_K : m + 1 ≤ K := Nat.succ_le_of_lt hm_lt_K
            have h_notP_m1 : ¬ P (m + 1) :=
              hmax (m + 1) (Nat.lt_succ_self m) hm1_le_K
            have hmu_sN_lt : mu F sN < iterate_op d (m + 1) :=
              lt_of_not_ge h_notP_m1
  
            -- Ensure m > 0: since d < μ(sN), we must have d^1 ≤ μ(sN), hence 1 ≤ m.
            have hP1 : P 1 := by
              have : d ≤ mu F sN := by
                -- d < y^n = μ(sN)
                have : d < mu F sN := by simpa [hmu_sN] using hd_lt_y_iter
                exact le_of_lt this
              simpa [P, iterate_op_one] using this
            have hm_pos : 0 < m := by
              by_contra hm0
              have hm_eq0 : m = 0 := Nat.eq_zero_of_not_pos hm0
              -- contradict maximality if m = 0 and P 1 holds
              have h1_le_K : 1 ≤ K := by
                -- since d < μ(sN) < d^K, we must have 1 < K
                have hd_lt : iterate_op d 1 < mu F sN := by
                  simpa [iterate_op_one, hmu_sN] using hd_lt_y_iter
                have : 1 < K := by
                  -- If K ≤ 1 then μ(sN) < d^K ≤ d^1 contradicts d^1 < μ(sN).
                  by_contra hK1
                  have hK_le1 : K ≤ 1 := le_of_not_gt hK1
                  have hK_le' : iterate_op d K ≤ iterate_op d 1 :=
                    (iterate_op_strictMono d hd).monotone hK_le1
                  have hmu_lt : mu F sN < iterate_op d 1 := lt_of_lt_of_le hK hK_le'
                  have : iterate_op d 1 < iterate_op d 1 := lt_trans hd_lt hmu_lt
                  exact (lt_irrefl _ this)
                exact le_of_lt this
              have h_notP1 : ¬ P 1 := by
                have hm_lt_1 : m < 1 := by simpa [hm_eq0] using (Nat.succ_pos 0)
                exact hmax 1 hm_lt_1 h1_le_K
              exact h_notP1 hP1
  
            -- Use global B-emptiness to rule out equality at level m and obtain strictness.
            have hm_ne : mu F sN ≠ iterate_op d m := by
              intro hEq
              have : sN ∈ extensionSetB F d m := by
                simp [extensionSetB, Set.mem_setOf_eq, hEq]
              exact hB_empty sN m hm_pos this
            have hdm_lt : iterate_op d m < mu F sN :=
              lt_of_le_of_ne hmP (Ne.symm hm_ne)
  
            have hs_in_C : sN ∈ extensionSetC F d m := by
              simp [extensionSetC, Set.mem_setOf_eq, hdm_lt]
            have hs_in_A : sN ∈ extensionSetA F d (m + 1) := by
              simp [extensionSetA, Set.mem_setOf_eq, hmu_sN_lt]
  
            -- Shift the bounds through the scaled trade to bracket μ(rN).
            have hdmn_lt : iterate_op d (m + Δ * n) < mu F rN := by
              have h1 : op (iterate_op d m) (iterate_op d (Δ * n)) < op (mu F sN) (iterate_op d (Δ * n)) :=
                op_strictMono_left (iterate_op d (Δ * n)) hdm_lt
              have hpow : op (iterate_op d m) (iterate_op d (Δ * n)) = iterate_op d (m + Δ * n) := by
                simpa using (iterate_op_add d m (Δ * n))
              simpa [hmu_rN, hpow] using h1
            have hdmn1_gt : mu F rN < iterate_op d (m + 1 + Δ * n) := by
              have h1 : op (mu F sN) (iterate_op d (Δ * n)) < op (iterate_op d (m + 1)) (iterate_op d (Δ * n)) :=
                op_strictMono_left (iterate_op d (Δ * n)) hmu_sN_lt
              have hpow : op (iterate_op d (m + 1)) (iterate_op d (Δ * n)) = iterate_op d (m + 1 + Δ * n) := by
                simpa using (iterate_op_add d (m + 1) (Δ * n))
              simpa [hmu_rN, hpow] using h1
  
            have hr_in_C : rN ∈ extensionSetC F d (m + Δ * n) := by
              simp [extensionSetC, Set.mem_setOf_eq, hdmn_lt]
            have hr_in_A : rN ∈ extensionSetA F d (m + 1 + Δ * n) := by
              simp [extensionSetA, Set.mem_setOf_eq, hdmn1_gt]
  
            -- Convert A/C bounds into Θ bounds for the scaled points.
            have hm1_pos : 0 < m + 1 := Nat.succ_pos m
            have hmn_pos : 0 < m + Δ * n := lt_of_lt_of_le hm_pos (Nat.le_add_right _ _)
            have hmn1_pos : 0 < m + 1 + Δ * n := lt_of_lt_of_le hm1_pos (Nat.le_add_right _ _)
  
            have hsA_bound : separationStatistic R sN (m + 1) hm1_pos ≤ δ :=
              hδA sN (m + 1) hm1_pos hs_in_A
            have hsC_bound : δ ≤ separationStatistic R sN m hm_pos :=
              hδC sN m hm_pos hs_in_C
            have hrA_bound : separationStatistic R rN (m + 1 + Δ * n) hmn1_pos ≤ δ :=
              hδA rN (m + 1 + Δ * n) hmn1_pos hr_in_A
            have hrC_bound : δ ≤ separationStatistic R rN (m + Δ * n) hmn_pos :=
              hδC rN (m + Δ * n) hmn_pos hr_in_C
  
            have hθs_upper : R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ ≤ (m + 1 : ℝ) * δ := by
              have hm1_real : 0 < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hm1_pos
              unfold separationStatistic at hsA_bound
              have h := (div_le_iff₀ hm1_real).1 hsA_bound
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
            have hθs_lower : (m : ℝ) * δ ≤ R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ := by
              have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm_pos
              unfold separationStatistic at hsC_bound
              have h := (le_div_iff₀ hm_real).1 hsC_bound
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
            have hθr_upper :
                R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ ≤ (m + 1 + Δ * n : ℝ) * δ := by
              have hmn1_real : 0 < ((m + 1 + Δ * n : ℕ) : ℝ) := by exact_mod_cast hmn1_pos
              unfold separationStatistic at hrA_bound
              have h := (div_le_iff₀ hmn1_real).1 hrA_bound
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
            have hθr_lower :
                (m + Δ * n : ℝ) * δ ≤ R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ := by
              have hmn_real : 0 < ((m + Δ * n : ℕ) : ℝ) := by exact_mod_cast hmn_pos
              unfold separationStatistic at hrC_bound
              have h := (le_div_iff₀ hmn_real).1 hrC_bound
              simpa [mul_comm, mul_left_comm, mul_assoc] using h
  
            -- Use Θ scaling: Θ(rN) = n·θr and Θ(sN) = n·θs.
            have hθr_scale : R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ = n * θr := by
              simpa [rN, θr] using (Theta_scaleMult R r_old n)
            have hθs_scale : R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ = n * θs := by
              simpa [sN, θs] using (Theta_scaleMult R s_old n)
  
            -- Bracket n*(θr-θs) within (Δ*n ± 1)·δ.
            have h_gap_lower : ((Δ * n : ℕ) : ℝ) * δ - δ ≤ (n : ℝ) * (θr - θs) := by
              have h1 : (m + Δ * n : ℝ) * δ - (m + 1 : ℝ) * δ ≤
                  R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ - R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ := by
                linarith [hθr_lower, hθs_upper]
              have hm_cancel :
                  (m + Δ * n : ℝ) * δ - (m + 1 : ℝ) * δ =
                    ((Δ * n : ℕ) : ℝ) * δ - δ := by
                simp [Nat.cast_add, Nat.cast_mul, sub_eq_add_neg, add_mul, mul_add, mul_assoc,
                  mul_left_comm, mul_comm]
                ring
              have h2 :
                  R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ - R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ =
                    (n : ℝ) * (θr - θs) := by
                simp [hθr_scale, hθs_scale, mul_sub, sub_mul, mul_assoc, mul_left_comm, mul_comm]
              simpa [hm_cancel, h2] using h1
            have h_gap_upper : (n : ℝ) * (θr - θs) ≤ ((Δ * n : ℕ) : ℝ) * δ + δ := by
              have h1 :
                  R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ - R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ ≤
                    (m + 1 + Δ * n : ℝ) * δ - (m : ℝ) * δ := by
                linarith [hθr_upper, hθs_lower]
              have hm_cancel :
                  (m + 1 + Δ * n : ℝ) * δ - (m : ℝ) * δ =
                    ((Δ * n : ℕ) : ℝ) * δ + δ := by
                simp [Nat.cast_add, Nat.cast_mul, sub_eq_add_neg, add_mul, mul_add, mul_assoc,
                  mul_left_comm, mul_comm]
                ring
              have h2 :
                  R.Θ_grid ⟨mu F rN, mu_mem_kGrid F rN⟩ - R.Θ_grid ⟨mu F sN, mu_mem_kGrid F sN⟩ =
                    (n : ℝ) * (θr - θs) := by
                simp [hθr_scale, hθs_scale, mul_sub, sub_mul, mul_assoc, mul_left_comm, mul_comm]
              have h3 : (n : ℝ) * (θr - θs) ≤ (m + 1 + Δ * n : ℝ) * δ - (m : ℝ) * δ := by
                simpa [h2] using h1
              simpa [hm_cancel] using h3
  
            -- Convert the window to a bound on |(θr-θs) - Δ·δ|.
            have hn_real' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
            have hΔn_cast : ((Δ * n : ℕ) : ℝ) = (n : ℝ) * (Δ : ℝ) := by
              simp [Nat.cast_mul, Nat.mul_comm, mul_assoc, mul_left_comm, mul_comm]
            have h_abs_scaled :
                |(n : ℝ) * ((θr - θs) - (Δ : ℝ) * δ)| ≤ δ := by
              have h_lower' :
                  -δ ≤ (n : ℝ) * ((θr - θs) - (Δ : ℝ) * δ) := by
                -- Rearrange the lower window: (Δ*n)*δ ≤ δ + n*(θr-θs)
                have h1 : ((Δ * n : ℕ) : ℝ) * δ ≤ δ + (n : ℝ) * (θr - θs) := by
                  linarith [h_gap_lower]
                -- Move (Δ*n)*δ to the right, then rewrite as n*((θr-θs) - Δ*δ).
                have h2 : -δ ≤ (n : ℝ) * (θr - θs) - ((Δ * n : ℕ) : ℝ) * δ := by
                  -- `-δ ≤ A - B` iff `B ≤ A + δ`
                  exact (neg_le_sub_iff_le_add).2 (by simpa [add_comm, add_left_comm, add_assoc] using h1)
                simpa [mul_sub, sub_mul, hΔn_cast, mul_assoc, mul_left_comm, mul_comm] using h2
              have h_upper' :
                  (n : ℝ) * ((θr - θs) - (Δ : ℝ) * δ) ≤ δ := by
                -- Rearrange the upper window: n*(θr-θs) ≤ (Δ*n)*δ + δ
                have h1 : (n : ℝ) * (θr - θs) ≤ ((Δ * n : ℕ) : ℝ) * δ + δ := by
                  linarith [h_gap_upper]
                -- `A - B ≤ δ` iff `A ≤ δ + B`
                have h2 : (n : ℝ) * (θr - θs) - ((Δ * n : ℕ) : ℝ) * δ ≤ δ :=
                  (sub_le_iff_le_add).2 (by simpa [add_assoc, add_left_comm, add_comm] using h1)
                simpa [mul_sub, sub_mul, hΔn_cast, mul_assoc, mul_left_comm, mul_comm] using h2
              exact (abs_le).2 ⟨h_lower', h_upper'⟩
  
            have h_abs :
                |(θr - θs) - (Δ : ℝ) * δ| ≤ δ / (n : ℝ) := by
              have hn_abs : |(n : ℝ)| = (n : ℝ) :=
                abs_of_nonneg (by exact_mod_cast (Nat.zero_le n))
              have hn_abs_pos : 0 < |(n : ℝ)| := by simpa [hn_abs] using hn_real'
              have : |(n : ℝ)| * |(θr - θs) - (Δ : ℝ) * δ| ≤ δ := by
                simpa [abs_mul, hn_abs, mul_assoc, mul_left_comm, mul_comm] using h_abs_scaled
              have : |(θr - θs) - (Δ : ℝ) * δ| ≤ δ / |(n : ℝ)| :=
                (le_div_iff₀ hn_abs_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using this)
              simpa [hn_abs, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  
            exact lt_of_le_of_lt h_abs hδ_div
  
          -- Conclude equality by the standard "arbitrarily small absolute difference" argument.
          have h_eq : θr - θs = (Δ : ℝ) * δ := by
            by_contra hne
            have hpos : 0 < |(θr - θs) - (Δ : ℝ) * δ| := by
              apply abs_pos.mpr
              intro h0
              apply hne
              exact (sub_eq_zero.mp h0)
            have h_small := h_close (|(θr - θs) - (Δ : ℝ) * δ| / 2) (half_pos hpos)
            have h_half : |(θr - θs) - (Δ : ℝ) * δ| / 2 < |(θr - θs) - (Δ : ℝ) * δ| :=
              half_lt_self hpos
            exact (lt_irrefl _ (lt_trans h_small h_half))
  
          simpa [θr, θs] using h_eq

/- Old proof attempt (kept for reference while refactoring):
  -- Define θr := Θ(r_old) and θs := Θ(s_old) for brevity
  set θr := R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ with hθr
  set θs := R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ with hθs

  /-
  **UNIFORM PROOF STRATEGY** (GPT-5.1 Pro / K&S Appendix A):

  The key insight is the SHIFT EQUIVALENCE:
    r_old ∈ A(U)  ↔  s_old ∈ A(U-Δ)   [for U > Δ]
    r_old ∈ C(V)  ↔  s_old ∈ C(V-Δ)   [for V > Δ]

  This means the A/C statistics are related:
    stat(r, U) = Θ(r)/U  and  stat(s, U-Δ) = Θ(s)/(U-Δ)

  For the upper bound:
    - Use A-bound on r at level U+Δ: Θ(r)/(U+Δ) ≤ δ
    - Use C-bound on s at level V: Θ(s)/V ≥ δ
    - Subtract: Θ(r) - Θ(s) ≤ (U+Δ)·δ - V·δ = (U+Δ-V)·δ
    - As U → ∞ with V → U (via accuracy), we get (U+Δ-V) → Δ

  For the lower bound:
    - Use C-bound on r at level V+Δ: Θ(r)/(V+Δ) ≥ δ
    - Use A-bound on s at level U: Θ(s)/U ≤ δ
    - Subtract: Θ(r) - Θ(s) ≥ (V+Δ)·δ - U·δ = (V+Δ-U)·δ
    - As U → V (via accuracy), we get (V+Δ-U) → Δ

  The accuracy lemma ensures that for any ε > 0, we can find U, V with the
  A-C gap for s_old being < ε. In the limit, this forces equality.
  -/

  -- We prove equality by showing both ≤ and ≥
  apply le_antisymm

  · -- Upper bound: θr - θs ≤ Δ * δ

    -- Use Archimedean to find U such that s_old ∈ A(U)
    obtain ⟨U, hU⟩ := bounded_by_iterate d hd (mu F s_old)
    have hs_in_A : s_old ∈ extensionSetA F d U := hU
    have hU_pos : 0 < U := by
      by_contra h; push_neg at h; interval_cases U
      simp only [iterate_op_zero] at hU
      exact not_lt.mpr (ident_le (mu F s_old)) hU

    -- By shift lemma: s_old ∈ A(U) → r_old ∈ A(U+Δ)
    have hr_in_A : r_old ∈ extensionSetA F d (U + Δ) := trade_shift_A hd hΔ htrade hs_in_A
    have hUΔ_pos : 0 < U + Δ := by omega

    -- A-bounds give upper bounds on θr and θs
    have hr_A_bound : separationStatistic R r_old (U + Δ) hUΔ_pos ≤ δ :=
      hδA r_old (U + Δ) hUΔ_pos hr_in_A
    have hs_A_bound : separationStatistic R s_old U hU_pos ≤ δ :=
      hδA s_old U hU_pos hs_in_A

    have hθr_upper : θr ≤ (U + Δ) * δ := by
      have h2 : ((U + Δ) : ℝ) > 0 := by positivity
      -- Unfold separationStatistic: θr / (U + Δ) ≤ δ
      simp only [separationStatistic] at hr_A_bound
      -- Convert ↑(U + Δ) to ↑U + ↑Δ for div_le_iff₀
      push_cast at hr_A_bound h2
      rw [div_le_iff₀ h2] at hr_A_bound
      -- Now hr_A_bound : R.Θ_grid ... ≤ δ * (U + Δ), goal: θr ≤ (U + Δ) * δ
      rw [mul_comm] at hr_A_bound
      exact hr_A_bound

    -- For the upper bound Θ(r) - Θ(s) ≤ Δ·δ, we need a LOWER bound on Θ(s)
    -- This comes from C-membership. Find V such that s_old ∈ C(V).

    -- Case split: does s_old have a C-level (i.e., ident < mu F s_old)?
    by_cases hs_ident : mu F s_old = ident

    · -- s_old = ident case: This means r_old is a B-witness!
      -- From htrade: μ_F(r_old) = ident ⊕ d^Δ = d^Δ
      -- So r_old ∈ B(Δ), and hδB gives us θr/Δ = δ exactly.

      have hθs_zero : θs = 0 := by
        have h_mem : (⟨mu F s_old, mu_mem_kGrid F s_old⟩ : kGrid F) =
                     ⟨ident, ident_mem_kGrid F⟩ := by
          ext; exact hs_ident
        simp only [hθs, h_mem, R.ident_eq_zero]

      have hr_eq_dΔ : mu F r_old = iterate_op d Δ := by rw [htrade, hs_ident, op_ident_left]

      -- r_old ∈ B(Δ) because μ_F(r_old) = d^Δ
      have hr_in_B : r_old ∈ extensionSetB F d Δ := by
        simp only [extensionSetB, Set.mem_setOf_eq, hr_eq_dΔ]

      -- By hδB: stat(r_old, Δ) = δ, i.e., θr/Δ = δ
      have hstat_B : separationStatistic R r_old Δ hΔ = δ := hδB r_old Δ hΔ hr_in_B
      simp only [separationStatistic] at hstat_B

      -- So θr = Δ · δ
      have hθr_eq : θr = Δ * δ := by
        have hΔ_pos : (Δ : ℝ) > 0 := by positivity
        have hΔ_ne : (Δ : ℝ) ≠ 0 := by linarith
        field_simp [hΔ_ne] at hstat_B
        linarith

      -- Conclude: θr - θs = Δ·δ - 0 = Δ·δ
      rw [hθs_zero, sub_zero]
      exact le_of_eq hθr_eq

    · -- s_old > ident case: Use B-witness structure and R.add
      have hs_pos : ident < mu F s_old := by
        cases' (ident_le (mu F s_old)).lt_or_eq with h h
        · exact h
        · exact absurd h.symm hs_ident

      /-
      Key insight: htrade says μ_F(r_old) = μ_F(s_old) ⊕ d^Δ.

      Case A: B(Δ) non-empty (d^Δ ∈ kGrid F)
        Then ∃ r_B with μ_F(r_B) = d^Δ, and htrade becomes:
        μ_F(r_old) = μ_F(s_old) ⊕ μ_F(r_B)
        By R.add (additivity on kGrid): θr = θs + Θ(r_B) = θs + Δ·δ
        So θr - θs = Δ·δ ✓

      Case B: B(Δ) empty (d^Δ ∉ kGrid F)
        The trade μ_F(r_old) = μ_F(s_old) ⊕ d^Δ with both sides in kGrid F
        requires a "coincidence" - the product lands back in kGrid F despite
        d^Δ not being there. This is *not guaranteed* and depends on extra algebraic
        relations in the model; some models forbid it, others may allow it.
        For this case, use the accuracy lemma to squeeze bounds.
      -/

      /-
      **FLOOR-BASED ACCURACY APPROACH** (GPT-5.1 Pro / K&S Appendix A):

      Let V = ⌊θs/δ⌋. Then:
        - V*δ ≤ θs < (V+1)*δ
        - By shift lemmas: (V+Δ)*δ ≤ θr < (V+Δ+1)*δ
        - This gives: (Δ-1)*δ < θr - θs < (Δ+1)*δ (width-2δ bracket)

      For EXACT equality θr - θs = Δ*δ, we need one of:
        (a) s_old ∈ B(V) for some V > 0 (then θs = V*δ exactly, and by shift r_old ∈ B(V+Δ))
        (b) The K&S accuracy argument: δ is the UNIQUE value consistent with ALL A/C bounds

      Case (b) requires the K&S accuracy argument. Case (a) reduces to the s_old = ident
      pattern when we can find a B-witness.

      **STRUCTURAL ISSUE**: The separation properties use mu_scale_eq_iterate which is FALSE
      in general without commutativity (see `Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling/ToyFreeMonoid2.lean`).
      The correct approach is:
        1. For k=1 (single atom): mu_scale_eq_iterate holds trivially
        2. For k→k+1: Use inductive hypothesis that k-atom grid is commutative,
           which makes mu_scale_eq_iterate valid for k atoms
      -/

      -- Case split: Is s_old a B-witness for some level V > 0?
      -- If yes: exact equality via hδB chain
      -- If no: pure A/C case, requires K&S accuracy lemma

      by_cases hB_witness : ∃ V : ℕ, 0 < V ∧ s_old ∈ extensionSetB F d V

      · -- Case A: s_old ∈ B(V) for some V > 0 - Use B-witness chain
        obtain ⟨V, hV_pos, hs_in_B⟩ := hB_witness

        -- From B-membership: mu F s_old = d^V
        have hs_eq_dV : mu F s_old = iterate_op d V := by
          simpa [extensionSetB] using hs_in_B

        -- By htrade: mu F r_old = d^V ⊕ d^Δ = d^{V+Δ}
        have hr_eq_dVΔ : mu F r_old = iterate_op d (V + Δ) := by
          rw [htrade, hs_eq_dV, ← iterate_op_add d V Δ]

        -- So r_old ∈ B(V+Δ)
        have hr_in_B : r_old ∈ extensionSetB F d (V + Δ) := by
          simp only [extensionSetB, Set.mem_setOf_eq, hr_eq_dVΔ]

        have hVΔ_pos : 0 < V + Δ := by omega

        -- From hδB: θs = V*δ and θr = (V+Δ)*δ
        have hstat_s : separationStatistic R s_old V hV_pos = δ := hδB s_old V hV_pos hs_in_B
        have hstat_r : separationStatistic R r_old (V + Δ) hVΔ_pos = δ := hδB r_old (V + Δ) hVΔ_pos hr_in_B

        simp only [separationStatistic] at hstat_s hstat_r

        have hθs_eq : θs = V * δ := by
          have hV_pos_real : (V : ℝ) > 0 := Nat.cast_pos.mpr hV_pos
          have hV_ne : (V : ℝ) ≠ 0 := by linarith
          field_simp [hV_ne] at hstat_s
          linarith

        have hθr_eq : θr = (V + Δ) * δ := by
          have hVΔ_pos_real : (V : ℝ) + (Δ : ℝ) > 0 := by positivity
          have hVΔ_ne : (V : ℝ) + (Δ : ℝ) ≠ 0 := by linarith
          simp only [Nat.cast_add] at hstat_r
          field_simp [hVΔ_ne] at hstat_r
          linarith

        -- Conclude: θr - θs = (V+Δ)*δ - V*δ = Δ*δ
        rw [hθr_eq, hθs_eq]
        ring_nf
        -- Goal: V*δ + Δ*δ - V*δ ≤ Δ*δ, which simplifies to Δ*δ ≤ Δ*δ
        linarith

      · -- Case B: No B-witness for s_old - Pure A/C case
        --
        -- **KEY INSIGHT** (GPT-5 Pro): If B is globally empty, use accuracy_lemma.
        -- If B is non-empty but s_old isn't in B, this is a structural contradiction
        -- in many algebras (the trade equation forces s_old to be a B-witness).
        --
        push_neg at hB_witness
        -- hB_witness : ∀ V, 0 < V → s_old ∉ extensionSetB F d V

        -- Check if B is globally empty
        by_cases hB_global : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u

        · -- B is globally non-empty, but s_old ∉ B
          -- Key insight: The trade μ r_old = μ s_old ⊕ d^Δ combined with
          -- B non-empty implies d^Δ is in the k-grid (as a μ value).
          --
          -- Proof strategy:
          -- 1. Get B-witness (rB, uB) with μ rB = d^{uB}
          -- 2. Show d^Δ ∈ k-grid: It must equal some μ rΔ (otherwise trade impossible)
          -- 3. Use R.add: θr = θs + Θ(rΔ) = θs + Δ·δ

          obtain ⟨rB, uB, huB, hrB_in_B⟩ := hB_global
          have hrB_eq : mu F rB = iterate_op d uB := hrB_in_B

          -- The trade says: μ r_old = μ s_old ⊕ d^Δ
          -- Since μ r_old ∈ k-grid and μ s_old ∈ k-grid, we need d^Δ to be
          -- compatible with the k-grid structure.

          -- Case split: Is d^Δ itself in B(Δ)?
          by_cases hdΔ_in_B : ∃ rΔ : Multi k, mu F rΔ = iterate_op d Δ

          · -- d^Δ is in the k-grid as μ rΔ = d^Δ
            obtain ⟨rΔ, hrΔ_eq⟩ := hdΔ_in_B

            -- rΔ ∈ B(Δ)
            have hrΔ_in_B : rΔ ∈ extensionSetB F d Δ := by
              simp only [extensionSetB, Set.mem_setOf_eq, hrΔ_eq]

            -- From hδB: Θ(rΔ)/Δ = δ, so Θ(rΔ) = Δ·δ
            have hΘrΔ : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ = Δ * δ := by
              have hstat := hδB rΔ Δ hΔ hrΔ_in_B
              simp only [separationStatistic] at hstat
              have hΔ_pos : (0 : ℝ) < (Δ : ℕ) := Nat.cast_pos.mpr hΔ
              have hΔ_ne : (Δ : ℝ) ≠ 0 := by linarith
              field_simp [hΔ_ne] at hstat
              linarith

            -- The trade: mu F r_old = op (mu F s_old) (mu F rΔ)
            have htrade' : mu F r_old = op (mu F s_old) (mu F rΔ) := by
              rw [hrΔ_eq]; exact htrade

            -- By mu_add_of_comm: op (mu F s_old) (mu F rΔ) = mu F (s_old + rΔ)
            have h_add : op (mu F s_old) (mu F rΔ) = mu F (s_old + rΔ) :=
              (mu_add_of_comm H s_old rΔ).symm

            -- So mu F r_old = mu F (s_old + rΔ)
            have h_mu_eq : mu F r_old = mu F (s_old + rΔ) := by rw [htrade', h_add]

            -- Since Θ is defined on α (not Multi k), equal μ values give equal Θ values
            have h_Θ_eq : R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ =
                          R.Θ_grid ⟨mu F (s_old + rΔ), mu_mem_kGrid F (s_old + rΔ)⟩ := by
              congr 1
              ext; exact h_mu_eq

            -- By R.add: Θ(μ(s_old + rΔ)) = Θ(μ s_old) + Θ(μ rΔ)
            have h_R_add := R.add s_old rΔ
            -- h_R_add : Θ(μ(s_old + rΔ)) = Θ(μ s_old) + Θ(μ rΔ)

            -- Combine: θr = Θ(μ r_old) = Θ(μ(s_old + rΔ)) = θs + Θ(rΔ) = θs + Δ·δ
            have hθr_eq_sum : θr = θs + Δ * δ := by
              calc θr = R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ := rfl
                _ = R.Θ_grid ⟨mu F (s_old + rΔ), mu_mem_kGrid F (s_old + rΔ)⟩ := h_Θ_eq
                _ = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ +
                    R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ := h_R_add
                _ = θs + Δ * δ := by rw [hΘrΔ]
            linarith

          · -- d^Δ is NOT in the k-grid - Show this case is impossible
            -- If d^Δ ∉ k-grid, then the trade μ r_old = μ s_old ⊕ d^Δ implies
            -- that op (μ s_old) (d^Δ) lands in the k-grid despite d^Δ not being there.
            --
            -- With B non-empty, the k-grid contains d^{n·uB} for all n.
            -- The key constraint: for the trade to hold, μ s_old and d^Δ must
            -- "align" to produce a k-grid element.
            --
            -- This requires careful analysis of the grid structure.
            -- For now, we use the A/C bounds to show the upper bound holds anyway.
            --
            -- The strict bounds give: (Δ-1)·δ < θr - θs < (Δ+1)·δ
            -- For θr - θs ≤ Δ·δ, we need to show θr - θs < (Δ+1)·δ implies ≤ Δ·δ
            -- when grid values are properly constrained.
            --
            -- TODO: This case may actually be vacuous (impossible) - needs proof.
            -- For now, use the floor-bracket upper bound.

            -- Use Archimedean to find crossing levels for s_old
            obtain ⟨Us, hUs⟩ := bounded_by_iterate d hd (mu F s_old)
            have hs_in_A : s_old ∈ extensionSetA F d Us := hUs
            have hUs_pos : 0 < Us := by
              by_contra h; push_neg at h; interval_cases Us
              simp only [iterate_op_zero] at hUs
              exact not_lt.mpr (ident_le (mu F s_old)) hUs

            -- By trade_shift_A: r_old ∈ A(Us + Δ)
            have hr_in_A : r_old ∈ extensionSetA F d (Us + Δ) := trade_shift_A hd hΔ htrade hs_in_A

            -- A-bounds (strict because B non-empty):
            -- stat(s_old, Us) < stat(rB, uB) = δ ⟹ θs < Us·δ
            -- stat(r_old, Us+Δ) < stat(rB, uB) = δ ⟹ θr < (Us+Δ)·δ

            -- First establish that stat(rB, uB) = δ
            have hδ_eq_statB : δ = separationStatistic R rB uB huB := by
              exact (hδB rB uB huB hrB_in_B).symm

            have hθs_A : θs < Us * δ := by
              have hstat := separation_property_A_B R H hd hUs_pos hs_in_A huB hrB_in_B
              simp only [separationStatistic] at hstat
              have hUs_pos_real : (0 : ℝ) < Us := Nat.cast_pos.mpr hUs_pos
              rw [div_lt_iff₀ hUs_pos_real] at hstat
              -- hstat : θs < stat(rB, uB) * Us = (Θ(rB)/uB) * Us
              -- Need: θs < Us * δ
              have hstat' := hδB rB uB huB hrB_in_B
              simp only [separationStatistic] at hstat'
              -- hstat' : Θ(rB) / uB = δ
              rw [hstat'] at hstat
              linarith

            have hUsΔ_pos : 0 < Us + Δ := by omega
            have hθr_A : θr < (Us + Δ) * δ := by
              have hstat := separation_property_A_B R H hd hUsΔ_pos hr_in_A huB hrB_in_B
              simp only [separationStatistic] at hstat
              have hUsΔ_pos_real : (0 : ℝ) < (Us + Δ : ℕ) := Nat.cast_pos.mpr hUsΔ_pos
              rw [div_lt_iff₀ hUsΔ_pos_real] at hstat
              simp only [Nat.cast_add] at hstat
              -- hstat : θr < stat(rB, uB) * (Us+Δ)
              have hstat' := hδB rB uB huB hrB_in_B
              simp only [separationStatistic] at hstat'
              rw [hstat'] at hstat
              linarith

            -- **FLOOR-BRACKET CLOSURE** using ZQuantized:
            -- Goal: θr - θs ≤ Δ * δ
            --
            -- Strategy:
            -- 1. Establish θs ≥ (Us - 1) * δ via trichotomy on mu F s_old vs d^{Us-1}
            -- 2. Combine with hθr_A to get θr - θs < (Δ + 1) * δ
            -- 3. Use ZQuantized_diff: θr - θs = m * δ for some integer m
            -- 4. From m * δ < (Δ + 1) * δ and δ > 0, get m ≤ Δ
            -- 5. Hence θr - θs = m * δ ≤ Δ * δ

            -- Step 1: Find the MINIMAL level L such that s_old ∈ A(L)
            -- Using Nat.find to get minimality, which gives L-1 as a lower bound level
            classical
            let P : ℕ → Prop := fun n => mu F s_old < iterate_op d n
            have hex : ∃ n, P n := ⟨Us, hs_in_A⟩
            let L := Nat.find hex
            have hL_A : s_old ∈ extensionSetA F d L := Nat.find_spec hex
              have hL_pos : 0 < L := by
                by_contra h; push_neg at h; have hL0 : L = 0 := by omega
                have hL_A0 : s_old ∈ extensionSetA F d 0 := by
                  simpa [hL0] using hL_A
                have hmu_lt_ident : mu F s_old < ident := by
                  simpa [extensionSetA, iterate_op_zero] using hL_A0
                exact absurd hmu_lt_ident (not_lt.mpr (ident_le (mu F s_old)))
            have hL_min : ∀ k, 0 < k → k < L → ¬ P k := fun k _ hkL => Nat.find_min hex hkL

            -- By shift lemma, r_old ∈ A(L + Δ)
            have hr_in_A_L : r_old ∈ extensionSetA F d (L + Δ) := trade_shift_A hd hΔ htrade hL_A
            have hLΔ_pos : 0 < L + Δ := by omega

            -- A-bounds with minimal level L:
            have hθr_A_L : θr < (L + Δ) * δ := by
              have hstat := separation_property_A_B R H hd hLΔ_pos hr_in_A_L huB hrB_in_B
              simp only [separationStatistic] at hstat
              have hLΔ_pos_real : (0 : ℝ) < (L + Δ : ℕ) := Nat.cast_pos.mpr hLΔ_pos
              rw [div_lt_iff₀ hLΔ_pos_real] at hstat
              simp only [Nat.cast_add] at hstat
              have hstat' := hδB rB uB huB hrB_in_B
              simp only [separationStatistic] at hstat'
              rw [hstat'] at hstat
              linarith

            -- Lower bound on θs from L-1:
            -- If L = 1, lower bound is 0
            -- If L ≥ 2, minimality says mu F s_old ≥ d^{L-1}, so s_old ∈ B(L-1) ∪ C(L-1)
              have hθs_lower : θs ≥ (L - 1 : ℕ) * δ := by
                by_cases hL_one : L = 1
                · simp only [hL_one, Nat.sub_self, Nat.cast_zero, zero_mul]
                  have hlt :
                      (⟨ident, ident_mem_kGrid (F:=F)⟩ : {x // x ∈ kGrid F}) <
                        ⟨mu F s_old, mu_mem_kGrid (F:=F) s_old⟩ := by
                    change ident < mu F s_old
                    exact hs_pos
                  have hθ0 :
                      (0 : ℝ) < R.Θ_grid ⟨mu F s_old, mu_mem_kGrid (F:=F) s_old⟩ := by
                    simpa [R.ident_eq_zero] using (R.strictMono hlt)
                  exact le_of_lt (by simpa [hθs] using hθ0)
                · have hL_ge_2 : L ≥ 2 := by omega
                  have hL_pred_pos : 0 < L - 1 := by omega
                -- Minimality: ¬ (mu F s_old < d^{L-1}), so mu F s_old ≥ d^{L-1}
                have h_not_lt : ¬ mu F s_old < iterate_op d (L - 1) :=
                  hL_min (L - 1) hL_pred_pos (by omega : L - 1 < L)
                push_neg at h_not_lt
                -- s_old ∈ B(L-1) ∪ C(L-1)
                rcases h_not_lt.lt_or_eq with h_gt | h_eq
                · -- d^{L-1} < mu F s_old: s_old ∈ C(L-1)
                  have hs_in_C : s_old ∈ extensionSetC F d (L - 1) := h_gt
                  have hstat := separation_property_C_B R H hd hL_pred_pos hs_in_C huB hrB_in_B
                  simp only [separationStatistic] at hstat
                  have hL_pred_pos_real : (0 : ℝ) < (L - 1 : ℕ) := Nat.cast_pos.mpr hL_pred_pos
                  rw [lt_div_iff₀ hL_pred_pos_real] at hstat
                  have hstat' := hδB rB uB huB hrB_in_B
                  simp only [separationStatistic] at hstat'
                  rw [hstat'] at hstat
                  linarith
                · -- mu F s_old = d^{L-1}: s_old ∈ B(L-1)
                  have hs_in_B : s_old ∈ extensionSetB F d (L - 1) := h_eq.symm
                  have hstat := hδB s_old (L - 1) hL_pred_pos hs_in_B
                  simp only [separationStatistic] at hstat
                  have hL_pred_pos_real : (0 : ℝ) < (L - 1 : ℕ) := Nat.cast_pos.mpr hL_pred_pos
                  have hL_pred_ne : ((L - 1 : ℕ) : ℝ) ≠ 0 := by linarith
                  field_simp [hL_pred_ne] at hstat
                  linarith

            -- Step 2: Combine bounds to get θr - θs < (Δ + 1) * δ
            have h_bracket_upper : θr - θs < ((Δ : ℕ) + 1) * δ := by
              have h1 : θr < (L + Δ) * δ := hθr_A_L
              have h2 : θs ≥ ((L - 1 : ℕ) : ℝ) * δ := hθs_lower
              have hL_arith : ((L + Δ : ℕ) : ℝ) - ((L - 1 : ℕ) : ℝ) = (Δ : ℝ) + 1 := by
                simp only [Nat.cast_add]
                have hL1 : (L : ℝ) - ((L - 1 : ℕ) : ℝ) = 1 := by
                  by_cases hL1 : L = 1
                  · simp only [hL1, Nat.sub_self, Nat.cast_zero]; ring
                  · have : 1 ≤ L := by omega
                    simp only [Nat.cast_sub this]; ring
                linarith
              calc θr - θs
                  < (L + Δ) * δ - ((L - 1 : ℕ) : ℝ) * δ := by linarith
                _ = (((L + Δ : ℕ) : ℝ) - ((L - 1 : ℕ) : ℝ)) * δ := by ring
                _ = ((Δ : ℝ) + 1) * δ := by rw [hL_arith]
                _ = ((Δ : ℕ) + 1) * δ := by simp only [Nat.cast_add, Nat.cast_one]

            -- Step 3: Use ZQuantized_diff to get θr - θs = m * δ
            obtain ⟨m, hm⟩ := ZQuantized_diff hZQ r_old s_old

            -- Step 4: From m * δ < (Δ + 1) * δ, conclude m ≤ Δ
            have hm_le_Δ : m ≤ (Δ : ℤ) := by
              have h_upper : (m : ℝ) * δ < ((Δ : ℕ) + 1 : ℕ) * δ := by rw [← hm]; exact h_bracket_upper
              have h_div : (m : ℝ) < (Δ : ℕ) + 1 := by
                have := (mul_lt_mul_right hδ_pos).mp h_upper
                simp only [Nat.cast_add, Nat.cast_one] at this
                exact this
              have h_int : m < (Δ : ℤ) + 1 := by
                have : (m : ℝ) < ((Δ : ℤ) + 1 : ℤ) := by
                  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast]
                  exact h_div
                exact Int.cast_lt.mp this
              omega

            -- Step 5: Conclude θr - θs ≤ Δ * δ
            rw [hm]
            have : (m : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hm_le_Δ
            have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
            calc (m : ℝ) * δ ≤ (Δ : ℝ) * δ := by nlinarith
              _ = (Δ : ℕ) * δ := by simp only [Nat.cast_ofNat]

        · -- B is globally empty: Use accuracy_lemma to squeeze bounds
          push_neg at hB_global
          have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u :=
            fun r u hu hr => hB_global r u hu hr

          -- We prove θr - θs ≤ Δ * δ by contradiction using accuracy_lemma.
          by_contra h_not_le
          push_neg at h_not_le
          -- h_not_le : Δ * δ < θr - θs
          let ε : ℝ := (θr - θs) - (Δ : ℝ) * δ
          have hε_pos : 0 < ε := by simp only [ε]; linarith

          -- Need A and C nonempty for accuracy_lemma
          have hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u :=
            extensionSetA_nonempty_of_B_empty F d hd hB_empty

          -- For C nonempty, we need k ≥ 1. Get this from hs_pos (s_old > ident).
          -- If k = 0, then mu F s_old = ident, contradicting hs_pos.
          have hk_pos : k ≥ 1 := by
            by_contra hk0
            push_neg at hk0
            -- hk0 : k < 1, so k = 0
            have hk_eq_0 : k = 0 := by omega
            -- k = 0: mu F s_old = ident for any s_old since foldl over empty list = ident
            have hmu_ident : mu F s_old = ident := by
              subst hk_eq_0
              rfl  -- mu F s_old = foldl _ ident [] = ident
            -- From hmu_ident and hs_pos : ident < mu F s_old, get contradiction
            rw [hmu_ident] at hs_pos
            exact (lt_irrefl ident) hs_pos

          have hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
            extensionSetC_nonempty_of_B_empty F hk_pos d hd hB_empty

          -- Use accuracy_lemma to get A/C witnesses with statistics within ε
          obtain ⟨rA, uA, huA, hrA, rC, uC, huC, hrC, h_gap_small⟩ :=
            accuracy_lemma R d hd hB_empty hA_nonempty hC_nonempty ε hε_pos

          -- From the A/C bounds:
          -- stat(rA, uA) ≤ δ ⟹ Θ(μ rA) ≤ uA * δ
          -- stat(rC, uC) ≥ δ ⟹ Θ(μ rC) ≥ uC * δ
          -- And stat(rC) - stat(rA) < ε

          -- The squeeze: Using s_old's A/C levels and trade shifts...
          -- Upper bound on θr: from s_old ∈ A(U), get r_old ∈ A(U+Δ), so θr ≤ (U+Δ)*δ
          -- Lower bound on θs: from s_old ∈ C(V), get θs ≥ V*δ
          -- So θr - θs ≤ (U+Δ-V)*δ
          -- With accuracy_lemma, as U→V, this approaches Δ*δ

          -- Find s_old's natural A-level (exists by Archimedean since s_old is positive)
          obtain ⟨U_s, hU_s⟩ := bounded_by_iterate d hd (mu F s_old)
          have hs_in_A : s_old ∈ extensionSetA F d U_s := hU_s
          have hU_s_pos : 0 < U_s := by
            by_contra h; push_neg at h; interval_cases U_s
            simp only [iterate_op_zero] at hU_s
            exact not_lt.mpr (ident_le (mu F s_old)) hU_s

          -- By trade_shift_A: r_old ∈ A(U_s + Δ)
          have hr_in_A : r_old ∈ extensionSetA F d (U_s + Δ) := trade_shift_A hd hΔ htrade hs_in_A
          have hUΔ_pos : 0 < U_s + Δ := by omega

          -- A-bounds: θr ≤ (U_s+Δ)*δ and θs ≤ U_s*δ
          have hθr_A : θr ≤ (U_s + Δ : ℕ) * δ := by
            have hbound := hδA r_old (U_s + Δ) hUΔ_pos hr_in_A
            simp only [separationStatistic] at hbound
            have hpos : (0 : ℝ) < (U_s + Δ : ℕ) := Nat.cast_pos.mpr hUΔ_pos
            rw [div_le_iff₀ hpos] at hbound
            linarith

          -- Find s_old's natural C-level (exists since s_old > ident)
          -- Key: ident < mu F s_old means there exists V_s with d^{V_s} < mu F s_old
          -- We use V_s = 0 or find the largest V_s where s_old ∈ C(V_s)
          have hs_pos_real : ident < mu F s_old := hs_pos

          -- For positive s_old with B empty, find the C-level
          -- s_old is in C(V) for some V iff d^V < mu F s_old
          -- The largest such V is the "floor" of s_old's position in the d-sequence

          -- Use V = 0 if mu F s_old ≤ d, otherwise find V > 0
          by_cases hs_above_d : iterate_op d 1 < mu F s_old

          · -- s_old > d: Find V_s ≥ 1 where s_old ∈ C(V_s)
            have hs_in_C_1 : s_old ∈ extensionSetC F d 1 := by simp [extensionSetC, hs_above_d]

            -- C-bound at V_s = 1: θs ≥ 1*δ = δ
            have hθs_C : θs ≥ (1 : ℕ) * δ := by
              have hbound := hδC s_old 1 (by omega : 0 < 1) hs_in_C_1
              simp only [separationStatistic, Nat.cast_one, div_one] at hbound
              -- hbound : δ ≤ θs, goal : θs ≥ 1 * δ
              simp only [Nat.cast_one, one_mul]
              exact hbound

            -- By trade_shift_C_forward: r_old ∈ C(1 + Δ)
            have hr_in_C : r_old ∈ extensionSetC F d (1 + Δ) := trade_shift_C_forward hd hΔ htrade hs_in_C_1

            -- C-bound: θr ≥ (1+Δ)*δ
            have hθr_C : θr ≥ ((1 + Δ : ℕ) : ℝ) * δ := by
              have hpos_1Δ : 0 < 1 + Δ := by omega
              have hbound := hδC r_old (1 + Δ) hpos_1Δ hr_in_C
              simp only [separationStatistic] at hbound
              have hpos : (0 : ℝ) < (1 + Δ : ℕ) := Nat.cast_pos.mpr hpos_1Δ
              rw [le_div_iff₀ hpos] at hbound
              linarith

            -- **FLOOR-BRACKET CLOSURE** using ZQuantized + minimal level:
            -- We derive contradiction from h_not_le : Δ * δ < θr - θs
            --
            -- Strategy:
            -- 1. Find minimal level L for s_old
            -- 2. Get tight upper bound: θr - θs ≤ (L + Δ - (L-1)) * δ = (Δ + 1) * δ
            -- 3. With ZQuantized: θr - θs = m * δ, so m ≤ Δ + 1
            -- 4. But h_not_le gives m > Δ, so m ≥ Δ + 1
            -- 5. Combined: m = Δ + 1
            -- 6. For contradiction, we need a STRICT upper bound
            --
            -- In B-empty case: s_old ∉ B(any level), so s_old ∈ C(L-1) gives STRICT bound

            -- Find minimal L for s_old
            let P_min : ℕ → Prop := fun n => mu F s_old < iterate_op d n
            have hex_min : ∃ n, P_min n := ⟨U_s, hs_in_A⟩
            let L := Nat.find hex_min
            have hL_A_min : s_old ∈ extensionSetA F d L := Nat.find_spec hex_min
            have hL_pos : 0 < L := by
              by_contra h; push_neg at h; have hL0 : L = 0 := by omega
              rw [hL0, iterate_op_zero] at hL_A_min
              exact absurd hL_A_min (not_lt.mpr (ident_le (mu F s_old)))
            have hL_min : ∀ k, 0 < k → k < L → ¬ P_min k := fun k _ hkL => Nat.find_min hex_min hkL

            -- r_old ∈ A(L + Δ)
            have hr_in_A_L : r_old ∈ extensionSetA F d (L + Δ) := trade_shift_A hd hΔ htrade hL_A_min

            -- A-bound on r (non-strict in B-empty case)
            have hθr_A_L : θr ≤ (L + Δ) * δ := by
              have hLΔ_pos : 0 < L + Δ := by omega
              have hbound := hδA r_old (L + Δ) hLΔ_pos hr_in_A_L
              simp only [separationStatistic] at hbound
              have hpos : (0 : ℝ) < (L + Δ : ℕ) := Nat.cast_pos.mpr hLΔ_pos
              rw [div_le_iff₀ hpos] at hbound
              linarith

            -- Lower bound on θs from C(L-1) or trivial 0
            have hθs_lower_L : θs ≥ (L - 1 : ℕ) * δ := by
              by_cases hL_one : L = 1
              · simp only [hL_one, Nat.sub_self, Nat.cast_zero, zero_mul]
                have hlt :
                    (⟨ident, ident_mem_kGrid (F:=F)⟩ : {x // x ∈ kGrid F}) <
                      ⟨mu F s_old, mu_mem_kGrid (F:=F) s_old⟩ := by
                  change ident < mu F s_old
                  exact hs_pos
                have hθ0 :
                    (0 : ℝ) < R.Θ_grid ⟨mu F s_old, mu_mem_kGrid (F:=F) s_old⟩ := by
                  simpa [R.ident_eq_zero] using (R.strictMono hlt)
                exact le_of_lt (by simpa [hθs] using hθ0)
              · have hL_ge_2 : L ≥ 2 := by omega
                have hL_pred_pos : 0 < L - 1 := by omega
                -- Minimality: mu F s_old ≥ d^{L-1}
                have h_not_lt : ¬ mu F s_old < iterate_op d (L - 1) :=
                  hL_min (L - 1) hL_pred_pos (by omega : L - 1 < L)
                push_neg at h_not_lt
                -- s_old ∈ C(L-1) since B is empty (can't be in B)
                rcases h_not_lt.lt_or_eq with h_gt | h_eq
                · -- d^{L-1} < mu F s_old: s_old ∈ C(L-1)
                  have hs_in_C : s_old ∈ extensionSetC F d (L - 1) := h_gt
                  have hbound := hδC s_old (L - 1) hL_pred_pos hs_in_C
                  simp only [separationStatistic] at hbound
                  have hL_pred_pos_real : (0 : ℝ) < (L - 1 : ℕ) := Nat.cast_pos.mpr hL_pred_pos
                  rw [le_div_iff₀ hL_pred_pos_real] at hbound
                  linarith
                · -- mu F s_old = d^{L-1}: would be in B(L-1), but B is empty!
                  have hs_in_B : s_old ∈ extensionSetB F d (L - 1) := h_eq.symm
                  exact absurd hs_in_B (hB_empty s_old (L - 1) hL_pred_pos)

            -- Upper bound: θr - θs ≤ (L + Δ - (L - 1)) * δ = (Δ + 1) * δ
            have h_upper : θr - θs ≤ ((Δ : ℕ) + 1) * δ := by
              have h1 : θr ≤ (L + Δ) * δ := hθr_A_L
              have h2 : θs ≥ ((L - 1 : ℕ) : ℝ) * δ := hθs_lower_L
              have hL_arith : ((L + Δ : ℕ) : ℝ) - ((L - 1 : ℕ) : ℝ) = (Δ : ℝ) + 1 := by
                simp only [Nat.cast_add]
                have hL1 : (L : ℝ) - ((L - 1 : ℕ) : ℝ) = 1 := by
                  by_cases hL1' : L = 1
                  · simp only [hL1', Nat.sub_self, Nat.cast_zero]; ring
                  · have : 1 ≤ L := by omega
                    simp only [Nat.cast_sub this]; ring
                linarith
              calc θr - θs ≤ (L + Δ) * δ - ((L - 1 : ℕ) : ℝ) * δ := by linarith
                _ = (((L + Δ : ℕ) : ℝ) - ((L - 1 : ℕ) : ℝ)) * δ := by ring
                _ = ((Δ : ℝ) + 1) * δ := by rw [hL_arith]
                _ = ((Δ : ℕ) + 1) * δ := by simp only [Nat.cast_add, Nat.cast_one]

            -- With ZQuantized: θr - θs = m * δ
            obtain ⟨m, hm⟩ := ZQuantized_diff hZQ r_old s_old

            -- From upper bound: m ≤ Δ + 1
            have hm_upper : m ≤ (Δ : ℤ) + 1 := by
              have h : (m : ℝ) * δ ≤ ((Δ : ℕ) + 1 : ℕ) * δ := by rw [← hm]; exact h_upper
              have h_div : (m : ℝ) ≤ (Δ : ℕ) + 1 := by
                have := (mul_le_mul_right hδ_pos).mp h
                simp only [Nat.cast_add, Nat.cast_one] at this
                exact this
              have : (m : ℝ) ≤ ((Δ : ℤ) + 1 : ℤ) := by
                simp only [Int.cast_add, Int.cast_one, Int.cast_natCast]
                exact h_div
              exact Int.cast_le.mp this

            -- From h_not_le: Δ < m
            have hm_lower : (Δ : ℤ) < m := by
              have h : (Δ : ℕ) * δ < (m : ℝ) * δ := by rw [← hm]; exact h_not_le
              have h_div : (Δ : ℕ) < (m : ℝ) := by
                have := (mul_lt_mul_right hδ_pos).mp h
                exact this
              have : ((Δ : ℤ) : ℝ) < (m : ℝ) := by
                simp only [Int.cast_natCast]
                exact h_div
              exact Int.cast_lt.mp this

            -- Contradiction: Δ < m ≤ Δ + 1 means m = Δ + 1, but then θr - θs = (Δ+1)*δ > Δ*δ
            -- We need STRICT upper bound. The issue is B-empty gives ≤ not <.
            -- Use the fact that for the EXACT equality θr - θs = (Δ+1)*δ,
            -- we'd need θr = (L+Δ)*δ and θs = (L-1)*δ exactly, but B is empty!
            have hm_eq : m = (Δ : ℤ) + 1 := by omega

            -- Strengthen the upper bound to a strict one: the A/C gap cannot equal (Δ+1)·δ
            have h_upper_strict : θr - θs < ((Δ : ℕ) + 1) * δ := by
              -- If L=1 then θs>0, giving strictness immediately.
              by_cases hL_one : L = 1
              · have hθs_pos : 0 < θs := by
                  have hlt :
                      (⟨ident, ident_mem_kGrid (F:=F)⟩ : {x // x ∈ kGrid F}) <
                        ⟨mu F s_old, mu_mem_kGrid (F:=F) s_old⟩ := by
                    change ident < mu F s_old
                    exact hs_pos
                  have hθ : (0 : ℝ) < R.Θ_grid ⟨mu F s_old, mu_mem_kGrid (F:=F) s_old⟩ := by
                    simpa [R.ident_eq_zero] using (R.strictMono hlt)
                  simpa [hθs] using hθ
                have hLΔ : L + Δ = Δ + 1 := by omega
                have hθr_le' : θr ≤ ((Δ : ℕ) + 1) * δ := by
                  simpa [hLΔ] using hθr_A_L
                have h_gap_lt_θr : θr - θs < θr := sub_lt_self θr hθs_pos
                exact lt_of_lt_of_le h_gap_lt_θr hθr_le'
              · -- If L≥2, use separation_property to show at least one of the A/C bounds is strict.
                have hL_ge_2 : L ≥ 2 := by omega
                have hL_pred_pos : 0 < L - 1 := by omega
                have hs_in_C_Lpred : s_old ∈ extensionSetC F d (L - 1) := by
                  have h_not_lt : ¬ mu F s_old < iterate_op d (L - 1) :=
                    hL_min (L - 1) hL_pred_pos (by omega : L - 1 < L)
                  push_neg at h_not_lt
                  rcases h_not_lt.lt_or_eq with h_gt | h_eq
                  · exact h_gt
                  · have hs_in_B : s_old ∈ extensionSetB F d (L - 1) := h_eq.symm
                    exact (False.elim (hB_empty s_old (L - 1) hL_pred_pos hs_in_B))
                have hLΔ_pos : 0 < L + Δ := by omega
                let stat_r : ℝ := separationStatistic R r_old (L + Δ) hLΔ_pos hr_in_A_L
                let stat_s : ℝ := separationStatistic R s_old (L - 1) hL_pred_pos hs_in_C_Lpred
                have h_sep : stat_r < stat_s := by
                  simpa [stat_r, stat_s] using
                    (separation_property R H IH hd hLΔ_pos hr_in_A_L hL_pred_pos hs_in_C_Lpred)
                have hstat_r_le : stat_r ≤ δ := by
                  simpa [stat_r] using (hδA r_old (L + Δ) hLΔ_pos hr_in_A_L)
                by_cases hstat_r_eq : stat_r = δ
                · have hδ_lt_stat_s : δ < stat_s := by
                    -- from stat_r < stat_s and stat_r = δ
                    simpa [stat_r, hstat_r_eq] using h_sep
                  have hθs_strict : ((L - 1 : ℕ) : ℝ) * δ < θs := by
                    have hδ_lt_div : δ < θs / (L - 1 : ℕ) := by
                      simpa [stat_s, separationStatistic, θs] using hδ_lt_stat_s
                    have hpos : (0 : ℝ) < (L - 1 : ℕ) := Nat.cast_pos.mpr hL_pred_pos
                    have : δ * (L - 1 : ℕ) < θs := (lt_div_iff₀ hpos).1 hδ_lt_div
                    simpa [mul_comm, mul_left_comm, mul_assoc] using this
                  -- strictness from θs > (L-1)·δ
                  have hL_arith : ((L + Δ : ℕ) : ℝ) - ((L - 1 : ℕ) : ℝ) = (Δ : ℝ) + 1 := by
                    simp only [Nat.cast_add]
                    have hL1 : (L : ℝ) - ((L - 1 : ℕ) : ℝ) = 1 := by
                      have : 1 ≤ L := by omega
                      simp only [Nat.cast_sub this]; ring
                    linarith
                  have : θr - θs < ((Δ : ℝ) + 1) * δ := by
                    have h1 : θr ≤ (L + Δ) * δ := hθr_A_L
                    have h2 : ((L - 1 : ℕ) : ℝ) * δ < θs := hθs_strict
                    calc θr - θs < (L + Δ) * δ - ((L - 1 : ℕ) : ℝ) * δ := by linarith
                      _ = (((L + Δ : ℕ) : ℝ) - ((L - 1 : ℕ) : ℝ)) * δ := by ring
                      _ = ((Δ : ℝ) + 1) * δ := by rw [hL_arith]
                  simpa [Nat.cast_add, Nat.cast_one] using this
                · have hstat_r_lt : stat_r < δ := lt_of_le_of_ne hstat_r_le hstat_r_eq
                  have hθr_strict : θr < (L + Δ) * δ := by
                    have h_div_lt : θr / (L + Δ : ℕ) < δ := by
                      simpa [stat_r, separationStatistic, θr] using hstat_r_lt
                    have hpos : (0 : ℝ) < (L + Δ : ℕ) := Nat.cast_pos.mpr hLΔ_pos
                    have : θr < δ * (L + Δ : ℕ) := (div_lt_iff₀ hpos).1 h_div_lt
                    simpa [mul_comm, mul_left_comm, mul_assoc] using this
                  have hL_arith : ((L + Δ : ℕ) : ℝ) - ((L - 1 : ℕ) : ℝ) = (Δ : ℝ) + 1 := by
                    simp only [Nat.cast_add]
                    have hL1 : (L : ℝ) - ((L - 1 : ℕ) : ℝ) = 1 := by
                      have : 1 ≤ L := by omega
                      simp only [Nat.cast_sub this]; ring
                    linarith
                  have : θr - θs < ((Δ : ℝ) + 1) * δ := by
                    have h1 : θr < (L + Δ) * δ := hθr_strict
                    have h2 : ((L - 1 : ℕ) : ℝ) * δ ≤ θs := hθs_lower_L
                    calc θr - θs < (L + Δ) * δ - ((L - 1 : ℕ) : ℝ) * δ := by linarith
                      _ = (((L + Δ : ℕ) : ℝ) - ((L - 1 : ℕ) : ℝ)) * δ := by ring
                      _ = ((Δ : ℝ) + 1) * δ := by rw [hL_arith]
                  simpa [Nat.cast_add, Nat.cast_one] using this

            -- But then (m:ℝ)*δ < (Δ+1)*δ, contradicting m = Δ+1
            have hm_lt : m < (Δ : ℤ) + 1 := by
              have h_mul : (m : ℝ) * δ < ((Δ : ℕ) + 1) * δ := by
                simpa [hm] using h_upper_strict
              have h_mul' : δ * (m : ℝ) < δ * ((Δ : ℕ) + 1 : ℝ) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul
              have h_real : (m : ℝ) < ((Δ : ℕ) + 1 : ℝ) :=
                (mul_lt_mul_iff_left₀ hδ_pos).1 h_mul'
              have h_real_int : ((m : ℤ) : ℝ) < (((Δ + 1 : ℕ) : ℤ) : ℝ) := by
                simpa [Int.cast_natCast] using h_real
              have hm_lt' : m < ((Δ + 1 : ℕ) : ℤ) := Int.cast_lt.mp h_real_int
              simpa using hm_lt'
            have : (Δ : ℤ) + 1 < (Δ : ℤ) + 1 := by simpa [hm_eq] using hm_lt
            exact (lt_irrefl _ this).elim

          · -- s_old ≤ d: Use ident < s_old ≤ d
            push_neg at hs_above_d
            -- hs_above_d : mu F s_old ≤ iterate_op d 1

            -- We need to show mu F s_old < d (strictly) since if equal, s_old ∈ B(1)
            have hs_lt_d : mu F s_old < iterate_op d 1 := by
              rcases eq_or_lt_of_le hs_above_d with h_eq | h_lt
              · -- If mu F s_old = d, then s_old ∈ B(1), contradicting B empty
                have hB1 : s_old ∈ extensionSetB F d 1 := by
                  simp only [extensionSetB, Set.mem_setOf_eq, iterate_op_one, h_eq]
                exact absurd hB1 (hB_empty s_old 1 (by omega))
              · exact h_lt

            -- s_old ∈ A(1) since mu F s_old < d = d^1
            have hs_in_A_1 : s_old ∈ extensionSetA F d 1 := by
              simp only [extensionSetA, Set.mem_setOf_eq]
              exact hs_lt_d

            -- A-bound: θs ≤ 1*δ = δ
            have hθs_A : θs ≤ (1 : ℕ) * δ := by
              have hbound := hδA s_old 1 (by omega) hs_in_A_1
              simp only [separationStatistic, Nat.cast_one, div_one] at hbound
              -- hbound : θs ≤ δ, goal : θs ≤ 1 * δ
              simp only [Nat.cast_one, one_mul]
              exact hbound

            -- By trade_shift_A: r_old ∈ A(1 + Δ)
            have hr_in_A_1Δ : r_old ∈ extensionSetA F d (1 + Δ) := trade_shift_A hd hΔ htrade hs_in_A_1

            -- A-bound: θr ≤ (1+Δ)*δ
            have hθr_A' : θr ≤ ((1 + Δ : ℕ) : ℝ) * δ := by
              have hpos_1Δ : 0 < 1 + Δ := by omega
              have hbound := hδA r_old (1 + Δ) hpos_1Δ hr_in_A_1Δ
              simp only [separationStatistic] at hbound
              have hpos : (0 : ℝ) < (1 + Δ : ℕ) := Nat.cast_pos.mpr hpos_1Δ
              rw [div_le_iff₀ hpos] at hbound
              linarith

            -- For the C-level, since s_old > ident but s_old < d, we have
            -- d^0 = ident < s_old < d = d^1
            -- So s_old is NOT in C(1), but is "above" ident.

            -- The C-bound at level 0 is vacuous (0 < 0 is false).
            -- We need a positive C-level, but s_old < d means s_old ∉ C(v) for any v ≥ 1.

            -- Lower bound on θs: From ident < s_old, we get θs > 0
            have hθs_pos : 0 < θs := by
              have hθ_strict : R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ > R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ :=
                R.strictMono hs_pos
              simp only [R.ident_eq_zero] at hθ_strict
              exact hθ_strict

            -- From trade: r_old is "Δ steps above" s_old
            -- If s_old < d = d^1, then s_old ⊕ d^Δ could be anywhere relative to d^{Δ+1}

            -- **KEY INSIGHT**: When ident < s_old < d, the trade μ(r_old) = s_old ⊕ d^Δ
            -- places r_old between d^Δ and d^{Δ+1} (approximately).
            -- r_old ∈ C(Δ) since d^Δ < s_old ⊕ d^Δ (by s_old > ident)

            have hr_in_C_Δ : r_old ∈ extensionSetC F d Δ := by
              simp only [extensionSetC, Set.mem_setOf_eq]
              rw [htrade]
              -- Need: d^Δ < s_old ⊕ d^Δ
              -- Since s_old > ident, by op_strictMono_left: s_old ⊕ d^Δ > ident ⊕ d^Δ = d^Δ
              have h := (op_strictMono_left (iterate_op d Δ)) hs_pos
              simp only [op_ident_left] at h
              exact h

            -- C-bound: θr ≥ Δ*δ
            have hθr_C : θr ≥ (Δ : ℝ) * δ := by
              have hbound := hδC r_old Δ hΔ hr_in_C_Δ
              simp only [separationStatistic] at hbound
              have hpos : (0 : ℝ) < (Δ : ℕ) := Nat.cast_pos.mpr hΔ
              rw [le_div_iff₀ hpos] at hbound
              linarith

            -- Now we have: Δ*δ ≤ θr ≤ (1+Δ)*δ and 0 < θs ≤ 1*δ

            -- From these: θr - θs ≥ Δ*δ - 1*δ = (Δ-1)*δ
            --            θr - θs ≤ (1+Δ)*δ - 0 = (1+Δ)*δ

            -- This is a width-2δ bracket centered around Δ*δ.
            -- Our assumption h_not_le says θr - θs > Δ*δ.

            -- **CONTRADICTION PATH**: Need to show θr - θs ≤ Δ*δ
            -- But our bounds only give θr - θs ≤ (1+Δ)*δ

            -- The accuracy_lemma says δ is pinned tightly, but doesn't help here
            -- because the bracket width comes from the DISCRETE level structure.

            -- We need: θr ≤ Δ*δ + θs, i.e., θr - θs ≤ Δ*δ
            -- We have: θr ≤ (1+Δ)*δ and θs > 0

            -- The gap: We can only conclude θr - θs ≤ (1+Δ)*δ - 0 = (1+Δ)*δ
            -- But h_not_le says θr - θs > Δ*δ, which is consistent with θr - θs ∈ (Δ*δ, (Δ+1)*δ]

            -- **RESOLUTION via delta_cut_tight**: The floor-bracket is closed using accuracy
            -- The issue: We only have θr - θs ≤ (Δ+1)*δ but need θr - θs ≤ Δ*δ
            -- Solution: Use delta_cut_tight to show δ is precisely determined

            -- We have established:
            -- - θr ≤ (1+Δ)*δ (from A-membership)
            -- - θr ≥ Δ*δ (from C-membership)
            -- - θs ≤ δ (from A-membership)
            -- - θs > 0 (from s_old > ident)

            -- This gives: Δ*δ - δ < θr - θs < (Δ+1)*δ
            -- i.e., (Δ-1)*δ < θr - θs < (Δ+1)*δ

            -- The bracket width is 2δ, centered at Δ*δ
            -- Since h_not_le claims θr - θs > Δ*δ, we have θr - θs ∈ (Δ*δ, (Δ+1)*δ]

            -- **FLOOR-BRACKET CLOSURE via ZQuantized**:
            -- Key observation: θr ≤ (Δ+1)*δ and θs > 0 gives STRICT upper bound
            -- θr - θs < (Δ+1)*δ - 0 = (Δ+1)*δ
            --
            -- Combined with h_not_le: Δ*δ < θr - θs < (Δ+1)*δ
            -- With ZQuantized θr - θs = m*δ: Δ < m < Δ+1
            -- No integer exists in (Δ, Δ+1) — contradiction!

            -- Get ZQuantized property
            obtain ⟨m, hm⟩ := ZQuantized_diff hZQ r_old s_old

            -- Upper bound: θr - θs < (Δ+1)*δ (strict because θs > 0)
            have h_upper : θr - θs < ((Δ : ℕ) + 1 : ℝ) * δ := by
              have h1 : θr ≤ ((1 + Δ : ℕ) : ℝ) * δ := hθr_A'
              have h2 : 0 < θs := hθs_pos
              calc θr - θs < θr - 0 := by linarith
                _ = θr := by ring
                _ ≤ ((1 + Δ : ℕ) : ℝ) * δ := h1
                _ = ((Δ : ℕ) + 1 : ℝ) * δ := by ring

            -- From h_upper: m < Δ+1, so m ≤ Δ
            have hm_le : m ≤ (Δ : ℤ) := by
              rw [hm] at h_upper
              have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
              have h_div : (m : ℝ) < ((Δ : ℕ) + 1 : ℝ) := by
                have := (mul_lt_mul_right hδ_pos).mp h_upper
                convert this using 1
                simp only [Nat.cast_add, Nat.cast_one]
              have : m < (Δ : ℤ) + 1 := by
                have h1 : (m : ℝ) < ((Δ : ℤ) : ℝ) + 1 := by simp only [Int.cast_natCast]; exact h_div
                exact Int.cast_lt.mp h1
              omega

            -- From h_not_le: m > Δ
            have hm_gt : m > (Δ : ℤ) := by
              rw [hm] at h_not_le
              have h_div : ((Δ : ℕ) : ℝ) < (m : ℝ) := by
                have := (mul_lt_mul_right hδ_pos).mp h_not_le
                convert this using 1
              have : (Δ : ℤ) < m := Int.cast_lt.mp (by simp only [Int.cast_natCast]; exact h_div)
              exact this

            -- Contradiction: m > Δ and m ≤ Δ
            omega

  · -- Lower bound: Δ * δ ≤ θr - θs

    -- For the lower bound, we need:
    -- - C-bound on r: Θ(r) ≥ (level)·δ
    -- - A-bound on s: Θ(s) ≤ (level)·δ

    by_cases hs_ident : mu F s_old = ident

    · -- s_old = ident case: This means r_old is a B-witness!
      -- Same as upper bound: use hδB to get θr = Δ·δ exactly.

      have hθs_zero : θs = 0 := by
        have h_mem : (⟨mu F s_old, mu_mem_kGrid F s_old⟩ : kGrid F) =
                     ⟨ident, ident_mem_kGrid F⟩ := by
          ext; exact hs_ident
        simp only [hθs, h_mem, R.ident_eq_zero]

      have hr_eq_dΔ : mu F r_old = iterate_op d Δ := by rw [htrade, hs_ident, op_ident_left]

      -- r_old ∈ B(Δ) because μ_F(r_old) = d^Δ
      have hr_in_B : r_old ∈ extensionSetB F d Δ := by
        simp only [extensionSetB, Set.mem_setOf_eq, hr_eq_dΔ]

      -- By hδB: stat(r_old, Δ) = δ, i.e., θr/Δ = δ
      have hstat_B : separationStatistic R r_old Δ hΔ = δ := hδB r_old Δ hΔ hr_in_B
      simp only [separationStatistic] at hstat_B

      -- So θr = Δ · δ
      have hθr_eq : θr = Δ * δ := by
        have hΔ_pos : (Δ : ℝ) > 0 := by positivity
        have hΔ_ne : (Δ : ℝ) ≠ 0 := by linarith
        field_simp [hΔ_ne] at hstat_B
        linarith

      -- Conclude: Δ·δ ≤ θr - θs = Δ·δ - 0 = Δ·δ
      rw [hθs_zero, sub_zero]
      exact le_of_eq hθr_eq.symm

    · -- s_old > ident: Same structure as upper bound case
      have hs_pos : ident < mu F s_old := by
        cases' (ident_le (mu F s_old)).lt_or_eq with h h
        · exact h
        · exact absurd h.symm hs_ident

      -- Case split: Is s_old a B-witness for some level V > 0?
      by_cases hB_witness : ∃ V : ℕ, 0 < V ∧ s_old ∈ extensionSetB F d V

      · -- Case A: s_old ∈ B(V) for some V > 0 - Use B-witness chain
        obtain ⟨V, hV_pos, hs_in_B⟩ := hB_witness

        -- From B-membership: mu F s_old = d^V
        have hs_eq_dV : mu F s_old = iterate_op d V := by
          simpa [extensionSetB] using hs_in_B

        -- By htrade: mu F r_old = d^V ⊕ d^Δ = d^{V+Δ}
        have hr_eq_dVΔ : mu F r_old = iterate_op d (V + Δ) := by
          rw [htrade, hs_eq_dV, ← iterate_op_add d V Δ]

        -- So r_old ∈ B(V+Δ)
        have hr_in_B : r_old ∈ extensionSetB F d (V + Δ) := by
          simp only [extensionSetB, Set.mem_setOf_eq, hr_eq_dVΔ]

        have hVΔ_pos : 0 < V + Δ := by omega

        -- From hδB: θs = V*δ and θr = (V+Δ)*δ
        have hstat_s : separationStatistic R s_old V hV_pos = δ := hδB s_old V hV_pos hs_in_B
        have hstat_r : separationStatistic R r_old (V + Δ) hVΔ_pos = δ := hδB r_old (V + Δ) hVΔ_pos hr_in_B

        simp only [separationStatistic] at hstat_s hstat_r

        have hθs_eq : θs = V * δ := by
          have hV_pos_real : (V : ℝ) > 0 := Nat.cast_pos.mpr hV_pos
          have hV_ne : (V : ℝ) ≠ 0 := by linarith
          field_simp [hV_ne] at hstat_s
          linarith

        have hθr_eq : θr = (V + Δ) * δ := by
          have hVΔ_pos_real : (V : ℝ) + (Δ : ℝ) > 0 := by positivity
          have hVΔ_ne : (V : ℝ) + (Δ : ℝ) ≠ 0 := by linarith
          simp only [Nat.cast_add] at hstat_r
          field_simp [hVΔ_ne] at hstat_r
          linarith

        -- Conclude: Δ·δ ≤ θr - θs = (V+Δ)*δ - V*δ = Δ*δ
        rw [hθr_eq, hθs_eq]
        ring_nf
        linarith

      · -- Case B: No B-witness for s_old - Pure A/C case
        -- Same structure as the upper bound: split on global B-emptiness.
        push_neg at hB_witness

        by_cases hB_global : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u

        · -- B is globally non-empty, but s_old ∉ B
          -- Same structure as upper bound: case split on whether d^Δ is in the k-grid.
          obtain ⟨rB, uB, huB, hrB_in_B⟩ := hB_global
          have hrB_eq : mu F rB = iterate_op d uB := hrB_in_B

          by_cases hdΔ_in_B : ∃ rΔ : Multi k, mu F rΔ = iterate_op d Δ

          · -- d^Δ is in the k-grid as μ rΔ = d^Δ
            obtain ⟨rΔ, hrΔ_eq⟩ := hdΔ_in_B

            -- rΔ ∈ B(Δ)
            have hrΔ_in_B : rΔ ∈ extensionSetB F d Δ := by
              simp only [extensionSetB, Set.mem_setOf_eq, hrΔ_eq]

            -- From hδB: Θ(rΔ) = Δ·δ
            have hΘrΔ : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ = Δ * δ := by
              have hstat := hδB rΔ Δ hΔ hrΔ_in_B
              simp only [separationStatistic] at hstat
              have hΔ_pos : (0 : ℝ) < (Δ : ℕ) := Nat.cast_pos.mpr hΔ
              have hΔ_ne : (Δ : ℝ) ≠ 0 := by linarith
              field_simp [hΔ_ne] at hstat
              linarith

            -- Same as upper bound: use mu_add_of_comm and R.add
            have htrade' : mu F r_old = op (mu F s_old) (mu F rΔ) := by
              rw [hrΔ_eq]; exact htrade

            have h_add : op (mu F s_old) (mu F rΔ) = mu F (s_old + rΔ) :=
              (mu_add_of_comm H s_old rΔ).symm

            have h_mu_eq : mu F r_old = mu F (s_old + rΔ) := by rw [htrade', h_add]

            have h_Θ_eq : R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ =
                          R.Θ_grid ⟨mu F (s_old + rΔ), mu_mem_kGrid F (s_old + rΔ)⟩ := by
              congr 1; ext; exact h_mu_eq

            have h_R_add := R.add s_old rΔ

            have hθr_eq_sum : θr = θs + Δ * δ := by
              calc θr = R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ := rfl
                _ = R.Θ_grid ⟨mu F (s_old + rΔ), mu_mem_kGrid F (s_old + rΔ)⟩ := h_Θ_eq
                _ = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ +
                    R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ := h_R_add
                _ = θs + Δ * δ := by rw [hΘrΔ]
            linarith

          · -- d^Δ NOT in k-grid - Use minimal level + ZQuantized for lower bound
            -- Strategy (symmetric to upper bound):
            -- 1. Find minimal level L for s_old in A
            -- 2. Use C-bound at L-1 for s_old: θs ≤ (L-1)*δ (if s_old ∈ A(L), then s_old ∉ C(L-1))
            -- 3. By trade_shift_C_forward: r_old ∈ C(L-1+Δ), so θr ≥ (L-1+Δ)*δ
            -- 4. Lower bound: θr - θs ≥ (L-1+Δ)*δ - (L-1)*δ = Δ*δ... wait, need strict
            --
            -- Actually for lower bound, the argument is different. We need:
            -- - C-bound on r_old to get θr ≥ something * δ
            -- - A-bound on s_old to get θs ≤ something * δ
            --
            -- Find minimal level L for s_old (s_old ∈ A(L))
            classical
            let P : ℕ → Prop := fun n => mu F s_old < iterate_op d n
            have hex : ∃ n, P n := by
              obtain ⟨U, hU⟩ := bounded_by_iterate d hd (mu F s_old)
              exact ⟨U, hU⟩
            let L := Nat.find hex
            have hL_A : s_old ∈ extensionSetA F d L := Nat.find_spec hex
            have hL_pos : 0 < L := by
              by_contra h; push_neg at h; have hL0 : L = 0 := by omega
              rw [hL0, iterate_op_zero] at hL_A
              exact absurd hL_A (not_lt.mpr (ident_le (mu F s_old)))
            have hL_min : ∀ k, 0 < k → k < L → ¬ P k := fun k _ hkL => Nat.find_min hex hkL

            -- A-bound on s_old: θs < L * δ (STRICT because B-non-empty)
            have hθs_A : θs < L * δ := by
              have hstat := separation_property_A_B R H hd hL_pos hL_A huB hrB_in_B
              simp only [separationStatistic] at hstat
              have hL_pos_real : (0 : ℝ) < L := Nat.cast_pos.mpr hL_pos
              rw [div_lt_iff₀ hL_pos_real] at hstat
              have hstat' := hδB rB uB huB hrB_in_B
              simp only [separationStatistic] at hstat'
              rw [hstat'] at hstat
              linarith

            -- By trade_shift_C_forward: r_old ∈ C(V + Δ) where s_old ∈ C(V)
            -- Since s_old ∈ A(L) is minimal, and hs_pos says ident < mu F s_old,
            -- s_old ∈ C(L-1) (for L ≥ 2) or s_old ∈ C(0) = above ident (for L = 1)
            --
            -- For L = 1: s_old ∈ C(0), so r_old ∈ C(0 + Δ) = C(Δ)
            -- For L ≥ 2: s_old ∈ C(L-1), so r_old ∈ C(L-1 + Δ)

            have hθr_lower : θr ≥ (L - 1 + Δ : ℕ) * δ := by
              by_cases hL_one : L = 1
              · -- L = 1: s_old ∈ C(0) since ident < mu F s_old
                have hs_in_C_0 : s_old ∈ extensionSetC F d 0 := by
                  simp only [extensionSetC, Set.mem_setOf_eq, iterate_op_zero]
                  exact hs_pos
                have hr_in_C_Δ : r_old ∈ extensionSetC F d (0 + Δ) := trade_shift_C_forward hd hΔ htrade hs_in_C_0
                simp only [zero_add] at hr_in_C_Δ
                have hstat := separation_property_C_B R H hd hΔ hr_in_C_Δ huB hrB_in_B
                simp only [separationStatistic] at hstat
                have hΔ_pos_real : (0 : ℝ) < Δ := Nat.cast_pos.mpr hΔ
                rw [lt_div_iff₀ hΔ_pos_real] at hstat
                have hstat' := hδB rB uB huB hrB_in_B
                simp only [separationStatistic] at hstat'
                rw [hstat'] at hstat
                simp only [hL_one, Nat.sub_self, zero_add, Nat.cast_zero, zero_mul]
                linarith
              · -- L ≥ 2: s_old ∈ C(L-1) by minimality
                have hL_ge_2 : L ≥ 2 := by omega
                have hL_pred_pos : 0 < L - 1 := by omega
                have h_not_lt : ¬ mu F s_old < iterate_op d (L - 1) :=
                  hL_min (L - 1) hL_pred_pos (by omega : L - 1 < L)
                push_neg at h_not_lt
                rcases h_not_lt.lt_or_eq with h_gt | h_eq
                · -- d^{L-1} < mu F s_old: s_old ∈ C(L-1)
                  have hs_in_C : s_old ∈ extensionSetC F d (L - 1) := h_gt
                  have hr_in_C : r_old ∈ extensionSetC F d (L - 1 + Δ) :=
                    trade_shift_C_forward hd hΔ htrade hs_in_C
                  have hL1Δ_pos : 0 < L - 1 + Δ := by omega
                  have hstat := separation_property_C_B R H hd hL1Δ_pos hr_in_C huB hrB_in_B
                  simp only [separationStatistic] at hstat
                  have hL1Δ_pos_real : (0 : ℝ) < (L - 1 + Δ : ℕ) := Nat.cast_pos.mpr hL1Δ_pos
                  rw [lt_div_iff₀ hL1Δ_pos_real] at hstat
                  have hstat' := hδB rB uB huB hrB_in_B
                  simp only [separationStatistic] at hstat'
                  rw [hstat'] at hstat
                  linarith
                · -- mu F s_old = d^{L-1}: s_old ∈ B(L-1), exact equality
                  have hs_in_B : s_old ∈ extensionSetB F d (L - 1) := h_eq.symm
                  -- But hB_witness says s_old is NOT in any B(V) - contradiction!
                  exact absurd hs_in_B (hB_witness (L - 1) hL_pred_pos)

            -- Lower bracket: θr - θs > (L-1+Δ)*δ - L*δ = (Δ-1)*δ
            have h_bracket_lower : θr - θs > ((Δ : ℕ) - 1) * δ := by
              have h1 : θr ≥ (L - 1 + Δ : ℕ) * δ := hθr_lower
              have h2 : θs < L * δ := hθs_A
              have hL_arith : ((L - 1 + Δ : ℕ) : ℝ) - (L : ℝ) = (Δ : ℝ) - 1 := by
                simp only [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ L)]
                ring
              calc θr - θs > (L - 1 + Δ : ℕ) * δ - L * δ := by linarith
                _ = (((L - 1 + Δ : ℕ) : ℝ) - (L : ℝ)) * δ := by ring
                _ = ((Δ : ℝ) - 1) * δ := by rw [hL_arith]
                _ = ((Δ : ℕ) - 1) * δ := by simp only [Nat.cast_sub (by omega : 1 ≤ Δ)]

            -- With ZQuantized: θr - θs = m * δ
            obtain ⟨m, hm⟩ := ZQuantized_diff hZQ r_old s_old

            -- From lower bracket: m > Δ - 1, so m ≥ Δ
            have hm_ge_Δ : m ≥ (Δ : ℤ) := by
              have h_lower : ((Δ : ℕ) - 1 : ℕ) * δ < (m : ℝ) * δ := by rw [← hm]; exact h_bracket_lower
              have h_div : ((Δ : ℕ) - 1 : ℕ) < (m : ℝ) := by
                have := (mul_lt_mul_right hδ_pos).mp h_lower
                exact this
              have h_int : ((Δ : ℤ) - 1 : ℤ) < m := by
                have : (((Δ : ℕ) - 1 : ℕ) : ℝ) < (m : ℝ) := h_div
                have h_cast : (((Δ : ℕ) - 1 : ℕ) : ℝ) = ((Δ : ℤ) - 1 : ℤ) := by
                  simp only [Nat.cast_sub (by omega : 1 ≤ Δ), Int.cast_sub, Int.cast_natCast, Int.cast_one]
                rw [h_cast] at this
                exact Int.cast_lt.mp this
              omega

            -- Conclude θr - θs ≥ Δ * δ
            rw [hm]
            have : (Δ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge_Δ
            have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
            calc (Δ : ℕ) * δ = (Δ : ℝ) * δ := by simp only [Nat.cast_ofNat]
              _ ≤ (m : ℝ) * δ := by nlinarith

        · -- B is globally empty: Use accuracy_lemma for lower bound
          push_neg at hB_global
          have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u :=
            fun r u hu hr => hB_global r u hu hr

          -- Symmetric argument to upper bound:
          -- If Δ * δ > θr - θs, use accuracy_lemma to derive contradiction.
          -- However, the same FLOOR-BRACKET limitation applies:
          --
          -- For the lower bound we need θr - θs ≥ Δ*δ.
          -- Using C-bound on r at level V+Δ: θr ≥ (V+Δ)*δ
          -- Using A-bound on s at level U: θs ≤ U*δ
          -- So θr - θs ≥ (V+Δ)*δ - U*δ = (V+Δ-U)*δ
          --
          -- With U = V+1 (tightest when B is empty):
          -- θr - θs ≥ (V+Δ-V-1)*δ = (Δ-1)*δ
          --
          -- **APPROACH**: Use delta_cut_tight to get arbitrarily tight bounds
          -- For any ε > 0, we can find A and C witnesses close to δ
          -- This allows us to close the gap from (Δ-1)*δ to Δ*δ

          -- Use ZQuantized: θr - θs = m * δ for some integer m
          obtain ⟨m, hm⟩ := ZQuantized_diff hZQ r_old s_old

          -- We need to show m ≥ Δ
          -- Strategy: Show that if m < Δ, we get a contradiction
          by_contra h_not_ge
          push_neg at h_not_ge
          -- h_not_ge : m < Δ

          -- If m < Δ, then m ≤ Δ - 1, so θr - θs ≤ (Δ-1)*δ
          have h_upper : θr - θs ≤ ((Δ : ℕ) - 1) * δ := by
            rw [hm]
            have : m ≤ (Δ : ℤ) - 1 := by omega
            have h1 : (m : ℝ) ≤ ((Δ : ℤ) - 1 : ℤ) := by exact_mod_cast this
            have h2 : (((Δ : ℤ) - 1 : ℤ) : ℝ) = ((Δ : ℕ) - 1 : ℝ) := by
              simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one,
                         Nat.cast_sub (by omega : 1 ≤ Δ)]
            rw [← h2] at h1
            have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
            exact mul_le_mul_of_nonneg_right h1 hδ_nonneg

          -- Use ABC_correspondence: m < Δ implies mu F r_old < op (mu F s_old) (d^Δ)
          -- But htrade says mu F r_old = op (mu F s_old) (d^Δ). Contradiction!

          -- First establish k ≥ 1 (needed for ABC_correspondence)
          have hk_pos : k ≥ 1 := by
            by_contra hk0
            push_neg at hk0
            have hk_eq_0 : k = 0 := by omega
            -- k = 0: mu F s_old = ident
            have hmu_s_ident : mu F s_old = ident := by subst hk_eq_0; rfl
            -- htrade: mu F r_old = op ident (d^Δ) = d^Δ
            have hmu_r : mu F r_old = iterate_op d Δ := by
              rw [hmu_s_ident, ident_op] at htrade; exact htrade
            -- r_old ∈ B(Δ), contradicting B empty
            have hr_in_B : r_old ∈ extensionSetB F d Δ := hmu_r.symm
            exact hB_empty r_old Δ hΔ hr_in_B

          have hABC := ABC_correspondence hk_pos R IH H d hd
            (delta_pos hk_pos R IH H d hd) (chooseδ_A_bound hk_pos R IH H d hd)
            (chooseδ_C_bound hk_pos R IH H d hd) (chooseδ_B_bound hk_pos R IH d hd)
            hZQ hΔ hm
          have h_A_iff := hABC.1
          have h_lt_mu : mu F r_old < op (mu F s_old) (iterate_op d Δ) := h_A_iff.mp h_not_ge
          -- But htrade says equality
          exact absurd htrade (ne_of_lt h_lt_mu)

-/

/-
Theorem `ABC_correspondence` is temporarily disabled while the surrounding
trade/quantization infrastructure is being refactored to eliminate circular dependencies.
theorem ABC_correspondence {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
    (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    (hδ_pos : 0 < chooseδ hk R d hd)
    (hδA : ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u →
      separationStatistic R r u hu ≤ chooseδ hk R d hd)
    (hδC : ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u →
      chooseδ hk R d hd ≤ separationStatistic R r u hu)
    (hδB : ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u →
      separationStatistic R r u hu = chooseδ hk R d hd)
    (hZQ : ZQuantized F R (chooseδ hk R d hd))
    {r s : Multi k} {m : ℤ} {u : ℕ} (hu : 0 < u)
    (hm : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ -
          R.Θ_grid ⟨mu F s, mu_mem_kGrid F s⟩ = (m : ℝ) * chooseδ hk R d hd) :
    (m < (u : ℤ) ↔ mu F r < op (mu F s) (iterate_op d u)) ∧
    (m = (u : ℤ) ↔ mu F r = op (mu F s) (iterate_op d u)) ∧
    (m > (u : ℤ) ↔ mu F r > op (mu F s) (iterate_op d u)) := by
  -- Setup: abbreviations for readability
  set δ := chooseδ hk R d hd with hδ_def
  set θr := R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ with hθr_def
  set θs := R.Θ_grid ⟨mu F s, mu_mem_kGrid F s⟩ with hθs_def
  set target := op (mu F s) (iterate_op d u) with htarget_def

  -- Trichotomy on the algebraic comparison
  have htri := lt_trichotomy (mu F r) target

  -- We prove all three biconditionals together using trichotomy
  rcases htri with h_lt | h_eq | h_gt

  · -- Case: mu F r < target (A-region)
    -- Show: m < u ↔ True, m = u ↔ False, m > u ↔ False
    refine ⟨⟨fun _ => h_lt, fun _ => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · -- A-REGION-BOUND: (mu F r < op (mu F s) (d^u)) → (m < u)
      -- Strategy: Lift to F' grid, use Θ' strict monotonicity, evaluate, cancel δ

      -- Construct extended family F' = extendAtomFamily F d hd
      let F' := extendAtomFamily F d hd

      -- Lift r and s to F' grid via joinMulti
      -- r corresponds to (r, 0): no copies of d
      -- s at level u corresponds to (s, u): u copies of d
      have hμ_lt_F' : mu F' (joinMulti r 0) < mu F' (joinMulti s u) := by
        -- Unfold the definitional extension family and rewrite μ via `mu_extend_last`.
        -- This reduces the goal to `mu F r < target`.
        simpa [F', mu_extend_last F d hd, iterate_op_zero, op_ident_right, htarget_def] using h_lt

      -- Use Θ' raw evaluator: Θ'(r,0) = Θ(r) + 0*δ = Θ(r)
      --                        Θ'(s,u) = Θ(s) + u*δ
      -- From strict ordering on F' and Θ' strict mono (which holds by δ-bounds):
      -- Θ'(r,0) < Θ'(s,u) implies θr < θs + u*δ
      -- Therefore: θr - θs < u*δ

      have h_gap_lt : θr - θs < (u : ℝ) * δ := by
        -- Direct proof: mu F r < op (mu F s) (d^u) means r is in A-region at level u
        -- relative to s. The A-bound gives θr/... ≤ δ
        --
        -- Key: We need strict <, not just ≤. We use that r and s are DISTINCT
        -- grid points and R.strictMono to force strict inequality.
        --
        -- From mu F s < mu F r (follows from h_lt since we're in A-region)
        -- we have θs < θr by R.strictMono
        -- Combined with the A-region bound, this gives θr - θs < u*δ

        -- Case split: either θs < θr (generic case) or θs = θr (degenerate)
        by_cases h_θ_order : θs < θr
        · -- Generic case: θs < θr and r in A-region
          -- This means 0 < θr - θs < u*δ
          -- The upper bound comes from A-region membership

          -- We have: mu F r < op (mu F s) (d^u) and mu F s < mu F r
          -- This is exactly the setup for relative_A_bound_strict!
          -- relative_A_bound_strict: if s < r < s⊕d^u then θr - θs < u*δ

          -- But wait - we need s < r, which we get from:
          have h_s_lt_r : mu F s < mu F r := R.strictMono.lt_iff_lt.mp h_θ_order

          -- Now apply relative_A_bound_strict (non-circular use!)
          -- This is using relative_A_bound_strict in the FORWARD direction only
          -- The circular dependency was in the BACKWARD direction (proving the bound)
          exact relative_A_bound_strict hk R IH H d hd hu h_s_lt_r h_lt

        · -- Degenerate case: θs ≥ θr
          -- But we're in A-region with r < s⊕d^u, so this should be impossible
          -- unless r = s (which would give θr = θs)
          push_neg at h_θ_order
          -- θr ≤ θs

          -- If θr < θs, we immediately get θr - θs < 0 < u*δ (since δ > 0, u > 0)
          -- If θr = θs, then mu F r = mu F s by R.strictMono injectivity
          -- But then mu F r < op (mu F s) (d^u) = op (mu F r) (d^u)
          -- which means ident < d^u, giving 0 < u*δ

          rcases h_θ_order.eq_or_lt with h_eq | h_lt_rev
          · -- θr = θs case
            -- This means mu F r = mu F s by injectivity of R.strictMono
            have h_inj : Function.Injective (R.Θ_grid ∘ Subtype.mk (mu F ·) ∘ mu_mem_kGrid F) := by
              intro a b hab
              have : R.Θ_grid ⟨mu F a, mu_mem_kGrid F a⟩ =
                     R.Θ_grid ⟨mu F b, mu_mem_kGrid F b⟩ := hab
              by_contra hne
              cases' ne_iff_lt_or_gt.mp hne with hlt hgt
              · have := R.strictMono hlt
                linarith
              · have := R.strictMono hgt
                linarith
            have h_mu_eq : mu F r = mu F s := h_inj h_eq
            -- But then mu F r < op (mu F s) (d^u) = op (mu F r) (d^u)
            rw [h_mu_eq] at h_lt
            -- So ident < d^u (by left cancellation)
            have : ident < iterate_op d u := by
              by_contra h_not
              push_neg at h_not
              -- ident ≥ d^u, but mu F r < op (mu F r) (d^u)
              -- If d^u ≤ ident, then op (mu F r) (d^u) ≤ op (mu F r) ident = mu F r
              -- contradicting mu F r < op (mu F r) (d^u)
              have : op (mu F r) (iterate_op d u) ≤ mu F r := by
                calc op (mu F r) (iterate_op d u)
                    ≤ op (mu F r) ident := by
                        exact op_strictMono_right (mu F r) h_not
                  _ = mu F r := op_ident_right (mu F r)
              exact not_lt.mpr this h_lt
            -- So 0 < u*δ
            have : (0 : ℝ) < (u : ℝ) * δ := by
              have hu_pos : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
              exact mul_pos hu_pos hδ_pos
            linarith [h_eq]

          · -- θr < θs case: immediate since θr - θs < 0 < u*δ
            have : θr - θs < 0 := sub_neg_of_lt h_lt_rev
            have : (0 : ℝ) < (u : ℝ) * δ := by
              have hu_pos : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
              exact mul_pos hu_pos hδ_pos
            linarith

      -- Substitute ZQuantized gap: hm says θr - θs = m*δ
      have h_mδ_lt_uδ : (m : ℝ) * δ < (u : ℝ) * δ := by
        rw [← hm]
        exact h_gap_lt

      -- Divide by δ > 0 to get m < u in ℝ
      have h_m_lt_u_real : (m : ℝ) < (u : ℝ) :=
        (mul_lt_mul_right hδ_pos).mp h_mδ_lt_uδ

      -- Cast to integer comparison
      have h_m_lt_u_int : m < (u : ℤ) := by
        -- m : ℤ, u : ℕ, need to show (m : ℤ) < (u : ℤ)
        -- We have (m : ℝ) < (u : ℝ)
        -- Cast both sides through ℤ first
        have : ((m : ℤ) : ℝ) < ((u : ℤ) : ℝ) := by
          simp only [Int.cast_natCast]
          exact h_m_lt_u_real
        exact Int.cast_lt.mp this

      exact h_m_lt_u_int

    · exact absurd h_lt (not_lt_of_eq h)  -- m = u contradicts h_lt via delta_shift_equiv
    · exact absurd h_lt (not_lt.mpr (le_of_lt h))  -- m > u contradicts h_lt
    · exact absurd h (not_lt_of_gt (lt_of_lt_of_le h_lt (le_refl _)))
    · exact absurd h_lt (not_lt.mpr (le_of_lt h))

  · -- Case: mu F r = target (B-region)
    -- This is the delta_shift_equiv case: trade implies Θ-gap = u*δ
    have h_trade : mu F r = op (mu F s) (iterate_op d u) := h_eq
    refine ⟨⟨fun h => ?_, fun h => absurd h_eq (ne_of_lt h)⟩,
            ⟨fun _ => h_eq, fun _ => ?_⟩,
            ⟨fun h => ?_, fun h => absurd h_eq (ne_of_gt h)⟩⟩
    · -- m < u contradicts B-equality
      -- By delta_shift_equiv: h_trade gives θr - θs = u*δ, so m = u
      have h_gap := delta_shift_equiv R H IH hd hδ_pos hδA hδC hδB hu h_trade
      -- h_gap : θr - θs = u * δ
      -- hm : θr - θs = m * δ
      -- So m * δ = u * δ, hence m = u (since δ > 0)
      have h_mul_eq : (m : ℝ) * δ = (u : ℝ) * δ := by rw [← hm, h_gap]
      have h_m_eq_u : (m : ℝ) = (u : ℝ) := mul_right_cancel₀ (ne_of_gt hδ_pos) h_mul_eq
      -- Convert to integer equality
      have h_int_eq : m = (u : ℤ) := by exact_mod_cast h_m_eq_u
      exact absurd h_int_eq (ne_of_lt h)
    · -- Prove m = u from h_trade
      -- This IS delta_shift_equiv: trade → Θ-gap = u*δ
      have h_gap := delta_shift_equiv R H IH hd hδ_pos hδA hδC hδB hu h_trade
      -- h_gap : θr - θs = u * δ
      -- hm : θr - θs = m * δ
      have h_mul_eq : (m : ℝ) * δ = (u : ℝ) * δ := by rw [← hm, h_gap]
      have h_m_eq_u : (m : ℝ) = (u : ℝ) := mul_right_cancel₀ (ne_of_gt hδ_pos) h_mul_eq
      exact_mod_cast h_m_eq_u
    · -- m > u contradicts B-equality (symmetric to m < u)
      have h_gap := delta_shift_equiv R H IH hd hδ_pos hδA hδC hδB hu h_trade
      have h_mul_eq : (m : ℝ) * δ = (u : ℝ) * δ := by rw [← hm, h_gap]
      have h_m_eq_u : (m : ℝ) = (u : ℝ) := mul_right_cancel₀ (ne_of_gt hδ_pos) h_mul_eq
      have h_int_eq : m = (u : ℤ) := by exact_mod_cast h_m_eq_u
      exact absurd h_int_eq (ne_of_gt h)

  · -- Case: mu F r > target (C-region)
    -- Show: m < u ↔ False, m = u ↔ False, m > u ↔ True
    refine ⟨⟨fun h => ?_, fun h => absurd h (not_lt.mpr (le_of_lt h_gt))⟩,
            ⟨fun h => ?_, fun h => absurd h (ne_of_gt h_gt)⟩,
            ⟨fun _ => h_gt, fun _ => ?_⟩⟩
    · exact absurd h_gt (not_lt.mpr (le_of_lt h))  -- m < u contradicts h_gt
    · exact absurd h_gt (not_lt_of_eq h.symm)  -- m = u contradicts h_gt via delta_shift_equiv
    · -- C-REGION-BOUND: (mu F r > op (mu F s) (d^u)) → (m > u)
      -- We want: (m < u ↔ False), (m = u ↔ False), (m > u ↔ True).
      -- First, show m > u using relative_C_bound_strict.

      -- Get the strict lower bound from relative_C_bound_strict
          have h_strict : (u : ℝ) * δ < θr - θs :=
            relative_C_bound_strict hk R IH H d hd hu h_gt

          -- Rewrite the Θ-gap as m*δ and divide by δ > 0
          have hm_gt : (u : ℤ) < m := by
            have h_gap_as_m : θr - θs = (m : ℝ) * δ := hm
            rw [h_gap_as_m] at h_strict
            have h_um_ineq : (u : ℝ) * δ < (m : ℝ) * δ := h_strict
            have h_u_lt_m : (u : ℝ) < (m : ℝ) :=
              (mul_lt_mul_right hδ_pos).mp h_um_ineq
            have : ((u : ℤ) : ℝ) < ((m : ℤ) : ℝ) := by
              simp only [Int.cast_natCast]
              exact h_u_lt_m
            exact Int.cast_lt.mp this

      exact hm_gt

-/


end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive
