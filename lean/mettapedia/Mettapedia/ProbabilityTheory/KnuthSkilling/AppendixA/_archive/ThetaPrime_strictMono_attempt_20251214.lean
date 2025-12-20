/-
ARCHIVE WARNING

This file preserves a disabled strict-monotonicity proof attempt that was previously
embedded (as a large comment block) inside:
  Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Core/Induction/ThetaPrime.lean

It is NOT imported by the build; it is kept only as reference material while the
current `StrictMono Θ'` proof is being rebuilt in `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Core/Induction/ThetaPrime.lean`.
-/

      /- Old proof attempt (disabled while refactoring):
      intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Θ']

      -- Get the δ-bounds for Theta'_well_defined
      have hδA := chooseδ_A_bound hk R IH H d hd
      have hδC := chooseδ_C_bound hk R IH H d hd
      have hδB := chooseδ_B_bound hk R IH d hd

      -- Extract witnesses
      set r_x := Classical.choose hx with hr_x_def
      set r_y := Classical.choose hy with hr_y_def

      -- Get specs: mu F' r_x = x and mu F' r_y = y
      have hμ_x : mu F' r_x = x := (Classical.choose_spec hx).symm
      have hμ_y : mu F' r_y = y := (Classical.choose_spec hy).symm

      -- Split into old + new components
      set r_old_x := (splitMulti r_x).1
      set t_x := (splitMulti r_x).2
      set r_old_y := (splitMulti r_y).1
      set t_y := (splitMulti r_y).2

      -- Round-trip through joinMulti/splitMulti
      have h_rx_join : r_x = joinMulti r_old_x t_x := (joinMulti_splitMulti r_x).symm
      have h_ry_join : r_y = joinMulti r_old_y t_y := (joinMulti_splitMulti r_y).symm

      -- Use mu_extend_last to express x and y
      have hx_eq : x = op (mu F r_old_x) (iterate_op d t_x) := by
        rw [← hμ_x, h_rx_join]
        exact mu_extend_last F d hd r_old_x t_x
      have hy_eq : y = op (mu F r_old_y) (iterate_op d t_y) := by
        rw [← hμ_y, h_ry_join]
        exact mu_extend_last F d hd r_old_y t_y

      -- The goal after simp [Θ'] is already in canonical form:
      -- R.Θ_grid(mu F r_old_x) + t_x*δ < R.Θ_grid(mu F r_old_y) + t_y*δ
      -- Case analysis on t_x vs t_y
      rcases lt_trichotomy t_x t_y with h_t_lt | h_t_eq | h_t_gt

      · -- Case: t_x < t_y
        -- Need: Θ(r_old_x) + t_x*δ < Θ(r_old_y) + t_y*δ
        --
        -- Strategy: Compare mu F r_old_x with mu F r_old_y
        by_cases h_mu_order : mu F r_old_x < mu F r_old_y

        · -- Sub-case A: mu F r_old_x < mu F r_old_y
          -- Use Theta'_strictMono_same_t at level t_x, then add the t difference
          have hθ_at_tx : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
            R.strictMono h_mu_order

          -- Since t_x < t_y, we have t_x*δ < t_y*δ
          have ht_ineq : (t_x : ℝ) * δ < (t_y : ℝ) * δ := by
            have h_delta_pos : 0 < δ := delta_pos
            have h_tx_lt_ty : (t_x : ℝ) < (t_y : ℝ) := Nat.cast_lt.mpr h_t_lt
            exact (mul_lt_mul_right h_delta_pos).mpr h_tx_lt_ty

          -- Combine: both Θ and t favor RHS
          linarith

        · -- Sub-case B: mu F r_old_y ≤ mu F r_old_x
          push_neg at h_mu_order
          -- In this case, since x < y but the old parts don't favor y,
          -- the t difference must compensate.
          -- From x < y: op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})

          rcases eq_or_lt_of_le h_mu_order with h_eq | h_gt

          · -- mu F r_old_x = mu F r_old_y
            -- Then Θ values are equal, and t_x < t_y gives the result
            -- Since t_x < t_y, we have t_x*δ < t_y*δ
            have ht_ineq : (t_x : ℝ) * δ < (t_y : ℝ) * δ := by
              have h_delta_pos : 0 < δ := delta_pos
              have h_tx_lt_ty : (t_x : ℝ) < (t_y : ℝ) := Nat.cast_lt.mpr h_t_lt
              nlinarith [sq_nonneg (t_y - t_x : ℝ), sq_nonneg δ]

            -- With mu F r_old_x = mu F r_old_y, the Θ parts are equal
            -- So the inequality follows from t_x < t_y alone
            calc R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (t_x : ℝ) * δ
                = R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_x : ℝ) * δ := by
                    simp only [h_eq]
              _ < R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_y : ℝ) * δ := by
                    linarith

          · -- mu F r_old_x > mu F r_old_y, t_x < t_y, but x < y
            -- **Proof strategy**: Show this case is impossible via contradiction.
            --
            -- From the orderings, we can derive bounds that contradict each other.
            -- Key: Use repetition/scaling to amplify the inequalities until the
            -- contradiction becomes apparent.

            -- Extract the α ordering from x < y
            have hxy_α : x < y := hxy

            -- Express in terms of split components
            have h_ordered : op (mu F r_old_x) (iterate_op d t_x) <
                             op (mu F r_old_y) (iterate_op d t_y) := by
              rw [← hx_eq, ← hy_eq]; exact hxy_α

            -- We have:
            -- (1) mu F r_old_x > mu F r_old_y (given h_gt)
            -- (2) t_x < t_y (given h_t_lt), so d^{t_x} < d^{t_y}
            -- (3) op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y}) (from x < y)
            --
            -- Strategy: Use (1) and (2) with monotonicity to bound the LHS from below
            -- and RHS from above, deriving a contradiction with (3).

            -- From (1) and left-monotonicity:
            -- op_strictMono_left z says: if x < y then op x z < op y z
            have h1 : op (mu F r_old_y) (iterate_op d t_x) <
                      op (mu F r_old_x) (iterate_op d t_x) :=
              op_strictMono_left (iterate_op d t_x) h_gt

            -- From (2) and right-monotonicity:
            -- op_strictMono_right z says: if x < y then op z x < op z y
            have h2 : op (mu F r_old_y) (iterate_op d t_x) <
                      op (mu F r_old_y) (iterate_op d t_y) :=
              op_strictMono_right (mu F r_old_y) (iterate_op_strictMono d hd h_t_lt)

            -- Chaining (by transitivity of <):
            -- op (mu F r_old_y) (d^{t_x}) < op (mu F r_old_x) (d^{t_x})  [by h1]
            -- op (mu F r_old_y) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})  [by h2]
            --
            -- These give us two independent lower bounds on different terms, but
            -- we CANNOT directly conclude op (mu F r_old_x) (d^{t_x}) ? op (mu F r_old_y) (d^{t_y})
            -- without knowing the relative magnitudes of the "gaps".
            --
            -- **MIXED COMPARISON (t_x < t_y, mu r_old_x > mu r_old_y case)**:
            -- Goal: Θ(r_old_x) + t_x*δ < Θ(r_old_y) + t_y*δ
            -- i.e., Θ(r_old_x) - Θ(r_old_y) < (t_y - t_x)*δ = Δ*δ
            --
            -- Key derivation from x < y:
            -- (mu F r_old_x) ⊕ d^{t_x} < (mu F r_old_y) ⊕ d^{t_y}
            -- = (mu F r_old_y) ⊕ d^{t_x} ⊕ d^Δ  (by iterate_op_add)
            -- By left-cancellation-like argument: mu F r_old_x < (mu F r_old_y) ⊕ d^Δ
            --
            -- So the gap between r_old_x and r_old_y is bounded by d^Δ.
            -- This should give Θ(r_old_x) - Θ(r_old_y) < Δ*δ.

            let Δ := t_y - t_x
            have hΔ_pos : 0 < Δ := Nat.sub_pos_of_lt h_t_lt
            have hΔ_eq : t_y = t_x + Δ := (Nat.add_sub_cancel' (le_of_lt h_t_lt)).symm

            -- Derive: mu F r_old_x < (mu F r_old_y) ⊕ d^Δ
            have h_gap_bound : mu F r_old_x < op (mu F r_old_y) (iterate_op d Δ) := by
              -- From x < y: (mu F r_old_x) ⊕ d^{t_x} < (mu F r_old_y) ⊕ d^{t_y}
              have h1 : op (mu F r_old_x) (iterate_op d t_x) <
                        op (mu F r_old_y) (iterate_op d t_y) := by
                rw [← hx_eq, ← hy_eq]; exact hxy
              -- Rewrite t_y = t_x + Δ
              rw [hΔ_eq, ← iterate_op_add] at h1
              -- h1 : (mu F r_old_x) ⊕ d^{t_x} < (mu F r_old_y) ⊕ d^Δ ⊕ d^{t_x}
              -- Use associativity: (mu F r_old_y) ⊕ d^Δ ⊕ d^{t_x} = ((mu F r_old_y) ⊕ d^Δ) ⊕ d^{t_x}
              rw [← op_assoc (mu F r_old_y) (iterate_op d t_x) (iterate_op d Δ)] at h1
              -- Now use "left cancellation": if a ⊕ c < b ⊕ c then a < b
              -- This follows from strict monotonicity being injective
              by_contra h_not_lt
              push_neg at h_not_lt
              have h2 : op (op (mu F r_old_y) (iterate_op d Δ)) (iterate_op d t_x) ≤
                        op (mu F r_old_x) (iterate_op d t_x) := by
                rcases eq_or_lt_of_le h_not_lt with h_eq | h_lt
                · rw [h_eq]
                · exact le_of_lt (op_strictMono_left (iterate_op d t_x) h_lt)
              exact not_lt_of_le h2 h1

            -- Now: mu F r_old_x > mu F r_old_y (h_gt) but mu F r_old_x < (mu F r_old_y) ⊕ d^Δ
            -- The Θ-gap is bounded: Θ(r_old_x) - Θ(r_old_y) < Δ * δ
            --
            -- Strategy: Use the A-bound. Since mu F r_old_x < (mu F r_old_y) ⊕ d^Δ,
            -- and we need Θ(r_old_x) - Θ(r_old_y) < Δ*δ.

            -- We have θx := Θ(r_old_x) and θy := Θ(r_old_y)
            let θx := R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩
            let θy := R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩

            -- From h_gt: μ r_old_x > μ r_old_y, so θx > θy (by R.strictMono)
            have hθx_gt_θy : θx > θy := R.strictMono h_gt

            -- Goal: θx + t_x*δ < θy + t_y*δ, i.e., θx - θy < Δ*δ
            -- Using iterate_op_add:
            have h_Δ_decomp : iterate_op d t_y = op (iterate_op d t_x) (iterate_op d Δ) := by
              rw [hΔ_eq, iterate_op_add]

            -- The key bound: θx - θy < Δ * δ
            -- This follows from h_gap_bound and the separation structure.
            --
            -- Specifically, since mu F r_old_x < (mu F r_old_y) ⊕ d^Δ and mu F r_old_x > mu F r_old_y,
            -- r_old_x is in A(Δ) relative to r_old_y (in a shifted sense).
            -- The A-bound gives: (θx - θy) / Δ ≤ δ (approximately).
            -- But we need STRICT inequality.
            --
            -- Use ZQuantized: θx - θy = m * δ for some integer m.
            -- From h_gap_bound: m < Δ (because r_old_x is STRICTLY below r_old_y ⊕ d^Δ)
            -- So θx - θy ≤ (Δ-1) * δ < Δ * δ.

            -- Since strict inequality requires careful handling, use the order directly:
            -- We need: θx + t_x*δ < θy + t_y*δ
            -- Rearranging: θx - θy < (t_y - t_x)*δ = Δ*δ

            -- Direct approach: combine the bounds we have
            have h_t_ineq : ((t_x : ℕ) : ℝ) * δ < ((t_y : ℕ) : ℝ) * δ := by
              have h_delta_pos : 0 < δ := delta_pos
              have h_tx_lt_ty : (t_x : ℝ) < (t_y : ℝ) := Nat.cast_lt.mpr h_t_lt
              exact (mul_lt_mul_right h_delta_pos).mpr h_tx_lt_ty

            -- The gap θx - θy is positive (from hθx_gt_θy) but bounded by Δ*δ
            -- This follows from h_gap_bound: r_old_x < r_old_y ⊕ d^Δ
            -- Using the representation being order-preserving on extensions:
            --
            -- Consider in the (k+1)-grid: r_old_y ⊕ d^Δ has Θ' = θy + Δ*δ
            -- r_old_x (viewed in k+1 grid with t=0) has Θ' = θx + 0 = θx
            -- From r_old_x < r_old_y ⊕ d^Δ in the algebra, we expect θx < θy + Δ*δ
            --
            -- Since we're constructing Θ' to be strictly monotone, this should hold
            -- by the way δ was chosen (satisfying A/C bounds).

            -- The A/C bounds ensure: for any x in A(u), θ(x)/u ≤ δ
            -- Here, r_old_x < (mu F r_old_y) ⊕ d^Δ is like A-membership relative to r_old_y.

            -- For now, use the fact that the goal reduces to showing θx - θy < Δ*δ
            -- which should follow from h_gap_bound and the separation structure.
            -- The complete proof requires showing the A-bound applies in this relative setting.

            -- Simplified proof using just the ordering structure:
            -- From hθx_gt_θy: θx > θy, so θx - θy > 0
            -- From h_t_ineq: t_x*δ < t_y*δ
            -- Together: θx + t_x*δ ? θy + t_y*δ
            --
            -- The ordering x < y encodes that the "t advantage" outweighs the "θ disadvantage".
            -- In the representation framework, this is captured by the A/C separation bounds.

            -- Since the detailed proof requires additional infrastructure (relative A-bounds),
            -- keep a TODO marker but with more context:
            suffices h_bound : θx - θy < Δ * δ by linarith

            -- Use ZQuantized to express the gap as an integer multiple
            obtain ⟨m, hm⟩ := ZQuantized_diff hZQ r_old_x r_old_y

            -- Goal: show m < Δ, which gives θx - θy = m*δ < Δ*δ
            -- From h_gap_bound: r_old_x < r_old_y ⊕ d^Δ
            -- Strategy: Use that both sides are ⊕'d with d^{t_x} to lift to (k+1)-grid,
            -- then use delta_shift_equiv on a suitable trade witness.
            --
            -- Consider joinMulti r_old_x t_y vs joinMulti r_old_y t_y in F':
            -- From h_gap_bound and associativity:
            -- r_old_x ⊕ d^{t_y} < (r_old_y ⊕ d^Δ) ⊕ d^{t_y} = r_old_y ⊕ d^{Δ+t_y}

            -- We need a tighter bound. Use that h_gap_bound is STRICT.
            -- If we had r_old_x = r_old_y ⊕ d^Δ, then by strictMono: θx = θy + Δ*δ (using delta_shift_equiv)
            -- But h_gap_bound is <, so θx < θy + Δ*δ
            -- With ZQuantized: θx - θy = m*δ and θx - θy < Δ*δ gives m < Δ

            -- The key: treat r_old_y ⊕ d^Δ as a "virtual" extension level
            -- and use that r_old_x is strictly below it.
            --
            -- By GridBridge/Archimedean, we can find a witness r_bridge such that:
            -- r_old_x ≤ r_bridge < r_old_y ⊕ d^Δ  and r_bridge ∈ kGrid F
            --
            -- Then θx ≤ θ(r_bridge) < θy + Δ*δ by bounds on the bridge.

            -- **KEY K&S INSIGHT**: Strict algebraic inequality + ZQuantized = strict Θ inequality
            --
            -- If m = Δ, then θx - θy = Δ*δ exactly. By delta_shift_equiv (in reverse),
            -- this would require mu F r_old_x = op (mu F r_old_y) (iterate_op d Δ).
            -- But h_gap_bound says r_old_x < r_old_y ⊕ d^Δ (STRICT). Contradiction!
            -- So m ≤ Δ - 1, hence θx - θy ≤ (Δ-1)*δ < Δ*δ.

            have hm_lt : m < (Δ : ℤ) := by
              by_contra h_not_lt
              push_neg at h_not_lt
              -- h_not_lt : m ≥ Δ, so m ≥ Δ ≥ 1 (since Δ = t_y - t_x > 0)

              -- From θx - θy = m*δ ≥ Δ*δ and ZQuantized, we can derive r_old_x ≥ r_old_y ⊕ d^Δ
              -- which contradicts h_gap_bound: r_old_x < r_old_y ⊕ d^Δ
              --
              -- The key is that δ is precisely calibrated (via chooseδ) so that
              -- Δ*δ corresponds to exactly Δ "d-steps" in the representation.

              -- For the contradiction: consider joinMulti r_old_y Δ in F' (the (k+1)-grid).
              -- Its μ-value is: mu F r_old_y ⊕ d^Δ
              -- Its Θ'-value is: θy + Δ*δ
              --
              -- Similarly, joinMulti r_old_x 0 has μ-value = mu F r_old_x and Θ'-value = θx.
              --
              -- If θx ≥ θy + Δ*δ, then in the (k+1)-grid ordering:
              -- Θ'(joinMulti r_old_x 0) ≥ Θ'(joinMulti r_old_y Δ)
              --
              -- Since Θ' is being constructed to be strictly monotone, this would mean
              -- mu F r_old_x ≥ mu F r_old_y ⊕ d^Δ in α. But h_gap_bound says <!

              -- The formal argument uses that Θ' strict mono is EQUIVALENT to the algebraic
              -- ordering being preserved. We're proving one direction (algebraic → Θ),
              -- and the above shows the contrapositive.

              -- Direct approach: From m ≥ Δ and θx - θy = m*δ:
              have h_θ_gap : θx - θy ≥ (Δ : ℝ) * δ := by
                have h1 : (m : ℝ) ≥ (Δ : ℝ) := Int.cast_le.mpr h_not_lt
                have h2 : θx - θy = (m : ℝ) * δ := hm
                rw [h2]
                have hδ_nonneg : 0 ≤ δ := le_of_lt delta_pos
                exact mul_le_mul_of_nonneg_right h1 hδ_nonneg

              -- From h_θ_gap: θx ≥ θy + Δ*δ
              -- We need to derive: mu F r_old_x ≥ mu F r_old_y ⊕ d^Δ
              -- This contradicts h_gap_bound.
              --
              -- The connection is through the representation being order-isomorphic.
              -- Since θx > θy (from h_gt and R.strictMono), and the gap is ≥ Δ*δ,
              -- the "d-step count" from r_old_y to r_old_x is at least Δ.
              --
              -- Formalized via: if θx - θy ≥ Δ*δ, then for the (k+1)-elements:
              -- joinMulti r_old_x 0 and joinMulti r_old_y Δ satisfy:
              -- Θ'(joinMulti r_old_x 0) = θx ≥ θy + Δ*δ = Θ'(joinMulti r_old_y Δ)
              --
              -- By Θ' monotonicity (being proven): mu F r_old_x ≥ mu F r_old_y ⊕ d^Δ

              -- But we're IN the monotonicity proof! To avoid circularity, observe:
              -- The ordering x < y on the (k+1)-grid ALREADY encodes that
              -- r_old_x ⊕ d^{t_x} < r_old_y ⊕ d^{t_y}. Combined with h_gap_bound,
              -- we derived that the Θ-gap must be < Δ*δ.
              --
              -- The direct contradiction: h_θ_gap says θx - θy ≥ Δ*δ,
              -- but we also have r_old_x < r_old_y ⊕ d^Δ from h_gap_bound.
              -- These are incompatible given δ is the exact "step size".

              -- Use hδA: for elements in A(u), statistic ≤ δ
              -- r_old_x < r_old_y ⊕ d^Δ means r_old_x is "A-like" at level Δ relative to r_old_y.
              -- So (θx - θy)/Δ ≤ δ, i.e., θx - θy ≤ Δ*δ.
              -- Combined with h_θ_gap (θx - θy ≥ Δ*δ), we get θx - θy = Δ*δ exactly.
              -- But then r_old_x is at EXACTLY level Δ relative to r_old_y,
              -- meaning mu F r_old_x = mu F r_old_y ⊕ d^Δ, contradicting h_gap_bound (<, not =).

              -- **KEY INSIGHT (K&S)**: If m ≥ Δ, then Θ'(joinMulti r_old_x 0) ≥ Θ'(joinMulti r_old_y Δ).
              -- But h_gap_bound says joinMulti r_old_x 0 < joinMulti r_old_y Δ algebraically.
              -- For Θ' to be strictly mono, we need < on Θ' values.
              --
              -- The contradiction: if m ≥ Δ, the Θ' formula FAILS to be order-preserving
              -- for the pair (joinMulti r_old_x 0, joinMulti r_old_y Δ).
              -- Since we're constructing Θ' to be order-preserving, this is impossible.
              --
              -- Formally: the pair (joinMulti r_old_x 0, joinMulti r_old_y Δ) with h_gap_bound
              -- requires θx < θy + Δ*δ for strict mono. If m ≥ Δ, we get θx ≥ θy + Δ*δ.

              -- Consider the two (k+1)-grid elements:
              -- a = joinMulti r_old_x 0 with Θ'(a) = θx
              -- b = joinMulti r_old_y Δ with Θ'(b) = θy + Δ*δ
              -- By h_gap_bound: μ(a) = mu F r_old_x < mu F r_old_y ⊕ d^Δ = μ(b)
              -- So a < b in the (k+1)-grid.

              -- If m = Δ: Θ'(a) = θx = θy + Δ*δ = Θ'(b)
              -- Two different elements (a ≠ b since μ(a) < μ(b)) have the same Θ' value.
              -- This violates strict monotonicity (which requires injectivity).

              -- If m > Δ: Θ'(a) > Θ'(b) but μ(a) < μ(b).
              -- The Θ' ordering is opposite to the algebraic ordering.
              -- This violates strict monotonicity (order-reversing).

              -- In both cases, Θ' fails to be strictly mono for (a, b).
              -- But we're CONSTRUCTING Θ' to be strictly mono for ALL pairs including (a, b).
              -- The assumption m ≥ Δ makes this impossible for (a, b).

              -- For the formal contradiction, we observe:
              -- When t_x = 0: the pair (a, b) = (x, y), and h_θ_gap directly contradicts
              -- the goal θx - θy < Δ*δ from suffices.
              -- When t_x > 0: use that (a, b) has t_x' = 0 < t_x for induction.

              -- Since h_gap_bound ensures μ(a) ≠ μ(b) (strict <), and h_θ_gap gives
              -- Θ'(a) = θx ≥ θy + Δ*δ = Θ'(b), we have Θ'(a) ≥ Θ'(b).
              -- For m = Δ: Θ'(a) = Θ'(b), but a < b. Contradiction with strict mono requirement.
              -- For m > Δ: Θ'(a) > Θ'(b), but a < b. Also contradiction.

              -- The formal derivation: assume m ≥ Δ leads to the Θ' formula not working.
              -- Since the formula IS designed to work (via chooseδ), this is impossible.
              -- More precisely: the chooseδ constraints ensure m < Δ for such configurations.

              -- Use the explicit contradiction: h_θ_gap gives θx - θy ≥ Δ*δ.
              -- The pair (joinMulti r_old_x 0, joinMulti r_old_y Δ) with μ-ordering from h_gap_bound
              -- needs Θ' to give < ordering. h_θ_gap says Θ' gives ≥ ordering. Contradiction.

              -- This is ultimately an A-bound argument: r_old_x in A-region means bounded Θ-gap.
              -- Formalize via: if (θx - θy)/Δ ≥ δ, then r_old_x would be in C-region, not A.
              -- But h_gap_bound puts r_old_x in A-region. So (θx - θy)/Δ < δ, giving m < Δ.

              -- For this formalization, we note that the separation bound from chooseδ
              -- constrains the Θ-values on the k-grid in a way that prevents m ≥ Δ.
              have h_contra : θx - θy ≥ (Δ : ℝ) * δ ∧ θx - θy < (Δ : ℝ) * δ → False := by
                intro ⟨h_ge, h_lt⟩
                linarith

              -- The key: showing θx - θy < Δ*δ follows from h_gap_bound via A-bound.
              -- Since r_old_y < r_old_x < r_old_y ⊕ d^Δ, the k-grid Θ-values satisfy
              -- the separation constraint: (θx - θy)/Δ ≤ δ (from A-membership structure).
              -- Combined with h_gap_bound being strict: (θx - θy)/Δ < δ.

              -- For now, we derive the contradiction by observing that the suffices goal
              -- θx - θy < Δ*δ is incompatible with h_θ_gap: θx - θy ≥ Δ*δ.
              -- The suffices is proven AFTER we establish m < Δ, but inside by_contra,
              -- we've assumed the opposite (m ≥ Δ), leading to h_θ_gap.
              -- The contradiction comes from the structure of the chooseδ bounds.

              -- Apply the A-bound reasoning: from h_gap_bound and h_gt, r_old_x is in
              -- the A-region relative to r_old_y at level Δ. The A-bound from chooseδ
              -- ensures (θx - θy)/Δ < δ for elements strictly in A (not on boundary B).
              -- Hence θx - θy < Δ*δ, contradicting h_θ_gap.

              -- The direct formalization uses that ZQuantized + A-bound gives m ≤ Δ,
              -- and strictness of h_gap_bound (not ≤ but <) gives m ≠ Δ, hence m < Δ.
              -- With m ≥ Δ from h_not_lt, we get m = Δ (omega on m ≤ Δ, m ≥ Δ).
              -- Then strictness argument gives contradiction.

              -- Step 1: Show m ≤ Δ from A-bound reasoning
              -- r_old_x in A-region means: mu F r_old_y < mu F r_old_x < mu F r_old_y ⊕ d^Δ
              -- This is exactly h_gt and h_gap_bound. By the chooseδ A-bound property,
              -- elements in this region have bounded Θ-gap.

              -- For the complete proof, we'd need a lemma:
              -- relative_A_bound : h_gt → h_gap_bound → θx - θy ≤ Δ*δ
              -- Then with h_not_lt (m ≥ Δ), we get m = Δ.
              -- Strictness of h_gap_bound then gives contradiction.

              -- Using the existing hδA structure applied to the (k+1)-grid comparison:
              -- The element joinMulti r_old_x 0 compared to joinMulti r_old_y Δ
              -- satisfies the A-region constraints. By the separation statistic bounds,
              -- θx < θy + Δ*δ, contradicting h_θ_gap.

              -- **DIRECT PROOF**: Use that for the ordered pair (a, b) with a < b,
              -- strict mono requires Θ'(a) < Θ'(b). h_θ_gap gives Θ'(a) ≥ Θ'(b).
              -- These are directly contradictory for the goal of strict mono.

              -- Since the goal of h_strictMono is ∀ x y, x < y → Θ'(x) < Θ'(y),
              -- and (a, b) = (joinMulti r_old_x 0, joinMulti r_old_y Δ) satisfies a < b,
              -- if we had Θ'(a) ≥ Θ'(b), the goal would fail for (a, b).
              -- The construction ensures this doesn't happen, hence m < Δ.

              -- The formal contradiction: h_θ_gap (from m ≥ Δ) implies the Θ' formula
              -- produces ≥ ordering for a pair that should have < ordering (by h_gap_bound).
              -- This inconsistency with the designed behavior of Θ' is the contradiction.

              -- **OMEGA FINISH**: From m ≥ Δ and the structure, derive False.
              -- The A-bound gives m ≤ Δ, so m = Δ. Then strictness gives m < Δ. Contradiction.
              -- For now, use that the proof goal (h_bound from suffices) is θx - θy < Δ*δ,
              -- and assuming its negation (via m ≥ Δ giving h_θ_gap: θx - θy ≥ Δ*δ)
              -- leads to the Θ' formula not being order-preserving, which contradicts
              -- the design of Θ' via chooseδ.

              -- The key external fact: by the way chooseδ picks δ, for any elements
              -- r, s in the k-grid with mu F s < mu F r < mu F s ⊕ d^u, we have
              -- R.Θ_grid(r) - R.Θ_grid(s) < u * δ (A-bound for k-grid).
              -- This is derivable from hδA + the inductive structure of R.

              -- Apply this with s = r_old_y, r = r_old_x, u = Δ:
              -- θx - θy < Δ * δ, contradicting h_θ_gap.

              -- For the formal derivation, we need the k-grid A-bound lemma.
              -- Here we use that the overall proof structure ensures consistency.

              -- **ULTIMATE CONTRADICTION**: The design of Θ' via Θ'_raw and chooseδ
              -- guarantees that for a < b (algebraically), we have Θ'(a) < Θ'(b).
              -- If m ≥ Δ, then for (a, b) = (joinMulti r_old_x 0, joinMulti r_old_y Δ),
              -- we have a < b but Θ'(a) ≥ Θ'(b), violating the guarantee.
              -- Since the guarantee holds (by construction), m < Δ.

              -- TODO: Formalize that the chooseδ constraints imply the k-grid A-bound.
              -- This is mathematically true but requires additional lemmas.

              -- **DIRECT PATH**: Use omega on the Integer bounds.
              -- From h_θ_gap: (m : ℝ) * δ ≥ (Δ : ℝ) * δ, so m ≥ Δ (since δ > 0).
              -- We have h_not_lt: m ≥ Δ. These are consistent, not contradictory.
              -- The contradiction must come from an EXTERNAL bound on m.

              -- The external bound is: by the A-region structure, m ≤ Δ.
              -- And by strict h_gap_bound, m ≠ Δ (else r_old_x would be on boundary B).
              -- So m < Δ, contradicting h_not_lt: m ≥ Δ.

              -- **USE RELATIVE A-BOUND**: Apply relative_A_bound_strict to get contradiction
              -- h_gt and h_gap_bound satisfy the hypotheses of relative_A_bound_strict
              have h_rel_bound := relative_A_bound_strict hk R IH H d hd hΔ_pos h_gt h_gap_bound
              -- h_rel_bound : θx - θy < Δ * δ (using that δ = chooseδ hk R d hd)
              -- But h_θ_gap says θx - θy ≥ Δ * δ
              -- Contradiction!
              linarith

            -- From m < Δ: m*δ < Δ*δ (since δ > 0)
            have hm_bound : (m : ℝ) * δ < (Δ : ℝ) * δ := by
              have h1 : (m : ℝ) < (Δ : ℝ) := Int.cast_lt.mpr hm_lt
              exact (mul_lt_mul_right delta_pos).mpr h1

            rw [hm] at hm_bound
            exact hm_bound

      · -- Case: t_x = t_y
        -- Since x < y and t_x = t_y, we have mu F r_old_x ⊕ d^t < mu F r_old_y ⊕ d^t
        -- By cancellative property, mu F r_old_x < mu F r_old_y
        rw [h_t_eq]
        -- Now goal: R.Θ_grid(...r_old_x...) + t_y*δ < R.Θ_grid(...r_old_y...) + t_y*δ

        -- First, extract the α ordering from the subtype ordering
        have hxy_α : x < y := hxy

        -- Express the ordering in terms of split components
        have h_ordered : op (mu F r_old_x) (iterate_op d t_x) < op (mu F r_old_y) (iterate_op d t_y) := by
          rw [← hx_eq, ← hy_eq]; exact hxy_α

        -- Since t_x = t_y, we can cancel the d^t term
        rw [h_t_eq] at h_ordered
        -- h_ordered : op (mu F r_old_x) (iterate_op d t_y) < op (mu F r_old_y) (iterate_op d t_y)

        -- Use contraposition: if mu F r_old_x ≥ mu F r_old_y, then the op would be ≥
        have h_mu_lt : mu F r_old_x < mu F r_old_y := by
          by_contra h_not_lt
          push_neg at h_not_lt
          have h_ge : op (mu F r_old_x) (iterate_op d t_y) ≥ op (mu F r_old_y) (iterate_op d t_y) := by
            rcases eq_or_lt_of_le h_not_lt with h_eq | h_lt
            · rw [h_eq]
            · exact le_of_lt ((op_strictMono_left (iterate_op d t_y)) h_lt)
          exact not_lt_of_ge h_ge h_ordered

        -- Now use R.strictMono (need to convert to subtype ordering)
        have hθ_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                     R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
          R.strictMono h_mu_lt
        linarith

      · -- Case: t_x > t_y
        -- Need: Θ(r_old_x) + t_x*δ < Θ(r_old_y) + t_y*δ
        -- Equivalently: Θ(r_old_y) - Θ(r_old_x) > (t_x - t_y)*δ
        --
        -- Since x < y and t_x > t_y, the old part r_old_y must be larger
        -- than r_old_x to overcome the t disadvantage.

        -- First, show that mu F r_old_x < mu F r_old_y (by contradiction)
        have h_mu_lt : mu F r_old_x < mu F r_old_y := by
          by_contra h_not_lt
          push_neg at h_not_lt
          -- h_not_lt : mu F r_old_y ≤ mu F r_old_x

          -- From x < y:
          have hxy_α : x < y := hxy
          rw [hx_eq, hy_eq] at hxy_α
          -- hxy_α : op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})

          -- Since t_x > t_y and iterate_op is strictly increasing:
          have h_dt_gt : iterate_op d t_y < iterate_op d t_x :=
            iterate_op_strictMono d hd h_t_gt

          -- By monotonicity: mu F r_old_x >= mu F r_old_y implies
          -- op (mu F r_old_x) (d^{t_x}) >= op (mu F r_old_y) (d^{t_x})
          have h1 : op (mu F r_old_y) (iterate_op d t_x) ≤ op (mu F r_old_x) (iterate_op d t_x) := by
            rcases eq_or_lt_of_le h_not_lt with h_eq | h_lt
            · rw [h_eq]
            · exact le_of_lt (op_strictMono_left (iterate_op d t_x) h_lt)

          -- By monotonicity: d^{t_y} < d^{t_x} implies
          -- op (mu F r_old_y) (d^{t_y}) < op (mu F r_old_y) (d^{t_x})
          have h2 : op (mu F r_old_y) (iterate_op d t_y) < op (mu F r_old_y) (iterate_op d t_x) :=
            (op_strictMono_right (mu F r_old_y)) h_dt_gt

          -- Combining: op (mu F r_old_y) (d^{t_y}) < ... <= op (mu F r_old_x) (d^{t_x})
          have h_ge : op (mu F r_old_y) (iterate_op d t_y) < op (mu F r_old_x) (iterate_op d t_x) :=
            lt_of_lt_of_le h2 h1

          -- But this gives y < x, contradicting x < y
          exact not_lt_of_gt h_ge hxy_α

        -- Now we have mu F r_old_x < mu F r_old_y, so Θ(r_old_x) < Θ(r_old_y)
        have hθ_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                     R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
          R.strictMono h_mu_lt

        -- Strategy (GPT-5 Pro): Use Theta'_shift_by to reduce to same t-level
        let Δ := t_x - t_y
        have hΔ_pos : 0 < Δ := Nat.sub_pos_of_lt h_t_gt
        have hΔ_eq : t_x = t_y + Δ := (Nat.add_sub_cancel' (le_of_lt h_t_gt)).symm

        -- Apply vertical shift: Θ'(x) = Θ'(joinMulti r_old_x t_y) + Δ*δ
        have h_x_shift : Θ' ⟨mu F' (joinMulti r_old_x t_x), mu_mem_kGrid F' (joinMulti r_old_x t_x)⟩ =
                         Θ' ⟨mu F' (joinMulti r_old_x t_y), mu_mem_kGrid F' (joinMulti r_old_x t_y)⟩ + (Δ : ℝ) * δ := by
          have := Theta'_shift_by r_old_x t_y Δ
          convert this using 2
          rw [hΔ_eq]

        -- Goal: Θ'(x) < Θ'(y)
        -- Expanding: Θ'(joinMulti r_old_x t_y) + Δ*δ < Θ'(joinMulti r_old_y t_y)
        -- Rearranging: Θ'(joinMulti r_old_x t_y) < Θ'(joinMulti r_old_y t_y) - Δ*δ
        -- Since mu F r_old_x < mu F r_old_y, we have Θ'(joinMulti r_old_x t_y) < Θ'(joinMulti r_old_y t_y)
        -- So we need: the Θ gap is > Δ*δ
        --
        -- The constraint x < y gives us: op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})
        --
        -- TO PROVE: Θ(r_old_y) - Θ(r_old_x) > Δ*δ
        --
        -- This requires showing that the old-part advantage (Θ(r_old_y) > Θ(r_old_x))
        -- is large enough to overcome the vertical disadvantage (Δ*δ).
        --
        -- **MIXED COMPARISON ISSUE** (t_x > t_y case):
        -- Need: Θ(r_old_y) - Θ(r_old_x) > Δ*δ where Δ = t_x - t_y > 0
        --
        -- The ordering x < y on combined values doesn't directly give us
        -- a quantitative bound on the Θ-gap. Approaches:
        -- (a) Use commutativity: op (mu F r_old_x) (d^Δ) < mu F r_old_y,
        --     then apply separation to get Θ-bound
        -- (b) Use delta_shift_equiv directly on the trade structure
        --
        -- We need to show the Θ-gap is large enough: Θ(r_old_y) - Θ(r_old_x) > Δ*δ
        -- From x < y and the monotonicity analysis, we know mu F r_old_x < mu F r_old_y
        -- The constraint x < y gives: op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})
        -- With t_x = t_y + Δ, this becomes:
        -- op (mu F r_old_x) (d^{t_y} ⊕ d^Δ) < op (mu F r_old_y) (d^{t_y})

        -- Using commutativity and associativity:
        -- op (op (mu F r_old_x) (d^Δ)) (d^{t_y}) < op (mu F r_old_y) (d^{t_y})
        -- By strict monotonicity, this implies:
        -- op (mu F r_old_x) (d^Δ) < mu F r_old_y

        -- So r_old_x ⊕ d^Δ < r_old_y, which means r_old_y is in C-region relative to r_old_x at level Δ
        -- This gives us: Θ(r_old_y) - Θ(r_old_x) > Δ*δ

        -- Derive: op (mu F r_old_x) (d^Δ) < mu F r_old_y from x < y
        have h_trade_bound : op (mu F r_old_x) (iterate_op d Δ) < mu F r_old_y := by
          -- From x < y: op (mu F r_old_x) (d^{t_x}) < op (mu F r_old_y) (d^{t_y})
          have h1 : op (mu F r_old_x) (iterate_op d t_x) <
                    op (mu F r_old_y) (iterate_op d t_y) := by
            rw [← hx_eq, ← hy_eq]; exact hxy
          -- Rewrite t_x = t_y + Δ
          have hΔ_eq : t_x = t_y + Δ := (Nat.add_sub_cancel' (le_of_lt h_t_gt)).symm
          rw [hΔ_eq, ← iterate_op_add] at h1
          -- h1 : op (mu F r_old_x) (d^{t_y} ⊕ d^Δ) < op (mu F r_old_y) (d^{t_y})
          rw [← op_assoc] at h1
          -- Use cancellation: if a ⊕ c < b ⊕ c then a < b
          by_contra h_not_lt
          push_neg at h_not_lt
          have h2 : op (mu F r_old_y) (iterate_op d t_y) ≤
                    op (op (mu F r_old_x) (iterate_op d Δ)) (iterate_op d t_y) := by
            rcases eq_or_lt_of_le h_not_lt with h_eq | h_lt
            · rw [h_eq]
            · exact le_of_lt (op_strictMono_left (iterate_op d t_y) h_lt)
          exact not_lt_of_le h2 h1

        -- Now we have: mu F r_old_x < op (mu F r_old_x) (d^Δ) < mu F r_old_y
        -- r_old_y is in C-region relative to r_old_x at level Δ
        -- We need to show Θ(r_old_y) - Θ(r_old_x) > Δ*δ

        -- Use ZQuantized: the Θ-gap is m*δ for some integer m
        have hZQ := ZQuantized_of_chooseδ hk R IH H d hd
        obtain ⟨m, hm_gap⟩ := ZQuantized_diff hZQ r_old_y r_old_x

        -- Define θx and θy for clarity
        set θx := R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩
        set θy := R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩

        -- From h_mu_lt: θy > θx (strict monotonicity)
        have hθ_lt : θx < θy := R.strictMono h_mu_lt

        -- We need: θy - θx > Δ*δ, i.e., m*δ > Δ*δ, i.e., m > Δ
        -- Proof by contradiction: if m ≤ Δ, then by relative_A_bound_strict,
        -- we'd have mu F r_old_y ≤ op (mu F r_old_x) (d^Δ), contradicting h_trade_bound

        have hm_gt_Δ : m > (Δ : ℤ) := by
          by_contra h_not_gt
          push_neg at h_not_gt
          -- h_not_gt : m ≤ Δ
          -- This means θy - θx = m*δ ≤ Δ*δ
          -- By the separation structure, this puts r_old_y in A or B region
          -- relative to r_old_x, contradicting h_trade_bound (which says C-region)

          -- Use ABC_correspondence to get mu F r_old_y ≤ op (mu F r_old_x) (d^Δ)
          have hABC := ABC_correspondence hk R IH H d hd
            (delta_pos hk R IH H d hd) (chooseδ_A_bound hk R IH H d hd)
            (chooseδ_C_bound hk R IH H d hd) (chooseδ_B_bound hk R IH d hd)
            hZQ hΔ_pos hm_gap
          rcases h_not_gt.eq_or_lt with h_eq | h_lt
          · -- m = Δ: B-boundary, so mu F r_old_y = op (mu F r_old_x) (d^Δ)
            have h_eq_mu : mu F r_old_y = op (mu F r_old_x) (iterate_op d Δ) :=
              hABC.2.1.mp h_eq
            exact absurd h_eq_mu (ne_of_gt h_trade_bound)
          · -- m < Δ: A-region, so mu F r_old_y < op (mu F r_old_x) (d^Δ)
            have h_lt_mu : mu F r_old_y < op (mu F r_old_x) (iterate_op d Δ) :=
              hABC.1.mp h_lt
            exact absurd h_trade_bound (not_lt.mpr (le_of_lt h_lt_mu))

        -- From m > Δ: θy - θx = m*δ > Δ*δ
        have hδ_pos : 0 < δ := delta_pos
        have h_gap_bound : θy - θx > (Δ : ℝ) * δ := by
          rw [hm_gap]
          have h1 : (Δ : ℝ) < (m : ℝ) := Int.cast_lt.mpr hm_gt_Δ
          exact (mul_lt_mul_right hδ_pos).mpr h1

        -- Now use h_gap_bound to establish strict monotonicity
        -- Goal: Θ'(x) < Θ'(y) where x = joinMulti r_old_x t_x, y = joinMulti r_old_y t_y
        -- We have Θ'(x) = θx + t_x*δ and Θ'(y) = θy + t_y*δ
        -- From h_x_shift: Θ'(x) = Θ'(joinMulti r_old_x t_y) + Δ*δ
        -- So we need: Θ'(joinMulti r_old_x t_y) + Δ*δ < Θ'(y)
        -- i.e., θx + t_y*δ + Δ*δ < θy + t_y*δ
        -- i.e., θx + Δ*δ < θy
        -- i.e., θy - θx > Δ*δ ✓ (this is h_gap_bound!)

        rw [h_x_shift]
        -- Goal: Θ'(joinMulti r_old_x t_y) + Δ*δ < Θ'(joinMulti r_old_y t_y)
        -- By Θ' definition: θx + t_y*δ + Δ*δ < θy + t_y*δ
        simp only [Θ', Theta'_raw]
        -- After unfolding, this reduces to θx + Δ*δ < θy, which is h_gap_bound
        linarith

    -/
