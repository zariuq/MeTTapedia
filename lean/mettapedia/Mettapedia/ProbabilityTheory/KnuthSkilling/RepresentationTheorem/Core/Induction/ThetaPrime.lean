import Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.Core.Induction.DeltaShift

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem

open Classical
open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra
open SandwichSeparation.SeparationToArchimedean

variable {α : Type*} [KnuthSkillingAlgebra α] [KSSeparation α]

/-!
## Θ' Infrastructure (core induction step `k → k+1`)

We define `Θ'` via a raw evaluator `Theta'_raw` and prove it is constant on μ-fibers of the
extended grid. This avoids `Classical.choose`-dependence in later additivity/monotonicity proofs.

### Executive Summary (for reviewers)
- The main theorem here is `extend_grid_rep_with_atom`, which constructs a `MultiGridRep` on the
  extended atom family `extendAtomFamily F d hd`.
- The *only* remaining explicit blocker for that construction is
  `ChooseδBaseAdmissible hk R d hd` (defined below): the chosen
  `δ := chooseδ hk R d hd` must be strictly base-admissible for every base `r0` and level `u > 0`
  (K&S Appendix A.3.4 “fixdelta → fixm” / base-invariance step).
- In the global `B = ∅` regime, `ChooseδBaseAdmissible` is equivalent to the older strict-gap
  interface `BEmptyStrictGapSpec`; see
  `Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Core/Induction/Goertzel.lean`.

### Note: `ZQuantized` vs `chooseδ` (legacy/optional)
Some older lemmas in this file assume `hZQ : ZQuantized F R (chooseδ hk R d hd)`, i.e. every
k-grid Θ-value is an integer multiple of the *new* δ. This is a strong commensurability premise:
it is **not** required by `extend_grid_rep_with_atom`, and it can fail even in additive models.

See:
- `Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Counterexamples/ZQuantizedBEmpty.lean`
- `Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Counterexamples/ZQuantizedBNonempty.lean`
-/

/-- Raw evaluator on witnesses for F': old part + t·δ. -/
noncomputable def Theta'_raw
  {k} {F : AtomFamily α k} (R : MultiGridRep F)
  (d : α) (δ : ℝ)
  (r_old : Multi k) (t : ℕ) : ℝ :=
  R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ

/-- **Key well-definedness**: Theta'_raw is constant on μ-fibers of F'.

This is the foundational lemma that makes Θ' well-defined despite using Classical.choose.
The proof uses the A/C separation bounds for δ to show that any two witnesses
with the same μ-value must yield the same Theta'_raw value.

**Proof strategy** (K&S "trade argument"):
- If mu F' r = mu F' s, write as: mu F r_old ⊕ d^t = mu F s_old ⊕ d^u
- Case t=u: Use R.strictMono + equality to conclude r_old = s_old
- Case t<u: Use A/C bounds to show (u-t)·δ equals the old-part difference
- Case t>u: Symmetric

The δ bounds (hδA, hδC) are precisely what make this work.
-/
lemma Theta'_well_defined
  {k} {F : AtomFamily α k} (R : MultiGridRep F)
  (H : GridComm F) (IH : GridBridge F) (d : α) (hd : ident < d)
  (δ : ℝ) (hδ_pos : 0 < δ)
  (hδA : ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u → separationStatistic R r u hu ≤ δ)
  (hδC : ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u → δ ≤ separationStatistic R r u hu)
  (hδB : ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u → separationStatistic R r u hu = δ)
  {r s : Multi (k+1)}
  (hμ : mu (extendAtomFamily F d hd) r = mu (extendAtomFamily F d hd) s) :
  @Theta'_raw α _ _ k F R d δ (splitMulti r).1 (splitMulti r).2 =
  @Theta'_raw α _ _ k F R d δ (splitMulti s).1 (splitMulti s).2 := by
  classical
  -- Extract the split components
  set r_old := (splitMulti r).1 with hr_old_def
  set t := (splitMulti r).2 with ht_def
  set s_old := (splitMulti s).1 with hs_old_def
  set u := (splitMulti s).2 with hu_def

  -- Use mu_extend_last to rewrite hμ
  -- We need to show: r and s round-trip through splitMulti/joinMulti
  have hr_roundtrip : r = joinMulti r_old t := by
    have := joinMulti_splitMulti r
    simp only [hr_old_def, ht_def] at this
    exact this.symm

  have hs_roundtrip : s = joinMulti s_old u := by
    have := joinMulti_splitMulti s
    simp only [hs_old_def, hu_def] at this
    exact this.symm

  have hμ_split : op (mu F r_old) (iterate_op d t) = op (mu F s_old) (iterate_op d u) := by
    have hr := mu_extend_last F d hd r_old t
    have hs := mu_extend_last F d hd s_old u
    rw [hr_roundtrip] at hμ
    rw [hs_roundtrip] at hμ
    rw [← hr, ← hs]
    exact hμ

  -- Trichotomy on t vs u (GPT-5.1 Pro's case split)
  rcases Nat.lt_trichotomy t u with (hlt | heq | hgt)

  · -- Case t < u: The "trade argument"
    -- We need to show: Θ'(r_old, t) = Θ'(s_old, u)
    -- Equivalently: Θ(r_old) + t·δ = Θ(s_old) + u·δ
    -- Equivalently: Θ(r_old) - Θ(s_old) = (u - t)·δ

    unfold Theta'_raw

    -- Extract Δ = u - t > 0
    have hΔ_def : u = t + (u - t) := by omega
    set Δ := u - t with hΔ_eq
    have hΔ_pos : 0 < Δ := by omega

    -- Key identity: d^u = d^t ⊕ d^Δ
    have hdu_split : iterate_op d u = op (iterate_op d t) (iterate_op d Δ) := by
      rw [hΔ_def]
      exact (iterate_op_add d t (u - t)).symm

    -- From hμ_split: mu F r_old ⊕ d^t = mu F s_old ⊕ d^u
    -- We want: mu F r_old = mu F s_old ⊕ d^Δ
    -- Check: (mu F s_old ⊕ d^Δ) ⊕ d^t = mu F s_old ⊕ (d^Δ ⊕ d^t) = mu F s_old ⊕ d^{Δ+t} = mu F s_old ⊕ d^u ✓
    have hμ_trade : mu F r_old = op (mu F s_old) (iterate_op d Δ) := by
      -- Direct proof: show op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) = RHS of hμ_split
      have hkey : op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) =
                  op (mu F s_old) (iterate_op d u) := by
        rw [op_assoc]
        congr 1
        have hΔt_eq_u : Δ + t = u := by omega
        rw [← hΔt_eq_u]
        exact iterate_op_add d Δ t
      -- So: op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) = op (mu F s_old) (iterate_op d u)
      --     = op (mu F r_old) (iterate_op d t)  [by hμ_split]
      -- Cancel (iterate_op d t) from both sides using strict monotonicity
      by_contra h_ne
      rcases Ne.lt_or_gt h_ne with (hlt | hgt)
      · -- mu F r_old < op (mu F s_old) (iterate_op d Δ)
        have h1 : op (mu F r_old) (iterate_op d t) <
                  op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) :=
          op_strictMono_left (iterate_op d t) hlt
        rw [hμ_split, hkey] at h1
        exact lt_irrefl _ h1
      · -- op (mu F s_old) (iterate_op d Δ) < mu F r_old
        have h1 : op (op (mu F s_old) (iterate_op d Δ)) (iterate_op d t) <
                  op (mu F r_old) (iterate_op d t) :=
          op_strictMono_left (iterate_op d t) hgt
        rw [hkey, ← hμ_split] at h1
        exact lt_irrefl _ h1

    -- The trade: r_old = s_old ⊕ d^Δ
    -- Goal: Show Θ(r_old) + t*δ = Θ(s_old) + u*δ
    -- Equivalently: Θ(r_old) - Θ(s_old) = (u - t)*δ = Δ*δ

    -- Apply the delta_shift_equiv lemma!
    have h_trade_eq := delta_shift_equiv R H IH hd hδ_pos hδA hδC hδB hΔ_pos hμ_trade
    -- h_trade_eq: Θ(r_old) - Θ(s_old) = Δ * δ

    -- Rearrange to get: Θ(r_old) + t*δ = Θ(s_old) + u*δ
    -- Since Δ = u - t, we have: Θ(r_old) - Θ(s_old) = (u - t) * δ
    -- So: Θ(r_old) = Θ(s_old) + (u - t) * δ
    -- And: Θ(r_old) + t*δ = Θ(s_old) + (u - t)*δ + t*δ = Θ(s_old) + u*δ

    -- Help linarith by providing explicit casts and the key relation
    have hΔ_real : (Δ : ℝ) = (u : ℝ) - (t : ℝ) := by
      simp only [hΔ_eq]
      exact Nat.cast_sub (le_of_lt hlt)

    -- Make the substitution explicit: θr = θs + Δ * δ
    have h_θr_eq : R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ =
                   R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + (Δ : ℝ) * δ := by
      linarith

    -- Now the goal becomes: (θs + Δ * δ) + t * δ = θs + u * δ
    -- Which simplifies to: Δ * δ + t * δ = u * δ
    -- Since Δ = u - t, this is: (u - t) * δ + t * δ = u * δ ✓

    -- Substitute and simplify algebraically
    calc R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ
        = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + (Δ : ℝ) * δ + (t : ℝ) * δ := by
            rw [h_θr_eq]
      _ = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + ((Δ : ℝ) + (t : ℝ)) * δ := by ring
      _ = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + (u : ℝ) * δ := by
            rw [hΔ_real]; ring

  · -- Case t = u: Use injectivity of R.strictMono
    unfold Theta'_raw
    -- Since t = u, the goal becomes Θ(r_old) + t*δ = Θ(s_old) + t*δ
    -- Need to show Θ(r_old) = Θ(s_old)
    simp only [heq]
    -- Now: mu F r_old ⊕ d^u = mu F s_old ⊕ d^u (by hμ_split with t = u)
    -- Use cancellation to get: mu F r_old = mu F s_old
    have hμ_split' : op (mu F r_old) (iterate_op d u) = op (mu F s_old) (iterate_op d u) := by
      rw [heq] at hμ_split; exact hμ_split
    have h_mu_eq : mu F r_old = mu F s_old := by
      -- Cancellation via strict monotonicity
      by_contra h_ne
      rcases Ne.lt_or_gt h_ne with (hlt | hgt)
      · -- If mu F r_old < mu F s_old, then op (mu F r_old) z < op (mu F s_old) z
        have : op (mu F r_old) (iterate_op d u) < op (mu F s_old) (iterate_op d u) :=
          op_strictMono_left (iterate_op d u) hlt
        rw [hμ_split'] at this
        exact lt_irrefl _ this
      · -- Symmetric case
        have : op (mu F s_old) (iterate_op d u) < op (mu F r_old) (iterate_op d u) :=
          op_strictMono_left (iterate_op d u) hgt
        rw [← hμ_split'] at this
        exact lt_irrefl _ this

    -- Since mu F r_old = mu F s_old and R.strictMono is injective on the grid
    have h_theta_eq : R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ =
                       R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ := by
      congr 1
      ext
      exact h_mu_eq

    -- Therefore the full expressions are equal
    rw [h_theta_eq]

  · -- Case t > u: Symmetric trade argument
    unfold Theta'_raw

    -- Extract Δ = t - u > 0
    have hΔ_def : t = u + (t - u) := by omega
    set Δ := t - u with hΔ_eq
    have hΔ_pos : 0 < Δ := by omega

    -- Key identity: d^t = d^u ⊕ d^Δ
    have hdt_split : iterate_op d t = op (iterate_op d u) (iterate_op d Δ) := by
      rw [hΔ_def]
      exact (iterate_op_add d u (t - u)).symm

    -- From hμ_split: mu F r_old ⊕ d^t = mu F s_old ⊕ d^u
    -- We want: mu F s_old = mu F r_old ⊕ d^Δ
    -- Check: (mu F r_old ⊕ d^Δ) ⊕ d^u = mu F r_old ⊕ (d^Δ ⊕ d^u) = mu F r_old ⊕ d^{Δ+u} = mu F r_old ⊕ d^t ✓
    have hμ_trade : mu F s_old = op (mu F r_old) (iterate_op d Δ) := by
      -- Direct proof: show op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) = LHS of hμ_split
      have hkey : op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) =
                  op (mu F r_old) (iterate_op d t) := by
        rw [op_assoc]
        congr 1
        have hΔu_eq_t : Δ + u = t := by omega
        rw [← hΔu_eq_t]
        exact iterate_op_add d Δ u
      -- So: op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) = op (mu F r_old) (iterate_op d t)
      --     = op (mu F s_old) (iterate_op d u)  [by hμ_split]
      -- Cancel (iterate_op d u) from both sides using strict monotonicity
      by_contra h_ne
      rcases Ne.lt_or_gt h_ne with (hlt | hgt)
      · -- mu F s_old < op (mu F r_old) (iterate_op d Δ)
        have h1 : op (mu F s_old) (iterate_op d u) <
                  op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) :=
          op_strictMono_left (iterate_op d u) hlt
        rw [← hμ_split, hkey] at h1
        exact lt_irrefl _ h1
      · -- op (mu F r_old) (iterate_op d Δ) < mu F s_old
        have h1 : op (op (mu F r_old) (iterate_op d Δ)) (iterate_op d u) <
                  op (mu F s_old) (iterate_op d u) :=
          op_strictMono_left (iterate_op d u) hgt
        rw [hkey, hμ_split] at h1
        exact lt_irrefl _ h1

    -- Symmetric trade: s_old = r_old ⊕ d^Δ
    -- Goal: Show Θ(r_old) + t*δ = Θ(s_old) + u*δ
    -- Equivalently: Θ(s_old) - Θ(r_old) = (t - u)*δ = Δ*δ

    -- Apply delta_shift_equiv with s_old as the "larger" element
    have h_trade_eq := delta_shift_equiv R H IH hd hδ_pos hδA hδC hδB hΔ_pos hμ_trade
    -- h_trade_eq: Θ(s_old) - Θ(r_old) = Δ * δ

    -- Rearrange to get: Θ(r_old) + t*δ = Θ(s_old) + u*δ
    -- Since Δ = t - u, we have: Θ(s_old) - Θ(r_old) = (t - u) * δ
    -- So: Θ(s_old) = Θ(r_old) + (t - u) * δ
    -- And: Θ(r_old) + t*δ = Θ(r_old) + u*δ + (t-u)*δ = Θ(s_old) + u*δ

    -- Help linarith by providing explicit casts and the key relation
    have hΔ_real : (Δ : ℝ) = (t : ℝ) - (u : ℝ) := by
      simp only [hΔ_eq]
      exact Nat.cast_sub (le_of_lt hgt)

    -- Make the substitution explicit: θs = θr + Δ * δ
    have h_θs_eq : R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ =
                   R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (Δ : ℝ) * δ := by
      linarith

    -- Now the goal becomes: θr + t * δ = (θr + Δ * δ) + u * δ
    -- Which simplifies to: t * δ = Δ * δ + u * δ = (Δ + u) * δ
    -- Since Δ = t - u, this is: t * δ = (t - u + u) * δ = t * δ ✓

    -- Substitute and simplify algebraically
    calc R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ
        = R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + ((Δ : ℝ) + (u : ℝ)) * δ := by
            rw [hΔ_real]; ring
      _ = R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (Δ : ℝ) * δ + (u : ℝ) * δ := by ring
      _ = R.Θ_grid ⟨mu F s_old, mu_mem_kGrid F s_old⟩ + (u : ℝ) * δ := by rw [← h_θs_eq]

/-- **Crossing Characterization**: In B-empty case, elements are strictly separated from boundaries.

For any element r in extensionSetA at level u, we have μr < d^u strictly because
B is empty (equality would put r in B). This strict inequality is the key to showing
that no A-statistic can achieve the supremum δ. -/
lemma strict_inequality_B_empty
    {k : ℕ} {F : AtomFamily α k} (d : α)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (r : Multi k) (u : ℕ) (hu : 0 < u) (hrA : r ∈ extensionSetA F d u) :
    mu F r < iterate_op d u := by
  -- r ∈ A means μr < d^u (possibly equal)
  have hr_le : mu F r < iterate_op d u := hrA
  -- But equality would put r in B, contradicting B-empty
  have hr_ne : mu F r ≠ iterate_op d u := by
    intro h_eq
    have : r ∈ extensionSetB F d u := by
      simpa [extensionSetB] using h_eq
    exact hB_empty r u hu this
  -- Therefore the inequality is strict
  exact lt_of_le_of_ne (le_of_lt hr_le) hr_ne

/-- **Key Lemma (A-side strictness)**: An A-statistic is strictly below `δ`.

If `μ(F,r) < d^u`, then the separation statistic `Θ(μ(F,r))/u` is strictly less than
`δ := chooseδ hk R d hd`.

This uses the abstract `KSSeparation` property to build a strictly larger statistic that is still
bounded by `δ` via the A/B bounds at a suitable scaled level, following the K&S
repetition/separation argument. -/
lemma A_statistic_lt_chooseδ
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (IH : GridBridge F)
    (d : α) (hd : ident < d)
    [KSSeparation α]
    (r : Multi k) (u : ℕ) (hu : 0 < u) (hrA : r ∈ extensionSetA F d u) :
    separationStatistic R r u hu < chooseδ hk R d hd := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  have hδ_pos : 0 < δ := by simpa [δ] using delta_pos hk R IH H d hd

  -- If μr = ident, then the statistic is 0 < δ.
  by_cases hμr : mu F r = ident
  · have hθr : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ = 0 := by
      have hsub :
          (⟨mu F r, mu_mem_kGrid F r⟩ : {x // x ∈ kGrid F}) = ⟨ident, ident_mem_kGrid F⟩ := by
        ext
        simpa [hμr]
      simpa [hsub] using R.ident_eq_zero
    have hstat0 : separationStatistic R r u hu = 0 := by
      simp [separationStatistic, hθr]
    linarith [hstat0, hδ_pos]

  -- Otherwise, μr is positive; use KSSeparation to build a strictly larger A/B-statistic ≤ δ.
  have hμr_pos : ident < mu F r := by
    exact lt_of_le_of_ne (ident_le (mu F r)) (Ne.symm hμr)
  have hd_pow_pos : ident < iterate_op d u := iterate_op_pos d hd u hu

  have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  let i₀ : Fin k := ⟨0, hk_pos⟩
  let a : α := F.atoms i₀
  have ha : ident < a := F.pos i₀

  obtain ⟨n, m, hm_pos, h_gap, h_in_y⟩ :=
    KSSeparation.separation (a := a) (x := mu F r) (y := iterate_op d u) ha hμr_pos hd_pow_pos hrA

  have huM_pos : 0 < u * m := Nat.mul_pos hu hm_pos

  -- Convert the separator inequality to a Θ-inequality on the grid.
  have hμ_gap_grid : mu F (scaleMult m r) < mu F (unitMulti i₀ n) := by
    have hμ_left : mu F (scaleMult m r) = iterate_op (mu F r) m := IH.bridge r m
    have hμ_right : mu F (unitMulti i₀ n) = iterate_op a n := by
      simpa [a] using (mu_unitMulti F i₀ n)
    simpa [hμ_left, hμ_right] using h_gap

  have hθ_gap_grid :
      R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ <
        R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ :=
    R.strictMono hμ_gap_grid

  have hθ_scale :
      R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ =
        m * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ :=
    Theta_scaleMult (R := R) (r := r) m

  have hθ_lt :
      (m : ℝ) * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ <
        R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ := by
    simpa [hθ_scale] using hθ_gap_grid

  -- Turn that Θ-inequality into a strict statistic inequality.
  have hstat_lt :
      separationStatistic R r u hu <
        separationStatistic R (unitMulti i₀ n) (u * m) huM_pos := by
    have hu_pos_real : 0 < (u : ℝ) := Nat.cast_pos.mpr hu
    have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
    have hθ_div :
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ <
          R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / (m : ℝ) := by
      have hmul :
          R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ * (m : ℝ) <
            R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hθ_lt
      exact (lt_div_iff₀ hm_pos_real).2 hmul
    have hθ_div_u :
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / (u : ℝ) <
          (R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / (m : ℝ)) / (u : ℝ) :=
      div_lt_div_of_pos_right hθ_div hu_pos_real
    simpa [separationStatistic, Nat.cast_mul, div_div, mul_assoc, mul_comm, mul_left_comm] using hθ_div_u

  -- Bound the target statistic by δ using A/B cases at level (u*m).
  have h_in_bound : separationStatistic R (unitMulti i₀ n) (u * m) huM_pos ≤ δ := by
    have hμ_right : mu F (unitMulti i₀ n) = iterate_op a n := by
      simpa [a] using (mu_unitMulti F i₀ n)
    have h_y_pow : iterate_op (iterate_op d u) m = iterate_op d (u * m) := by
      simpa using (iterate_op_mul d u m)
    have h_le : iterate_op a n ≤ iterate_op d (u * m) := by
      simpa [h_y_pow] using h_in_y
    rcases lt_or_eq_of_le h_le with hlt | heq
    · have hA : unitMulti i₀ n ∈ extensionSetA F d (u * m) := by
        simp [extensionSetA, Set.mem_setOf_eq, hμ_right, hlt]
      have hA_le := chooseδ_A_bound hk R IH H d hd (unitMulti i₀ n) (u * m) huM_pos hA
      simpa [δ] using hA_le
    · have hB : unitMulti i₀ n ∈ extensionSetB F d (u * m) := by
        simp [extensionSetB, Set.mem_setOf_eq, hμ_right, heq]
      have hB_eq := chooseδ_B_bound hk R IH d hd (unitMulti i₀ n) (u * m) huM_pos hB
      have : separationStatistic R (unitMulti i₀ n) (u * m) huM_pos = δ := by
        simpa [δ] using hB_eq
      exact le_of_eq this

  exact lt_of_lt_of_le hstat_lt h_in_bound

/-- In the globally B-empty case, every k-grid point lies in its *floor bracket* w.r.t. `δ`.

Let `K` be the *least* natural number with `mu F r < d^K`. Then:

- lower bound: `((K-1) : ℝ) * δ ≤ Θ(mu F r)`
- upper bound: `Θ(mu F r) < (K : ℝ) * δ`

where `δ := chooseδ hk R d hd`.

This is the order-theoretic content of the “crossing index” analysis in K&S Appendix A.3.4
*without* assuming any global commensurability (`ZQuantized`) between the k-grid Θ-values and
the new δ chosen for the atom `d`. -/
lemma theta_floor_bracket_of_B_empty
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (r : Multi k) :
    let δ : ℝ := chooseδ hk R d hd
    let P : ℕ → Prop := fun n => mu F r < iterate_op d n
    let hP_ex : ∃ n : ℕ, P n := bounded_by_iterate d hd (mu F r)
    let K : ℕ := Nat.find hP_ex
    (((K - 1 : ℕ) : ℝ) * δ ≤ R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩) ∧
      (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ < (K : ℝ) * δ) := by
  classical
  -- Unpack the “least iterate bound” K for μr.
  set δ : ℝ := chooseδ hk R d hd
  set P : ℕ → Prop := fun n => mu F r < iterate_op d n
  have hP_ex : ∃ n : ℕ, P n := bounded_by_iterate d hd (mu F r)
  set K : ℕ := Nat.find hP_ex
  have hK : mu F r < iterate_op d K := by
    simpa [K, P] using (Nat.find_spec hP_ex)
  have hK_pos : 0 < K := by
    by_contra h_not
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h_not)
    rw [hK0, iterate_op_zero] at hK
    exact not_lt.mpr (ident_le (mu F r)) hK

  -- Upper bound: r ∈ A(K) and A-statistic is strictly below δ.
  have hrA_K : r ∈ extensionSetA F d K := by
    simpa [extensionSetA] using hK
  have hstat_r_lt : separationStatistic R r K hK_pos < δ :=
    A_statistic_lt_chooseδ hk R H IH d hd r K hK_pos hrA_K
  have hK_pos_real : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK_pos
  have hθ_lt_Kδ :
      R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ < (K : ℝ) * δ := by
    have := (div_lt_iff₀ hK_pos_real).1 (by simpa [separationStatistic, δ] using hstat_r_lt)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

  -- Lower bound: either K=1 (trivial), or r ∈ C(K-1) and C-bound gives (K-1)·δ ≤ Θ(r).
  by_cases hK1 : K = 1
  · have hθ_nonneg : 0 ≤ R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      have h_ident_le : ident ≤ mu F r := ident_le _
      rcases h_ident_le.eq_or_lt with h_eq | h_lt
      · have hsub :
            (⟨mu F r, mu_mem_kGrid F r⟩ : {x // x ∈ kGrid F}) = ⟨ident, ident_mem_kGrid F⟩ := by
          ext; exact h_eq.symm
        simp [hsub, R.ident_eq_zero]
      · have hθ_pos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := R.strictMono h_lt
        have : 0 ≤ R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
          simpa [R.ident_eq_zero] using (le_of_lt hθ_pos)
        exact this
    refine ⟨?_, hθ_lt_Kδ⟩
    -- (K-1)=0 when K=1.
    simpa [δ, K, hK1] using hθ_nonneg
  · have hKm1_pos : 0 < K - 1 := by omega
    have h_not_lt_Km1 : ¬ mu F r < iterate_op d (K - 1) := by
      intro hlt
      have hle : K ≤ K - 1 := by
        have : Nat.find hP_ex ≤ K - 1 := Nat.find_min' hP_ex (by simpa [P] using hlt)
        simpa [K] using this
      omega
    have hrC_Km1 : r ∈ extensionSetC F d (K - 1) := by
      have hne : mu F r ≠ iterate_op d (K - 1) := by
        intro hEq
        have : r ∈ extensionSetB F d (K - 1) := by
          simp [extensionSetB, Set.mem_setOf_eq, hEq]
        exact hB_empty r (K - 1) hKm1_pos this
      have hle : iterate_op d (K - 1) ≤ mu F r := le_of_not_gt h_not_lt_Km1
      exact lt_of_le_of_ne hle (Ne.symm hne)
    have hδ_le_stat :
        δ ≤ separationStatistic R r (K - 1) hKm1_pos :=
      chooseδ_C_bound hk R IH H d hd r (K - 1) hKm1_pos hrC_Km1
    have hKm1_pos_real : (0 : ℝ) < ((K - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hKm1_pos
    have hθ_ge_Km1δ :
        ((K - 1 : ℕ) : ℝ) * δ ≤ R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      have := (le_div_iff₀ hKm1_pos_real).1 (by simpa [separationStatistic, δ] using hδ_le_stat)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    refine ⟨?_, hθ_lt_Kδ⟩
    simpa [δ, K] using hθ_ge_Km1δ

/-- In the globally B-empty case, every k-grid point has Θ-value exactly on the δ-lattice.

Let `K` be the *least* natural number with `mu F r < d^K`. Then:
`Θ(mu F r) = (K-1)·δ`, where `δ := chooseδ hk R d hd`.

This is a *strictly stronger* statement than the floor-bracket inequalities of
`theta_floor_bracket_of_B_empty`: it additionally assumes a global commensurability hypothesis
`hZQ : ZQuantized F R (chooseδ hk R d hd)`.

K&S Appendix A.3.4 explicitly discusses the possibility that the new δ is incommensurate with
previous grid values; in such cases one should expect only the floor-bracket inequalities, not an
exact δ-lattice equality for all k-grid points. -/
lemma theta_eq_min_iterate_bound_of_B_empty
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hZQ : ZQuantized F R (chooseδ hk R d hd))
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (r : Multi k) :
    let δ : ℝ := chooseδ hk R d hd
    let P : ℕ → Prop := fun n => mu F r < iterate_op d n
    let hP_ex : ∃ n : ℕ, P n := bounded_by_iterate d hd (mu F r)
    let K : ℕ := Nat.find hP_ex
    R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ = ((K - 1 : ℕ) : ℝ) * δ := by
  classical
  -- Unpack the “least iterate bound” K for μr.
  set δ : ℝ := chooseδ hk R d hd
  set P : ℕ → Prop := fun n => mu F r < iterate_op d n
  have hP_ex : ∃ n : ℕ, P n := bounded_by_iterate d hd (mu F r)
  set K : ℕ := Nat.find hP_ex
  have hK : mu F r < iterate_op d K := by
    simpa [K, P] using (Nat.find_spec hP_ex)

  have hK_pos : 0 < K := by
    by_contra h_not
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h_not)
    rw [hK0, iterate_op_zero] at hK
    exact not_lt.mpr (ident_le (mu F r)) hK

  have h_not_lt_Km1 : ¬ mu F r < iterate_op d (K - 1) := by
    intro hlt
    have hle : K ≤ K - 1 := by
      -- If μr < d^(K-1), minimality forces K ≤ K-1.
      have : Nat.find hP_ex ≤ K - 1 := Nat.find_min' hP_ex (by simpa [P] using hlt)
      simpa [K] using this
    omega

  -- A at level K (by definition), and (since B is empty) C at level K-1 unless K=1.
  have hrA_K : r ∈ extensionSetA F d K := by
    simpa [extensionSetA] using hK

  -- The strict A-bound at level K gives Θ(r) < K·δ.
  have hstat_r_lt : separationStatistic R r K hK_pos < δ :=
    A_statistic_lt_chooseδ hk R H IH d hd r K hK_pos hrA_K
  have hK_pos_real : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK_pos
  have hθ_lt_Kδ :
      R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ < (K : ℝ) * δ := by
    have := (div_lt_iff₀ hK_pos_real).1 (by simpa [separationStatistic, δ] using hstat_r_lt)
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

  -- Use Z-quantization: Θ(r) = m·δ for some integer m.
  rcases hZQ r with ⟨m, hm⟩

  -- If K=1, then Θ(r) < δ forces m=0, hence Θ(r)=0 and μr=ident.
  by_cases hK1 : K = 1
  · -- Avoid `cases/subst` here: `K` is a `set`-binder and appears in dependent hypotheses.
    -- From Θ(r) < 1·δ, get m < 1.
    have hδ_pos : 0 < δ := delta_pos hk R IH H d hd
    have hm_lt_one : (m : ℝ) < (1 : ℝ) := by
      have : (m : ℝ) * δ < (1 : ℝ) * δ := by
        simpa [hK1, hm, mul_one] using hθ_lt_Kδ
      exact (mul_lt_mul_iff_left₀ hδ_pos).1 this
    have hm_le0 : m ≤ 0 := by
      have : (m : ℝ) < ((0 : ℤ) + 1 : ℤ) := by
        simpa [Int.cast_add, Int.cast_zero, Int.cast_one] using hm_lt_one
      exact (Int.lt_add_one_iff).1 (Int.cast_lt.mp this)
    -- Also Θ(r) ≥ 0 since ident ≤ μr and Θ(ident)=0.
    have hθ_nonneg : 0 ≤ R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      have h_ident_le : ident ≤ mu F r := ident_le _
      rcases h_ident_le.eq_or_lt with h_eq | h_lt'
      · have hsub :
            (⟨mu F r, mu_mem_kGrid F r⟩ : {x // x ∈ kGrid F}) = ⟨ident, ident_mem_kGrid F⟩ := by
          ext
          exact h_eq.symm
        simp [hsub, R.ident_eq_zero]
      · have hθ_pos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := R.strictMono h_lt'
        simpa [R.ident_eq_zero] using (le_of_lt hθ_pos)
    have hm_nonneg : 0 ≤ m := by
      have hδ_pos : 0 < δ := delta_pos hk R IH H d hd
      have hm_nonneg_real : (0 : ℝ) ≤ (m : ℝ) := by
        have : (0 : ℝ) ≤ (m : ℝ) * δ := by simpa [hm] using hθ_nonneg
        exact (mul_nonneg_iff_left_nonneg_of_pos hδ_pos).1 this
      exact (Int.cast_nonneg_iff).1 hm_nonneg_real
    have hm_eq0 : m = 0 := le_antisymm hm_le0 hm_nonneg
    -- Now K-1 = 0, so the goal is Θ(r) = 0.
    have hθ_eq0 : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ = 0 := by
      simpa [hm_eq0] using hm
    simpa [K, hK1, δ] using hθ_eq0

  · -- K > 1: use the C-bound at level K-1 to get (K-1)·δ ≤ Θ(r).
    have hKm1_pos : 0 < K - 1 := by omega
    have hrC_Km1 : r ∈ extensionSetC F d (K - 1) := by
      -- Since ¬(μr < d^(K-1)) and B is empty, we must have d^(K-1) < μr.
      have hne : mu F r ≠ iterate_op d (K - 1) := by
        intro hEq
        have : r ∈ extensionSetB F d (K - 1) := by
          simp [extensionSetB, Set.mem_setOf_eq, hEq]
        exact hB_empty r (K - 1) hKm1_pos this
      have hle : iterate_op d (K - 1) ≤ mu F r := le_of_not_gt h_not_lt_Km1
      exact lt_of_le_of_ne hle (Ne.symm hne)
    have hδ_le_stat :
        δ ≤ separationStatistic R r (K - 1) hKm1_pos :=
      chooseδ_C_bound hk R IH H d hd r (K - 1) hKm1_pos hrC_Km1
    have hKm1_pos_real : (0 : ℝ) < ((K - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hKm1_pos
    have hθ_ge_Km1δ :
        ((K - 1 : ℕ) : ℝ) * δ ≤ R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      have := (le_div_iff₀ hKm1_pos_real).1 (by simpa [separationStatistic, δ] using hδ_le_stat)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this

    -- Combine with Θ(r) = m·δ to pin m = K-1.
    have hδ_pos : 0 < δ := delta_pos hk R IH H d hd
    have hm_ge : ((K - 1 : ℕ) : ℤ) ≤ m := by
      -- (K-1)·δ ≤ m·δ  ⇒  (K-1) ≤ m
      have : (((K - 1 : ℕ) : ℤ) : ℝ) * δ ≤ (m : ℝ) * δ := by simpa [hm] using hθ_ge_Km1δ
      exact Int.cast_le.mp ((mul_le_mul_iff_left₀ hδ_pos).1 this)
    have hm_lt : m < (K : ℤ) := by
      -- m·δ < K·δ  ⇒  m < K
      have : (m : ℝ) * δ < (K : ℝ) * δ := by simpa [hm] using hθ_lt_Kδ
      have : (m : ℝ) < (K : ℝ) := (mul_lt_mul_iff_left₀ hδ_pos).1 this
      exact Int.cast_lt.mp (by simpa [Int.cast_natCast] using this)
    have hm_eq : m = ((K - 1 : ℕ) : ℤ) := by omega

    -- Conclude Θ(r) = (K-1)·δ.
    simpa [δ, hm_eq] using hm

/-!
### K&S Appendix A.3.4 (B-empty) strict gap lemmas

In the “globally B-empty” regime, the mixed-`t` cases for `Θ'` require strict relative Θ-gap
bounds. In this refactor, we keep the missing step explicit by packaging it as a `Prop`-valued
assumption (`BEmptyStrictGapSpec`) rather than using `sorry`.

Important nuance (Ben/Goertzel v2): K&S’s A/B/C sets in Appendix A.3.4 are **base-indexed**:
they compare old-grid values to a target of the form `X0 ⊕ d^u` for a fixed old-grid base `X0`.
This differs from the absolute predicate `extensionSetB F d u := {r | mu F r = d^u}`, which is
the special case `X0 = ident`. The base-indexed version is recorded in
`Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Core/Induction/Goertzel.lean`.
-/

/-
### Circularity marker (formal)

The two “strict gap” statements below are not new independent facts: they are *exactly*
the inequalities needed for strict monotonicity of the extended raw evaluator `Theta'_raw`
on the concrete witness pair:
- `joinMulti r_old_x 0` (old grid element)
- `joinMulti r_old_y Δ` (shifted by Δ steps of the new atom `d`)

Unfolding `Theta'_raw` shows:
`Theta'_raw r_old_x 0 < Theta'_raw r_old_y Δ`  ↔  `Θ(r_old_x) - Θ(r_old_y) < Δ·δ`,
and similarly for the C-side.

This makes the dependency cycle explicit:
- `extend_grid_rep_with_atom` needs strict monotonicity of the Θ′ construction,
  whose mixed-`t` branch reduces to these strict gap inequalities;
- proving these strict gap inequalities by “apply strictMono of Θ′” is circular,
  because that strictMono is itself what the induction step is trying to establish.
-/

lemma theta_gap_lt_iff_Theta'_raw_lt
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (δ : ℝ) (r_old_x r_old_y : Multi k) (Δ : ℕ) :
    (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ) ↔
      (Theta'_raw R d δ r_old_x 0 < Theta'_raw R d δ r_old_y Δ) := by
  -- Unfold the raw evaluator and simplify.
  simp [Theta'_raw, sub_lt_iff_lt_add, add_assoc, add_comm, add_left_comm]

lemma theta_gap_gt_iff_Theta'_raw_lt
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (δ : ℝ) (r_old_x r_old_y : Multi k) (Δ : ℕ) :
    ((Δ : ℝ) * δ <
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩) ↔
      (Theta'_raw R d δ r_old_x Δ < Theta'_raw R d δ r_old_y 0) := by
  -- Unfold the raw evaluator and simplify.
  simp [Theta'_raw, lt_sub_iff_add_lt, add_assoc, add_comm, add_left_comm]

/-- If an extension evaluator `Θ'` is strictly monotone on the extended μ-grid and agrees with
`Theta'_raw` on `joinMulti` witnesses, then the A-side strict gap inequality follows immediately.

This lemma is the formal “circularity” warning: using strict monotonicity of the Θ′ construction
to prove the strict gap bound is circular, because strict monotonicity of Θ′ in mixed-`t` cases
*reduces to* these strict gap inequalities. -/
lemma theta_gap_lt_of_strictMono_extension
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d) (δ : ℝ)
    (Θ' : {x // x ∈ kGrid (extendAtomFamily F d hd)} → ℝ)
    (h_on_join :
      ∀ (r_old : Multi k) (t : ℕ),
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩ =
          Theta'_raw R d δ r_old t)
    (h_strict : StrictMono Θ')
    (r_old_x r_old_y : Multi k) (Δ : ℕ)
    (h_lt : mu F r_old_x < op (mu F r_old_y) (iterate_op d Δ)) :
    R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ := by
  classical
  let F' := extendAtomFamily F d hd
  have hμx :
      mu F' (joinMulti r_old_x 0) = mu F r_old_x := by
    -- μ(F', join(r,0)) = μ(F,r) ⊕ d^0 = μ(F,r)
    simpa [F', iterate_op_zero, op_ident_right] using (mu_extend_last F d hd r_old_x 0)
  have hμy :
      mu F' (joinMulti r_old_y Δ) = op (mu F r_old_y) (iterate_op d Δ) := by
    simpa [F'] using (mu_extend_last F d hd r_old_y Δ)
  have hμ_lt' :
      mu F' (joinMulti r_old_x 0) < mu F' (joinMulti r_old_y Δ) := by
    simpa [hμx, hμy] using h_lt
  have hΘ' :
      Θ' ⟨mu F' (joinMulti r_old_x 0), mu_mem_kGrid F' (joinMulti r_old_x 0)⟩ <
        Θ' ⟨mu F' (joinMulti r_old_y Δ), mu_mem_kGrid F' (joinMulti r_old_y Δ)⟩ :=
    h_strict hμ_lt'
  have hraw :
      Theta'_raw R d δ r_old_x 0 < Theta'_raw R d δ r_old_y Δ := by
    simpa [F', h_on_join] using hΘ'
  exact (theta_gap_lt_iff_Theta'_raw_lt (R := R) (d := d) (δ := δ)
      (r_old_x := r_old_x) (r_old_y := r_old_y) (Δ := Δ)).2 hraw

/-- C-side version of `theta_gap_lt_of_strictMono_extension`. -/
lemma theta_gap_gt_of_strictMono_extension
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d) (δ : ℝ)
    (Θ' : {x // x ∈ kGrid (extendAtomFamily F d hd)} → ℝ)
    (h_on_join :
      ∀ (r_old : Multi k) (t : ℕ),
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩ =
          Theta'_raw R d δ r_old t)
    (h_strict : StrictMono Θ')
    (r_old_x r_old_y : Multi k) (Δ : ℕ)
    (h_lt : op (mu F r_old_x) (iterate_op d Δ) < mu F r_old_y) :
    (Δ : ℝ) * δ <
      R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
        R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
  classical
  let F' := extendAtomFamily F d hd
  have hμx :
      mu F' (joinMulti r_old_x Δ) = op (mu F r_old_x) (iterate_op d Δ) := by
    simpa [F'] using (mu_extend_last F d hd r_old_x Δ)
  have hμy :
      mu F' (joinMulti r_old_y 0) = mu F r_old_y := by
    simpa [F', iterate_op_zero, op_ident_right] using (mu_extend_last F d hd r_old_y 0)
  have hμ_lt' :
      mu F' (joinMulti r_old_x Δ) < mu F' (joinMulti r_old_y 0) := by
    simpa [hμx, hμy] using h_lt
  have hΘ' :
      Θ' ⟨mu F' (joinMulti r_old_x Δ), mu_mem_kGrid F' (joinMulti r_old_x Δ)⟩ <
        Θ' ⟨mu F' (joinMulti r_old_y 0), mu_mem_kGrid F' (joinMulti r_old_y 0)⟩ :=
    h_strict hμ_lt'
  have hraw :
      Theta'_raw R d δ r_old_x Δ < Theta'_raw R d δ r_old_y 0 := by
    simpa [F', h_on_join] using hΘ'
  exact (theta_gap_gt_iff_Theta'_raw_lt (R := R) (d := d) (δ := δ)
      (r_old_x := r_old_x) (r_old_y := r_old_y) (Δ := Δ)).2 hraw

/-- In a `ZQuantized` grid with step `δ>0`, any strict μ-increase costs at least one `δ` in Θ. -/
lemma zquantized_gap_ge_delta
    {k : ℕ} {F : AtomFamily α k} {R : MultiGridRep F} {δ : ℝ}
    (hδ_pos : 0 < δ) (hZQ : ZQuantized F R δ)
    (r s : Multi k) (hμ : mu F s < mu F r) :
    δ ≤
      R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ -
        R.Θ_grid ⟨mu F s, mu_mem_kGrid F s⟩ := by
  rcases hZQ r with ⟨mr, hmr⟩
  rcases hZQ s with ⟨ms, hms⟩
  have hθ : R.Θ_grid ⟨mu F s, mu_mem_kGrid F s⟩ <
      R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := R.strictMono hμ
  have hθ_pos :
      0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ -
          R.Θ_grid ⟨mu F s, mu_mem_kGrid F s⟩ := sub_pos.mpr hθ
  have hms_lt_hmr : (ms : ℤ) < mr := by
    -- (mr-ms)*δ > 0 ⇒ mr-ms > 0 ⇒ ms < mr
    have : (0 : ℝ) < ((mr - ms : ℤ) : ℝ) * δ := by
      simpa [hmr, hms, Int.cast_sub, sub_mul] using hθ_pos
    have : (0 : ℝ) < ((mr - ms : ℤ) : ℝ) := (mul_pos_iff_of_pos_right hδ_pos).1 this
    have : 0 < (mr - ms : ℤ) := by exact_mod_cast this
    omega
  have hone_le : (1 : ℤ) ≤ mr - ms := by omega
  have : (1 : ℝ) * δ ≤ ((mr - ms : ℤ) : ℝ) * δ := by
    have h : (1 : ℝ) ≤ ((mr - ms : ℤ) : ℝ) := by exact_mod_cast hone_le
    exact mul_le_mul_of_nonneg_right h (le_of_lt hδ_pos)
  -- Rewrite the gap as (mr-ms)*δ and conclude.
  simpa [hmr, hms, Int.cast_sub, sub_mul, one_mul] using this

/-- **Ben/Goertzel v2 Lemma 7 (base-indexed form, on the μ-grid)**.

If two “extended” μ-values coincide at different `t`-levels,
`μ(r₀) ⊕ d^u = μ(ry) ⊕ d^v` with `v ≤ u`, then right-cancellation yields the base-indexed equality
`μ(ry) = μ(r₀) ⊕ d^(u-v)`, i.e. a witness that `ry ∈ extensionSetB_base F d r₀ (u-v)`.

This is purely algebraic (associativity + strict monotonicity ⇒ injective translations) and does
not use any Θ/δ machinery. -/
lemma extensionSetB_base_of_mu_joinMulti_eq
    {k : ℕ} {F : AtomFamily α k} (d : α) (hd : ident < d)
    (r0 ry : Multi k) (u v : ℕ) (huv : v ≤ u)
    (hEq :
      mu (extendAtomFamily F d hd) (joinMulti r0 u) =
        mu (extendAtomFamily F d hd) (joinMulti ry v)) :
    ry ∈ extensionSetB_base F d r0 (u - v) := by
  classical
  -- Rewrite the equality using `mu_extend_last`, then cancel the common `d^v` tail.
  have hEq' :
      op (mu F r0) (iterate_op d u) = op (mu F ry) (iterate_op d v) := by
    have hx :
        mu (extendAtomFamily F d hd) (joinMulti r0 u) =
          op (mu F r0) (iterate_op d u) := by
      simpa using (mu_extend_last F d hd r0 u)
    have hy :
        mu (extendAtomFamily F d hd) (joinMulti ry v) =
          op (mu F ry) (iterate_op d v) := by
      simpa using (mu_extend_last F d hd ry v)
    simpa [hx, hy] using hEq
  have :
      mu F ry = op (mu F r0) (iterate_op d (u - v)) :=
    cancel_right_iterate_eq (F := F) (d := d) r0 ry u v huv hEq'
  -- Package as base-indexed B-membership.
  simpa [extensionSetB_base, Set.mem_setOf_eq] using this

/-- **Blocked K&S Appendix A.3.4 step (B-empty strict relative gaps)**.

The refactored `Θ'` construction reduces strict monotonicity in the mixed-`t` cases to two
“relative gap” inequalities on the old k-grid:
- **A-side**: `μy < μx < μy ⊕ d^Δ` implies `Θx - Θy < Δ·δ`
- **C-side**: `μx ⊕ d^Δ < μy` implies `Δ·δ < Θy - Θx`

In the globally `B = ∅` regime (no exact witnesses `μ(F,r)=d^u`), the codebase currently proves
the *non-strict* bounds via crossing-index analysis, but does not yet provide a placeholder-free proof
of the strict boundary exclusion needed to upgrade `≤` to `<` *in the genuinely external case*
where the boundary value `μy ⊕ d^Δ` is itself **not** already on the old k-grid.

To keep the rest of the development mechanically checkable (and to make the dependency explicit),
we package the missing A.3.4 strictness as a Prop. -/
structure BEmptyStrictGapSpec
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d) [KSSeparation α] : Prop where
  /-- A-side strictness in the globally B-empty regime (expressed using absolute `extensionSetB`),
      for the external subcase where the boundary `μy ⊕ d^Δ` is not on the old k-grid.

      Note (Ben/Goertzel v2): this is most naturally expressed as a **base-indexed statistic**
      inequality:
      `(Θ(x) - Θ(y))/Δ < δ` for `x < y ⊕ d^Δ`, i.e. `separationStatistic_base R y x Δ < δ`. -/
  A :
    (∀ r u, 0 < u → r ∉ extensionSetB F d u) →
    ∀ (r_old_x r_old_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ),
      mu F r_old_y < mu F r_old_x →
      r_old_x ∈ extensionSetA_base F d r_old_y Δ →
      (¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r_old_y Δ) →
        separationStatistic_base R r_old_y r_old_x Δ hΔ < chooseδ hk R d hd
  /-- C-side strictness in the globally B-empty regime (expressed using absolute `extensionSetB`),
      for the external subcase where the boundary `μx ⊕ d^Δ` is not on the old k-grid.

      Base-indexed form: `δ < (Θ(y) - Θ(x))/Δ`, i.e. `δ < separationStatistic_base R x y Δ`. -/
  C :
    (∀ r u, 0 < u → r ∉ extensionSetB F d u) →
    ∀ (r_old_x r_old_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ),
      mu F r_old_x < mu F r_old_y →
      r_old_y ∈ extensionSetC_base F d r_old_x Δ →
      (¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r_old_x Δ) →
        chooseδ hk R d hd < separationStatistic_base R r_old_x r_old_y Δ hΔ

/-- Equivalent “no-common-prefix” form of `BEmptyStrictGapSpec`.

Using `commonMulti`/`remMultiLeft`/`remMultiRight`, any base-indexed comparison can be reduced to
the case where the base and witness share **no** coordinatewise common part.  This mirrors the
`ChooseδBaseAdmissible_noCommon` interface in
`Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Core/Induction/Goertzel.lean`, but for the
strict-gap blocker itself.

This reduction is valuable because it isolates the genuinely “non-translate” case: if a proof or
countermodel exists, it should already appear in the disjoint-support situation. -/
structure BEmptyStrictGapSpec_noCommon
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d) [KSSeparation α] : Prop where
  /-- A-side strictness, reduced to the case `commonMulti r_old_y r_old_x = 0`. -/
  A_noCommon :
    (∀ r u, 0 < u → r ∉ extensionSetB F d u) →
    ∀ (r_old_x r_old_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ),
      mu F r_old_y < mu F r_old_x →
      r_old_x ∈ extensionSetA_base F d r_old_y Δ →
      (¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r_old_y Δ) →
      commonMulti r_old_y r_old_x = 0 →
        separationStatistic_base R r_old_y r_old_x Δ hΔ < chooseδ hk R d hd
  /-- C-side strictness, reduced to the case `commonMulti r_old_x r_old_y = 0`. -/
  C_noCommon :
    (∀ r u, 0 < u → r ∉ extensionSetB F d u) →
    ∀ (r_old_x r_old_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ),
      mu F r_old_x < mu F r_old_y →
      r_old_y ∈ extensionSetC_base F d r_old_x Δ →
      (¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r_old_x Δ) →
      commonMulti r_old_x r_old_y = 0 →
        chooseδ hk R d hd < separationStatistic_base R r_old_x r_old_y Δ hΔ

/-- **Strong interface**: the chosen `δ := chooseδ …` is base-admissible for *every* base `r0`
and level `u > 0`.

This is stronger than `BEmptyStrictGapSpec` (which only needs strictness in the “external” mixed
cases), but it is a clean sufficient condition: it makes the Θ′ strict-monotonicity proof entirely
local, by directly bounding all base-indexed A/C statistics at the relevant `(r0,u)` pairs. -/
class ChooseδBaseAdmissible
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d) : Prop where
  base :
    ∀ (r0 : Multi k) (u : ℕ) (hu : 0 < u),
      (∀ r : Multi k, r ∈ extensionSetA_base F d r0 u →
          separationStatistic_base R r0 r u hu < chooseδ hk R d hd) ∧
        (∀ r : Multi k, r ∈ extensionSetC_base F d r0 u →
          chooseδ hk R d hd < separationStatistic_base R r0 r u hu)

theorem bEmptyStrictGapSpec_noCommon_of_bEmptyStrictGapSpec
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (h : BEmptyStrictGapSpec (α := α) hk R IH H d hd) :
    BEmptyStrictGapSpec_noCommon (α := α) hk R IH H d hd := by
  refine ⟨?_, ?_⟩
  · intro hB_empty r_old_x r_old_y Δ hΔ hμ hA hB _hcommon
    exact h.A hB_empty r_old_x r_old_y Δ hΔ hμ hA hB
  · intro hB_empty r_old_x r_old_y Δ hΔ hμ hC hB _hcommon
    exact h.C hB_empty r_old_x r_old_y Δ hΔ hμ hC hB

theorem bEmptyStrictGapSpec_of_bEmptyStrictGapSpec_noCommon
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (h : BEmptyStrictGapSpec_noCommon (α := α) hk R IH H d hd) :
    BEmptyStrictGapSpec (α := α) hk R IH H d hd := by
  classical
  refine ⟨?_, ?_⟩
  · intro hB_empty r_old_x r_old_y Δ hΔ hμ hA hB
    -- Cancel the coordinatewise common prefix between `r_old_y` and `r_old_x`.
    let c : Multi k := commonMulti r_old_y r_old_x
    let r0' : Multi k := remMultiLeft r_old_y r_old_x
    let r' : Multi k := remMultiRight r_old_y r_old_x
    have hrA' : r' ∈ extensionSetA_base F d r0' Δ :=
      (extensionSetA_base_iff_remMulti (H := H) d r_old_y r_old_x Δ).1 hA
    have hcommon : commonMulti r0' r' = (0 : Multi k) := by
      simpa [c, r0', r'] using commonMulti_remMultiLeft_remMultiRight_eq_zero (r := r_old_y) (s := r_old_x)
    have hμ' : mu F r0' < mu F r' := by
      have hr0_vec : r_old_y = c + r0' := (commonMulti_add_remMultiLeft r_old_y r_old_x).symm
      have hr_vec : r_old_x = c + r' := (commonMulti_add_remMultiRight r_old_y r_old_x).symm
      have hr0 : mu F r_old_y = op (mu F c) (mu F r0') := by
        calc
          mu F r_old_y = mu F (c + r0') := by simpa [hr0_vec]
          _ = op (mu F c) (mu F r0') := mu_add_of_comm (F := F) H c r0'
      have hr : mu F r_old_x = op (mu F c) (mu F r') := by
        calc
          mu F r_old_x = mu F (c + r') := by simpa [hr_vec]
          _ = op (mu F c) (mu F r') := mu_add_of_comm (F := F) H c r'
      have hlt : op (mu F c) (mu F r0') < op (mu F c) (mu F r') := by
        simpa [hr0, hr] using hμ
      have hle : mu F r0' ≤ mu F r' :=
        cancellative_right (z := mu F c) (x := mu F r0') (y := mu F r') (le_of_lt hlt)
      have hne : mu F r0' ≠ mu F r' := by
        intro hEq
        have hEq' : op (mu F c) (mu F r0') = op (mu F c) (mu F r') := by simpa [hEq]
        exact (ne_of_lt hlt) hEq'
      exact lt_of_le_of_ne hle hne
    have hB' : (¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0' Δ) := by
      intro hB0
      rcases hB0 with ⟨rB', hrB'⟩
      -- Lift a reduced-base B-witness back to the original base by adding the cancelled prefix `c`.
      refine hB ?_
      refine ⟨c + rB', ?_⟩
      -- Expand the definition and use `mu_add_of_comm` + associativity.
      have hμB' : mu F rB' = op (mu F r0') (iterate_op d Δ) := by
        simpa [extensionSetB_base, Set.mem_setOf_eq] using hrB'
      have hμadd : mu F (c + rB') = op (mu F c) (mu F rB') :=
        mu_add_of_comm (F := F) H c rB'
      have hμr0 : mu F r_old_y = op (mu F c) (mu F r0') := by
        have hr0_vec : r_old_y = c + r0' := (commonMulti_add_remMultiLeft r_old_y r_old_x).symm
        calc
          mu F r_old_y = mu F (c + r0') := by simpa [hr0_vec]
          _ = op (mu F c) (mu F r0') := mu_add_of_comm (F := F) H c r0'
      -- Now `mu(c+rB') = mu(r_old_y) ⊕ d^Δ`.
      have : mu F (c + rB') = op (mu F r_old_y) (iterate_op d Δ) := by
        calc
          mu F (c + rB') = op (mu F c) (mu F rB') := hμadd
          _ = op (mu F c) (op (mu F r0') (iterate_op d Δ)) := by rw [hμB']
          _ = op (op (mu F c) (mu F r0')) (iterate_op d Δ) := by
                simpa [op_assoc] using (op_assoc (mu F c) (mu F r0') (iterate_op d Δ)).symm
          _ = op (mu F r_old_y) (iterate_op d Δ) := by simpa [hμr0]
      simpa [extensionSetB_base, Set.mem_setOf_eq] using this
    have hlt' :
        separationStatistic_base R r0' r' Δ hΔ < chooseδ hk R d hd :=
      h.A_noCommon hB_empty r' r0' Δ hΔ hμ' hrA' hB' (by simpa using hcommon)
    simpa [separationStatistic_base_eq_remMulti (R := R) r_old_y r_old_x Δ hΔ, r0', r'] using hlt'
  · intro hB_empty r_old_x r_old_y Δ hΔ hμ hC hB
    let c : Multi k := commonMulti r_old_x r_old_y
    let r0' : Multi k := remMultiLeft r_old_x r_old_y
    let r' : Multi k := remMultiRight r_old_x r_old_y
    have hrC' : r' ∈ extensionSetC_base F d r0' Δ :=
      (extensionSetC_base_iff_remMulti (H := H) d r_old_x r_old_y Δ).1 hC
    have hcommon : commonMulti r0' r' = (0 : Multi k) := by
      simpa [c, r0', r'] using commonMulti_remMultiLeft_remMultiRight_eq_zero (r := r_old_x) (s := r_old_y)
    have hμ' : mu F r0' < mu F r' := by
      have hr0_vec : r_old_x = c + r0' := (commonMulti_add_remMultiLeft r_old_x r_old_y).symm
      have hr_vec : r_old_y = c + r' := (commonMulti_add_remMultiRight r_old_x r_old_y).symm
      have hr0 : mu F r_old_x = op (mu F c) (mu F r0') := by
        calc
          mu F r_old_x = mu F (c + r0') := by simpa [hr0_vec]
          _ = op (mu F c) (mu F r0') := mu_add_of_comm (F := F) H c r0'
      have hr : mu F r_old_y = op (mu F c) (mu F r') := by
        calc
          mu F r_old_y = mu F (c + r') := by simpa [hr_vec]
          _ = op (mu F c) (mu F r') := mu_add_of_comm (F := F) H c r'
      have hlt : op (mu F c) (mu F r0') < op (mu F c) (mu F r') := by
        simpa [hr0, hr] using hμ
      have hle : mu F r0' ≤ mu F r' :=
        cancellative_right (z := mu F c) (x := mu F r0') (y := mu F r') (le_of_lt hlt)
      have hne : mu F r0' ≠ mu F r' := by
        intro hEq
        have hEq' : op (mu F c) (mu F r0') = op (mu F c) (mu F r') := by simpa [hEq]
        exact (ne_of_lt hlt) hEq'
      exact lt_of_le_of_ne hle hne
    have hB' : (¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0' Δ) := by
      intro hB0
      rcases hB0 with ⟨rB', hrB'⟩
      refine hB ?_
      refine ⟨c + rB', ?_⟩
      have hμB' : mu F rB' = op (mu F r0') (iterate_op d Δ) := by
        simpa [extensionSetB_base, Set.mem_setOf_eq] using hrB'
      have hμadd : mu F (c + rB') = op (mu F c) (mu F rB') :=
        mu_add_of_comm (F := F) H c rB'
      have hμr0 : mu F r_old_x = op (mu F c) (mu F r0') := by
        have hr0_vec : r_old_x = c + r0' := (commonMulti_add_remMultiLeft r_old_x r_old_y).symm
        calc
          mu F r_old_x = mu F (c + r0') := by simpa [hr0_vec]
          _ = op (mu F c) (mu F r0') := mu_add_of_comm (F := F) H c r0'
      have : mu F (c + rB') = op (mu F r_old_x) (iterate_op d Δ) := by
        calc
          mu F (c + rB') = op (mu F c) (mu F rB') := hμadd
          _ = op (mu F c) (op (mu F r0') (iterate_op d Δ)) := by rw [hμB']
          _ = op (op (mu F c) (mu F r0')) (iterate_op d Δ) := by
                simpa [op_assoc] using (op_assoc (mu F c) (mu F r0') (iterate_op d Δ)).symm
          _ = op (mu F r_old_x) (iterate_op d Δ) := by simpa [hμr0]
      simpa [extensionSetB_base, Set.mem_setOf_eq] using this
    have hlt' :
        chooseδ hk R d hd < separationStatistic_base R r0' r' Δ hΔ :=
      h.C_noCommon hB_empty r0' r' Δ hΔ hμ' hrC' hB' (by simpa using hcommon)
    simpa [separationStatistic_base_eq_remMulti (R := R) r_old_x r_old_y Δ hΔ, r0', r'] using hlt'

theorem bEmptyStrictGapSpec_iff_bEmptyStrictGapSpec_noCommon
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α] :
    BEmptyStrictGapSpec (α := α) hk R IH H d hd ↔
      BEmptyStrictGapSpec_noCommon (α := α) hk R IH H d hd := by
  constructor
  · intro h
    exact bEmptyStrictGapSpec_noCommon_of_bEmptyStrictGapSpec (α := α) hk R IH H d hd h
  · intro h
    exact bEmptyStrictGapSpec_of_bEmptyStrictGapSpec_noCommon (α := α) hk R IH H d hd h

/-
Ben/Goertzel v2 perspective: one route to discharging `BEmptyStrictGapSpec` is to prove a
“realizability interval” statement saying that an open interval of δ-choices yields a valid
strictly monotone extension evaluator agreeing with `Theta'_raw`.  Then:

1. a boundary equality forces a flip under δ-perturbation, hence a critical δ₀ with
   `Theta'_raw … = Theta'_raw …` (pure affine algebra), and
2. strict monotonicity at δ₀ turns that numeric equality into an equality on the extended μ-grid,
   which cancels to a base-indexed B-witness, contradicting the external `B = ∅` assumption.

This conditional “flip ⇒ base-indexed B-witness” lemma is implemented (without placeholders) as
`Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem.flip_implies_baseIndexed_B_witness` in
`Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Core/Induction/Goertzel.lean`.

Note: the v2 notes sometimes speak of an “interval of admissible δ” globally.  For the *global*
admissibility predicate `AdmissibleDelta` (quantifying over all A/C witnesses at all levels),
this cannot happen:
`Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Core/Induction/Goertzel.lean` proves
`no_open_interval_of_global_admissibleDelta`.  Any interval-of-freedom argument must therefore
use a strictly more local/base-indexed admissibility notion, as K&S do in A.3.4. -/

/-- Legacy helper hypothesis (not used by `extend_grid_rep_with_atom`): a strong commensurability
premise for the “globally `B ≠ ∅`” branch.

Warning: this is *not* automatic. Even in the additive model (`α = ℝ≥0`, `op = (+)`, `Θ = id`),
there are `B ≠ ∅` extensions where this implication fails; see
`Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Counterexamples/ZQuantizedBNonempty.lean`. -/
abbrev ZQuantized_chooseδ_if_B_nonempty
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d) : Prop :=
  (∃ r u, 0 < u ∧ r ∈ extensionSetB F d u) → ZQuantized F R (chooseδ hk R d hd)

/-- **False-lead blocker**: if one (incorrectly) assumes the *new* `δ := chooseδ hk R d hd`
also quantizes the *old* k-grid (`ZQuantized F R δ`), then the Δ=1 B-empty strict-gap claim
cannot coexist with an actual strict “between” configuration `μy < μx < μy ⊕ d`.

This does **not** refute K&S Appendix A. It refutes a *proof strategy* that tries to combine:
- `ZQuantized F R (chooseδ …)` (commensurability of old grid with the new δ), and
- B-empty strict relative gaps measured in the same δ.

In additive models with `B = ∅`, one typically has the opposite situation: `δ` is
*incommensurate* with old grid values, so `ZQuantized F R (chooseδ …)` fails. -/
theorem zquantized_chooseδ_blocks_strict_gap_Δ1
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hZQ : ZQuantized F R (chooseδ hk R d hd))
    (hStrict : BEmptyStrictGapSpec hk R IH H d hd)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (r_old_x r_old_y : Multi k)
    (hμ : mu F r_old_y < mu F r_old_x)
    (h_between : r_old_x ∈ extensionSetA_base F d r_old_y 1)
    (hB_base : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r_old_y 1) :
    False := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  have hδ_pos : 0 < δ := by simpa [δ] using delta_pos hk R IH H d hd
  have h_ge : δ ≤
      R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
    zquantized_gap_ge_delta (hδ_pos := hδ_pos) (hZQ := by simpa [δ] using hZQ) r_old_x r_old_y hμ
  have h_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < δ := by
    have hstat :=
      hStrict.A hB_empty r_old_x r_old_y 1 Nat.one_pos hμ h_between hB_base
    -- `separationStatistic_base` at `Δ = 1` is just the Θ-gap.
    simpa [separationStatistic_base, δ] using hstat
  linarith

-- The rest of the broken proof attempt has been removed. The `BEmptyStrictGapSpec` hypothesis
-- captures the missing K&S A.3.4 strictness step explicitly.
-- BEGIN REMOVED PROOF BODY
/-
  classical
  set δ : ℝ := chooseδ hk R d hd

  -- Step 1: Define the crossing indices Kx and Ky (note: swapped from A-side)
  let Px : ℕ → Prop := fun n => mu F r_old_x < iterate_op d n
  have hPx_ex : ∃ n : ℕ, Px n := bounded_by_iterate d hd (mu F r_old_x)
  let Kx : ℕ := Nat.find hPx_ex
  have hKx : mu F r_old_x < iterate_op d Kx := Nat.find_spec hPx_ex
  have hKx_pos : 0 < Kx := by
    by_contra h
    have hKx0 : Kx = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
    rw [hKx0, iterate_op_zero] at hKx
    exact not_lt.mpr (ident_le (mu F r_old_x)) hKx

  let Py : ℕ → Prop := fun n => mu F r_old_y < iterate_op d n
  have hPy_ex : ∃ n : ℕ, Py n := bounded_by_iterate d hd (mu F r_old_y)
  let Ky : ℕ := Nat.find hPy_ex
  have hKy : mu F r_old_y < iterate_op d Ky := Nat.find_spec hPy_ex
  have hKy_pos : 0 < Ky := by
    by_contra h
    have hKy0 : Ky = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
    rw [hKy0, iterate_op_zero] at hKy
    exact not_lt.mpr (ident_le (mu F r_old_y)) hKy

  -- Step 2: Get θx = (Kx-1)·δ and θy = (Ky-1)·δ from B-empty characterization
  have hθx_eq :
      R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ = ((Kx - 1 : ℕ) : ℝ) * δ := by
    simpa [δ, Px, Kx, hPx_ex] using
      (theta_eq_min_iterate_bound_of_B_empty hk R IH H d hd (hZQ := by simpa [δ] using hZQ) hB_empty r_old_x)
  have hθy_eq :
      R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ = ((Ky - 1 : ℕ) : ℝ) * δ := by
    simpa [δ, Py, Ky, hPy_ex] using
      (theta_eq_min_iterate_bound_of_B_empty hk R IH H d hd (hZQ := by simpa [δ] using hZQ) hB_empty r_old_y)

  -- Step 3: From μx < d^Kx, get μx ⊕ d^Δ < d^(Kx+Δ).
  -- Since μx ⊕ d^Δ < μy < d^Ky, we get Ky ≤ Kx + Δ.
  -- We need to show Ky > Kx + Δ - this is where the C-side differs!
  -- Actually: μy > μx ⊕ d^Δ ≥ d^(Kx-1) ⊕ d^Δ = d^(Kx-1+Δ) = d^(Kx+Δ-1)
  -- So d^(Kx+Δ-1) < μy, which means Ky ≥ Kx + Δ (by minimality of Ky).

  -- By minimality of Kx: NOT(μx < d^(Kx-1)), so μx ≥ d^(Kx-1)
  have h_not_lt_Kxm1 : ¬ mu F r_old_x < iterate_op d (Kx - 1) := by
    intro hlt
    have hle : Kx ≤ Kx - 1 := by
      have : Nat.find hPx_ex ≤ Kx - 1 := Nat.find_min' hPx_ex (by simpa [Px] using hlt)
      simpa [Kx] using this
    have hlt' : Kx - 1 < Kx := Nat.sub_lt hKx_pos Nat.one_pos
    exact (lt_irrefl Kx) (lt_of_le_of_lt hle hlt')
  have hμx_ge : iterate_op d (Kx - 1) ≤ mu F r_old_x := le_of_not_gt h_not_lt_Kxm1

  -- μx ⊕ d^Δ ≥ d^(Kx-1) ⊕ d^Δ = d^(Kx-1+Δ) = d^(Kx+Δ-1)
  have hμx_op_ge : iterate_op d (Kx + Δ - 1) ≤ op (mu F r_old_x) (iterate_op d Δ) := by
    have h1 : iterate_op d (Kx - 1 + Δ) ≤ op (mu F r_old_x) (iterate_op d Δ) := by
      have h2 : op (iterate_op d (Kx - 1)) (iterate_op d Δ) ≤ op (mu F r_old_x) (iterate_op d Δ) :=
        op_mono_left (iterate_op d Δ) hμx_ge
      have h3 : op (iterate_op d (Kx - 1)) (iterate_op d Δ) = iterate_op d (Kx - 1 + Δ) := by
        simpa using (iterate_op_add d (Kx - 1) Δ)
      simpa [h3] using h2
    have h4 : Kx - 1 + Δ = Kx + Δ - 1 := by
      have hKx_ge1 : 1 ≤ Kx := Nat.succ_le_iff.mpr hKx_pos
      omega
    simpa [h4] using h1

  -- d^(Kx+Δ-1) ≤ μx ⊕ d^Δ < μy, so d^(Kx+Δ-1) < μy
  have h_dKxΔm1_lt_μy : iterate_op d (Kx + Δ - 1) < mu F r_old_y := by
    exact lt_of_le_of_lt hμx_op_ge h_lt

  -- By minimality of Ky with Ky > Kx + Δ - 1, we get Ky ≥ Kx + Δ
  have hKy_ge : Ky ≥ Kx + Δ := by
    -- If Ky ≤ Kx + Δ - 1, then d^(Kx+Δ-1) < μy < d^Ky ≤ d^(Kx+Δ-1), contradiction
    by_contra h
    push_neg at h
    have hKy_le : Ky ≤ Kx + Δ - 1 := Nat.lt_succ_iff.mp h
    -- d^Ky ≤ d^(Kx+Δ-1) by monotonicity
    have h_dKy_le : iterate_op d Ky ≤ iterate_op d (Kx + Δ - 1) := iterate_op_mono d hd hKy_le
    -- But μy < d^Ky and d^(Kx+Δ-1) < μy gives contradiction
    have : mu F r_old_y < iterate_op d (Kx + Δ - 1) := lt_of_lt_of_le hKy h_dKy_le
    exact not_lt.mpr (le_of_lt h_dKxΔm1_lt_μy) this

  -- Step 4: Prove Ky > Kx + Δ (strict) by ruling out equality
  have hKy_gt : Ky > Kx + Δ := by
    by_contra h_not_gt
    push_neg at h_not_gt
    have hKy_eq : Ky = Kx + Δ := le_antisymm h_not_gt hKy_ge

    -- By minimality of Ky: NOT(μy < d^(Ky-1)), so μy ≥ d^(Ky-1) = d^(Kx+Δ-1)
    have h_not_lt_Kym1 : ¬ mu F r_old_y < iterate_op d (Ky - 1) := by
      intro hlt
      have hle : Ky ≤ Ky - 1 := by
        have : Nat.find hPy_ex ≤ Ky - 1 := Nat.find_min' hPy_ex (by simpa [Py] using hlt)
        simpa [Ky] using this
      have hlt' : Ky - 1 < Ky := Nat.sub_lt hKy_pos Nat.one_pos
      exact (lt_irrefl Ky) (lt_of_le_of_lt hle hlt')
    have hμy_ge : iterate_op d (Ky - 1) ≤ mu F r_old_y := le_of_not_gt h_not_lt_Kym1

    -- Substituting Ky = Kx + Δ: μy ≥ d^(Kx+Δ-1)
    have hμy_ge' : iterate_op d (Kx + Δ - 1) ≤ mu F r_old_y := by
      have : Ky - 1 = Kx + Δ - 1 := by omega
      simpa [this] using hμy_ge

    -- But we showed d^(Kx+Δ-1) < μy (strictly), and also μy ≥ d^(Kx+Δ-1)
    -- This is NOT a contradiction! We need a different argument.
    -- The issue: Ky = Kx + Δ means d^(Kx+Δ-1) ≤ μy < d^(Kx+Δ)

    -- Actually the contradiction comes from: μx ⊕ d^Δ < μy and μx ≥ d^(Kx-1)
    -- gives μx ⊕ d^Δ ≥ d^(Kx+Δ-1). But if Ky = Kx + Δ, then μy ≥ d^(Kx+Δ-1).
    -- So μx ⊕ d^Δ ≥ d^(Kx+Δ-1) and μy ≥ d^(Kx+Δ-1). This doesn't contradict μx ⊕ d^Δ < μy!

    -- Let me reconsider. The A-side worked because:
    -- μx < μy ⊕ d^Δ gave an upper bound on Kx.
    -- The C-side: μx ⊕ d^Δ < μy gives a lower bound on Ky.

    -- For strict inequality, on the A-side we used:
    -- If Kx = Ky + Δ, then μx ≥ d^(Ky+Δ-1) but μy ⊕ d^Δ ≥ d^(Ky+Δ-1) from μy ≥ d^(Ky-1).
    -- This gave μx < μy ⊕ d^Δ ≤ d^(Ky+Δ-1) ≤ μx, contradiction!

    -- On the C-side, if Ky = Kx + Δ:
    -- μy ≥ d^(Kx+Δ-1) = d^(Ky-1) by minimality of Ky
    -- μx ⊕ d^Δ ≥ d^(Kx-1) ⊕ d^Δ = d^(Kx+Δ-1) = d^(Ky-1)
    -- So both μy and μx ⊕ d^Δ are ≥ d^(Ky-1). This doesn't give μx ⊕ d^Δ ≥ μy.

    -- Wait, let me look at the A-side again. We had:
    -- μy ⊕ d^Δ ≥ d^(Ky-1) ⊕ d^Δ = d^(Ky+Δ-1)
    -- And μx ≥ d^(Kx-1) = d^(Ky+Δ-1) (when Kx = Ky + Δ)
    -- But h_lt says μx < μy ⊕ d^Δ.
    -- Combined: μx < μy ⊕ d^Δ and μy ⊕ d^Δ ≥ d^(Ky+Δ-1) and μx ≥ d^(Ky+Δ-1)
    -- Hmm, this says μx < μy ⊕ d^Δ and μx ≥ d^(Ky+Δ-1) ≤ μy ⊕ d^Δ
    -- No contradiction from this alone!

    -- Actually in the A-side proof, we had:
    -- μy ⊕ d^Δ ≥ d^(Ky-1+Δ) = d^(Ky+Δ-1)
    -- But we need μx ⊕ d^Δ ≥ μy (or μx < some bound).

    -- Let me re-read the A-side. The key was:
    -- have : mu F r_old_x < iterate_op d (Ky + Δ - 1) := lt_of_lt_of_le h_lt hμy_op_ge
    -- exact not_lt.mpr hμx_ge' this
    --
    -- Here hμx_ge' : d^(Ky+Δ-1) ≤ μx
    -- And the `have` says μx < d^(Ky+Δ-1)
    -- Contradiction!

    -- On the C-side:
    -- h_lt says μx ⊕ d^Δ < μy
    -- We have hμx_op_ge : d^(Kx+Δ-1) ≤ μx ⊕ d^Δ
    -- And hμy_ge' : d^(Kx+Δ-1) ≤ μy (when Ky = Kx + Δ)
    --
    -- From h_lt and hμx_op_ge: d^(Kx+Δ-1) ≤ μx ⊕ d^Δ < μy
    -- So d^(Kx+Δ-1) < μy (strictly)
    -- But hμy_ge' says d^(Kx+Δ-1) ≤ μy (non-strictly)
    -- No contradiction from these!

    -- The issue is we need μy ≤ μx ⊕ d^Δ to get contradiction, but h_lt says the opposite.

    -- I think the C-side argument needs to be different. Let me look at what we actually need.
    -- We want: Ky - 1 - (Kx - 1) > Δ, i.e., Ky - Kx > Δ, i.e., Ky > Kx + Δ.

    -- We've shown Ky ≥ Kx + Δ. Can we rule out Ky = Kx + Δ?

    -- If Ky = Kx + Δ, then from μy < d^Ky = d^(Kx+Δ) and μx < d^Kx:
    -- We have d^(Kx-1) ≤ μx < d^Kx and d^(Kx+Δ-1) ≤ μy < d^(Kx+Δ)

    -- From h_lt: μx ⊕ d^Δ < μy
    -- μx ⊕ d^Δ < d^Kx ⊕ d^Δ = d^(Kx+Δ) (since μx < d^Kx)
    -- So μx ⊕ d^Δ < d^(Kx+Δ)
    -- And d^(Kx+Δ-1) ≤ μy < d^(Kx+Δ)
    -- So μx ⊕ d^Δ < d^(Kx+Δ) and d^(Kx+Δ-1) ≤ μy

    -- If μx ⊕ d^Δ ≥ d^(Kx+Δ-1), then combined with μx ⊕ d^Δ < μy and μy < d^(Kx+Δ),
    -- we get d^(Kx+Δ-1) ≤ μx ⊕ d^Δ < μy < d^(Kx+Δ).
    -- This is consistent - no contradiction.

    -- Actually, we do have μx ⊕ d^Δ ≥ d^(Kx+Δ-1) from hμx_op_ge (shown earlier).
    -- So d^(Kx+Δ-1) ≤ μx ⊕ d^Δ < μy and d^(Kx+Δ-1) ≤ μy.
    -- Still no contradiction.

    -- Hmm, the C-side is trickier. Let me think about this differently.

    -- Actually wait - on the A-side, the key was:
    -- μx < μy ⊕ d^Δ (given by h_lt on A-side)
    -- μy ⊕ d^Δ ≥ d^(Ky+Δ-1) (from μy ≥ d^(Ky-1))
    -- μx ≥ d^(Kx-1) = d^(Ky+Δ-1) (when Kx = Ky + Δ)
    -- Combined: μx < μy ⊕ d^Δ but μy ⊕ d^Δ ≥ d^(Ky+Δ-1) ≤ μx - wait that's wrong.
    -- Actually: μx ≥ d^(Ky+Δ-1) and μx < μy ⊕ d^Δ, so μy ⊕ d^Δ > d^(Ky+Δ-1).
    -- But we also have μy ⊕ d^Δ ≥ d^(Ky+Δ-1). So μy ⊕ d^Δ > μx ≥ d^(Ky+Δ-1).
    -- This is consistent with h_lt!

    -- I think I made an error in the A-side proof. Let me re-check...
    -- Actually looking back at the A-side proof I wrote:
    -- have : mu F r_old_x < iterate_op d (Ky + Δ - 1) := lt_of_lt_of_le h_lt hμy_op_ge
    -- Here h_lt says μx < μy ⊕ d^Δ
    -- And hμy_op_ge says d^(Ky+Δ-1) ≤ μy ⊕ d^Δ
    -- Hmm wait, that gives μx < μy ⊕ d^Δ, and d^(Ky+Δ-1) ≤ μy ⊕ d^Δ
    -- From these we can't conclude μx < d^(Ky+Δ-1)!

    -- Oh I see the issue - I used lt_of_lt_of_le which should be lt_of_lt_of_le h_lt hμy_op_ge
    -- But that would give μx < d^(Ky+Δ-1) only if μy ⊕ d^Δ ≤ d^(Ky+Δ-1), which is backwards!

    -- Let me re-examine. Actually the correct direction is:
    -- hμy_op_ge : d^(Ky+Δ-1) ≤ μy ⊕ d^Δ
    -- From h_lt: μx < μy ⊕ d^Δ
    -- If we had μx ≥ d^(Ky+Δ-1), then combined with d^(Ky+Δ-1) ≤ μy ⊕ d^Δ and μx < μy ⊕ d^Δ,
    -- we get d^(Ky+Δ-1) ≤ μx < μy ⊕ d^Δ.
    -- This is consistent!

    -- So my A-side proof has a bug! The line:
    -- have : mu F r_old_x < iterate_op d (Ky + Δ - 1) := lt_of_lt_of_le h_lt hμy_op_ge
    -- should fail because lt_of_lt_of_le requires a ≤ b and b < c to give a < c,
    -- but here we have a < b (h_lt: μx < μy ⊕ d^Δ) and c ≤ b (hμy_op_ge: d^(Ky+Δ-1) ≤ μy ⊕ d^Δ).

    -- Actually wait, I need to re-read my proof. Let me look at it again...
    -- have hμy_op_ge : iterate_op d (Ky + Δ - 1) ≤ op (mu F r_old_y) (iterate_op d Δ)
    -- have : mu F r_old_x < iterate_op d (Ky + Δ - 1) := lt_of_lt_of_le h_lt hμy_op_ge
    --
    -- lt_of_lt_of_le : a < b → b ≤ c → a < c
    -- Here a = μx, b should be μy ⊕ d^Δ (from h_lt: μx < μy ⊕ d^Δ)
    -- And we need b ≤ c, i.e., μy ⊕ d^Δ ≤ d^(Ky+Δ-1)
    -- But hμy_op_ge says d^(Ky+Δ-1) ≤ μy ⊕ d^Δ, which is c ≤ b, not b ≤ c!
    --
    -- So lt_of_lt_of_le h_lt hμy_op_ge would require:
    -- h_lt : μx < (μy ⊕ d^Δ)
    -- hμy_op_ge : μy ⊕ d^Δ ≤ d^(Ky+Δ-1)
    -- But that's not what hμy_op_ge says!
    --
    -- I think I made a typo or the direction is wrong. Let me check the actual goal again.
    --
    -- The goal was to show contradiction when Kx = Ky + Δ.
    -- We have:
    -- - μx ≥ d^(Kx-1) = d^(Ky+Δ-1) (by minimality of Kx, when Kx = Ky + Δ)
    -- - μy ≥ d^(Ky-1) (by minimality of Ky)
    -- - h_lt: μx < μy ⊕ d^Δ (given)
    --
    -- From μy ≥ d^(Ky-1):
    -- μy ⊕ d^Δ ≥ d^(Ky-1) ⊕ d^Δ = d^(Ky-1+Δ) = d^(Ky+Δ-1)
    --
    -- So: μx ≥ d^(Ky+Δ-1) and μy ⊕ d^Δ ≥ d^(Ky+Δ-1) and μx < μy ⊕ d^Δ
    -- This is d^(Ky+Δ-1) ≤ μx < μy ⊕ d^Δ and d^(Ky+Δ-1) ≤ μy ⊕ d^Δ
    -- Perfectly consistent!
    --
    -- So the A-side proof I wrote is WRONG. The `lt_of_lt_of_le h_lt hμy_op_ge` doesn't typecheck
    -- because the order is wrong.
    --
    -- This is a problem. Let me think about the correct argument...
    --
    -- Actually, maybe I need to be more careful about what h_lt says on the A-side vs C-side.
    --
    -- A-side h_lt: μx < μy ⊕ d^Δ (μx is between μy and μy ⊕ d^Δ)
    -- C-side h_lt: μx ⊕ d^Δ < μy (μy is beyond μx ⊕ d^Δ)
    --
    -- For the A-side, we want to show θx - θy < Δ·δ.
    -- For the C-side, we want to show θy - θx > Δ·δ.
    --
    -- The A-side argument should work as follows:
    -- If θx - θy = Δ·δ (boundary case), then Kx - Ky = Δ, i.e., Kx = Ky + Δ.
    -- We need to derive a contradiction from Kx = Ky + Δ and h_lt: μx < μy ⊕ d^Δ.
    --
    -- From Kx = Ky + Δ:
    -- - d^(Kx-1) ≤ μx < d^Kx, i.e., d^(Ky+Δ-1) ≤ μx < d^(Ky+Δ)
    -- - d^(Ky-1) ≤ μy < d^Ky
    --
    -- From μy < d^Ky:
    -- μy ⊕ d^Δ < d^Ky ⊕ d^Δ = d^(Ky+Δ)
    --
    -- So μy ⊕ d^Δ < d^(Ky+Δ).
    -- And μx ≥ d^(Ky+Δ-1).
    --
    -- h_lt says μx < μy ⊕ d^Δ.
    -- So d^(Ky+Δ-1) ≤ μx < μy ⊕ d^Δ < d^(Ky+Δ).
    --
    -- This is d^(Ky+Δ-1) ≤ μx < μy ⊕ d^Δ < d^(Ky+Δ).
    -- Still consistent!
    --
    -- Hmm, but wait - we also have the lower bound on μy:
    -- d^(Ky-1) ≤ μy
    -- So μy ⊕ d^Δ ≥ d^(Ky-1) ⊕ d^Δ = d^(Ky+Δ-1).
    --
    -- So we have:
    -- - μy ⊕ d^Δ ≥ d^(Ky+Δ-1) (from μy ≥ d^(Ky-1))
    -- - μy ⊕ d^Δ < d^(Ky+Δ) (from μy < d^Ky)
    -- - μx ≥ d^(Ky+Δ-1) (from minimality of Kx when Kx = Ky+Δ)
    -- - μx < d^(Ky+Δ) (from definition of Kx)
    -- - h_lt: μx < μy ⊕ d^Δ
    --
    -- So: d^(Ky+Δ-1) ≤ μx < μy ⊕ d^Δ and d^(Ky+Δ-1) ≤ μy ⊕ d^Δ < d^(Ky+Δ)
    -- And: d^(Ky+Δ-1) ≤ μx < d^(Ky+Δ)
    --
    -- All of these are consistent! The gap between d^(Ky+Δ-1) and d^(Ky+Δ) can contain
    -- both μx and μy ⊕ d^Δ with μx < μy ⊕ d^Δ.
    --
    -- So there's no immediate contradiction from Kx = Ky + Δ on the A-side!
    --
    -- This suggests that the K&S argument must be more subtle. Let me re-read the TODO comment.
    --
    -- The comment says to use `delta_cut_tight_common_den` to get A/C witnesses and derive
    -- a contradiction. This suggests the argument needs more machinery than just the crossing
    -- index bounds.
    --
    -- Actually, let me think about this differently. The key is that B is empty.
    -- When B is empty, δ is defined as sSup(A-statistics).
    -- Maybe the contradiction comes from the tight cut property of δ itself.
    --
    -- Actually, looking back at my proof, I used `lt_of_lt_of_le h_lt hμy_op_ge` but
    -- I may have had the arguments in the wrong order or used a different lemma name.
    -- Let me check what lt_of_lt_of_le actually does...
    --
    -- lt_of_lt_of_le : ∀ {a b c : α} [inst : Preorder α], a < b → b ≤ c → a < c
    --
    -- So lt_of_lt_of_le h_lt hμy_op_ge would need:
    -- h_lt : a < b, i.e., μx < μy ⊕ d^Δ (this is correct)
    -- hμy_op_ge : b ≤ c, i.e., μy ⊕ d^Δ ≤ c
    --
    -- But hμy_op_ge : d^(Ky+Δ-1) ≤ μy ⊕ d^Δ, which is the wrong direction!
    --
    -- So my proof has a type error. The build would catch this. Let me try building and see what happens.
    --
    -- Actually, maybe I should just try to compile and see what errors come up.

    -- For now, let me try a different approach for the C-side that might actually work.
    -- The C-side goal is θy - θx > Δ·δ, i.e., (Ky-1) - (Kx-1) > Δ, i.e., Ky - Kx > Δ.
    -- We showed Ky ≥ Kx + Δ. If we can't prove Ky > Kx + Δ directly, maybe we need
    -- the delta_cut_tight argument.

    -- This proof attempt is obsolete (left here only as a narrative comment).
    -- (no Lean code)

  -- Step 5: From Ky > Kx + Δ, conclude θy - θx > Δ·δ
  have hδ_pos : 0 < δ := delta_pos hk R IH H d hd
  have hKy_sub_Kx_gt : Ky - 1 - (Kx - 1) > Δ := by
    have h1 : Ky - 1 > Kx + Δ - 1 := by
      have hKx_ge1 : 1 ≤ Kx := Nat.succ_le_iff.mpr hKx_pos
      omega
    have h2 : Kx + Δ - 1 - (Kx - 1) = Δ := by
      have hKx_ge1 : 1 ≤ Kx := Nat.succ_le_iff.mpr hKx_pos
      omega
    omega

  calc (Δ : ℝ) * δ
      < ((Ky - 1 : ℕ) - (Kx - 1 : ℕ) : ℝ) * δ := by
        have h : (Δ : ℝ) < ((Ky - 1 : ℕ) - (Kx - 1 : ℕ) : ℝ) := by
          have : Δ < (Ky - 1 : ℕ) - (Kx - 1 : ℕ) := hKy_sub_Kx_gt
          exact_mod_cast this
        exact (mul_lt_mul_right hδ_pos).mpr h
    _ = ((Ky - 1 : ℕ) : ℝ) * δ - ((Kx - 1 : ℕ) : ℝ) * δ := by ring
    _ = R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by rw [hθy_eq, hθx_eq]
-/
-- END REMOVED PROOF BODY

/-- Legacy relative Θ-gap upper bound (A-side).

If `mu F r_old_y < mu F r_old_x` but `mu F r_old_x < mu F r_old_y ⊕ d^Δ`, then the Θ-gap is
strictly less than `Δ * δ`, where `δ := chooseδ hk R d hd`.

The internal (`d^Δ` already on the old grid) branch is proved; the genuinely external case is
still pending.

This lemma is retained for historical context; the current extension theorem does **not** use it.
For the refactored gap bound used by `extend_grid_rep_with_atom`, see
`theta_gap_lt_of_mu_lt_op_of_chooseδBaseAdmissible`. -/
lemma theta_gap_lt_of_mu_lt_op
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hZQ_if : ZQuantized_chooseδ_if_B_nonempty (α := α) hk R d hd)
    (hStrict : BEmptyStrictGapSpec hk R IH H d hd)
    (r_old_x r_old_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ)
    (h_mu : mu F r_old_y < mu F r_old_x)
    (h_lt : mu F r_old_x < op (mu F r_old_y) (iterate_op d Δ)) :
    R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩
      < (Δ : ℝ) * chooseδ hk R d hd := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  have hδB := chooseδ_B_bound hk R IH d hd
  by_cases hBΔ : ∃ rΔ : Multi k, rΔ ∈ extensionSetB F d Δ
  · rcases hBΔ with ⟨rΔ, hrΔB⟩
    have hμ_rΔ : mu F rΔ = iterate_op d Δ := by
      simpa [extensionSetB, Set.mem_setOf_eq] using hrΔB

    have hμ_sum :
        mu F (r_old_y + rΔ) = op (mu F r_old_y) (iterate_op d Δ) := by
      calc
        mu F (r_old_y + rΔ) = op (mu F r_old_y) (mu F rΔ) := by
          simpa using (mu_add_of_comm (F := F) H r_old_y rΔ)
        _ = op (mu F r_old_y) (iterate_op d Δ) := by rw [hμ_rΔ]

    have hμ_lt_grid : mu F r_old_x < mu F (r_old_y + rΔ) := by
      simpa [hμ_sum] using h_lt

    have hθ_lt :
        R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
          R.Θ_grid ⟨mu F (r_old_y + rΔ), mu_mem_kGrid F (r_old_y + rΔ)⟩ :=
      R.strictMono hμ_lt_grid

    have hθ_add :
        R.Θ_grid ⟨mu F (r_old_y + rΔ), mu_mem_kGrid F (r_old_y + rΔ)⟩ =
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ +
            R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ := by
      simpa [Pi.add_apply] using (R.add r_old_y rΔ)

    have hδBΔ : separationStatistic R rΔ Δ hΔ = δ := by
      simpa [δ] using (hδB rΔ Δ hΔ hrΔB)

    have hθ_rΔ : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ = (Δ : ℝ) * δ := by
      have hΔ_ne : (Δ : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_zero_of_lt hΔ)
      have hdiv : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ / (Δ : ℝ) = δ := by
        simpa [separationStatistic] using hδBΔ
      have hmul : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ = δ * (Δ : ℝ) :=
        (div_eq_iff hΔ_ne).1 hdiv
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

    have hθ_lt' :
        R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ +
            R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ := by
      simpa [hθ_add] using hθ_lt

    have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ := by
      linarith [hθ_lt', hθ_rΔ]
    simpa [δ] using this
  · -- External case: no B-witness for d^Δ specifically.
    push_neg at hBΔ
    have hδ_pos : 0 < δ := delta_pos hk R IH H d hd

    -- If the boundary `μy ⊕ d^Δ` itself lies on the old k-grid, we can reduce to the
    -- (already proved) trade-equality case via `delta_shift_equiv`.
    -- This is a *base-indexed* equality witness for base `μy`, and does not follow from
    -- global `extensionSetB F d Δ` (see
    -- `Mettapedia/ProbabilityTheory/KnuthSkilling/RepresentationTheorem/Counterexamples/GoertzelLemma7.lean`).
    by_cases hB_base : ∃ rB : Multi k, mu F rB = op (mu F r_old_y) (iterate_op d Δ)
    · rcases hB_base with ⟨rB, hrB⟩
      have hμ_lt_grid : mu F r_old_x < mu F rB := by
        simpa [hrB] using h_lt
      have hθ_lt :
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
            R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ :=
        R.strictMono hμ_lt_grid
      have hδA := chooseδ_A_bound hk R IH H d hd
      have hδC := chooseδ_C_bound hk R IH H d hd
      have hδB' := chooseδ_B_bound hk R IH d hd
      have h_gap_eq :
          R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ -
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ = (Δ : ℝ) * δ :=
        delta_shift_equiv (R := R) (H := H) (IH := IH) (d := d) (hd := hd) (δ := δ)
          (hδ_pos := hδ_pos) (hδA := hδA) (hδC := hδC) (hδB := hδB')
          (hΔ := hΔ) (htrade := hrB)
      have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ := by
        linarith [hθ_lt, h_gap_eq]
      simpa [δ] using this

    -- Split on global B nonempty vs empty (rational vs irrational δ cases).
    by_cases hB_global : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u
    · -- Global B ≠ ∅: strict A/B/C separation forces μy to sit on an exact d^n boundary.
      have hZQ : ZQuantized F R δ := by
        simpa [δ] using (hZQ_if hB_global)
      rcases hB_global with ⟨rB, uB, huB, hrB⟩

      have hδB_uB : separationStatistic R rB uB huB = δ := by
        simpa [δ] using chooseδ_B_bound hk R IH d hd rB uB huB hrB

      have hA_lt_δ :
          ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u → separationStatistic R r u hu < δ := by
        intro r u hu hrA
        have hAB :
            separationStatistic R r u hu < separationStatistic R rB uB huB :=
          separation_property_A_B R H hd hu hrA huB hrB
        simpa [hδB_uB] using hAB

      have hδ_lt_C :
          ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u → δ < separationStatistic R r u hu := by
        intro r u hu hrC
        have hBC :
            separationStatistic R rB uB huB < separationStatistic R r u hu :=
          separation_property_B_C R H hd huB hrB hu hrC
        simpa [hδB_uB] using hBC

      -- Define K as the minimal iterate bound for μy: μy < d^K and ¬(μy < d^(K-1)).
      let P : ℕ → Prop := fun n => mu F r_old_y < iterate_op d n
      have hP_ex : ∃ n : ℕ, P n := bounded_by_iterate d hd (mu F r_old_y)
      let K : ℕ := Nat.find hP_ex
      have hK : mu F r_old_y < iterate_op d K := Nat.find_spec hP_ex
      have hK_pos : 0 < K := by
        by_contra h
        have hK0 : K = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
        rw [hK0, iterate_op_zero] at hK
        exact not_lt.mpr (ident_le (mu F r_old_y)) hK

      have h_not_lt_Km1 : ¬ mu F r_old_y < iterate_op d (K - 1) := by
        intro hlt
        have hle : K ≤ K - 1 := by
          -- If `mu F r_old_y < d^(K-1)`, then minimality of `K` forces `K ≤ K-1`.
          have : Nat.find hP_ex ≤ K - 1 := Nat.find_min' hP_ex hlt
          simpa [K] using this
        omega

      -- K = 1 is a special case (K-1 = 0); handle it by quantization.
      by_cases hK1 : K = 1
      · have hyA1 : r_old_y ∈ extensionSetA F d 1 := by
          simpa [hK1, extensionSetA, iterate_op_one] using hK
        have hstat_y_lt : separationStatistic R r_old_y 1 Nat.one_pos < δ :=
          hA_lt_δ r_old_y 1 Nat.one_pos hyA1
        have hθy_lt : R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < δ := by
          simpa [separationStatistic] using hstat_y_lt
        rcases hZQ r_old_y with ⟨my, hmy⟩
        have hmy_lt_one : (my : ℝ) < (1 : ℝ) := by
          have : (my : ℝ) * δ < (1 : ℝ) * δ := by simpa [hmy, mul_one] using hθy_lt
          exact (mul_lt_mul_iff_left₀ hδ_pos).1 this
        have hmy_le0 : my ≤ 0 := by
          have : (my : ℝ) < ((0 : ℤ) + 1 : ℤ) := by
            simpa [Int.cast_add, Int.cast_zero, Int.cast_one] using hmy_lt_one
          exact (Int.lt_add_one_iff).1 (Int.cast_lt.mp this)
        have hθy_nonneg : 0 ≤ R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
          have h_ident_le : ident ≤ mu F r_old_y := ident_le _
          rcases h_ident_le.eq_or_lt with h_eq | h_lt'
          · have hsub :
                (⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ : {x // x ∈ kGrid F}) =
                  ⟨ident, ident_mem_kGrid F⟩ := by
                ext
                exact h_eq.symm
            simp [hsub, R.ident_eq_zero]
          · have hθ_pos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
                R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := R.strictMono h_lt'
            simpa [R.ident_eq_zero] using (le_of_lt hθ_pos)
        have hmy_nonneg : 0 ≤ my := by
          have hmy_nonneg_real : (0 : ℝ) ≤ (my : ℝ) := by
            have : (0 : ℝ) ≤ (my : ℝ) * δ := by simpa [hmy] using hθy_nonneg
            -- Cancel `δ` from the right, since `δ > 0`.
            exact (mul_nonneg_iff_left_nonneg_of_pos hδ_pos).1 this
          exact (Int.cast_nonneg_iff).1 hmy_nonneg_real
        have hmy_eq0 : my = 0 := le_antisymm hmy_le0 hmy_nonneg
        have hθy_eq0 : R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ = 0 := by
          simpa [hmy_eq0] using hmy
        have hμy_eq_ident : mu F r_old_y = ident := by
          by_contra hne
          have hpos : ident < mu F r_old_y :=
            lt_of_le_of_ne (ident_le (mu F r_old_y)) (Ne.symm hne)
          have hθpos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
                R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := R.strictMono hpos
          simpa [R.ident_eq_zero, hθy_eq0] using hθpos
        have hxA : r_old_x ∈ extensionSetA F d Δ := by
          have : mu F r_old_x < iterate_op d Δ := by
            simpa [hμy_eq_ident, op_ident_left] using h_lt
          simpa [extensionSetA] using this
        have hstat_x_lt : separationStatistic R r_old_x Δ hΔ < δ :=
          hA_lt_δ r_old_x Δ hΔ hxA
        have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
        have hθx_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ < (Δ : ℝ) * δ := by
          have := (div_lt_iff₀ hΔ_pos_real).1 (by simpa [separationStatistic] using hstat_x_lt)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ := by
          simpa [hμy_eq_ident, R.ident_eq_zero, hθy_eq0] using hθx_lt
        simpa [δ] using this
      · have hKm1_pos : 0 < K - 1 := by omega
        have hyA : r_old_y ∈ extensionSetA F d K := by
          simpa [extensionSetA] using hK
        have hstat_y_lt : separationStatistic R r_old_y K hK_pos < δ :=
          hA_lt_δ r_old_y K hK_pos hyA
        have hK_pos_real : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK_pos
        have hθy_lt :
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (K : ℝ) * δ := by
          have := (div_lt_iff₀ hK_pos_real).1 (by simpa [separationStatistic] using hstat_y_lt)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        rcases hZQ r_old_y with ⟨my, hmy⟩
        have hy_eq_or_gt :
            mu F r_old_y = iterate_op d (K - 1) ∨ iterate_op d (K - 1) < mu F r_old_y := by
          rcases lt_trichotomy (mu F r_old_y) (iterate_op d (K - 1)) with hlt | heq | hgt
          · exact False.elim (h_not_lt_Km1 hlt)
          · exact Or.inl heq
          · exact Or.inr hgt
        have hμy_eq : mu F r_old_y = iterate_op d (K - 1) := by
          rcases hy_eq_or_gt with hEq | hGt
          · exact hEq
          · have hyC : r_old_y ∈ extensionSetC F d (K - 1) := by
              simpa [extensionSetC] using hGt
            have hstat_y_gt : δ < separationStatistic R r_old_y (K - 1) hKm1_pos :=
              hδ_lt_C r_old_y (K - 1) hKm1_pos hyC
            have hKm1_pos_real : (0 : ℝ) < ((K - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hKm1_pos
            have hθy_gt : ((K - 1 : ℕ) : ℝ) * δ <
                R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
              have := (lt_div_iff₀ hKm1_pos_real).1 (by simpa [separationStatistic] using hstat_y_gt)
              simpa [mul_comm, mul_left_comm, mul_assoc] using this
            have h_between :
                ((K - 1 : ℕ) : ℝ) * δ < (my : ℝ) * δ ∧ (my : ℝ) * δ < (K : ℝ) * δ := by
              constructor
              · simpa [hmy] using hθy_gt
              · simpa [hmy] using hθy_lt
            have h_between' : ((K - 1 : ℕ) : ℝ) < (my : ℝ) ∧ (my : ℝ) < (K : ℝ) := by
              constructor
              · exact (mul_lt_mul_iff_left₀ hδ_pos).1 h_between.1
              · exact (mul_lt_mul_iff_left₀ hδ_pos).1 h_between.2
            have h_lt : (my : ℤ) < (K : ℤ) := by
              have : (my : ℝ) < (K : ℤ) := by simpa [Int.cast_natCast] using h_between'.2
              exact Int.cast_lt.mp this
            have h_gt : ((K - 1 : ℕ) : ℤ) < my := by
              have : (((K - 1 : ℕ) : ℤ) : ℝ) < (my : ℝ) := by
                simpa [Int.cast_natCast] using h_between'.1
              exact Int.cast_lt.mp this
            omega
        have hyB : r_old_y ∈ extensionSetB F d (K - 1) := by
          simpa [extensionSetB, Set.mem_setOf_eq, hμy_eq]
        have hstat_y_eq : separationStatistic R r_old_y (K - 1) hKm1_pos = δ := by
          simpa [δ] using chooseδ_B_bound hk R IH d hd r_old_y (K - 1) hKm1_pos hyB
        have hθy_eq :
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ = ((K - 1 : ℕ) : ℝ) * δ := by
          have hKm1_ne : ((K - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hKm1_pos
          have := (div_eq_iff hKm1_ne).1 (by simpa [separationStatistic] using hstat_y_eq)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have hxA : r_old_x ∈ extensionSetA F d (K - 1 + Δ) := by
          have : mu F r_old_x < iterate_op d (K - 1 + Δ) := by
            calc
              mu F r_old_x < op (mu F r_old_y) (iterate_op d Δ) := h_lt
              _ = op (iterate_op d (K - 1)) (iterate_op d Δ) := by rw [hμy_eq]
              _ = iterate_op d (K - 1 + Δ) := by simpa using (iterate_op_add d (K - 1) Δ)
          simpa [extensionSetA] using this
        have hx_level_pos : 0 < (K - 1 + Δ) := Nat.add_pos_left hKm1_pos Δ
        have hstat_x_lt : separationStatistic R r_old_x (K - 1 + Δ) hx_level_pos < δ :=
          hA_lt_δ r_old_x (K - 1 + Δ) hx_level_pos hxA
        have hx_pos_real : (0 : ℝ) < ((K - 1 + Δ : ℕ) : ℝ) := Nat.cast_pos.mpr hx_level_pos
        have hθx_lt :
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ < ((K - 1 + Δ : ℕ) : ℝ) * δ := by
          have := (div_lt_iff₀ hx_pos_real).1 (by simpa [separationStatistic] using hstat_x_lt)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ := by
          have h_expand :
              ((K - 1 + Δ : ℕ) : ℝ) * δ = ((K - 1 : ℕ) : ℝ) * δ + (Δ : ℝ) * δ := by
            simp [Nat.cast_add, add_mul]
          have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (Δ : ℝ) * δ := by
            linarith [hθx_lt, hθy_eq, h_expand]
          linarith
        simpa [δ] using this
    · -- Global B = ∅: TODO(K&S Appendix A): use delta_cut_tight + Z-quantization.
      have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u := by
        intro r u hu hrB
        exact hB_global ⟨r, u, hu, hrB⟩
      have hB_base' : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r_old_y Δ := by
        simpa [extensionSetB_base] using hB_base
      have hstat :
          separationStatistic_base R r_old_y r_old_x Δ hΔ < δ :=
        by
          simpa [δ] using hStrict.A hB_empty r_old_x r_old_y Δ hΔ h_mu h_lt hB_base'
      have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
      have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ := by
        have h' := (div_lt_iff₀ hΔ_pos_real).1 (by simpa [separationStatistic_base] using hstat)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h'
      simpa [δ] using this
      /-
      -- First get a **non-strict** bound `θx - θy ≤ Δ·δ` from crossing indices.
      -- The remaining work is to rule out the boundary case `= Δ·δ` using
      -- `delta_cut_tight` (K&S Appendix A.3.4).
      have hZQ' : ZQuantized F R δ := by simpa [δ] using hZQ

      -- Define the least iterate bounds for μy and μx.
      let Py : ℕ → Prop := fun n => mu F r_old_y < iterate_op d n
      have hPy_ex : ∃ n : ℕ, Py n := bounded_by_iterate d hd (mu F r_old_y)
      let Ky : ℕ := Nat.find hPy_ex
      have hKy : mu F r_old_y < iterate_op d Ky := Nat.find_spec hPy_ex
      have hKy_pos : 0 < Ky := by
        by_contra h
        have hKy0 : Ky = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
        rw [hKy0, iterate_op_zero] at hKy
        exact not_lt.mpr (ident_le (mu F r_old_y)) hKy

      let Px : ℕ → Prop := fun n => mu F r_old_x < iterate_op d n
      have hPx_ex : ∃ n : ℕ, Px n := bounded_by_iterate d hd (mu F r_old_x)
      let Kx : ℕ := Nat.find hPx_ex
      have hKx : mu F r_old_x < iterate_op d Kx := Nat.find_spec hPx_ex

      -- θy = (Ky-1)·δ and θx = (Kx-1)·δ (B-empty crossing characterization).
      have hθy_eq :
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ = ((Ky - 1 : ℕ) : ℝ) * δ := by
        simpa [δ, Py, Ky, hPy_ex] using
          (theta_eq_min_iterate_bound_of_B_empty hk R IH H d hd (hZQ := by simpa [δ] using hZQ) hB_empty r_old_y)
      have hθx_eq :
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ = ((Kx - 1 : ℕ) : ℝ) * δ := by
        simpa [δ, Px, Kx, hPx_ex] using
          (theta_eq_min_iterate_bound_of_B_empty hk R IH H d hd (hZQ := by simpa [δ] using hZQ) hB_empty r_old_x)

      -- From μy < d^Ky, get μy ⊕ d^Δ < d^(Ky+Δ), hence μx < d^(Ky+Δ).
      have hμx_lt_dKyΔ : mu F r_old_x < iterate_op d (Ky + Δ) := by
        have h1 : op (mu F r_old_y) (iterate_op d Δ) < op (iterate_op d Ky) (iterate_op d Δ) :=
          op_strictMono_left (iterate_op d Δ) hKy
        have h2 : op (iterate_op d Ky) (iterate_op d Δ) = iterate_op d (Ky + Δ) := by
          simpa using (iterate_op_add d Ky Δ)
        have : mu F r_old_x < op (iterate_op d Ky) (iterate_op d Δ) := lt_trans h_lt h1
        simpa [h2] using this

      have hKx_le : Kx ≤ Ky + Δ := by
        -- minimality of Kx with predicate Px
        have : Nat.find hPx_ex ≤ Ky + Δ := Nat.find_min' hPx_ex (by simpa [Px] using hμx_lt_dKyΔ)
        simpa [Kx] using this

      have hKx_m1_le : Kx - 1 ≤ Ky + Δ - 1 := Nat.sub_le_sub_right hKx_le 1

      have hδ_pos : 0 < δ := delta_pos hk R IH H d hd
      have hθx_le :
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ ≤ ((Ky + Δ - 1 : ℕ) : ℝ) * δ := by
        -- convert Kx-1 ≤ Ky+Δ-1 into θx ≤ (Ky+Δ-1)·δ using hθx_eq
        have : ((Kx - 1 : ℕ) : ℝ) * δ ≤ ((Ky + Δ - 1 : ℕ) : ℝ) * δ := by
          have : ((Kx - 1 : ℕ) : ℝ) ≤ ((Ky + Δ - 1 : ℕ) : ℝ) := by exact_mod_cast hKx_m1_le
          exact mul_le_mul_of_nonneg_right this (le_of_lt hδ_pos)
        simpa [hθx_eq] using this

      have hθy_eq' :
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ = ((Ky - 1 : ℕ) : ℝ) * δ := hθy_eq

      have h_non_strict :
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ ≤ (Δ : ℝ) * δ := by
        have h_expand :
            ((Ky + Δ - 1 : ℕ) : ℝ) * δ = ((Ky - 1 : ℕ) : ℝ) * δ + (Δ : ℝ) * δ := by
          -- (Ky+Δ-1) = (Ky-1)+Δ
          have hKy_ge1 : 1 ≤ Ky := Nat.succ_le_iff.mpr hKy_pos
          have : Ky + Δ - 1 = (Ky - 1) + Δ := by
            -- Use the standard identity (a+b)-c = a+(b-c) when c ≤ b.
            -- We apply it to Δ + Ky - 1 = Δ + (Ky - 1) and then commute.
            calc
              Ky + Δ - 1 = Δ + Ky - 1 := by omega
              _ = Δ + (Ky - 1) := by
                    -- `Nat.add_sub_assoc` is `(k + n) - m = k + (n - m)` when `m ≤ n`.
                    -- Here: (Δ + Ky) - 1 = Δ + (Ky - 1).
                    simpa using (Nat.add_sub_assoc hKy_ge1 Δ)
              _ = (Ky - 1) + Δ := by omega
          simp [this, Nat.cast_add, add_mul]
        -- θx ≤ (Ky+Δ-1)·δ and θy = (Ky-1)·δ
        linarith [hθx_le, hθy_eq', h_expand]

      -- TODO(K&S Appendix A.3.4): upgrade `≤` to strict `<` by ruling out equality
      -- using `delta_cut_tight` + the strict μ-inequality `h_lt`.
      have h_not_eq :
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ ≠ (Δ : ℝ) * δ := by
        simpa [δ] using
          (theta_gap_lt_of_mu_lt_op_B_empty_no_eq (hk := hk) (R := R) (IH := IH) (H := H)
            (d := d) (hd := hd) (hB_empty := hB_empty)
            (r_old_x := r_old_x) (r_old_y := r_old_y) (Δ := Δ) (hΔ := hΔ) (h_mu := h_mu)
            (h_lt := h_lt))

      exact lt_of_le_of_ne h_non_strict h_not_eq
      -/

/-- Legacy relative Θ-gap lower bound (C-side).

If `mu F r_old_x < mu F r_old_y` and `(mu F r_old_x) ⊕ d^Δ < mu F r_old_y`, then the Θ-gap is
strictly greater than `Δ * δ`, where `δ := chooseδ hk R d hd`.

The internal (`d^Δ` already on the old grid) branch is proved; the genuinely external case is
still pending.

This lemma is retained for historical context; the current extension theorem does **not** use it.
For the refactored gap bound used by `extend_grid_rep_with_atom`, see
`theta_gap_gt_of_op_lt_mu_of_chooseδBaseAdmissible`. -/
lemma theta_gap_gt_of_op_lt_mu
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hZQ_if : ZQuantized_chooseδ_if_B_nonempty (α := α) hk R d hd)
    (hStrict : BEmptyStrictGapSpec hk R IH H d hd)
    (r_old_x r_old_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ)
    (h_mu : mu F r_old_x < mu F r_old_y)
    (h_lt : op (mu F r_old_x) (iterate_op d Δ) < mu F r_old_y) :
    (Δ : ℝ) * chooseδ hk R d hd <
      R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
        R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  have hδB := chooseδ_B_bound hk R IH d hd
  by_cases hBΔ : ∃ rΔ : Multi k, rΔ ∈ extensionSetB F d Δ
  · rcases hBΔ with ⟨rΔ, hrΔB⟩
    have hμ_rΔ : mu F rΔ = iterate_op d Δ := by
      simpa [extensionSetB, Set.mem_setOf_eq] using hrΔB

    have hμ_sum :
        mu F (r_old_x + rΔ) = op (mu F r_old_x) (iterate_op d Δ) := by
      calc
        mu F (r_old_x + rΔ) = op (mu F r_old_x) (mu F rΔ) := by
          simpa using (mu_add_of_comm (F := F) H r_old_x rΔ)
        _ = op (mu F r_old_x) (iterate_op d Δ) := by rw [hμ_rΔ]

    have hμ_lt_grid : mu F (r_old_x + rΔ) < mu F r_old_y := by
      simpa [hμ_sum] using h_lt

    have hθ_lt :
        R.Θ_grid ⟨mu F (r_old_x + rΔ), mu_mem_kGrid F (r_old_x + rΔ)⟩ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
      R.strictMono hμ_lt_grid

    have hθ_add :
        R.Θ_grid ⟨mu F (r_old_x + rΔ), mu_mem_kGrid F (r_old_x + rΔ)⟩ =
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ +
            R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ := by
      simpa [Pi.add_apply] using (R.add r_old_x rΔ)

    have hδBΔ : separationStatistic R rΔ Δ hΔ = δ := by
      simpa [δ] using (hδB rΔ Δ hΔ hrΔB)

    have hθ_rΔ : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ = (Δ : ℝ) * δ := by
      have hΔ_ne : (Δ : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_zero_of_lt hΔ)
      have hdiv : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ / (Δ : ℝ) = δ := by
        simpa [separationStatistic] using hδBΔ
      have hmul : R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ = δ * (Δ : ℝ) :=
        (div_eq_iff hΔ_ne).1 hdiv
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

    have hθ_lt' :
        R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ +
            R.Θ_grid ⟨mu F rΔ, mu_mem_kGrid F rΔ⟩ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
      simpa [hθ_add] using hθ_lt

    have : (Δ : ℝ) * δ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
      linarith [hθ_lt', hθ_rΔ]
    simpa [δ] using this
  · -- External case: no B-witness for d^Δ specifically.
    push_neg at hBΔ
    have hδ_pos : 0 < δ := delta_pos hk R IH H d hd

    -- If the boundary `μx ⊕ d^Δ` lies on the old k-grid, use `delta_shift_equiv` as in the A-side.
    by_cases hB_base : ∃ rB : Multi k, mu F rB = op (mu F r_old_x) (iterate_op d Δ)
    · rcases hB_base with ⟨rB, hrB⟩
      have hμ_lt_grid : mu F rB < mu F r_old_y := by
        simpa [hrB] using h_lt
      have hθ_lt :
          R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ <
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
        R.strictMono hμ_lt_grid
      have hδA := chooseδ_A_bound hk R IH H d hd
      have hδC := chooseδ_C_bound hk R IH H d hd
      have hδB' := chooseδ_B_bound hk R IH d hd
      have h_gap_eq :
          R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ -
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ = (Δ : ℝ) * δ :=
        delta_shift_equiv (R := R) (H := H) (IH := IH) (d := d) (hd := hd) (δ := δ)
          (hδ_pos := hδ_pos) (hδA := hδA) (hδC := hδC) (hδB := hδB')
          (hΔ := hΔ) (htrade := hrB)
      have : (Δ : ℝ) * δ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
        -- θ(rB) = θx + Δ·δ and θ(rB) < θy
        linarith [hθ_lt, h_gap_eq]
      simpa [δ] using this

    -- Split on global B nonempty vs empty (rational vs irrational δ cases).
    by_cases hB_global : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u
    · -- Global B ≠ ∅: strict A/B/C separation forces μx to sit on an exact d^n boundary.
      have hZQ : ZQuantized F R δ := by
        simpa [δ] using (hZQ_if hB_global)
      rcases hB_global with ⟨rB, uB, huB, hrB⟩

      have hδB_uB : separationStatistic R rB uB huB = δ := by
        simpa [δ] using chooseδ_B_bound hk R IH d hd rB uB huB hrB

      have hA_lt_δ :
          ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u → separationStatistic R r u hu < δ := by
        intro r u hu hrA
        have hAB :
            separationStatistic R r u hu < separationStatistic R rB uB huB :=
          separation_property_A_B R H hd hu hrA huB hrB
        simpa [hδB_uB] using hAB

      have hδ_lt_C :
          ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u → δ < separationStatistic R r u hu := by
        intro r u hu hrC
        have hBC :
            separationStatistic R rB uB huB < separationStatistic R r u hu :=
          separation_property_B_C R H hd huB hrB hu hrC
        simpa [hδB_uB] using hBC

      -- Define K as the minimal iterate bound for μx: μx < d^K and ¬(μx < d^(K-1)).
      let P : ℕ → Prop := fun n => mu F r_old_x < iterate_op d n
      have hP_ex : ∃ n : ℕ, P n := bounded_by_iterate d hd (mu F r_old_x)
      let K : ℕ := Nat.find hP_ex
      have hK : mu F r_old_x < iterate_op d K := Nat.find_spec hP_ex
      have hK_pos : 0 < K := by
        by_contra h
        have hK0 : K = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
        rw [hK0, iterate_op_zero] at hK
        exact not_lt.mpr (ident_le (mu F r_old_x)) hK

      have h_not_lt_Km1 : ¬ mu F r_old_x < iterate_op d (K - 1) := by
        intro hlt
        have hle : K ≤ K - 1 := by
          have : Nat.find hP_ex ≤ K - 1 := Nat.find_min' hP_ex hlt
          simpa [K] using this
        omega

      -- K = 1 is a special case (K-1 = 0); handle it by quantization.
      by_cases hK1 : K = 1
      · have hxA1 : r_old_x ∈ extensionSetA F d 1 := by
          simpa [hK1, extensionSetA, iterate_op_one] using hK
        have hstat_x_lt : separationStatistic R r_old_x 1 Nat.one_pos < δ :=
          hA_lt_δ r_old_x 1 Nat.one_pos hxA1
        have hθx_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ < δ := by
          simpa [separationStatistic] using hstat_x_lt
        rcases hZQ r_old_x with ⟨mx, hmx⟩
        have hmx_lt_one : (mx : ℝ) < (1 : ℝ) := by
          have : (mx : ℝ) * δ < (1 : ℝ) * δ := by simpa [hmx, mul_one] using hθx_lt
          exact (mul_lt_mul_iff_left₀ hδ_pos).1 this
        have hmx_le0 : mx ≤ 0 := by
          have : (mx : ℝ) < ((0 : ℤ) + 1 : ℤ) := by
            simpa [Int.cast_add, Int.cast_zero, Int.cast_one] using hmx_lt_one
          exact (Int.lt_add_one_iff).1 (Int.cast_lt.mp this)
        have hθx_nonneg : 0 ≤ R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
          have h_ident_le : ident ≤ mu F r_old_x := ident_le _
          rcases h_ident_le.eq_or_lt with h_eq | h_lt'
          · have hsub :
                (⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ : {x // x ∈ kGrid F}) =
                  ⟨ident, ident_mem_kGrid F⟩ := by
                ext
                exact h_eq.symm
            simp [hsub, R.ident_eq_zero]
          · have hθ_pos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
                R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := R.strictMono h_lt'
            simpa [R.ident_eq_zero] using (le_of_lt hθ_pos)
        have hmx_nonneg : 0 ≤ mx := by
          have hmx_nonneg_real : (0 : ℝ) ≤ (mx : ℝ) := by
            have : (0 : ℝ) ≤ (mx : ℝ) * δ := by simpa [hmx] using hθx_nonneg
            exact (mul_nonneg_iff_left_nonneg_of_pos hδ_pos).1 this
          exact (Int.cast_nonneg_iff).1 hmx_nonneg_real
        have hmx_eq0 : mx = 0 := le_antisymm hmx_le0 hmx_nonneg
        have hθx_eq0 : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ = 0 := by
          simpa [hmx_eq0] using hmx
        have hμx_eq_ident : mu F r_old_x = ident := by
          by_contra hne
          have hpos : ident < mu F r_old_x :=
            lt_of_le_of_ne (ident_le (mu F r_old_x)) (Ne.symm hne)
          have hθpos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
                R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := R.strictMono hpos
          simpa [R.ident_eq_zero, hθx_eq0] using hθpos
        have hyC : r_old_y ∈ extensionSetC F d Δ := by
          have : iterate_op d Δ < mu F r_old_y := by
            simpa [hμx_eq_ident, op_ident_left] using h_lt
          simpa [extensionSetC] using this
        have hstat_y_gt : δ < separationStatistic R r_old_y Δ hΔ :=
          hδ_lt_C r_old_y Δ hΔ hyC
        have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
        have hθy_gt : (Δ : ℝ) * δ <
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
          have := (lt_div_iff₀ hΔ_pos_real).1 (by simpa [separationStatistic] using hstat_y_gt)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have : (Δ : ℝ) * δ <
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
                R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
          simpa [hμx_eq_ident, R.ident_eq_zero, hθx_eq0] using hθy_gt
        simpa [δ] using this
      · have hKm1_pos : 0 < K - 1 := by omega
        have hxA : r_old_x ∈ extensionSetA F d K := by
          simpa [extensionSetA] using hK
        have hstat_x_lt : separationStatistic R r_old_x K hK_pos < δ :=
          hA_lt_δ r_old_x K hK_pos hxA
        have hK_pos_real : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK_pos
        have hθx_lt :
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ < (K : ℝ) * δ := by
          have := (div_lt_iff₀ hK_pos_real).1 (by simpa [separationStatistic] using hstat_x_lt)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        rcases hZQ r_old_x with ⟨mx, hmx⟩
        have hx_eq_or_gt :
            mu F r_old_x = iterate_op d (K - 1) ∨ iterate_op d (K - 1) < mu F r_old_x := by
          rcases lt_trichotomy (mu F r_old_x) (iterate_op d (K - 1)) with hlt | heq | hgt
          · exact False.elim (h_not_lt_Km1 hlt)
          · exact Or.inl heq
          · exact Or.inr hgt
        have hμx_eq : mu F r_old_x = iterate_op d (K - 1) := by
          rcases hx_eq_or_gt with hEq | hGt
          · exact hEq
          · have hxC : r_old_x ∈ extensionSetC F d (K - 1) := by
              simpa [extensionSetC] using hGt
            have hstat_x_gt : δ < separationStatistic R r_old_x (K - 1) hKm1_pos :=
              hδ_lt_C r_old_x (K - 1) hKm1_pos hxC
            have hKm1_pos_real : (0 : ℝ) < ((K - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hKm1_pos
            have hθx_gt : ((K - 1 : ℕ) : ℝ) * δ <
                R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
              have := (lt_div_iff₀ hKm1_pos_real).1 (by simpa [separationStatistic] using hstat_x_gt)
              simpa [mul_comm, mul_left_comm, mul_assoc] using this
            have h_between :
                ((K - 1 : ℕ) : ℝ) * δ < (mx : ℝ) * δ ∧ (mx : ℝ) * δ < (K : ℝ) * δ := by
              constructor
              · simpa [hmx] using hθx_gt
              · simpa [hmx] using hθx_lt
            have h_between' : ((K - 1 : ℕ) : ℝ) < (mx : ℝ) ∧ (mx : ℝ) < (K : ℝ) := by
              constructor
              · exact (mul_lt_mul_iff_left₀ hδ_pos).1 h_between.1
              · exact (mul_lt_mul_iff_left₀ hδ_pos).1 h_between.2
            have h_lt : (mx : ℤ) < (K : ℤ) := by
              have : (mx : ℝ) < (K : ℤ) := by simpa [Int.cast_natCast] using h_between'.2
              exact Int.cast_lt.mp this
            have h_gt : ((K - 1 : ℕ) : ℤ) < mx := by
              have : (((K - 1 : ℕ) : ℤ) : ℝ) < (mx : ℝ) := by
                simpa [Int.cast_natCast] using h_between'.1
              exact Int.cast_lt.mp this
            omega
        have hxB : r_old_x ∈ extensionSetB F d (K - 1) := by
          simpa [extensionSetB, Set.mem_setOf_eq, hμx_eq]
        have hstat_x_eq : separationStatistic R r_old_x (K - 1) hKm1_pos = δ := by
          simpa [δ] using chooseδ_B_bound hk R IH d hd r_old_x (K - 1) hKm1_pos hxB
        have hθx_eq :
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ = ((K - 1 : ℕ) : ℝ) * δ := by
          have hKm1_ne : ((K - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hKm1_pos
          have := (div_eq_iff hKm1_ne).1 (by simpa [separationStatistic] using hstat_x_eq)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have hyC : r_old_y ∈ extensionSetC F d (K - 1 + Δ) := by
          have : iterate_op d (K - 1 + Δ) < mu F r_old_y := by
            calc
              iterate_op d (K - 1 + Δ) = op (iterate_op d (K - 1)) (iterate_op d Δ) := by
                simpa using (iterate_op_add d (K - 1) Δ).symm
              _ = op (mu F r_old_x) (iterate_op d Δ) := by rw [hμx_eq]
              _ < mu F r_old_y := h_lt
          simpa [extensionSetC] using this
        have hy_level_pos : 0 < (K - 1 + Δ) := Nat.add_pos_left hKm1_pos Δ
        have hstat_y_gt : δ < separationStatistic R r_old_y (K - 1 + Δ) hy_level_pos :=
          hδ_lt_C r_old_y (K - 1 + Δ) hy_level_pos hyC
        have hy_pos_real : (0 : ℝ) < ((K - 1 + Δ : ℕ) : ℝ) := Nat.cast_pos.mpr hy_level_pos
        have hθy_gt :
            ((K - 1 + Δ : ℕ) : ℝ) * δ <
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
          have := (lt_div_iff₀ hy_pos_real).1 (by simpa [separationStatistic] using hstat_y_gt)
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        have : (Δ : ℝ) * δ <
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
                R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
          have h_expand :
              ((K - 1 + Δ : ℕ) : ℝ) * δ = ((K - 1 : ℕ) : ℝ) * δ + (Δ : ℝ) * δ := by
            simp [Nat.cast_add, add_mul]
          have : ((K - 1 : ℕ) : ℝ) * δ + (Δ : ℝ) * δ <
                R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
            linarith [hθy_gt, h_expand]
          linarith [this, hθx_eq]
        simpa [δ] using this
    · -- Global B = ∅: TODO(K&S Appendix A): use delta_cut_tight + Z-quantization.
      have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u := by
        intro r u hu hrB
        exact hB_global ⟨r, u, hu, hrB⟩
      have hB_base' : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r_old_x Δ := by
        simpa [extensionSetB_base] using hB_base
      have hstat :
          δ < separationStatistic_base R r_old_x r_old_y Δ hΔ :=
        by
          simpa [δ] using hStrict.C hB_empty r_old_x r_old_y Δ hΔ h_mu h_lt hB_base'
      have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
      have : (Δ : ℝ) * δ <
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
        -- `δ < (gap)/Δ`  ⇒  δ*Δ < gap  ⇒  Δ*δ < gap
        have h' :
            δ * (Δ : ℝ) <
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
                R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
          exact (lt_div_iff₀ hΔ_pos_real).1 (by simpa [separationStatistic_base] using hstat)
        simpa [mul_comm, mul_left_comm, mul_assoc] using h'
      simpa [δ] using this
      /-

      -- As in the A-side lemma: reduce to a non-strict inequality from crossing indices, then
      -- rule out equality using the K&S A.3.4 “irrational δ” argument (`delta_cut_tight`).

      -- Define the least iterate bounds for μx and μy.
      let Px : ℕ → Prop := fun n => mu F r_old_x < iterate_op d n
      have hPx_ex : ∃ n : ℕ, Px n := bounded_by_iterate d hd (mu F r_old_x)
      let Kx : ℕ := Nat.find hPx_ex
      have hKx : mu F r_old_x < iterate_op d Kx := Nat.find_spec hPx_ex
      have hKx_pos : 0 < Kx := by
        by_contra h
        have hKx0 : Kx = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
        rw [hKx0, iterate_op_zero] at hKx
        exact not_lt.mpr (ident_le (mu F r_old_x)) hKx

      let Py : ℕ → Prop := fun n => mu F r_old_y < iterate_op d n
      have hPy_ex : ∃ n : ℕ, Py n := bounded_by_iterate d hd (mu F r_old_y)
      let Ky : ℕ := Nat.find hPy_ex
      have hKy : mu F r_old_y < iterate_op d Ky := Nat.find_spec hPy_ex
      have hKy_pos : 0 < Ky := by
        by_contra h
        have hKy0 : Ky = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
        rw [hKy0, iterate_op_zero] at hKy
        exact not_lt.mpr (ident_le (mu F r_old_y)) hKy

      -- θx = (Kx-1)·δ and θy = (Ky-1)·δ (B-empty crossing characterization).
      have hθx_eq :
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ = ((Kx - 1 : ℕ) : ℝ) * δ := by
        simpa [δ, Px, Kx, hPx_ex] using
          (theta_eq_min_iterate_bound_of_B_empty hk R IH H d hd (hZQ := by simpa [δ] using hZQ) hB_empty r_old_x)
      have hθy_eq :
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ = ((Ky - 1 : ℕ) : ℝ) * δ := by
        simpa [δ, Py, Ky, hPy_ex] using
          (theta_eq_min_iterate_bound_of_B_empty hk R IH H d hd (hZQ := by simpa [δ] using hZQ) hB_empty r_old_y)

      -- Show `d^(Kx-1+Δ) < μy` by pushing `d^(Kx-1)` through monotonicity of `op _ (d^Δ)`.
      -- We only need `d^(Kx-1) ≤ μx`, which follows from minimality of `Kx`.
      have h_dKx_m1_le_μx : iterate_op d (Kx - 1) ≤ mu F r_old_x := by
        have h_not_lt : ¬ mu F r_old_x < iterate_op d (Kx - 1) := by
          intro hlt
          have hle : Kx ≤ Kx - 1 := by
            have : Nat.find hPx_ex ≤ Kx - 1 := Nat.find_min' hPx_ex (by simpa [Px] using hlt)
            simpa [Kx] using this
          have hlt' : Kx - 1 < Kx := Nat.sub_lt hKx_pos Nat.one_pos
          exact (lt_irrefl Kx) (lt_of_le_of_lt hle hlt')
        exact le_of_not_gt h_not_lt

      have h_dKx_m1Δ_lt_μy : iterate_op d (Kx - 1 + Δ) < mu F r_old_y := by
        -- d^(Kx-1+Δ) = d^(Kx-1) ⊕ d^Δ ≤ μx ⊕ d^Δ < μy
        have h1 :
            op (iterate_op d (Kx - 1)) (iterate_op d Δ) ≤ op (mu F r_old_x) (iterate_op d Δ) :=
          (op_strictMono_left (iterate_op d Δ)).monotone h_dKx_m1_le_μx
        have h2 : op (iterate_op d (Kx - 1)) (iterate_op d Δ) = iterate_op d (Kx - 1 + Δ) := by
          simpa using (iterate_op_add d (Kx - 1) Δ)
        have : op (iterate_op d (Kx - 1)) (iterate_op d Δ) < mu F r_old_y := lt_of_le_of_lt h1 h_lt
        simpa [h2] using this

      -- From `d^(Kx-1+Δ) < μy`, deduce `Ky ≥ Kx+Δ`.
      have hKy_ge : Kx + Δ ≤ Ky := by
        have h_not_lt : ¬ mu F r_old_y < iterate_op d (Kx - 1 + Δ) := not_lt_of_ge (le_of_lt h_dKx_m1Δ_lt_μy)
        -- If Ky ≤ (Kx-1+Δ), then μy < d^Ky ≤ d^(Kx-1+Δ), contradiction.
        have : Kx - 1 + Δ < Ky := by
          by_contra hle
          have hKy_le : Ky ≤ Kx - 1 + Δ := le_of_not_gt hle
          have hmono : Monotone (iterate_op d) := (iterate_op_strictMono d hd).monotone
          have hKy_le_iter : iterate_op d Ky ≤ iterate_op d (Kx - 1 + Δ) := hmono hKy_le
          have : mu F r_old_y < iterate_op d (Kx - 1 + Δ) := lt_of_lt_of_le hKy hKy_le_iter
          exact h_not_lt this
        -- turn (Kx-1+Δ) < Ky into Kx+Δ ≤ Ky
        have h_succ : (Kx - 1 + Δ) + 1 ≤ Ky := Nat.succ_le_iff.mpr this
        -- Rewrite the LHS as `Kx + Δ` using `Kx - 1 + 1 = Kx` (since `0 < Kx`).
        have hKx_sub_add : Kx - 1 + 1 = Kx := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hKx_pos)
        have hLHS : (Kx - 1 + Δ) + 1 = Kx + Δ := by
          calc
            (Kx - 1 + Δ) + 1 = (Kx - 1) + (Δ + 1) := by simp [Nat.add_assoc]
            _ = (Kx - 1) + (1 + Δ) := by simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = (Kx - 1 + 1) + Δ := by simp [Nat.add_assoc]
            _ = Kx + Δ := by simp [hKx_sub_add, Nat.add_assoc]
        simpa [hLHS] using h_succ

      have hδ_pos : 0 < δ := delta_pos hk R IH H d hd
      have h_non_strict :
          (Δ : ℝ) * δ ≤
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
        -- Use hKy_ge to get (Kx+Δ-1) ≤ (Ky-1), then compare lattice values.
        have h_le_nat : Kx + Δ - 1 ≤ Ky - 1 := Nat.sub_le_sub_right hKy_ge 1
        have hmul_le :
            ((Kx + Δ - 1 : ℕ) : ℝ) * δ ≤ ((Ky - 1 : ℕ) : ℝ) * δ := by
          have : ((Kx + Δ - 1 : ℕ) : ℝ) ≤ ((Ky - 1 : ℕ) : ℝ) := by exact_mod_cast h_le_nat
          exact mul_le_mul_of_nonneg_right this (le_of_lt hδ_pos)
        have h_expand :
            ((Kx + Δ - 1 : ℕ) : ℝ) * δ = ((Kx - 1 : ℕ) : ℝ) * δ + (Δ : ℝ) * δ := by
          have hKx_ge1 : 1 ≤ Kx := Nat.succ_le_iff.mpr hKx_pos
          have : Kx + Δ - 1 = (Kx - 1) + Δ := by
            calc
              Kx + Δ - 1 = Δ + Kx - 1 := by omega
              _ = Δ + (Kx - 1) := by
                    simpa using (Nat.add_sub_assoc hKx_ge1 Δ)
              _ = (Kx - 1) + Δ := by omega
          simp [this, Nat.cast_add, add_mul]
        -- Finish by rewriting θy and θx.
        have hθy_ge : ((Kx + Δ - 1 : ℕ) : ℝ) * δ ≤ R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
          simpa [hθy_eq] using hmul_le
        have hθx' : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ = ((Kx - 1 : ℕ) : ℝ) * δ := hθx_eq
        linarith [hθy_ge, hθx', h_expand]

      have h_not_eq :
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ ≠ (Δ : ℝ) * δ := by
        simpa [δ] using
          (theta_gap_gt_of_op_lt_mu_B_empty_no_eq (hk := hk) (R := R) (IH := IH) (H := H)
            (d := d) (hd := hd) (hZQ := by simpa [δ] using hZQ) (hB_empty := hB_empty)
            (r_old_x := r_old_x) (r_old_y := r_old_y) (Δ := Δ) (hΔ := hΔ) (h_mu := h_mu)
            (h_lt := h_lt))

      -- Conclude strictness.
      exact lt_of_le_of_ne h_non_strict h_not_eq.symm
      -/

/-- Relative Θ-gap upper bound (A-side), derived from `ChooseδBaseAdmissible`.

If `mu F r_old_x < mu F r_old_y ⊕ d^Δ`, then the Θ-gap is strictly less than `Δ * δ`, where
`δ := chooseδ hk R d hd`. -/
lemma theta_gap_lt_of_mu_lt_op_of_chooseδBaseAdmissible
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hBase : ChooseδBaseAdmissible (α := α) hk R d hd)
    (r_old_x r_old_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ)
    (h_lt : mu F r_old_x < op (mu F r_old_y) (iterate_op d Δ)) :
    R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩
      < (Δ : ℝ) * chooseδ hk R d hd := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  have hA_base : r_old_x ∈ extensionSetA_base F d r_old_y Δ := by
    simpa [extensionSetA_base, Set.mem_setOf_eq] using h_lt
  have hstat :
      separationStatistic_base R r_old_y r_old_x Δ hΔ < δ :=
    (hBase.base r_old_y Δ hΔ).1 r_old_x hA_base
  have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
  have h' :
      R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < δ * (Δ : ℝ) := by
    exact
      (div_lt_iff₀ hΔ_pos_real).1 (by simpa [separationStatistic_base, δ] using hstat)
  have :
      R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ := by
    simpa [mul_comm] using h'
  simpa [δ] using this

/-- Relative Θ-gap lower bound (C-side), derived from `ChooseδBaseAdmissible`.

If `(mu F r_old_x) ⊕ d^Δ < mu F r_old_y`, then the Θ-gap is strictly greater than `Δ * δ`, where
`δ := chooseδ hk R d hd`. -/
lemma theta_gap_gt_of_op_lt_mu_of_chooseδBaseAdmissible
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hBase : ChooseδBaseAdmissible (α := α) hk R d hd)
    (r_old_x r_old_y : Multi k) (Δ : ℕ) (hΔ : 0 < Δ)
    (h_lt : op (mu F r_old_x) (iterate_op d Δ) < mu F r_old_y) :
    (Δ : ℝ) * chooseδ hk R d hd <
      R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
        R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  have hC_base : r_old_y ∈ extensionSetC_base F d r_old_x Δ := by
    simpa [extensionSetC_base, Set.mem_setOf_eq] using h_lt
  have hstat :
      δ < separationStatistic_base R r_old_x r_old_y Δ hΔ :=
    (hBase.base r_old_x Δ hΔ).2 r_old_y hC_base
  have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
  have h' :
      δ * (Δ : ℝ) <
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
    exact
      (lt_div_iff₀ hΔ_pos_real).1 (by simpa [separationStatistic_base, δ] using hstat)
  have :
      (Δ : ℝ) * δ <
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
    simpa [mul_comm] using h'
  simpa [δ] using this

theorem extend_grid_rep_with_atom
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hBase : ChooseδBaseAdmissible (α := α) hk R d hd) :
      ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        -- KEY EXTENSION PROPERTY: R' extends R via the Theta'_raw formula
        (∀ r_old : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
          R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * chooseδ hk R d hd) := by
  -- Layer A: Define extended family F'
  let F' := extendAtomFamily F d hd

  refine ⟨F', ?_, ?_, ?_⟩

  -- Prove F' preserves old atoms
  · intro i
    exact extendAtomFamily_old F d hd i

  -- Prove F' has new atom at position k
  · exact extendAtomFamily_new F d hd

  -- Prove ∃ R' : MultiGridRep F', True (Layer B: Construct R')
  · -- Layer B: Construct R' (representation on extended grid)
    let δ := chooseδ hk R d hd

    -- Define Θ' on the extended grid
    -- For μ(F', r') where r' : Multi (k+1), we split as (r_old, t) and compute:
    --   Θ'(μ(F', r_old, t)) = Θ(μ(F, r_old)) + t * δ
    let Θ' : {x // x ∈ kGrid F'} → ℝ := fun ⟨x, hx⟩ =>
      -- Extract witness r' : Multi (k+1) with μ(F', r') = x
      let r' := Classical.choose hx
      let hr' := Classical.choose_spec hx
      -- Split r' into (r_old, t)
      let (r_old, t) := splitMulti r'
      -- Compute Θ'(x) = Θ(μ(F, r_old)) + t * δ
      R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + t * δ

    -- Construct R' : MultiGridRep F'
    -- We'll prove the four required properties step by step

    -- Helper: show that ident has witness (fun _ => 0)
    have h_ident_witness : mu F' (fun _ => 0) = ident := mu_zero (F := F')

    -- Property 4: Normalization - Θ'(ident) = 0
    have h_norm : Θ' ⟨ident, ident_mem_kGrid F'⟩ = 0 := by
      -- First reduce Θ' application with simp/dsimp
      simp only [Θ']
      -- Goal is now the raw computation with let bindings

      -- Name the key expressions for clarity
      set r' := Classical.choose (ident_mem_kGrid F') with hr'_def
      have hr' : ident = mu F' r' := Classical.choose_spec (ident_mem_kGrid F')
      set r_old := (splitMulti r').1 with hr_old_def
      set t := (splitMulti r').2 with ht_def

      -- Key: use joinMulti_splitMulti to show r' = joinMulti r_old t
      have hr'_eq : r' = joinMulti r_old t := by
        have h := joinMulti_splitMulti r'
        -- h : (let (r_old, t) := splitMulti r'; joinMulti r_old t) = r'
        -- Definitionally, this is joinMulti (splitMulti r').1 (splitMulti r').2 = r'
        -- Which equals joinMulti r_old t = r' by our definitions
        exact h.symm

      -- Now use mu_extend_last
      have h_mu_extend : mu F' r' = op (mu F r_old) (iterate_op d t) := by
        rw [hr'_eq]
        exact mu_extend_last F d hd r_old t

      -- Combine with hr' : ident = mu F' r'
      have h_ident_eq : ident = op (mu F r_old) (iterate_op d t) := by
        rw [← h_mu_extend]
        exact hr'

      -- Show t must be 0
      have ht_zero : t = 0 := by
        by_contra h_ne
        have ht_pos : 0 < t := Nat.pos_of_ne_zero h_ne

        -- If t > 0, then iterate_op d t > ident (since d > ident)
        have hdt_pos : ident < iterate_op d t := iterate_op_pos d hd t ht_pos

        -- By positivity: op (mu F r_old) (iterate_op d t) > ident
        have h_mu_gt : ident < op (mu F r_old) (iterate_op d t) := by
          have h_mu_ge : ident ≤ mu F r_old := ident_le _
          by_cases h_mu_eq : mu F r_old = ident
          · rw [h_mu_eq, op_ident_left]
            exact hdt_pos
          · have h_mu_gt : ident < mu F r_old := lt_of_le_of_ne h_mu_ge (Ne.symm h_mu_eq)
            calc ident
              _ < iterate_op d t := hdt_pos
              _ = op ident (iterate_op d t) := (op_ident_left _).symm
              _ < op (mu F r_old) (iterate_op d t) := by
                  have hmono : StrictMono (fun x => op x (iterate_op d t)) := op_strictMono_left _
                  exact hmono h_mu_gt

        -- This contradicts h_ident_eq : ident = op (mu F r_old) (iterate_op d t)
        rw [← h_ident_eq] at h_mu_gt
        exact lt_irrefl ident h_mu_gt

      -- Show mu F r_old = ident
      have hr_old_ident : mu F r_old = ident := by
        rw [ht_zero, iterate_op_zero, op_ident_right] at h_ident_eq
        exact h_ident_eq.symm

      -- Now the goal has the let-bound form. Use convert to handle the definitional equality.
      -- Goal: R.Θ_grid ⟨mu F (splitMulti (Classical.choose _)).1, _⟩ +
      --       (splitMulti (Classical.choose _)).2 * δ = 0
      -- These are definitionally equal to r_old and t respectively
      have h_final : R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ = 0 := by
        rw [ht_zero, Nat.cast_zero, zero_mul, add_zero]
        have h_subtype_eq :
            (⟨mu F r_old, mu_mem_kGrid F r_old⟩ : {x // x ∈ kGrid F}) =
              ⟨ident, ident_mem_kGrid F⟩ := by
          ext
          exact hr_old_ident
        rw [h_subtype_eq]
        exact R.ident_eq_zero
      -- r_old and t are definitionally equal to the expressions in the goal
      exact h_final

    /- ### Helper Lemmas for Θ' Strict Monotonicity

    The following lemmas break down the strict monotonicity proof into manageable pieces,
    following GPT-5.1 Pro's recommendation (§5.1). -/

    -- δ bounds used throughout the Θ' helper lemmas
    have hδA := chooseδ_A_bound hk R IH H d hd
    have hδC := chooseδ_C_bound hk R IH H d hd
    have hδB := chooseδ_B_bound hk R IH d hd

    -- Helper 1: Θ' formula in terms of splitMulti components (definitional unfolding)
    have Theta'_split :
        ∀ (x : {x // x ∈ kGrid F'}),
          Θ' x =
            (let r := Classical.choose x.property
             let r_old := (splitMulti r).1
             let t := (splitMulti r).2
             R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ) := by
      intro _
      rfl  -- Θ' is defined this way

    -- Helper 1b: canonical evaluation on joinMulti witnesses
    have Theta'_on_join :
        ∀ (r_old : Multi k) (t : ℕ),
          Θ' ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
            Theta'_raw R d δ r_old t := by
      intro r_old t
      classical
      set r' := Classical.choose (mu_mem_kGrid F' (joinMulti r_old t)) with hr'_def
      have hr'_spec : mu F' r' = mu F' (joinMulti r_old t) :=
        (Classical.choose_spec (mu_mem_kGrid F' (joinMulti r_old t))).symm
      have hWD :=
        Theta'_well_defined R H IH d hd δ (by simpa [δ] using delta_pos hk R IH H d hd) hδA hδC hδB
          hr'_spec
      -- Θ' is defined via the Classical.choose witness; hWD lets us replace it by the canonical joinMulti
      simp [Θ', Theta'_raw, hr'_def, splitMulti_joinMulti] at hWD ⊢
      -- hWD already states the chosen witness coincides with the canonical one
      -- after unfolding Theta'_raw
      exact hWD

    -- Helper 2: Incrementing t by 1 increases Θ' by exactly δ (when old part is fixed)
    have Theta'_increment_t : ∀ (r_old : Multi k) (t : ℕ),
        Θ' ⟨mu F' (joinMulti r_old (t+1)), mu_mem_kGrid F' (joinMulti r_old (t+1))⟩ =
        Θ' ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ + δ := by
      intro r_old t
      -- Expand both sides to the raw form and simplify algebraically
      simp [Theta'_on_join, Theta'_raw, Nat.cast_add, mul_add, add_comm, add_left_comm, add_assoc]
      ring

    -- Helper 2b: Generalize to shifting by arbitrary Δ steps
    have Theta'_shift_by : ∀ (r_old : Multi k) (t Δ : ℕ),
        Θ' ⟨mu F' (joinMulti r_old (t + Δ)), mu_mem_kGrid F' (joinMulti r_old (t + Δ))⟩ =
        Θ' ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ + (Δ : ℝ) * δ := by
      intro r_old t Δ
      induction Δ with
      | zero =>
        simp only [Nat.add_zero, Nat.cast_zero, zero_mul, add_zero]
      | succ Δ ih =>
        calc Θ' ⟨mu F' (joinMulti r_old (t + (Δ + 1))), _⟩
            = Θ' ⟨mu F' (joinMulti r_old ((t + Δ) + 1)), _⟩ := by
                rfl
          _ = Θ' ⟨mu F' (joinMulti r_old (t + Δ)), _⟩ + δ :=
                Theta'_increment_t r_old (t + Δ)
          _ = (Θ' ⟨mu F' (joinMulti r_old t), _⟩ + (Δ : ℝ) * δ) + δ := by rw [ih]
          _ = Θ' ⟨mu F' (joinMulti r_old t), _⟩ + ((Δ + 1 : ℕ) : ℝ) * δ := by
                simp only [Nat.cast_add, Nat.cast_one]; ring

    -- Helper 3: δ is strictly positive
    have delta_pos : 0 < δ := by
      -- Unfold δ to expose chooseδ structure
      show 0 < chooseδ hk R d hd
      unfold chooseδ
      -- Case split based on how δ was chosen
      split_ifs with hB
      · -- Case B ≠ ∅: δ = B_common_statistic
        -- Extract a concrete B-witness without destroying hB
        have ⟨r, u, hu, hr⟩ := hB

        -- B_common_statistic equals any B-witness's statistic
        have hstat_eq : B_common_statistic R d hd hB = separationStatistic R r u hu :=
          B_common_statistic_eq_any_witness R IH d hd hB r u hu hr

        rw [hstat_eq]
        -- Now show separationStatistic R r u hu > 0
        unfold separationStatistic

        -- From hr: r ∈ extensionSetB F d u means mu F r = d^u
        simp only [extensionSetB, Set.mem_setOf_eq] at hr
        have hmu_eq : mu F r = iterate_op d u := hr

        -- d^u > ident (since d > ident and u > 0)
        have hdu_pos : ident < iterate_op d u := iterate_op_pos d hd u hu

        -- Θ(mu F r) = Θ(d^u) > 0
        have h_theta_pos : 0 < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
          have h_ident_zero : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ = 0 := R.ident_eq_zero
          have h_mu_pos : ident < mu F r := by rw [hmu_eq]; exact hdu_pos
          have : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ < R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ :=
            R.strictMono h_mu_pos
          rw [h_ident_zero] at this
          exact this

        -- θ / u > 0 when θ > 0 and u > 0
        exact div_pos h_theta_pos (Nat.cast_pos.mpr hu)
      · -- Case B = ∅: δ = B_empty_delta
        -- Need to show B_empty_delta > 0
        -- Strategy: Find an A-witness with positive statistic, then use le_csSup
        -- The A-witness (fun _ => 0, 1) has statistic 0, so we need a different one

        -- Since k ≥ 1, there exists an atom a₀ in F
        have hk_pos : 0 < k := hk
        let i₀ : Fin k := ⟨0, hk_pos⟩
        let a₀ := F.atoms i₀
        have ha₀_pos : ident < a₀ := F.pos i₀

        -- By Archimedean, ∃ N such that a₀ < d^N
        obtain ⟨N, hN⟩ := bounded_by_iterate d hd a₀

        -- Then unitMulti i₀ 1 (i.e., a₀) is in A(N)
        have ha₀_in_A : unitMulti i₀ 1 ∈ extensionSetA F d N := by
          simp only [extensionSetA, Set.mem_setOf_eq]
          have : mu F (unitMulti i₀ 1) = iterate_op a₀ 1 := mu_unitMulti F i₀ 1
          rw [this, iterate_op_one]
          exact hN

        -- The statistic for this witness is positive
        have hN_pos : 0 < N := by
          -- Since a₀ > ident and d > ident, d^1 = d ≥ ident
          -- a₀ < d^N with N = 0 would mean a₀ < ident, contradiction
          by_contra h_not_pos
          push_neg at h_not_pos
          interval_cases N
          -- N = 0: a₀ < d^0 = ident, contradicts a₀ > ident
          simp only [iterate_op_zero] at hN
          exact absurd hN (not_lt.mpr (le_of_lt ha₀_pos))

        have h_theta_a₀_pos : 0 < R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ := by
          have h_ident_zero : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ = 0 := R.ident_eq_zero
          have h_mu_pos : ident < mu F (unitMulti i₀ 1) := by
            have : mu F (unitMulti i₀ 1) = iterate_op a₀ 1 := mu_unitMulti F i₀ 1
            rw [this, iterate_op_one]
            exact ha₀_pos
          have : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
                 R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ :=
            R.strictMono h_mu_pos
          rw [h_ident_zero] at this
          exact this

        have h_stat_pos : 0 < R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ / N :=
          div_pos h_theta_a₀_pos (Nat.cast_pos.mpr hN_pos)

        -- B_empty_delta is the sSup of A-statistics
        -- Our statistic h_stat_pos is in this set, so sSup ≥ h_stat_pos > 0
        unfold B_empty_delta
        -- Need: sSup {s | ∃ r u, ...} > 0
        -- Use: 0 < h_stat_pos ≤ sSup (since h_stat_pos is in the set)

        -- Define the set being supremumed
        let AStats := {s : ℝ | ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u ∧
                                s = R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u}

        have h_in_set : R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ / N ∈ AStats := by
          use unitMulti i₀ 1, N, hN_pos, ha₀_in_A

        -- The set is bounded above (using a C-witness)
        have hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u :=
          fun r u hu hr => hB ⟨r, u, hu, hr⟩
        have hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
          extensionSetC_nonempty_of_B_empty F hk d hd hB_empty

        have h_bdd : BddAbove AStats := by
          rcases hC_nonempty with ⟨rC, uC, huC, hrC⟩
          let σC := separationStatistic R rC uC huC
          use σC
          intro s ⟨r', u', hu', hrA', hs⟩
          subst hs
          exact le_of_lt (separation_property R H IH hd hu' hrA' huC hrC)

        -- Apply le_csSup to get sSup ≥ our positive statistic
        have h_ge : R.Θ_grid ⟨mu F (unitMulti i₀ 1), mu_mem_kGrid F _⟩ / N ≤ sSup AStats :=
          le_csSup h_bdd h_in_set

        linarith

    -- Helper 3b: Generalized vertical shift by Δ steps (GPT-5 Pro Step 2 extension)
    have Theta'_shift_by : ∀ (r_old : Multi k) (t Δ : ℕ),
        Θ' ⟨mu F' (joinMulti r_old (t + Δ)), mu_mem_kGrid F' (joinMulti r_old (t + Δ))⟩ =
        Θ' ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ + (Δ : ℝ) * δ := by
      intro r_old t Δ
      induction Δ with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, add_zero]
      | succ Δ ih =>
        -- Goal: Θ'(...t + (Δ+1)...) = Θ'(...t...) + ((Δ+1) : ℝ) * δ
        have h_add_assoc : t + (Δ + 1) = (t + Δ) + 1 := by omega
        calc Θ' ⟨mu F' (joinMulti r_old (t + (Δ + 1))), _⟩
            = Θ' ⟨mu F' (joinMulti r_old ((t + Δ) + 1)), _⟩ := by
                rw [← h_add_assoc]
          _ = Θ' ⟨mu F' (joinMulti r_old (t + Δ)), _⟩ + δ :=
                Theta'_increment_t r_old (t + Δ)
          _ = Θ' ⟨mu F' (joinMulti r_old t), _⟩ + (Δ : ℝ) * δ + δ := by
                rw [ih]
          _ = Θ' ⟨mu F' (joinMulti r_old t), _⟩ + ((Δ : ℝ) + 1) * δ := by
                ring
          _ = Θ' ⟨mu F' (joinMulti r_old t), _⟩ + ((Δ + 1 : ℕ) : ℝ) * δ := by
                simp only [Nat.cast_add, Nat.cast_one]

    -- Helper 4: Strict monotonicity when t-components are equal
    have Theta'_strictMono_same_t : ∀ (r_old_x r_old_y : Multi k) (t : ℕ),
        mu F r_old_x < mu F r_old_y →
        Θ' ⟨mu F' (joinMulti r_old_x t), mu_mem_kGrid F' (joinMulti r_old_x t)⟩ <
        Θ' ⟨mu F' (joinMulti r_old_y t), mu_mem_kGrid F' (joinMulti r_old_y t)⟩ := by
      intro r_old_x r_old_y t h_mu
      have hθ_lt : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                   R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
        R.strictMono h_mu
      have hθ_lt' := add_lt_add_right hθ_lt ((t : ℝ) * δ)
      -- rewrite both sides using the canonical Θ' evaluation
      simpa [Theta'_on_join, Theta'_raw] using hθ_lt'

    -- Property 2: Strict monotonicity
    --
    -- PROOF STRATEGY (K&S Appendix A):
    -- Given x < y where x, y ∈ kGrid F':
    -- 1. Extract witnesses: x = mu F' r_x and y = mu F' r_y
    -- 2. Split: r_x = (r_old_x, t_x) and r_y = (r_old_y, t_y)
    -- 3. By mu_extend_last: x = mu F r_old_x ⊕ d^{t_x}, y = mu F r_old_y ⊕ d^{t_y}
    -- 4. Key case analysis using helper lemmas above:
    --    (a) If t_x < t_y: Use Theta'_increment_t + delta_pos
    --    (b) If t_x = t_y: Use Theta'_strictMono_same_t
    --    (c) If t_x > t_y: Derive contradiction from δ separation properties
    -- 5. The δ choice (from chooseδ using separation A/B/C sets) ensures all cases work
    --
    -- This requires showing δ is in the "gap" between A-statistics and C-statistics.
    -- The accuracy_lemma shows the gap can be made arbitrarily small but non-zero.
    have h_strictMono : StrictMono Θ' := by
      classical
      -- K&S Appendix A strategy:
      -- Reduce `x < y` in the (k+1)-grid to inequalities between the old parts and a d-shift,
      -- then compare the corresponding `Θ_grid` values with the Δ·δ shift.
      --
      -- The remaining hard sublemmas are the *relative* A/C bounds:
      --   `mu F r < (mu F s) ⊕ d^Δ`  →  Θ(r) - Θ(s) < Δ·δ
      --   `(mu F r) ⊕ d^Δ < mu F s`  →  Δ·δ < Θ(s) - Θ(r)
      --
      -- These are the missing “mixed-t compensation” steps in the archived attempt.

      intro ⟨x, hx⟩ ⟨y, hy⟩ hxy

      -- Extract witnesses and split components.
      set r_x := Classical.choose hx with hr_x_def
      set r_y := Classical.choose hy with hr_y_def
      have hμ_x : mu F' r_x = x := (Classical.choose_spec hx).symm
      have hμ_y : mu F' r_y = y := (Classical.choose_spec hy).symm

      set r_old_x : Multi k := (splitMulti r_x).1
      set t_x : ℕ := (splitMulti r_x).2
      set r_old_y : Multi k := (splitMulti r_y).1
      set t_y : ℕ := (splitMulti r_y).2

      have h_rx_join : r_x = joinMulti r_old_x t_x := (joinMulti_splitMulti r_x).symm
      have h_ry_join : r_y = joinMulti r_old_y t_y := (joinMulti_splitMulti r_y).symm

      have hx_eq : x = op (mu F r_old_x) (iterate_op d t_x) := by
        rw [← hμ_x, h_rx_join]
        exact mu_extend_last F d hd r_old_x t_x
      have hy_eq : y = op (mu F r_old_y) (iterate_op d t_y) := by
        rw [← hμ_y, h_ry_join]
        exact mu_extend_last F d hd r_old_y t_y

      -- Unfold Θ' at the chosen witnesses.
      -- After the `set`s above, `simp [Θ']` reduces to the raw `Θ_grid + t·δ` form.
      simp only [Θ', hr_x_def.symm, hr_y_def.symm, r_old_x, t_x, r_old_y, t_y]

      -- Compare t-components.
      rcases lt_trichotomy t_x t_y with h_t_lt | h_t_eq | h_t_gt

      · -- Case t_x < t_y
        have ht_mul : (t_x : ℝ) * δ < (t_y : ℝ) * δ :=
          mul_lt_mul_of_pos_right (Nat.cast_lt.mpr h_t_lt) delta_pos
        rcases lt_trichotomy (mu F r_old_x) (mu F r_old_y) with hμ_lt | hμ_eq | hμ_gt
        · -- old part already favors RHS
          have hθ_lt :
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ :=
            R.strictMono hμ_lt
          calc
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (t_x : ℝ) * δ
                < R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_x : ℝ) * δ :=
              by simpa using add_lt_add_right hθ_lt ((t_x : ℝ) * δ)
            _ < R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_y : ℝ) * δ := by
              simpa using
                add_lt_add_left ht_mul (R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩)
        · -- old parts equal: t-term decides
          have hθ_eq :
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ =
                R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
            have hsub :
                (⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ : {x // x ∈ kGrid F}) =
                  ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
              ext
              exact hμ_eq
            simpa using congrArg R.Θ_grid hsub
          -- Reduce to the strict t-inequality.
          calc
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (t_x : ℝ) * δ
                = R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_x : ℝ) * δ := by
                    simpa [hθ_eq]
            _ < R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_y : ℝ) * δ :=
                    add_lt_add_left ht_mul (R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩)
        · -- mixed case: old part favors LHS, but t-term favors RHS; use relative A-bound.
          have hΔ_pos : 0 < (t_y - t_x) := Nat.sub_pos_of_lt h_t_lt
          set Δ : ℕ := t_y - t_x
          have hΔ_eq : t_y = t_x + Δ := (Nat.add_sub_cancel' (le_of_lt h_t_lt)).symm
          -- From x<y, cancel the common `d^{t_x}` factor to get μ-gap bound.
          have h_gap_bound : mu F r_old_x < op (mu F r_old_y) (iterate_op d Δ) := by
            have h1 : op (mu F r_old_x) (iterate_op d t_x) <
                op (mu F r_old_y) (iterate_op d t_y) := by
              -- rewrite back to x<y
              simpa [hx_eq, hy_eq] using hxy
            -- Rewrite `d^{t_y}` as `d^Δ ⊕ d^{t_x}` and cancel `d^{t_x}` using monotone reflection.
            have ht_split : iterate_op d t_y = op (iterate_op d Δ) (iterate_op d t_x) := by
              have : t_y = Δ + t_x := by omega
              simpa [this] using (iterate_op_add d Δ t_x).symm
            have h1' :
                op (mu F r_old_x) (iterate_op d t_x) <
                  op (op (mu F r_old_y) (iterate_op d Δ)) (iterate_op d t_x) := by
              simpa [ht_split, op_assoc] using h1
            have hmono : Monotone (fun z : α => op z (iterate_op d t_x)) :=
              (op_strictMono_left (iterate_op d t_x)).monotone
            exact hmono.reflect_lt h1'
          -- Now apply the strict relative A-bound to get the Θ-gap bound.
          have hθ_gap :
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
                R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ :=
            by
              simpa [δ] using
              theta_gap_lt_of_mu_lt_op_of_chooseδBaseAdmissible hk R IH H d hd hBase r_old_x r_old_y Δ hΔ_pos h_gap_bound
          -- Conclude θx + t_x·δ < θy + t_y·δ using t_y = t_x + Δ.
          have ht_y_cast : (t_y : ℝ) * δ = (t_x : ℝ) * δ + (Δ : ℝ) * δ := by
            -- expand (t_x + Δ)·δ
            simpa [hΔ_eq, Nat.cast_add, add_mul]
          have hθ_gap' :
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
                R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (Δ : ℝ) * δ := by
            linarith
          calc
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (t_x : ℝ) * δ
                < (R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (Δ : ℝ) * δ) + (t_x : ℝ) * δ := by
                    simpa [add_assoc] using add_lt_add_right hθ_gap' ((t_x : ℝ) * δ)
            _ = R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + ((t_x : ℝ) * δ + (Δ : ℝ) * δ) := by
                    ring
            _ = R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_y : ℝ) * δ := by
                    simpa [ht_y_cast, add_assoc, add_comm, add_left_comm]

      · -- Case t_x = t_y
        -- Cancel common right factor to reduce to the old grid ordering.
        have hmono : Monotone (fun z : α => op z (iterate_op d t_x)) :=
          (op_strictMono_left (iterate_op d t_x)).monotone
        have h_mu : mu F r_old_x < mu F r_old_y := by
          have : op (mu F r_old_x) (iterate_op d t_x) < op (mu F r_old_y) (iterate_op d t_x) := by
            simpa [hx_eq, hy_eq, h_t_eq] using hxy
          exact hmono.reflect_lt this
        have h_mu' : mu F (splitMulti r_x).1 < mu F (splitMulti r_y).1 := by
          simpa [r_old_x, r_old_y] using h_mu
        have hθ_lt :
            R.Θ_grid ⟨mu F (splitMulti r_x).1, mu_mem_kGrid F (splitMulti r_x).1⟩ <
              R.Θ_grid ⟨mu F (splitMulti r_y).1, mu_mem_kGrid F (splitMulti r_y).1⟩ :=
          R.strictMono h_mu'
        have ht_eq' : (splitMulti r_x).2 = (splitMulti r_y).2 := by
          simpa [t_x, t_y] using h_t_eq
        -- Rewrite the RHS t-component to match the LHS, then add the common t-term.
        rw [← ht_eq']
        exact add_lt_add_right hθ_lt (((splitMulti r_x).2 : ℝ) * δ)

      · -- Case t_x > t_y
        have hΔ_pos : 0 < (t_x - t_y) := Nat.sub_pos_of_lt h_t_gt
        set Δ : ℕ := t_x - t_y
        have hΔ_eq : t_x = t_y + Δ := (Nat.add_sub_cancel' (le_of_lt h_t_gt)).symm
        have h_trade_bound : op (mu F r_old_x) (iterate_op d Δ) < mu F r_old_y := by
          have h1 : op (mu F r_old_x) (iterate_op d t_x) <
              op (mu F r_old_y) (iterate_op d t_y) := by
            simpa [hx_eq, hy_eq] using hxy
          have ht_split : iterate_op d t_x = op (iterate_op d Δ) (iterate_op d t_y) := by
            have : t_x = Δ + t_y := by omega
            simpa [this] using (iterate_op_add d Δ t_y).symm
          have h1' :
              op (op (mu F r_old_x) (iterate_op d Δ)) (iterate_op d t_y) <
                op (mu F r_old_y) (iterate_op d t_y) := by
            simpa [ht_split, op_assoc] using h1
          have hmono : Monotone (fun z : α => op z (iterate_op d t_y)) :=
            (op_strictMono_left (iterate_op d t_y)).monotone
          exact hmono.reflect_lt h1'
        -- Old part must satisfy mu F r_old_x < mu F r_old_y (since d^Δ > ident).
        have hμ_lt : mu F r_old_x < mu F r_old_y := by
          have hpos : ident < iterate_op d Δ := iterate_op_pos d hd Δ hΔ_pos
          have hinc : mu F r_old_x < op (mu F r_old_x) (iterate_op d Δ) := by
            -- x < x ⊕ d^Δ since ident < d^Δ
            have : op (mu F r_old_x) ident < op (mu F r_old_x) (iterate_op d Δ) :=
              (op_strictMono_right (mu F r_old_x)) hpos
            simpa [op_ident_right] using this
          exact lt_trans hinc h_trade_bound
        have hθ_gap :
            (Δ : ℝ) * δ <
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
                R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ :=
          by
            simpa [δ] using
              theta_gap_gt_of_op_lt_mu_of_chooseδBaseAdmissible hk R IH H d hd hBase r_old_x r_old_y Δ hΔ_pos h_trade_bound
        have ht_x_cast : (t_x : ℝ) * δ = (t_y : ℝ) * δ + (Δ : ℝ) * δ := by
          simpa [hΔ_eq, Nat.cast_add, add_mul]
        have hθ_gap' :
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (Δ : ℝ) * δ <
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
          linarith
        calc
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (t_x : ℝ) * δ
              = (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (Δ : ℝ) * δ) + (t_y : ℝ) * δ := by
                  -- reorder using ht_x_cast
                  simp [ht_x_cast]
                  ring
          _ < R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (t_y : ℝ) * δ := by
                  simpa [add_assoc] using add_lt_add_right hθ_gap' ((t_y : ℝ) * δ)

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

        -- Now we have:
        --   mu F r_old_x < mu F r_old_y
        -- and (from x < y with t_x = t_y + Δ):
        --   op (mu F r_old_x) (d^Δ) < mu F r_old_y
        -- This is exactly the C-side hypothesis needed to bound the Θ-gap from below.

        have h_gap_bound :
            (Δ : ℝ) * δ <
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
                R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
          have h :=
            theta_gap_gt_of_op_lt_mu hk R IH H d hd r_old_x r_old_y Δ hΔ_pos h_mu_lt h_trade_bound
          simpa [δ] using h

        rw [h_x_shift]
        -- Goal: Θ'(joinMulti r_old_x t_y) + Δ*δ < Θ'(joinMulti r_old_y t_y)
        -- By Θ' definition: θx + t_y*δ + Δ*δ < θy + t_y*δ
        simp only [Θ', Theta'_raw]
        -- After unfolding, this reduces to θx + Δ*δ < θy, which is h_gap_bound
        linarith [h_gap_bound]

    -/

    -- Property 3: Additivity (componentwise on multiplicities)
    --
    -- PROOF STRATEGY:
    -- 1. For multiplicities r, s : Multi (k+1), split as (r_old, t_r) and (s_old, t_s)
    -- 2. Then (r + s) splits as (r_old + s_old, t_r + t_s)
    -- 3. By mu_extend_last:
    --    mu F' (r+s) = mu F (r_old + s_old) ⊕ d^{t_r + t_s}
    -- 4. By R.add (additivity on old grid) and iterate_op_add:
    --    mu F (r_old + s_old) = mu F r_old ⊕ mu F s_old  (this is R.add!)
    --    d^{t_r + t_s} = d^{t_r} ⊕ d^{t_s}  (iterate_op_add)
    -- 5. Θ' computation:
    --    Θ'(mu F' (r+s)) = R.Θ_grid(mu F (r_old + s_old)) + (t_r + t_s) * δ
    --                    = [R.Θ_grid(mu F r_old) + R.Θ_grid(mu F s_old)] + (t_r + t_s) * δ
    --                    = [R.Θ_grid(mu F r_old) + t_r * δ] + [R.Θ_grid(mu F s_old) + t_s * δ]
    --                    = Θ'(mu F' r) + Θ'(mu F' s)
    --
    -- Technical issue: Classical.choose may pick different witnesses, but the values
    -- should be independent of witness choice (Θ' well-defined on grid points).
    have h_additive : ∀ (r s : Multi (k+1)),
        Θ' ⟨mu F' (fun i => r i + s i), mu_mem_kGrid (F:=F') (r:=fun i => r i + s i)⟩ =
        Θ' ⟨mu F' r, mu_mem_kGrid (F:=F') r⟩ +
        Θ' ⟨mu F' s, mu_mem_kGrid (F:=F') s⟩ := by
      intro r s
      simp only [Θ']

      -- Get the δ-bounds for Theta'_well_defined
      have hδA := chooseδ_A_bound hk R IH H d hd
      have hδC := chooseδ_C_bound hk R IH H d hd
      have hδB := chooseδ_B_bound hk R IH d hd

      -- Key: splitMulti distributes over addition
      have h_split_add : splitMulti (fun i => r i + s i) =
          ((fun i => (splitMulti r).1 i + (splitMulti s).1 i),
           (splitMulti r).2 + (splitMulti s).2) := splitMulti_add r s

      -- LHS witness for (r + s)
      set r'_sum := Classical.choose (mu_mem_kGrid F' (fun i => r i + s i))
      have hr'_sum_spec : mu F' r'_sum = mu F' (fun i => r i + s i) :=
        (Classical.choose_spec (mu_mem_kGrid F' (fun i => r i + s i))).symm

      -- Witnesses for r and s
      set r'_r := Classical.choose (mu_mem_kGrid F' r)
      have hr'_r_spec : mu F' r'_r = mu F' r :=
        (Classical.choose_spec (mu_mem_kGrid F' r)).symm

      set r'_s := Classical.choose (mu_mem_kGrid F' s)
      have hr'_s_spec : mu F' r'_s = mu F' s :=
        (Classical.choose_spec (mu_mem_kGrid F' s)).symm

      -- For joinMulti, we can use exact representatives
      -- joinMulti_splitMulti says: joinMulti (splitMulti r).1 (splitMulti r).2 = r
      have h_r_join : joinMulti (splitMulti r).1 (splitMulti r).2 = r := joinMulti_splitMulti r
      have h_s_join : joinMulti (splitMulti s).1 (splitMulti s).2 = s := joinMulti_splitMulti s

      -- The sum also satisfies the joinMulti property
      have h_sum_join : joinMulti (fun i => (splitMulti r).1 i + (splitMulti s).1 i)
                                  ((splitMulti r).2 + (splitMulti s).2) =
                        (fun i => r i + s i) := by
        rw [← joinMulti_add]
        -- Now goal: (fun i => joinMulti (splitMulti r).1 (splitMulti r).2 i +
        --                    joinMulti (splitMulti s).1 (splitMulti s).2 i) = fun i => r i + s i
        funext i
        simp only [h_r_join, h_s_join]

      -- Build the equality proofs for Theta'_well_defined
      -- For sum: mu F' r'_sum = mu F' (joinMulti (r_old+s_old) (t_r+t_s))
      have h_mu_sum : mu F' r'_sum =
          mu F' (joinMulti (fun i => (splitMulti r).1 i + (splitMulti s).1 i)
                          ((splitMulti r).2 + (splitMulti s).2)) := by
        rw [hr'_sum_spec, h_sum_join]

      -- For r: mu F' r'_r = mu F' (joinMulti (splitMulti r).1 (splitMulti r).2)
      have h_mu_r : mu F' r'_r = mu F' (joinMulti (splitMulti r).1 (splitMulti r).2) := by
        rw [hr'_r_spec, h_r_join]

      -- For s: mu F' r'_s = mu F' (joinMulti (splitMulti s).1 (splitMulti s).2)
      have h_mu_s : mu F' r'_s = mu F' (joinMulti (splitMulti s).1 (splitMulti s).2) := by
        rw [hr'_s_spec, h_s_join]

      -- Apply Theta'_well_defined to each
      have hWD_sum := Theta'_well_defined R H IH d hd δ delta_pos hδA hδC hδB h_mu_sum
      have hWD_r := Theta'_well_defined R H IH d hd δ delta_pos hδA hδC hδB h_mu_r
      have hWD_s := Theta'_well_defined R H IH d hd δ delta_pos hδA hδC hδB h_mu_s

      -- Unfold Theta'_raw in the well-definedness results
      simp only [Theta'_raw, splitMulti_joinMulti] at hWD_sum hWD_r hWD_s

      -- Now LHS = R.Θ_grid(mu F (r_old_r + r_old_s)) + (t_r + t_s) * δ
      -- and RHS = [R.Θ_grid(mu F r_old_r) + t_r * δ] + [R.Θ_grid(mu F r_old_s) + t_s * δ]
      -- By R.add: R.Θ_grid(mu F (r_old_r + r_old_s)) = R.Θ_grid(mu F r_old_r) + R.Θ_grid(mu F r_old_s)
      rw [hWD_sum, hWD_r, hWD_s]

      -- Use R.add for the old-grid additivity
      have h_R_add := R.add (splitMulti r).1 (splitMulti s).1

      -- Rewrite using R.add
      -- Goal: R.Θ_grid(...(r_old + s_old)...) + (t_r + t_s) * δ =
      --       (R.Θ_grid(...r_old...) + t_r * δ) + (R.Θ_grid(...s_old...) + t_s * δ)
      rw [h_R_add]
      push_cast
      ring

    /-
    -- Helper 4: Thread ZQuantized from k-grid to (k+1)-grid
    -- If the k-grid has the ZQuantized property, so does the extended (k+1)-grid
    have ZQuantized_succ : ∀ (hZQ : ZQuantized F R δ),
        ZQuantized F' ⟨Θ', h_strictMono, h_additive, h_norm⟩ δ := by
      intro hZQ r
      -- Split r : Multi (k+1) into (r_old, t)
      set r_old := (splitMulti r).1 with hr_old
      set t := (splitMulti r).2 with ht
      -- Quantization on the old k-grid
      obtain ⟨m, hm⟩ := hZQ r_old
      -- Θ' on r expands to R.Θ_grid(r_old) + t*δ
      use m + (t : ℤ)
      -- Show Θ'(r) - Θ'((0,...,0)) = (m + t) * δ
      have h_zero : mu F' (fun _ => 0) = ident := mu_zero F'
      -- Θ'(r) = Θ'(joinMulti r_old t) = R.Θ(r_old) + t*δ
      -- Θ'(0) = R.Θ(0) + 0*δ = 0
      have hr_eq : r = joinMulti r_old t := by
        rw [← hr_old, ← ht]
        exact joinMulti_splitMulti r
      calc (⟨Θ', h_strictMono, h_additive, h_norm⟩ : MultiGridRep F').Θ_grid
              ⟨mu F' r, mu_mem_kGrid F' r⟩
          - (⟨Θ', h_strictMono, h_additive, h_norm⟩ : MultiGridRep F').Θ_grid
              ⟨ident, ident_mem_kGrid F'⟩
          = Θ' ⟨mu F' r, mu_mem_kGrid F' r⟩ - 0 := by simp [h_norm]
        _ = Θ' ⟨mu F' (joinMulti r_old t), _⟩ := by congr 1; congr 1; rw [← hr_eq]
        _ = R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ := by
            simp [Θ', Theta'_raw]; rfl
          _ = (m : ℝ) * δ + (t : ℝ) * δ := by rw [← hm, R.ident_eq_zero]; ring
          _ = ((m + (t : ℤ)) : ℝ) * δ := by simp [mul_add]; norm_cast
    -/

    -- Construct the MultiGridRep F' (representation complete!)
    let R' : MultiGridRep F' := ⟨Θ', h_strictMono, h_additive, h_norm⟩

    -- Prove the extension property: R'.Θ_grid(joinMulti r_old t) = R.Θ_grid(r_old) + t * δ
    have h_extends : ∀ r_old : Multi k, ∀ t : ℕ,
        R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
        R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ := by
      intro r_old t
      -- Use Theta'_on_join which shows Θ'(joinMulti r_old t) = Theta'_raw R d δ r_old t
      have h1 := Theta'_on_join r_old t
      simp only [Theta'_raw] at h1
      exact h1

    refine ⟨R', h_extends⟩

/-- **ZQuantized property extends through atom family extension**

If the k-grid has the ZQuantized property with δ, then the extended (k+1)-grid
also has the ZQuantized property with the same δ.

This is crucial for threading the quantization property through the k→k+1 induction. -/
lemma ZQuantized_extend
  {k : ℕ} {F : AtomFamily α k} (hk : k ≥ 1)
  (R : MultiGridRep F) (IH : GridBridge F) (H : GridComm F)
  (d : α) (hd : ident < d)
  (hZQ : ZQuantized F R (chooseδ hk R d hd))
  {F' : AtomFamily α (k+1)} (hF' : F' = extendAtomFamily F d hd)
  {R' : MultiGridRep F'}
  -- Assume R' was built using the standard Θ' construction from extend_grid_rep_with_atom
  (hR'_extends : ∀ r t,
    R'.Θ_grid ⟨mu F' (joinMulti r t), mu_mem_kGrid F' (joinMulti r t)⟩ =
    R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ + (t : ℝ) * chooseδ hk R d hd) :
  ZQuantized F' R' (chooseδ hk R d hd) := by
  classical
  intro r
  set δ : ℝ := chooseδ hk R d hd
  have hZQδ : ZQuantized F R δ := by
    simpa [δ] using hZQ

  -- Decompose `r : Multi (k+1)` as `joinMulti r_old t`.
  set r_old : Multi k := (splitMulti r).1 with hr_old
  set t : ℕ := (splitMulti r).2 with ht
  have hr_join : r = joinMulti r_old t := by
    -- `joinMulti_splitMulti` is written with a `let`; unfold it with our names.
    simpa [r_old, t] using (joinMulti_splitMulti r).symm

  -- Quantization on the old grid.
  rcases hZQδ r_old with ⟨m, hm⟩
  refine ⟨m + (t : ℤ), ?_⟩

  -- Expand `Θ` on the extended grid using the extension formula.
  have hΘr :
      R'.Θ_grid ⟨mu F' r, mu_mem_kGrid F' r⟩ =
        R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ := by
    simpa [δ, hr_join] using (hR'_extends r_old t)

  -- Convert to an integer multiple of `δ`.
  have hΘ_mul : R'.Θ_grid ⟨mu F' r, mu_mem_kGrid F' r⟩ = (m : ℝ) * δ + (t : ℝ) * δ := by
    simpa [hΘr, hm]
  -- Now just do the cast bookkeeping.
  simpa [hΘ_mul] using (zquantized_cast_add m t δ)

theorem extend_grid_rep_with_atom_of_gridComm
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hBase : ChooseδBaseAdmissible (α := α) hk R d hd) :
      ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        (∀ r_old : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
          R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * chooseδ hk R d hd) := by
  have IH : GridBridge F := gridBridge_of_gridComm (F := F) H
  exact extend_grid_rep_with_atom (α := α) (hk := hk) (R := R) (IH := IH) (H := H) (d := d)
    (hd := hd) hBase

  end Mettapedia.ProbabilityTheory.KnuthSkilling.RepresentationTheorem
