import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Proofs.Direct.FibonacciProof

/-!
# ARCHIVED: Incomplete Theorems from FibonacciProof.lean

These theorems represent alternative approaches that were NOT needed for the final
K&S Appendix B formalization. They are archived here for reference but contain
unfinished proofs (sorries).

**Why archived**: The main theorem `ks_appendix_b_fibonacci_strictMono` succeeds
by deriving continuity from ProductEquation + StrictMono + Positivity directly,
then applying `productEquation_solution_of_continuous_strictMono`. This bypasses
the need for these alternative approaches.

**Date archived**: 2026-01-15
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Scratch.FibonacciProofScratch

open Real
open scoped Topology goldenRatio

-- Re-export ProductEquation for convenience
open Multiplicative

/-! ## ARCHIVED: Deriving strict monotonicity from continuity

**Status**: INCOMPLETE (has sorry)

**Approach**: Show ProductEquation + Continuous + Positive → StrictMono ∨ StrictAnti
by proving injectivity via the doubling property.

**Why not needed**: K&S Appendix A already provides StrictMono from the order isomorphism.
-/

/-- **ARCHIVED**: ProductEquation + positivity + continuity → StrictMono ∨ StrictAnti.

**Proof strategy** (uses `Continuous.strictMono_of_inj` from Mathlib):
1. Show Ψ is injective: if Ψ(x) = Ψ(y) with x ≠ y, let δ = y - x.
2. The doubling Ψ(t + a) = 2Ψ(t) implies Ψ(x + na) = Ψ(y + na) for all n ∈ ℤ.
3. If δ/a is rational (δ = (p/q)a): shifting by appropriate multiples gives 2^p = 1, contradiction.
4. If δ/a is irrational: Ψ agrees with 2^n·Ψ(0) on the dense set ℤδ + ℤa, but range of
   continuous function is connected, contradiction.
5. Hence Ψ is injective, so `Continuous.strictMono_of_inj` gives StrictMono ∨ StrictAnti.
-/
lemma productEquation_strictMono_or_strictAnti
    {Ψ : ℝ → ℝ} {ζ : ℝ → ℝ → ℝ}
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (hCont : Continuous Ψ) :
    StrictMono Ψ ∨ StrictAnti Ψ := by
  -- Use Continuous.strictMono_of_inj: continuous + injective → StrictMono ∨ StrictAnti
  apply Continuous.strictMono_of_inj hCont
  -- Prove injectivity
  let a := ζ 0 0
  have hShift : ∀ t : ℝ, Ψ (t + a) = 2 * Ψ t := fun t => ProductEquation.shift_two_mul hProd t
  have ha_ne : a ≠ 0 := by
    intro ha0
    have h := hShift 0
    simp only [ha0, add_zero] at h
    have hpos := hPos 0
    linarith
  intro x y hxy
  by_contra hne
  let δ := y - x
  have hδ_ne : δ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let g : ℝ → ℝ := fun t => Real.log (Ψ t)
  have hg_cont : Continuous g := hCont.log (fun t => ne_of_gt (hPos t))
  have hg_shift : ∀ t, g (t + a) = g t + Real.log 2 := fun t => by
    simp only [g]
    rw [hShift t, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (hPos t))]
    ring
  let c := Real.log 2 / a
  let h : ℝ → ℝ := fun t => g t - c * t
  have _hh_periodic : ∀ t, h (t + a) = h t := fun t => by
    simp only [h]
    rw [hg_shift]
    ring_nf
    simp only [c]
    have ha : a ≠ 0 := ha_ne
    field_simp [ha]
    ring
  have _hh_cont : Continuous h := hg_cont.sub (continuous_const.mul continuous_id')
  have hgxy : g x = g y := by simp only [g]; rw [hxy]
  have _hh_diff : h x - h y = c * δ := by simp only [h, δ]; rw [hgxy]; ring
  -- TODO: Complete with rational/irrational case analysis
  sorry

/-! ## ARCHIVED: Theorem variants with assumed continuity

**Status**: Uses the sorry lemma above

**Why not needed**: We can bypass this by assuming StrictMono directly (from Appendix A).
-/

/-- **ARCHIVED**: K&S Appendix B with continuity ASSUMED.

This version explicitly assumes continuity and uses the sorry lemma above to get
StrictMono ∨ StrictAnti. See `ks_appendix_b_fibonacci_strictMono` in the main file
for the complete version. -/
theorem ks_appendix_b_fibonacci
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (_hBdd : ∃ M > 0, ∀ x ∈ Set.Icc (0 : ℝ) 1, Ψ x ≤ M)
    (hCont : Continuous Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  rcases productEquation_strictMono_or_strictAnti hProd hPos hCont with hMono | hAnti
  · exact productEquation_solution_of_continuous_strictMono hProd hPos hCont hMono
  · let Ψ' : ℝ → ℝ := fun x => Ψ (-x)
    let ζ' : ℝ → ℝ → ℝ := fun ξ η => -ζ (-ξ) (-η)
    have hProd' : ProductEquation Ψ' ζ' := by
      intro τ ξ η
      simp only [Ψ', ζ']
      have := hProd (-τ) (-ξ) (-η)
      simp only [neg_add_rev] at this ⊢
      convert this using 2 <;> ring
    have hPos' : ∀ x, 0 < Ψ' x := fun x => hPos (-x)
    have hCont' : Continuous Ψ' := hCont.comp continuous_neg
    have hMono' : StrictMono Ψ' := hAnti.comp (fun _ _ h => neg_lt_neg h)
    obtain ⟨C', A', hC'_pos, hΨ'_eq⟩ := productEquation_solution_of_continuous_strictMono
      hProd' hPos' hCont' hMono'
    refine ⟨C', -A', hC'_pos, ?_⟩
    intro x
    have := hΨ'_eq (-x)
    simp only [Ψ', neg_neg] at this
    simp only [mul_neg, neg_mul] at this ⊢
    exact this

/-! ## ARCHIVED: Deriving strict monotonicity from weak monotonicity

**Status**: INCOMPLETE (has sorry)

**Approach**: Show ProductEquation + Monotone + Positive → StrictMono using the
doubling property to rule out constant segments.

**Why not needed**: K&S Appendix A already provides StrictMono directly.
-/

/-- **ARCHIVED**: K&S Appendix B with weak monotonicity assumed.

This version tries to derive StrictMono from Monotone using the ProductEquation
structure, but the proof is incomplete. -/
theorem ks_appendix_b_fibonacci_derived
    (Ψ : ℝ → ℝ) (ζ : ℝ → ℝ → ℝ)
    (hProd : ProductEquation Ψ ζ)
    (hPos : ∀ x, 0 < Ψ x)
    (_hBdd : ∃ M > 0, ∀ x ∈ Set.Icc (0 : ℝ) 1, Ψ x ≤ M)
    (hMono : Monotone Ψ ∨ Antitone Ψ) :
    ∃ C A : ℝ, 0 < C ∧ ∀ x : ℝ, Ψ x = C * Real.exp (A * x) := by
  let a : ℝ := ζ 0 0
  have hShift : ∀ τ : ℝ, Ψ (τ + a) = 2 * Ψ τ := fun τ => by
    simpa using ProductEquation.shift_two_mul hProd τ
  have ha_ne : a ≠ 0 := by
    intro ha0; have h := hShift 0; simp only [ha0, add_zero] at h; linarith [hPos 0]

  have ha_sign : (0 < a ↔ Monotone Ψ) ∧ (a < 0 ↔ Antitone Ψ) := by
    constructor
    · constructor
      · intro ha_pos
        cases hMono with
        | inl hm => exact hm
        | inr hanti =>
          have h1 : Ψ a ≤ Ψ 0 := hanti (le_of_lt ha_pos)
          have h2 : Ψ a = 2 * Ψ 0 := by simpa using hShift 0
          linarith [hPos 0]
      · intro hm
        by_contra h
        push_neg at h
        have ha_neg : a ≤ 0 := h
        rcases ha_neg.lt_or_eq with ha_neg' | ha_zero
        · have h1 : Ψ a ≤ Ψ 0 := hm (le_of_lt ha_neg')
          have h2 : Ψ a = 2 * Ψ 0 := by simpa using hShift 0
          linarith [hPos 0]
        · exact ha_ne ha_zero
    · constructor
      · intro ha_neg
        cases hMono with
        | inr hanti => exact hanti
        | inl hm =>
          have h1 : Ψ a ≤ Ψ 0 := hm (le_of_lt ha_neg)
          have h2 : Ψ a = 2 * Ψ 0 := by simpa using hShift 0
          linarith [hPos 0]
      · intro hanti
        by_contra h
        push_neg at h
        have ha_nonneg : 0 ≤ a := h
        rcases ha_nonneg.lt_or_eq with ha_pos | ha_zero
        · have h1 : Ψ a ≤ Ψ 0 := hanti (le_of_lt ha_pos)
          have h2 : Ψ a = 2 * Ψ 0 := by simpa using hShift 0
          linarith [hPos 0]
        · exact ha_ne ha_zero.symm

  let C := Ψ 0
  let A := Real.log 2 / a
  have hC_pos : 0 < C := hPos 0

  -- TODO: Complete the derivation of StrictMono from Monotone
  -- The key step that's incomplete: showing Ψ(x) = Ψ(y) with x < y is impossible
  use C, A, hC_pos
  intro x
  sorry

end Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Scratch.FibonacciProofScratch
