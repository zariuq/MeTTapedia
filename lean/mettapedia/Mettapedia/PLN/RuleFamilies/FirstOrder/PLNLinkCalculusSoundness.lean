import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNLinkCalculus
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation

/-!
# PLN Link Calculus: Measure-Theoretic Soundness (Deduction)

This file provides a *first* soundness lemma for the weight-first PLN link calculus:

- A semantic interpretation sends formulas to measurable events in a probability space.
- Term judgments `term A t` assert `t.strength = P(A)`.
- Link judgments `link A B t` assert `t.strength = P(B|A)`.

We prove local soundness for the **deduction** truth function by reusing the existing
measure-theoretic theorem `pln_deduction_from_total_probability_ctx` from
`Mettapedia/PLN/RuleFamilies/FirstOrder/PLNDerivation.lean`.

We intentionally do **not** claim anything about weights here: weight/evidence soundness is a
separate meta-level story.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.PLNLinkCalculus.Soundness

open MeasureTheory ProbabilityTheory Set

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
open Mettapedia.PLN.TruthValues.PLNWeightTV
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNLinkCalculus

universe u v

variable {F : Type u}
variable {Ω : Type v} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (interp : F → Set Ω)

/-! ## Semantics for judgments (strength only) -/

def holdsTerm (A : F) (t : WTV) : Prop :=
  t.strength = μ.real (interp A)

def holdsLink (A B : F) (t : WTV) : Prop :=
  t.strength = μ.real (interp B ∩ interp A) / μ.real (interp A)

def holds : Judgment F → Prop
  | .term A t => holdsTerm (μ := μ) (interp := interp) A t
  | .link A B t => holdsLink (μ := μ) (interp := interp) A B t

/-! ## A basic bound: conditional probability is in [0,1] -/

lemma condProb_mem_unit {A C : Set Ω} (hA_pos : μ A ≠ 0) :
    μ.real (C ∩ A) / μ.real A ∈ Set.Icc (0 : ℝ) 1 := by
  have hA_real_pos : 0 < μ.real A := by
    simp only [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hA_pos, measure_lt_top μ A⟩
  constructor
  · -- Nonnegativity
    apply div_nonneg
    · simp [Measure.real]
    · exact le_of_lt hA_real_pos
  · -- Upper bound
    rw [div_le_one hA_real_pos]
    have hle : μ (C ∩ A) ≤ μ A := by
      apply measure_mono
      intro x hx
      exact hx.2
    have hA_top : μ A ≠ ⊤ := measure_ne_top μ A
    have hCA_top : μ (C ∩ A) ≠ ⊤ := measure_ne_top μ (C ∩ A)
    have hle_real : (μ (C ∩ A)).toReal ≤ (μ A).toReal :=
      (ENNReal.toReal_le_toReal hCA_top hA_top).2 hle
    simpa [Measure.real] using hle_real

/-! ## Soundness: deduction truth function -/

theorem truth_deduction_sound
    {A B C : F} {tA tB tC tAB tBC : WTV}
    (ctx : PLNDeductionMeasureContext (μ := μ) (A := interp A) (B := interp B) (C := interp C))
    (_hA : holdsTerm (μ := μ) (interp := interp) A tA)
    (hB : holdsTerm (μ := μ) (interp := interp) B tB)
    (hC : holdsTerm (μ := μ) (interp := interp) C tC)
    (hAB : holdsLink (μ := μ) (interp := interp) A B tAB)
    (hBC : holdsLink (μ := μ) (interp := interp) B C tBC) :
    holdsLink (μ := μ) (interp := interp) A C (Truth.deduction tA tB tC tAB tBC) := by
  -- Reduce to a statement about strengths.
  unfold holdsLink
  -- `Truth.deduction` clamps the (already-correct) PLN formula into `[0,1]`.
  simp [Truth.deduction]
  -- Reuse the packaged measure-theoretic deduction theorem.
  have hctx :=
    (pln_deduction_from_total_probability_ctx (μ := μ) (A := interp A) (B := interp B) (C := interp C) ctx)
  -- Rewrite the RHS of the PLN theorem using the hypotheses connecting TVs to probabilities.
  have hAB' : μ.real (interp B ∩ interp A) / μ.real (interp A) = tAB.strength := by
    simpa [holdsLink] using hAB.symm
  have hBC' : μ.real (interp C ∩ interp B) / μ.real (interp B) = tBC.strength := by
    simpa [holdsLink] using hBC.symm
  have hB' : μ.real (interp B) = tB.strength := by
    simpa [holdsTerm] using hB.symm
  have hC' : μ.real (interp C) = tC.strength := by
    simpa [holdsTerm] using hC.symm
  have hpln :
      plnDeductionStrength tAB.strength tBC.strength tB.strength tC.strength =
        μ.real (interp C ∩ interp A) / μ.real (interp A) := by
    -- `hctx` is: P(C|A) = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C)).
    -- After rewriting the inputs to match the given TVs, it becomes the desired equality.
    -- We use the equality in the direction that matches our goal.
    have : μ.real (interp C ∩ interp A) / μ.real (interp A) =
        plnDeductionStrength tAB.strength tBC.strength tB.strength tC.strength := by
      -- First rewrite the link arguments (so we don't rewrite the denominator out from under them),
      -- then rewrite term probabilities.
      have h1 :
          μ.real (interp C ∩ interp A) / μ.real (interp A) =
            plnDeductionStrength tAB.strength tBC.strength (μ.real (interp B)) tC.strength := by
        simpa [hAB', hBC', hC'] using hctx
      simpa [hB'] using h1
    exact this.symm
  -- Replace the clamped PLN expression by the clamped semantic conditional probability.
  rw [hpln]
  -- And now `clamp01` is the identity because conditional probabilities lie in `[0,1]`.
  have hmem :
      μ.real (interp C ∩ interp A) / μ.real (interp A) ∈ Set.Icc (0 : ℝ) 1 :=
    condProb_mem_unit (μ := μ) (A := interp A) (C := interp C) ctx.hA_pos
  simpa using (clamp01_of_mem_unit hmem)

/-! ## Soundness: SourceRule (Induction) and SinkRule (Abduction)

These are definitional compositions of Bayes inversion + the deduction formula.

We reuse the same measure-theoretic deduction theorem and add a small Bayes algebra
step to rewrite the missing conditional probability.
-/

private lemma bayes_inversion_term_link
    {A B : F} {tA tB tBA : WTV}
    (hA : holdsTerm (μ := μ) (interp := interp) A tA)
    (hB : holdsTerm (μ := μ) (interp := interp) B tB)
    (hBA : holdsLink (μ := μ) (interp := interp) B A tBA)
    (hA_pos : μ (interp A) ≠ 0) (hB_pos : μ (interp B) ≠ 0) :
    bayesInversion tBA.strength tA.strength tB.strength =
      μ.real (interp B ∩ interp A) / μ.real (interp A) := by
  -- Expand Bayes inversion and rewrite the three inputs from the hypotheses.
  have hA' : tA.strength = μ.real (interp A) := hA
  have hB' : tB.strength = μ.real (interp B) := hB
  have hBA' : tBA.strength = μ.real (interp A ∩ interp B) / μ.real (interp B) := hBA
  -- Denominators are nonzero from the context (since `μ A ≠ 0` and `μ B ≠ 0`).
  have hA_real_pos : 0 < μ.real (interp A) := by
    simp only [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hA_pos, measure_lt_top μ (interp A)⟩
  have hB_real_pos : 0 < μ.real (interp B) := by
    simp only [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hB_pos, measure_lt_top μ (interp B)⟩
  have hA_ne : μ.real (interp A) ≠ 0 := ne_of_gt hA_real_pos
  have hB_ne : μ.real (interp B) ≠ 0 := ne_of_gt hB_real_pos
  -- Now simplify.
  unfold bayesInversion
  -- Replace TVs by their semantic meanings.
  -- Goal becomes: (P(A|B) * P(B)) / P(A) = P(B|A).
  -- In real arithmetic: (P(A∩B)/P(B) * P(B))/P(A) = P(A∩B)/P(A).
  -- Then commute intersection to match our `holdsLink` convention for `B|A`.
  simp [hA', hB', hBA', hB_ne, Set.inter_comm]

theorem truth_sourceRule_sound
    {A B C : F} {tA tB tC tBA tBC : WTV}
    (ctx : PLNDeductionMeasureContext (μ := μ) (A := interp A) (B := interp B) (C := interp C))
    (_hA : holdsTerm (μ := μ) (interp := interp) A tA)
    (hB : holdsTerm (μ := μ) (interp := interp) B tB)
    (hC : holdsTerm (μ := μ) (interp := interp) C tC)
    (hBA : holdsLink (μ := μ) (interp := interp) B A tBA)
    (hBC : holdsLink (μ := μ) (interp := interp) B C tBC) :
    holdsLink (μ := μ) (interp := interp) A C (Truth.sourceRule tA tB tC tBA tBC) := by
  unfold holdsLink
  simp [Truth.sourceRule]
  have hctx :=
    (pln_deduction_from_total_probability_ctx (μ := μ) (A := interp A) (B := interp B) (C := interp C) ctx)
  have hA' : μ.real (interp A) = tA.strength := by
    -- `_hA` is unused in the deduction proof, but it matters here for Bayes inversion.
    -- We keep it as an explicit hypothesis for rule alignment.
    simpa [holdsTerm] using _hA.symm
  have hB' : μ.real (interp B) = tB.strength := by
    simpa [holdsTerm] using hB.symm
  have hC' : μ.real (interp C) = tC.strength := by
    simpa [holdsTerm] using hC.symm
  have hBC' : μ.real (interp C ∩ interp B) / μ.real (interp B) = tBC.strength := by
    simpa [holdsLink] using hBC.symm
  -- Bayes inversion turns `P(A|B)` into `P(B|A)`.
  have h_bayes :
      bayesInversion tBA.strength tA.strength tB.strength =
        μ.real (interp B ∩ interp A) / μ.real (interp A) := by
    refine bayes_inversion_term_link (μ := μ) (interp := interp) (A := A) (B := B)
      (tA := tA) (tB := tB) (tBA := tBA) ?_ ?_ ?_ ctx.hA_pos ctx.hB_pos
    · simpa [holdsTerm] using _hA
    · exact hB
    · exact hBA
  have hpln :
      plnSourceRuleStrength tBA.strength tBC.strength tA.strength tB.strength tC.strength =
        μ.real (interp C ∩ interp A) / μ.real (interp A) := by
    -- Rewrite the RHS of the PLN theorem (`hctx`) into the induction form.
    have : μ.real (interp C ∩ interp A) / μ.real (interp A) =
        plnDeductionStrength (bayesInversion tBA.strength tA.strength tB.strength)
          tBC.strength tB.strength tC.strength := by
      -- Start from the deduction theorem and rewrite the inputs.
      -- First: rewrite P(B|A) using Bayes inversion.
      -- Then: rewrite P(C|B), P(B), P(C) using TV hypotheses.
      have h1 :
          μ.real (interp C ∩ interp A) / μ.real (interp A) =
            plnDeductionStrength (μ.real (interp B ∩ interp A) / μ.real (interp A))
              tBC.strength (μ.real (interp B)) (μ.real (interp C)) := by
        -- Avoid rewriting the denominator of the conditional-probability term out from under us.
        simpa [hBC'] using hctx
      -- Replace μ.real(B∩A)/μ.real A with Bayes inversion, and marginals with term TVs.
      -- (h_bayes is in the direction Bayes = conditional, so we use its symm.)
      have h2 : μ.real (interp B ∩ interp A) / μ.real (interp A) =
          bayesInversion tBA.strength tA.strength tB.strength := by
        simpa using h_bayes.symm
      -- Rewrite `μ.real (interp B)` and `μ.real (interp C)` to TV strengths.
      -- `plnSourceRuleStrength` expands to Bayes+Deduction.
      -- We convert stepwise to keep simp stable.
      -- Step: rewrite marginals.
      have h3 :
          plnDeductionStrength (μ.real (interp B ∩ interp A) / μ.real (interp A))
              tBC.strength (μ.real (interp B)) (μ.real (interp C)) =
            plnDeductionStrength (bayesInversion tBA.strength tA.strength tB.strength)
              tBC.strength tB.strength tC.strength := by
        -- Rewrite the remaining marginals to TV strengths.
        simp [h2, hB', hC']
      -- Combine.
      simpa [h3] using h1
    -- Now unfold the SourceRule strength alias.
    simpa [plnSourceRuleStrength, plnInductionStrength] using this.symm
  -- Replace by the semantic conditional probability and clamp away.
  rw [hpln]
  have hmem :
      μ.real (interp C ∩ interp A) / μ.real (interp A) ∈ Set.Icc (0 : ℝ) 1 :=
    condProb_mem_unit (μ := μ) (A := interp A) (C := interp C) ctx.hA_pos
  simpa using (clamp01_of_mem_unit hmem)

theorem truth_sinkRule_sound
    {A B C : F} {tA tB tC tAB tCB : WTV}
    (ctx : PLNDeductionMeasureContext (μ := μ) (A := interp A) (B := interp B) (C := interp C))
    (hA : holdsTerm (μ := μ) (interp := interp) A tA)
    (hB : holdsTerm (μ := μ) (interp := interp) B tB)
    (hC : holdsTerm (μ := μ) (interp := interp) C tC)
    (hAB : holdsLink (μ := μ) (interp := interp) A B tAB)
    (hCB : holdsLink (μ := μ) (interp := interp) C B tCB) :
    holdsLink (μ := μ) (interp := interp) A C (Truth.sinkRule tA tB tC tAB tCB) := by
  unfold holdsLink
  simp [Truth.sinkRule]
  have hctx :=
    (pln_deduction_from_total_probability_ctx (μ := μ) (A := interp A) (B := interp B) (C := interp C) ctx)
  have hA' : μ.real (interp A) = tA.strength := by
    simpa [holdsTerm] using hA.symm
  have hB' : μ.real (interp B) = tB.strength := by
    simpa [holdsTerm] using hB.symm
  have hC' : μ.real (interp C) = tC.strength := by
    simpa [holdsTerm] using hC.symm
  have hAB' : μ.real (interp B ∩ interp A) / μ.real (interp A) = tAB.strength := by
    simpa [holdsLink] using hAB.symm
  have hCB' : μ.real (interp B ∩ interp C) / μ.real (interp C) = tCB.strength := by
    simpa [holdsLink] using hCB.symm
  -- Bayes inversion turns `P(B|C)` into `P(C|B)`.
  have h_bayes :
      bayesInversion tCB.strength tB.strength tC.strength =
        μ.real (interp C ∩ interp B) / μ.real (interp B) := by
    have hB_term : tB.strength = μ.real (interp B) := by
      simpa [holdsTerm] using hB
    have hC_term : tC.strength = μ.real (interp C) := by
      simpa [holdsTerm] using hC
    have hB_real_pos : 0 < μ.real (interp B) := by
      simp only [Measure.real, ENNReal.toReal_pos_iff]
      exact ⟨pos_iff_ne_zero.mpr ctx.hB_pos, measure_lt_top μ (interp B)⟩
    have hB_ne : μ.real (interp B) ≠ 0 := ne_of_gt hB_real_pos
    by_cases hC0 : μ.real (interp C) = 0
    · -- If P(C)=0 then P(C|B)=0, and Bayes inversion also yields 0.
      have hμC0 : μ (interp C) = 0 := by
        have hμC : (μ (interp C)).toReal = 0 := by simpa [Measure.real] using hC0
        have h0 := (ENNReal.toReal_eq_zero_iff (μ (interp C))).1 hμC
        cases h0 with
        | inl h => exact h
        | inr h =>
            exfalso
            exact (measure_ne_top μ (interp C)) h
      have hμCB0 : μ (interp C ∩ interp B) = 0 := by
        have hle : μ (interp C ∩ interp B) ≤ μ (interp C) := by
          apply measure_mono
          intro x hx
          exact hx.1
        exact le_antisymm (by simpa [hμC0] using hle) bot_le
      have hCB0 : μ.real (interp C ∩ interp B) = 0 := by
        simp [Measure.real, hμCB0]
      have hC_strength0 : tC.strength = 0 := by
        simp [hC_term, hC0]
      -- Both sides simplify to 0.
      simp [bayesInversion, hB_term, hC_strength0, hCB0]
    · -- Otherwise we can cancel `μ.real (interp C)` in the Bayes inversion expression.
      have hC_ne : μ.real (interp C) ≠ 0 := hC0
      unfold bayesInversion
      have hCB_term : tCB.strength = μ.real (interp B ∩ interp C) / μ.real (interp C) := by
        simpa [holdsLink] using hCB
      -- Goal reduces to: (P(B|C) * P(C))/P(B) = P(C∩B)/P(B).
      simp [hCB_term, hB_term, hC_term, hC_ne, Set.inter_comm]
  have hpln :
      plnAbductionStrength tAB.strength tCB.strength tA.strength tB.strength tC.strength =
        μ.real (interp C ∩ interp A) / μ.real (interp A) := by
    have : μ.real (interp C ∩ interp A) / μ.real (interp A) =
        plnDeductionStrength tAB.strength (bayesInversion tCB.strength tB.strength tC.strength)
          tB.strength tC.strength := by
      -- Rewrite the deduction theorem inputs to match the abduction form.
      -- First: rewrite P(B|A) using `hAB'`.
      -- Second: rewrite P(C|B) using Bayes inversion.
      -- Finally: rewrite marginals using term TVs.
      have h1 :
          μ.real (interp C ∩ interp A) / μ.real (interp A) =
            plnDeductionStrength tAB.strength (μ.real (interp C ∩ interp B) / μ.real (interp B))
              (μ.real (interp B)) (μ.real (interp C)) := by
        -- Avoid rewriting the denominator of the conditional-probability term out from under us.
        simpa [hAB'] using hctx
      have h2 : μ.real (interp C ∩ interp B) / μ.real (interp B) =
          bayesInversion tCB.strength tB.strength tC.strength := by
        simpa using h_bayes.symm
      have h2' : μ.real (interp C ∩ interp B) / tB.strength =
          bayesInversion tCB.strength tB.strength tC.strength := by
        -- Rewrite the denominator of the conditional probability to match the TV.
        simpa [hB'] using h2
      -- Rewrite the remaining marginals.
      have h3 :
          plnDeductionStrength tAB.strength (μ.real (interp C ∩ interp B) / μ.real (interp B))
              (μ.real (interp B)) (μ.real (interp C)) =
            plnDeductionStrength tAB.strength (bayesInversion tCB.strength tB.strength tC.strength)
              tB.strength tC.strength := by
        simp [h2', hB', hC']
      simpa [h3] using h1
    -- Unfold abduction strength.
    simpa [plnAbductionStrength] using this.symm
  rw [hpln]
  have hmem :
      μ.real (interp C ∩ interp A) / μ.real (interp A) ∈ Set.Icc (0 : ℝ) 1 :=
    condProb_mem_unit (μ := μ) (A := interp A) (C := interp C) ctx.hA_pos
  simpa using (clamp01_of_mem_unit hmem)

end Mettapedia.PLN.RuleFamilies.FirstOrder.PLNLinkCalculus.Soundness
