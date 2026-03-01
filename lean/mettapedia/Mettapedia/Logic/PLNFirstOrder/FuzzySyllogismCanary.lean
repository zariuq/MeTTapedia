import Mettapedia.Logic.PLNFirstOrder.QuantifierWorkedExamples

/-!
# Chapter 11 Extended Fuzzy-Syllogism Canaries

This module adds:

1. A Zadeh-style quantified syllogism theorem family (`most ∘ most`, `few ∘ most`)
   using the multiplicative composition pattern already used in Chapter-11 examples.
2. QFM-oriented canaries:
   - monotonicity under pointwise profile increase,
   - conservativity-style invariance when the `nearOne` witness signature is unchanged.
-/

namespace Mettapedia.Logic.PLNFirstOrder

section Generic

variable {U : Type*} [Fintype U]

/-- QFM-abstract syllogism transport from two fuzzy quantifier intervals. -/
theorem qfm_syllogism_interval
    (q : QFMCompose)
    (pAB pBC : FuzzyQuantifierParams)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds pAB profileAB)
    (hBC : fuzzyIntervalHolds pBC profileBC) :
    q.comp pAB.LPC pBC.LPC ≤
        q.comp (nearOneFraction pAB profileAB) (nearOneFraction pBC profileBC) ∧
      q.comp (nearOneFraction pAB profileAB) (nearOneFraction pBC profileBC) ≤
        q.comp pAB.UPC pBC.UPC :=
  qfm_compose_interval_of_fuzzyIntervals q pAB pBC profileAB profileBC hAB hBC

/-- QFM-abstract `MOST ∘ MOST` theorem. -/
theorem qfm_syllogism_most_most
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11MostParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    q.comp ch11MostParams.LPC ch11MostParams.LPC ≤
        q.comp (nearOneFraction ch11MostParams profileAB)
          (nearOneFraction ch11MostParams profileBC) ∧
      q.comp (nearOneFraction ch11MostParams profileAB)
          (nearOneFraction ch11MostParams profileBC) ≤
        q.comp ch11MostParams.UPC ch11MostParams.UPC :=
  qfm_syllogism_interval q ch11MostParams ch11MostParams profileAB profileBC hAB hBC

/-- QFM-abstract `FEW ∘ MOST` theorem. -/
theorem qfm_syllogism_few_most
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11FewParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    q.comp ch11FewParams.LPC ch11MostParams.LPC ≤
        q.comp (nearOneFraction ch11FewParams profileAB)
          (nearOneFraction ch11MostParams profileBC) ∧
      q.comp (nearOneFraction ch11FewParams profileAB)
          (nearOneFraction ch11MostParams profileBC) ≤
        q.comp ch11FewParams.UPC ch11MostParams.UPC :=
  qfm_syllogism_interval q ch11FewParams ch11MostParams profileAB profileBC hAB hBC

/-- Reusable selector bundle (`MOST ∘ MOST`) for any QFM operator. -/
noncomputable def qfm_selector_bundle_most_most
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11MostParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    QFMSyllogismEnvelope :=
  qfm_compose_interval_bundle q ch11MostParams ch11MostParams profileAB profileBC hAB hBC

/-- Reusable selector bundle (`FEW ∘ MOST`) for any QFM operator. -/
noncomputable def qfm_selector_bundle_few_most
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11FewParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    QFMSyllogismEnvelope :=
  qfm_compose_interval_bundle q ch11FewParams ch11MostParams profileAB profileBC hAB hBC

/-- Soundness projection for the selector bundle (`MOST ∘ MOST`). -/
theorem qfm_selector_bundle_most_most_sound
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11MostParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    let B := qfm_selector_bundle_most_most q profileAB profileBC hAB hBC
    B.lower ≤ B.score ∧ B.score ≤ B.upper := by
  intro B
  exact ⟨B.lower_le_score, B.score_le_upper⟩

/-- Soundness projection for the selector bundle (`FEW ∘ MOST`). -/
theorem qfm_selector_bundle_few_most_sound
    (q : QFMCompose)
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11FewParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    let B := qfm_selector_bundle_few_most q profileAB profileBC hAB hBC
    B.lower ≤ B.score ∧ B.score ≤ B.upper := by
  intro B
  exact ⟨B.lower_le_score, B.score_le_upper⟩

/-- Zadeh-style family: if both legs are `MOST`, the composed score is in `[0.49, 0.81]`. -/
theorem zadeh_syllogism_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11MostParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0.49 : ℝ) ≤
        nearOneFraction ch11MostParams profileAB *
          nearOneFraction ch11MostParams profileBC ∧
      nearOneFraction ch11MostParams profileAB *
          nearOneFraction ch11MostParams profileBC ≤
        (0.81 : ℝ) := by
  have hProd :
      ch11MostParams.LPC * ch11MostParams.LPC ≤
          nearOneFraction ch11MostParams profileAB *
            nearOneFraction ch11MostParams profileBC ∧
        nearOneFraction ch11MostParams profileAB *
            nearOneFraction ch11MostParams profileBC ≤
          ch11MostParams.UPC * ch11MostParams.UPC := by
    simpa [qfmMul] using qfm_syllogism_most_most (q := qfmMul) profileAB profileBC hAB hBC
  have hL : ch11MostParams.LPC * ch11MostParams.LPC = (0.49 : ℝ) := by
    norm_num [ch11MostParams]
  have hU : ch11MostParams.UPC * ch11MostParams.UPC = (0.81 : ℝ) := by
    norm_num [ch11MostParams]
  constructor
  · simpa [hL] using hProd.1
  · simpa [hU] using hProd.2

/-- Zadeh-style family: if premise is `FEW` and rule-leg is `MOST`,
the composed score is in `[0.07, 0.27]`. -/
theorem zadeh_syllogism_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11FewParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0.07 : ℝ) ≤
        nearOneFraction ch11FewParams profileAB *
          nearOneFraction ch11MostParams profileBC ∧
      nearOneFraction ch11FewParams profileAB *
          nearOneFraction ch11MostParams profileBC ≤
        (0.27 : ℝ) := by
  have hProd :
      ch11FewParams.LPC * ch11MostParams.LPC ≤
          nearOneFraction ch11FewParams profileAB *
            nearOneFraction ch11MostParams profileBC ∧
        nearOneFraction ch11FewParams profileAB *
            nearOneFraction ch11MostParams profileBC ≤
          ch11FewParams.UPC * ch11MostParams.UPC := by
    simpa [qfmMul] using qfm_syllogism_few_most (q := qfmMul) profileAB profileBC hAB hBC
  have hL : ch11FewParams.LPC * ch11MostParams.LPC = (0.07 : ℝ) := by
    norm_num [ch11FewParams, ch11MostParams]
  have hU : ch11FewParams.UPC * ch11MostParams.UPC = (0.27 : ℝ) := by
    norm_num [ch11FewParams, ch11MostParams]
  constructor
  · simpa [hL] using hProd.1
  · simpa [hU] using hProd.2

/-- `qfmMin` specialization of `MOST ∘ MOST`:
composed score stays in the same MOST interval. -/
theorem qfmMin_syllogism_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11MostParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0.7 : ℝ) ≤
        min (nearOneFraction ch11MostParams profileAB)
            (nearOneFraction ch11MostParams profileBC) ∧
      min (nearOneFraction ch11MostParams profileAB)
          (nearOneFraction ch11MostParams profileBC) ≤
        (0.9 : ℝ) := by
  have h :
      min ch11MostParams.LPC ch11MostParams.LPC ≤
          min (nearOneFraction ch11MostParams profileAB)
              (nearOneFraction ch11MostParams profileBC) ∧
        min (nearOneFraction ch11MostParams profileAB)
            (nearOneFraction ch11MostParams profileBC) ≤
          min ch11MostParams.UPC ch11MostParams.UPC := by
    simpa [qfmMin] using qfm_syllogism_most_most (q := qfmMin) profileAB profileBC hAB hBC
  have hL : min ch11MostParams.LPC ch11MostParams.LPC = (0.7 : ℝ) := by
    norm_num [ch11MostParams]
  have hU : min ch11MostParams.UPC ch11MostParams.UPC = (0.9 : ℝ) := by
    norm_num [ch11MostParams]
  constructor
  · simpa [hL] using h.1
  · simpa [hU] using h.2

/-- `qfmMin` specialization of `FEW ∘ MOST`:
composed score stays in the FEW interval `[0.1,0.3]`. -/
theorem qfmMin_syllogism_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11FewParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0.1 : ℝ) ≤
        min (nearOneFraction ch11FewParams profileAB)
            (nearOneFraction ch11MostParams profileBC) ∧
      min (nearOneFraction ch11FewParams profileAB)
          (nearOneFraction ch11MostParams profileBC) ≤
        (0.3 : ℝ) := by
  have h :
      min ch11FewParams.LPC ch11MostParams.LPC ≤
          min (nearOneFraction ch11FewParams profileAB)
              (nearOneFraction ch11MostParams profileBC) ∧
        min (nearOneFraction ch11FewParams profileAB)
            (nearOneFraction ch11MostParams profileBC) ≤
          min ch11FewParams.UPC ch11MostParams.UPC := by
    simpa [qfmMin] using qfm_syllogism_few_most (q := qfmMin) profileAB profileBC hAB hBC
  have hL : min ch11FewParams.LPC ch11MostParams.LPC = (0.1 : ℝ) := by
    norm_num [ch11FewParams, ch11MostParams]
  have hU : min ch11FewParams.UPC ch11MostParams.UPC = (0.3 : ℝ) := by
    norm_num [ch11FewParams, ch11MostParams]
  constructor
  · simpa [hL] using h.1
  · simpa [hU] using h.2

/-- `qfmLukasiewicz` specialization of `MOST ∘ MOST`. -/
theorem qfmLukasiewicz_syllogism_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11MostParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0.4 : ℝ) ≤
        max 0 (nearOneFraction ch11MostParams profileAB +
          nearOneFraction ch11MostParams profileBC - 1) ∧
      max 0 (nearOneFraction ch11MostParams profileAB +
          nearOneFraction ch11MostParams profileBC - 1) ≤
        (0.8 : ℝ) := by
  have h :
      max 0 (ch11MostParams.LPC + ch11MostParams.LPC - 1) ≤
          max 0 (nearOneFraction ch11MostParams profileAB +
            nearOneFraction ch11MostParams profileBC - 1) ∧
        max 0 (nearOneFraction ch11MostParams profileAB +
            nearOneFraction ch11MostParams profileBC - 1) ≤
          max 0 (ch11MostParams.UPC + ch11MostParams.UPC - 1) := by
    simpa [qfmLukasiewicz] using
      qfm_syllogism_most_most (q := qfmLukasiewicz) profileAB profileBC hAB hBC
  have hL : max 0 (ch11MostParams.LPC + ch11MostParams.LPC - 1) = (0.4 : ℝ) := by
    norm_num [ch11MostParams]
  have hU : max 0 (ch11MostParams.UPC + ch11MostParams.UPC - 1) = (0.8 : ℝ) := by
    norm_num [ch11MostParams]
  constructor
  · simpa [hL] using h.1
  · simpa [hU] using h.2

/-- `qfmLukasiewicz` specialization of `FEW ∘ MOST`. -/
theorem qfmLukasiewicz_syllogism_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11FewParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0 : ℝ) ≤
        max 0 (nearOneFraction ch11FewParams profileAB +
          nearOneFraction ch11MostParams profileBC - 1) ∧
      max 0 (nearOneFraction ch11FewParams profileAB +
          nearOneFraction ch11MostParams profileBC - 1) ≤
        (0.2 : ℝ) := by
  have h :
      max 0 (ch11FewParams.LPC + ch11MostParams.LPC - 1) ≤
          max 0 (nearOneFraction ch11FewParams profileAB +
            nearOneFraction ch11MostParams profileBC - 1) ∧
        max 0 (nearOneFraction ch11FewParams profileAB +
            nearOneFraction ch11MostParams profileBC - 1) ≤
          max 0 (ch11FewParams.UPC + ch11MostParams.UPC - 1) := by
    simpa [qfmLukasiewicz] using
      qfm_syllogism_few_most (q := qfmLukasiewicz) profileAB profileBC hAB hBC
  have hL : max 0 (ch11FewParams.LPC + ch11MostParams.LPC - 1) = (0 : ℝ) := by
    norm_num [ch11FewParams, ch11MostParams]
  have hU : max 0 (ch11FewParams.UPC + ch11MostParams.UPC - 1) = (0.2 : ℝ) := by
    norm_num [ch11FewParams, ch11MostParams]
  constructor
  · calc
      (0 : ℝ) = max 0 (ch11FewParams.LPC + ch11MostParams.LPC - 1) := by simp [hL]
      _ ≤ max 0 (nearOneFraction ch11FewParams profileAB +
            nearOneFraction ch11MostParams profileBC - 1) := h.1
  · simpa [hU] using h.2

/-- `qfmProbSum` specialization of `MOST ∘ MOST`. -/
theorem qfmProbSum_syllogism_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11MostParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0.91 : ℝ) ≤
        (nearOneFraction ch11MostParams profileAB +
          nearOneFraction ch11MostParams profileBC -
          nearOneFraction ch11MostParams profileAB * nearOneFraction ch11MostParams profileBC) ∧
      (nearOneFraction ch11MostParams profileAB +
          nearOneFraction ch11MostParams profileBC -
          nearOneFraction ch11MostParams profileAB * nearOneFraction ch11MostParams profileBC) ≤
        (0.99 : ℝ) := by
  have h :
      (ch11MostParams.LPC + ch11MostParams.LPC - ch11MostParams.LPC * ch11MostParams.LPC) ≤
          (nearOneFraction ch11MostParams profileAB +
            nearOneFraction ch11MostParams profileBC -
            nearOneFraction ch11MostParams profileAB * nearOneFraction ch11MostParams profileBC) ∧
        (nearOneFraction ch11MostParams profileAB +
            nearOneFraction ch11MostParams profileBC -
            nearOneFraction ch11MostParams profileAB * nearOneFraction ch11MostParams profileBC) ≤
          (ch11MostParams.UPC + ch11MostParams.UPC - ch11MostParams.UPC * ch11MostParams.UPC) := by
    simpa [qfmProbSum] using
      qfm_syllogism_most_most (q := qfmProbSum) profileAB profileBC hAB hBC
  have hL : (ch11MostParams.LPC + ch11MostParams.LPC - ch11MostParams.LPC * ch11MostParams.LPC) =
      (0.91 : ℝ) := by
    norm_num [ch11MostParams]
  have hU : (ch11MostParams.UPC + ch11MostParams.UPC - ch11MostParams.UPC * ch11MostParams.UPC) =
      (0.99 : ℝ) := by
    norm_num [ch11MostParams]
  constructor
  · simpa [hL] using h.1
  · simpa [hU] using h.2

/-- `qfmProbSum` specialization of `FEW ∘ MOST`. -/
theorem qfmProbSum_syllogism_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11FewParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0.73 : ℝ) ≤
        (nearOneFraction ch11FewParams profileAB +
          nearOneFraction ch11MostParams profileBC -
          nearOneFraction ch11FewParams profileAB * nearOneFraction ch11MostParams profileBC) ∧
      (nearOneFraction ch11FewParams profileAB +
          nearOneFraction ch11MostParams profileBC -
          nearOneFraction ch11FewParams profileAB * nearOneFraction ch11MostParams profileBC) ≤
        (0.93 : ℝ) := by
  have h :
      (ch11FewParams.LPC + ch11MostParams.LPC - ch11FewParams.LPC * ch11MostParams.LPC) ≤
          (nearOneFraction ch11FewParams profileAB +
            nearOneFraction ch11MostParams profileBC -
            nearOneFraction ch11FewParams profileAB * nearOneFraction ch11MostParams profileBC) ∧
        (nearOneFraction ch11FewParams profileAB +
            nearOneFraction ch11MostParams profileBC -
            nearOneFraction ch11FewParams profileAB * nearOneFraction ch11MostParams profileBC) ≤
          (ch11FewParams.UPC + ch11MostParams.UPC - ch11FewParams.UPC * ch11MostParams.UPC) := by
    simpa [qfmProbSum] using
      qfm_syllogism_few_most (q := qfmProbSum) profileAB profileBC hAB hBC
  have hL :
      (ch11FewParams.LPC + ch11MostParams.LPC - ch11FewParams.LPC * ch11MostParams.LPC) = (0.73 : ℝ) := by
    norm_num [ch11FewParams, ch11MostParams]
  have hU :
      (ch11FewParams.UPC + ch11MostParams.UPC - ch11FewParams.UPC * ch11MostParams.UPC) = (0.93 : ℝ) := by
    norm_num [ch11FewParams, ch11MostParams]
  constructor
  · simpa [hL] using h.1
  · simpa [hU] using h.2

/-- Compact comparison block on common premises (`MOST ∘ MOST`) across QFM instances. -/
theorem qfm_instance_comparison_most_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11MostParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0.49 : ℝ) ≤
        nearOneFraction ch11MostParams profileAB *
          nearOneFraction ch11MostParams profileBC ∧
      nearOneFraction ch11MostParams profileAB *
          nearOneFraction ch11MostParams profileBC ≤
        (0.81 : ℝ) ∧
      (0.7 : ℝ) ≤
        min (nearOneFraction ch11MostParams profileAB)
            (nearOneFraction ch11MostParams profileBC) ∧
      min (nearOneFraction ch11MostParams profileAB)
          (nearOneFraction ch11MostParams profileBC) ≤
        (0.9 : ℝ) ∧
      (0.4 : ℝ) ≤
        max 0 (nearOneFraction ch11MostParams profileAB +
          nearOneFraction ch11MostParams profileBC - 1) ∧
      max 0 (nearOneFraction ch11MostParams profileAB +
          nearOneFraction ch11MostParams profileBC - 1) ≤
        (0.8 : ℝ) ∧
      (0.91 : ℝ) ≤
        (nearOneFraction ch11MostParams profileAB +
          nearOneFraction ch11MostParams profileBC -
          nearOneFraction ch11MostParams profileAB * nearOneFraction ch11MostParams profileBC) ∧
      (nearOneFraction ch11MostParams profileAB +
          nearOneFraction ch11MostParams profileBC -
          nearOneFraction ch11MostParams profileAB * nearOneFraction ch11MostParams profileBC) ≤
        (0.99 : ℝ) := by
  have hMul := zadeh_syllogism_most_most profileAB profileBC hAB hBC
  have hMin := qfmMin_syllogism_most_most profileAB profileBC hAB hBC
  have hLuk := qfmLukasiewicz_syllogism_most_most profileAB profileBC hAB hBC
  have hProb := qfmProbSum_syllogism_most_most profileAB profileBC hAB hBC
  exact ⟨hMul.1, hMul.2, hMin.1, hMin.2, hLuk.1, hLuk.2, hProb.1, hProb.2⟩

/-- Compact comparison block on common premises (`FEW ∘ MOST`) across QFM instances. -/
theorem qfm_instance_comparison_few_most
    (profileAB profileBC : U → ℝ)
    (hAB : fuzzyIntervalHolds ch11FewParams profileAB)
    (hBC : fuzzyIntervalHolds ch11MostParams profileBC) :
    (0.07 : ℝ) ≤
        nearOneFraction ch11FewParams profileAB *
          nearOneFraction ch11MostParams profileBC ∧
      nearOneFraction ch11FewParams profileAB *
          nearOneFraction ch11MostParams profileBC ≤
        (0.27 : ℝ) ∧
      (0.1 : ℝ) ≤
        min (nearOneFraction ch11FewParams profileAB)
            (nearOneFraction ch11MostParams profileBC) ∧
      min (nearOneFraction ch11FewParams profileAB)
          (nearOneFraction ch11MostParams profileBC) ≤
        (0.3 : ℝ) ∧
      (0 : ℝ) ≤
        max 0 (nearOneFraction ch11FewParams profileAB +
          nearOneFraction ch11MostParams profileBC - 1) ∧
      max 0 (nearOneFraction ch11FewParams profileAB +
          nearOneFraction ch11MostParams profileBC - 1) ≤
        (0.2 : ℝ) ∧
      (0.73 : ℝ) ≤
        (nearOneFraction ch11FewParams profileAB +
          nearOneFraction ch11MostParams profileBC -
          nearOneFraction ch11FewParams profileAB * nearOneFraction ch11MostParams profileBC) ∧
      (nearOneFraction ch11FewParams profileAB +
          nearOneFraction ch11MostParams profileBC -
          nearOneFraction ch11FewParams profileAB * nearOneFraction ch11MostParams profileBC) ≤
        (0.93 : ℝ) := by
  have hMul := zadeh_syllogism_few_most profileAB profileBC hAB hBC
  have hMin := qfmMin_syllogism_few_most profileAB profileBC hAB hBC
  have hLuk := qfmLukasiewicz_syllogism_few_most profileAB profileBC hAB hBC
  have hProb := qfmProbSum_syllogism_few_most profileAB profileBC hAB hBC
  exact ⟨hMul.1, hMul.2, hMin.1, hMin.2, hLuk.1, hLuk.2, hProb.1, hProb.2⟩

end Generic

section FiniteCanaries

/-- Uniform high profile on `Fin 4`, used for monotonicity canaries. -/
def allHighFin4 : Fin 4 → ℝ := fun _ => 0.95

/-- Alternate profile with same `nearOne` signature as `threeHighOneLow` under MOST parameters. -/
def mostSignatureAlt : Fin 4 → ℝ := fun u => if u = 0 then 0.2 else 0.91

/-- QFM-style monotonicity canary:
pointwise increase in profile values cannot decrease near-one mass. -/
theorem canary_qfm_monotonicity_most :
    nearOneFraction ch11MostParams threeHighOneLow ≤
      nearOneFraction ch11MostParams allHighFin4 := by
  have hmono :
      fuzzyExistsScore ch11MostParams threeHighOneLow ≤
        fuzzyExistsScore ch11MostParams allHighFin4 := by
    exact fuzzyExistsScore_mono_of_pointwise
      (p := ch11MostParams)
      (profile₁ := threeHighOneLow)
      (profile₂ := allHighFin4)
      (hle := by
        intro u
        fin_cases u <;> (simp [threeHighOneLow, allHighFin4]; try norm_num))
      (hub := by
        intro u
        simp [allHighFin4]
        norm_num)
  simpa [fuzzyExistsScore] using hmono

/-- Generic monotonicity schema instantiated on a finite profile pair. -/
theorem canary_qfm_forall_monotonicity_most :
    fuzzyForAllHolds ch11MostParams threeHighOneLow →
      fuzzyForAllHolds ch11MostParams allHighFin4 := by
  exact fuzzyForAllHolds_mono_of_pointwise
    (p := ch11MostParams)
    (profile₁ := threeHighOneLow)
    (profile₂ := allHighFin4)
    (hle := by
      intro u
      fin_cases u <;> (simp [threeHighOneLow, allHighFin4]; try norm_num))
    (hub := by
      intro u
      simp [allHighFin4]
      norm_num)

/-- QFM-style conservativity canary:
if the `nearOne` signature is unchanged, interval truth is unchanged. -/
theorem canary_qfm_conservativity_same_nearOne_signature :
    nearOneFraction ch11MostParams threeHighOneLow =
      nearOneFraction ch11MostParams mostSignatureAlt ∧
      (fuzzyIntervalHolds ch11MostParams threeHighOneLow ↔
        fuzzyIntervalHolds ch11MostParams mostSignatureAlt) := by
  have hSig :
      ∀ u : Fin 4,
        nearOne ch11MostParams (threeHighOneLow u) ↔ nearOne ch11MostParams (mostSignatureAlt u) := by
    intro u
    fin_cases u <;> (simp [nearOne, threeHighOneLow, mostSignatureAlt, ch11MostParams]; norm_num)
  have hA :
      nearOneFraction ch11MostParams threeHighOneLow =
        nearOneFraction ch11MostParams mostSignatureAlt := by
    exact nearOneFraction_eq_of_signatureEq ch11MostParams threeHighOneLow mostSignatureAlt hSig
  constructor
  · exact hA
  · exact fuzzyIntervalHolds_iff_of_signatureEq ch11MostParams threeHighOneLow mostSignatureAlt hSig

/-- Concrete `MOST ∘ MOST` fixture canary (3/4 composed with 3/4). -/
theorem canary_zadeh_most_most_fixture :
    (0.49 : ℝ) ≤
        nearOneFraction ch11MostParams threeHighOneLow *
          nearOneFraction ch11MostParams threeHighOneLow ∧
      nearOneFraction ch11MostParams threeHighOneLow *
          nearOneFraction ch11MostParams threeHighOneLow ≤
        (0.81 : ℝ) := by
  have hMost : fuzzyIntervalHolds ch11MostParams threeHighOneLow := by
    unfold fuzzyIntervalHolds
    rw [canary_ch11_most_fraction_threeQuarters]
    norm_num [ch11MostParams]
  exact zadeh_syllogism_most_most threeHighOneLow threeHighOneLow hMost hMost

/-- Concrete `FEW ∘ MOST` fixture canary (1/4 composed with 3/4). -/
theorem canary_zadeh_few_most_fixture :
    (0.07 : ℝ) ≤
        nearOneFraction ch11FewParams oneHighThreeLow *
          nearOneFraction ch11MostParams threeHighOneLow ∧
      nearOneFraction ch11FewParams oneHighThreeLow *
          nearOneFraction ch11MostParams threeHighOneLow ≤
        (0.27 : ℝ) := by
  have hFew : fuzzyIntervalHolds ch11FewParams oneHighThreeLow := by
    unfold fuzzyIntervalHolds
    rw [canary_ch11_few_fraction_oneQuarter]
    norm_num [ch11FewParams]
  have hMost : fuzzyIntervalHolds ch11MostParams threeHighOneLow := by
    unfold fuzzyIntervalHolds
    rw [canary_ch11_most_fraction_threeQuarters]
    norm_num [ch11MostParams]
  exact zadeh_syllogism_few_most oneHighThreeLow threeHighOneLow hFew hMost

end FiniteCanaries

end Mettapedia.Logic.PLNFirstOrder
