import Mettapedia.Logic.PLNIndefiniteTruth
import Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-!
# Walley's Binary IDM as a Finite Credal Set

This module gives the binary predictive Imprecise Dirichlet Model a semantic
object, not only a closed-form interval formula.

For finite binary counts `(n⁺, n⁻)` and IDM strength `s > 0`, the binary IDM
predictive credal set contains all Bernoulli predictive distributions

`P(true) = (n⁺ + s t) / (n⁺ + n⁻ + s)` for `t ∈ [0,1]`.

The lower and upper expectations of the true-event gamble are then derived as
the familiar Walley endpoints.
-/

open scoped BigOperators

namespace Mettapedia.Logic.WalleyBinaryIDM

open Mettapedia.ProbabilityTheory.ImpreciseProbability.DesirableGambles

/-! ## The binary predictive credal set -/

/-- The indicator gamble for the positive/true binary outcome. -/
noncomputable def trueGamble : Gamble Bool := fun b => if b = true then 1 else 0

/-- A Bernoulli predictive distribution from a binary IDM prior weight `t ∈ [0,1]`. -/
noncomputable def predictiveDist
    (nPlus nMinus s t : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hs : 0 < s) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ProbDist Bool :=
  let denom := nPlus + nMinus + s
  let pTrue := (nPlus + s * t) / denom
  let pFalse := (nMinus + s * (1 - t)) / denom
  have hden_pos : 0 < denom := by linarith
  have hpTrue_nonneg : 0 ≤ pTrue := by
    unfold pTrue
    exact div_nonneg (by nlinarith [ht.1, hs.le, hPlus]) (le_of_lt hden_pos)
  have hpFalse_nonneg : 0 ≤ pFalse := by
    unfold pFalse
    exact div_nonneg (by nlinarith [sub_nonneg.mpr ht.2, hs.le, hMinus]) (le_of_lt hden_pos)
  {
    prob := fun b => if b = true then pTrue else pFalse
    non_neg := by
      intro b
      by_cases hb : b = true <;> simp [hb, hpTrue_nonneg, hpFalse_nonneg]
    sum_one := by
      rw [show (Finset.univ : Finset Bool) = {false, true} by
        ext b
        cases b <;> simp]
      simp [pTrue, pFalse]
      field_simp [hden_pos.ne']
      ring
  }

@[simp] theorem predictiveDist_prob_true
    (nPlus nMinus s t : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hs : 0 < s) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (predictiveDist nPlus nMinus s t hPlus hMinus hs ht).prob true =
      (nPlus + s * t) / (nPlus + nMinus + s) := by
  simp [predictiveDist]

/-- The positive-outcome gamble's expectation is the distribution's true mass. -/
theorem expectedValue_trueGamble (P : ProbDist Bool) :
    expectedValue P trueGamble = P.prob true := by
  unfold expectedValue trueGamble
  rw [show (Finset.univ : Finset Bool) = {false, true} by
    ext b
    cases b <;> simp]
  simp

theorem predictiveDist_expected_trueGamble
    (nPlus nMinus s t : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus)
    (hs : 0 < s) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    expectedValue (predictiveDist nPlus nMinus s t hPlus hMinus hs ht) trueGamble =
      (nPlus + s * t) / (nPlus + nMinus + s) := by
  rw [expectedValue_trueGamble]
  simp

/-- The binary IDM predictive credal set over `Bool`. -/
noncomputable def credalSet
    (nPlus nMinus s : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus) (hs : 0 < s) :
    CredalSetFinite Bool :=
  {P | ∃ t : ℝ, ∃ ht : t ∈ Set.Icc (0 : ℝ) 1,
      P = predictiveDist nPlus nMinus s t hPlus hMinus hs ht}

noncomputable def lowerEndpoint (nPlus nMinus s : ℝ) : ℝ :=
  nPlus / (nPlus + nMinus + s)

noncomputable def upperEndpoint (nPlus nMinus s : ℝ) : ℝ :=
  (nPlus + s) / (nPlus + nMinus + s)

/-- Every predictive distribution in the binary IDM credal set lies above the
lower endpoint on the true-event gamble. -/
theorem lower_bound_each
    (nPlus nMinus s : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus) (hs : 0 < s)
    {P : ProbDist Bool} (hP : P ∈ credalSet nPlus nMinus s hPlus hMinus hs) :
    lowerEndpoint nPlus nMinus s ≤ expectedValue P trueGamble := by
  rcases hP with ⟨t, ht, rfl⟩
  rw [predictiveDist_expected_trueGamble]
  unfold lowerEndpoint
  have hden : 0 ≤ nPlus + nMinus + s := by linarith
  apply div_le_div_of_nonneg_right ?_ hden
  nlinarith [ht.1, hs.le]

/-- Every predictive distribution in the binary IDM credal set lies below the
upper endpoint on the true-event gamble. -/
theorem upper_bound_each
    (nPlus nMinus s : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus) (hs : 0 < s)
    {P : ProbDist Bool} (hP : P ∈ credalSet nPlus nMinus s hPlus hMinus hs) :
    expectedValue P trueGamble ≤ upperEndpoint nPlus nMinus s := by
  rcases hP with ⟨t, ht, rfl⟩
  rw [predictiveDist_expected_trueGamble]
  unfold upperEndpoint
  have hden : 0 ≤ nPlus + nMinus + s := by linarith
  apply div_le_div_of_nonneg_right ?_ hden
  nlinarith [ht.2, hs.le]

/-- The lower endpoint is attained by the prior extreme `t = 0`. -/
theorem lowerEndpoint_mem_values
    (nPlus nMinus s : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus) (hs : 0 < s) :
    lowerEndpoint nPlus nMinus s ∈
      Set.image (fun P => expectedValue P trueGamble)
        (credalSet nPlus nMinus s hPlus hMinus hs) := by
  refine ⟨predictiveDist nPlus nMinus s 0 hPlus hMinus hs (by norm_num), ?_, ?_⟩
  · exact ⟨0, by norm_num, rfl⟩
  · change expectedValue
      (predictiveDist nPlus nMinus s 0 hPlus hMinus hs (by norm_num))
        trueGamble = lowerEndpoint nPlus nMinus s
    rw [predictiveDist_expected_trueGamble]
    simp [lowerEndpoint]

/-- The upper endpoint is attained by the prior extreme `t = 1`. -/
theorem upperEndpoint_mem_values
    (nPlus nMinus s : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus) (hs : 0 < s) :
    upperEndpoint nPlus nMinus s ∈
      Set.image (fun P => expectedValue P trueGamble)
        (credalSet nPlus nMinus s hPlus hMinus hs) := by
  refine ⟨predictiveDist nPlus nMinus s 1 hPlus hMinus hs (by norm_num), ?_, ?_⟩
  · exact ⟨1, by norm_num, rfl⟩
  · change expectedValue
      (predictiveDist nPlus nMinus s 1 hPlus hMinus hs (by norm_num))
        trueGamble = upperEndpoint nPlus nMinus s
    rw [predictiveDist_expected_trueGamble]
    simp [upperEndpoint]

/-- The credal-set lower expectation derives Walley's binary IDM lower endpoint. -/
theorem lowerProb_trueGamble_eq
    (nPlus nMinus s : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus) (hs : 0 < s) :
    lowerProb (credalSet nPlus nMinus s hPlus hMinus hs) trueGamble =
      lowerEndpoint nPlus nMinus s := by
  unfold lowerProb
  let values := Set.image (fun P => expectedValue P trueGamble)
        (credalSet nPlus nMinus s hPlus hMinus hs)
  have hmem : lowerEndpoint nPlus nMinus s ∈ values :=
    lowerEndpoint_mem_values nPlus nMinus s hPlus hMinus hs
  have hbdd : BddBelow values := by
    refine ⟨lowerEndpoint nPlus nMinus s, ?_⟩
    intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact lower_bound_each nPlus nMinus s hPlus hMinus hs hP
  have hnonempty : values.Nonempty := ⟨lowerEndpoint nPlus nMinus s, hmem⟩
  apply le_antisymm
  · exact csInf_le hbdd hmem
  · apply le_csInf hnonempty
    intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact lower_bound_each nPlus nMinus s hPlus hMinus hs hP

/-- The credal-set upper expectation derives Walley's binary IDM upper endpoint. -/
theorem upperProb_trueGamble_eq
    (nPlus nMinus s : ℝ) (hPlus : 0 ≤ nPlus) (hMinus : 0 ≤ nMinus) (hs : 0 < s) :
    upperProb (credalSet nPlus nMinus s hPlus hMinus hs) trueGamble =
      upperEndpoint nPlus nMinus s := by
  unfold upperProb
  let values := Set.image (fun P => expectedValue P trueGamble)
        (credalSet nPlus nMinus s hPlus hMinus hs)
  have hmem : upperEndpoint nPlus nMinus s ∈ values :=
    upperEndpoint_mem_values nPlus nMinus s hPlus hMinus hs
  have hbdd : BddAbove values := by
    refine ⟨upperEndpoint nPlus nMinus s, ?_⟩
    intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact upper_bound_each nPlus nMinus s hPlus hMinus hs hP
  have hnonempty : values.Nonempty := ⟨upperEndpoint nPlus nMinus s, hmem⟩
  apply le_antisymm
  · apply csSup_le hnonempty
    intro y hy
    rcases hy with ⟨P, hP, rfl⟩
    exact upper_bound_each nPlus nMinus s hPlus hMinus hs hP
  · exact le_csSup hbdd hmem

/-! ## Bridge to the existing `ITV.fromWalleyIDMPredictive` constructor -/

open Mettapedia.Logic.EvidenceQuantale

/-- The binary IDM credal set induced by existing `BinaryEvidence` counts. -/
noncomputable def credalSetOfEvidence (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    CredalSetFinite Bool :=
  credalSet e.pos.toReal e.neg.toReal s
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hs

theorem lowerProb_credalSetOfEvidence_eq_itv_lower
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    lowerProb (credalSetOfEvidence e s hs) trueGamble =
      (Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive e s hs).lower := by
  unfold credalSetOfEvidence
  rw [lowerProb_trueGamble_eq]
  rw [Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive_lower]
  rfl

theorem upperProb_credalSetOfEvidence_eq_itv_upper
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    upperProb (credalSetOfEvidence e s hs) trueGamble =
      (Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive e s hs).upper := by
  unfold credalSetOfEvidence
  rw [upperProb_trueGamble_eq]
  rw [Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive_upper]
  rfl

/-- The existing Walley ITV constructor is exactly the true-event envelope of
the binary IDM credal set, together with the separate evidence-concentration
coordinate. -/
theorem credal_envelope_matches_Walley_ITV_bounds
    (e : BinaryEvidence) (s : ℝ) (hs : 0 < s) :
    lowerProb (credalSetOfEvidence e s hs) trueGamble =
        (Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive e s hs).lower ∧
      upperProb (credalSetOfEvidence e s hs) trueGamble =
        (Mettapedia.Logic.PLNIndefiniteTruth.ITV.fromWalleyIDMPredictive e s hs).upper :=
  ⟨lowerProb_credalSetOfEvidence_eq_itv_lower e s hs,
    upperProb_credalSetOfEvidence_eq_itv_upper e s hs⟩

end Mettapedia.Logic.WalleyBinaryIDM
