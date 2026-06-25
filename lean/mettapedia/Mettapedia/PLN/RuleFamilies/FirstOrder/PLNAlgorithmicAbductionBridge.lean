import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNInductionAbductionITVBridge
import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.IntensionalInheritanceSolomonoffBridge

/-!
# Algorithmic-Prior Abduction Ranking

`Truth_Abduction` supplies an inverse-deduction point estimate.  Explanation
selection also needs a prior over hypotheses.  This file gives the narrow
bridge used by WM-PLN:

* the prior-weighted interval is just the existing abduction interval scaled by
  a supplied hypothesis prior;
* when that prior is supplied by the universal-mixture/Solomonoff bridge, this
  is an algorithmic-prior explanation score;
* finite description-length weights give small executable canaries.

The file does not claim that a point score is tight.  Robust ranking is by
separated prior-weighted intervals.
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder

open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
open Mettapedia.KR.ConceptGeometry.IntensionalInheritance

/-- A simple finite description-length prior used for executable canaries:
`2^{-k}`.  The full universal-mixture prior is provided separately by
`priorFromConditional`. -/
noncomputable def descriptionLengthPrior (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ k

noncomputable def priorWeightedPoint (prior point : ℝ) : ℝ :=
  prior * point

noncomputable def priorWeightedLower (prior : ℝ) (itv : ITV) : ℝ :=
  prior * itv.lower

noncomputable def priorWeightedUpper (prior : ℝ) (itv : ITV) : ℝ :=
  prior * itv.upper

/-- Robust explanation ranking after applying hypothesis priors. -/
def priorWeightedIntervalStrictlyRanks
    (betterPrior worsePrior : ℝ) (better worse : ITV) : Prop :=
  priorWeightedUpper worsePrior worse < priorWeightedLower betterPrior better

/-- Prior-weighted intervals overlap when the weighted credal evidence still
does not justify a strict explanation ranking. -/
def priorWeightedIntervalsOverlap
    (xPrior yPrior : ℝ) (x y : ITV) : Prop :=
  priorWeightedLower xPrior x ≤ priorWeightedUpper yPrior y ∧
    priorWeightedLower yPrior y ≤ priorWeightedUpper xPrior x

/-- A strict prior-weighted interval ranking is sound for every pair of point
values selected from the ranked intervals, as long as the priors are
nonnegative.  This is the algorithmic-prior version of
`abductionIntervalStrictlyRanks_point_lt`. -/
theorem priorWeightedIntervalStrictlyRanks_point_lt
    {betterPrior worsePrior : ℝ} {better worse : ITV}
    {betterPoint worsePoint : ℝ}
    (hBetterPrior : 0 ≤ betterPrior)
    (hWorsePrior : 0 ≤ worsePrior)
    (hRank :
      priorWeightedIntervalStrictlyRanks
        betterPrior worsePrior better worse)
    (hBetter :
      better.lower ≤ betterPoint ∧ betterPoint ≤ better.upper)
    (hWorse :
      worse.lower ≤ worsePoint ∧ worsePoint ≤ worse.upper) :
    priorWeightedPoint worsePrior worsePoint <
      priorWeightedPoint betterPrior betterPoint := by
  unfold priorWeightedIntervalStrictlyRanks priorWeightedPoint
    priorWeightedLower priorWeightedUpper at *
  have hWorseLe :
      worsePrior * worsePoint ≤ worsePrior * worse.upper :=
    mul_le_mul_of_nonneg_left hWorse.2 hWorsePrior
  have hBetterLe :
      betterPrior * better.lower ≤ betterPrior * betterPoint :=
    mul_le_mul_of_nonneg_left hBetter.1 hBetterPrior
  linarith

/-- Universal-mixture prior-weighted lower endpoint.  This is the hook from
algorithmic/intensional explanation priors into the already-built abduction
interval surface. -/
noncomputable def universalMixtureAbductionLower
    (ξ : Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Semimeasure)
    (ctx hypothesis : Mettapedia.KR.ConceptGeometry.IntensionalInheritance.BinString)
    (itv : ITV) : ℝ :=
  priorWeightedLower (priorFromConditional ξ ctx hypothesis) itv

/-- Universal-mixture prior-weighted upper endpoint. -/
noncomputable def universalMixtureAbductionUpper
    (ξ : Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Semimeasure)
    (ctx hypothesis : Mettapedia.KR.ConceptGeometry.IntensionalInheritance.BinString)
    (itv : ITV) : ℝ :=
  priorWeightedUpper (priorFromConditional ξ ctx hypothesis) itv

/-- Universal-mixture priors are nonnegative after flattening to real values. -/
theorem priorFromConditional_nonneg
    (ξ : Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Semimeasure)
    (ctx hypothesis : Mettapedia.KR.ConceptGeometry.IntensionalInheritance.BinString) :
    0 ≤ priorFromConditional ξ ctx hypothesis :=
  ENNReal.toReal_nonneg

/-- A separated universal-mixture-prior interval ranking is sound for every
selected point inside the ranked intervals.

This is the load-bearing Solomonoff-facing version of the ranking discipline:
the prior comes from `priorFromConditional`, but the uncertainty calculus is
still the existing abduction ITV surface. -/
theorem universalMixtureAbduction_interval_rank_point_lt
    {ξ : Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Semimeasure}
    {ctx betterHypothesis worseHypothesis :
      Mettapedia.KR.ConceptGeometry.IntensionalInheritance.BinString}
    {better worse : ITV} {betterPoint worsePoint : ℝ}
    (hRank :
      universalMixtureAbductionUpper ξ ctx worseHypothesis worse <
        universalMixtureAbductionLower ξ ctx betterHypothesis better)
    (hBetter :
      better.lower ≤ betterPoint ∧ betterPoint ≤ better.upper)
    (hWorse :
      worse.lower ≤ worsePoint ∧ worsePoint ≤ worse.upper) :
    priorWeightedPoint (priorFromConditional ξ ctx worseHypothesis) worsePoint <
      priorWeightedPoint (priorFromConditional ξ ctx betterHypothesis)
        betterPoint := by
  exact priorWeightedIntervalStrictlyRanks_point_lt
    (priorFromConditional_nonneg ξ ctx betterHypothesis)
    (priorFromConditional_nonneg ξ ctx worseHypothesis)
    (by
      simpa [priorWeightedIntervalStrictlyRanks,
        universalMixtureAbductionLower, universalMixtureAbductionUpper])
    hBetter hWorse

/-- Canonical geometric-mixture specialization of
`universalMixtureAbduction_interval_rank_point_lt`.

This is the concrete Chapter-3 mixture surface: the ranking prior is no longer
an abstract `ξ`, but the geometric universal mixture `xiGeomSemimeasure`. -/
theorem xiGeomAbduction_interval_rank_point_lt
    {ν : ℕ → Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Semimeasure}
    {ctx betterHypothesis worseHypothesis :
      Mettapedia.KR.ConceptGeometry.IntensionalInheritance.BinString}
    {better worse : ITV} {betterPoint worsePoint : ℝ}
    (hRank :
      universalMixtureAbductionUpper
          (Mettapedia.UniversalAI.UniversalPrediction.xiGeomSemimeasure ν)
          ctx worseHypothesis worse <
        universalMixtureAbductionLower
          (Mettapedia.UniversalAI.UniversalPrediction.xiGeomSemimeasure ν)
          ctx betterHypothesis better)
    (hBetter :
      better.lower ≤ betterPoint ∧ betterPoint ≤ better.upper)
    (hWorse :
      worse.lower ≤ worsePoint ∧ worsePoint ≤ worse.upper) :
    priorWeightedPoint
        (priorFromConditional
          (Mettapedia.UniversalAI.UniversalPrediction.xiGeomSemimeasure ν)
          ctx worseHypothesis)
        worsePoint <
      priorWeightedPoint
        (priorFromConditional
          (Mettapedia.UniversalAI.UniversalPrediction.xiGeomSemimeasure ν)
          ctx betterHypothesis)
        betterPoint :=
  universalMixtureAbduction_interval_rank_point_lt
    hRank hBetter hWorse

/-- Prefix-complexity universal-mixture specialization of
`universalMixtureAbduction_interval_rank_point_lt`.

This is the machine-indexed Solomonoff-facing surface using the `2^{-Kpf}`
mixture.  Machine-independence constants live in `UniversalPrediction`; this
theorem only states the robust ranking rule once the chosen `xiKpf` prior
separates the candidate intervals. -/
theorem xiKpfAbduction_interval_rank_point_lt
    {U : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine}
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM U]
    {ν : Mettapedia.KR.ConceptGeometry.IntensionalInheritance.BinString →
      Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Semimeasure}
    {ctx betterHypothesis worseHypothesis :
      Mettapedia.KR.ConceptGeometry.IntensionalInheritance.BinString}
    {better worse : ITV} {betterPoint worsePoint : ℝ}
    (hRank :
      universalMixtureAbductionUpper
          (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
            (U := U) ν)
          ctx worseHypothesis worse <
        universalMixtureAbductionLower
          (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
            (U := U) ν)
          ctx betterHypothesis better)
    (hBetter :
      better.lower ≤ betterPoint ∧ betterPoint ≤ better.upper)
    (hWorse :
      worse.lower ≤ worsePoint ∧ worsePoint ≤ worse.upper) :
    priorWeightedPoint
        (priorFromConditional
          (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
            (U := U) ν)
          ctx worseHypothesis)
        worsePoint <
      priorWeightedPoint
        (priorFromConditional
          (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
            (U := U) ν)
          ctx betterHypothesis)
        betterPoint :=
  universalMixtureAbduction_interval_rank_point_lt
    hRank hBetter hWorse

/-- Prefix-complexity universal mixtures give comparable conditional priors
across universal prefix-free machines, up to the usual pair of invariance
constants.

This is intentionally weaker than a ranking-invariance theorem.  It consumes
the raw `xiKpfSemimeasure_mul_le_of_invariance` theorem at the conditional
prior surface and says that changing universal machines rescales the
conditional prior by a bounded multiplicative factor.  A robust abduction
ranking across machines still needs an explicit separation margin large enough
to absorb that factor. -/
theorem xiKpfConditionalENN_mul_le_of_invariance
    (U V : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine)
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM U]
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM V]
    (ν : Mettapedia.UniversalAI.UniversalPrediction.BinString →
      Mettapedia.UniversalAI.UniversalPrediction.Semimeasure) :
    ∃ c d : ℕ, ∀ ctx hyp : Mettapedia.UniversalAI.UniversalPrediction.BinString,
      (((2 : ENNReal) ^ (-(c : ℤ))) *
          ((2 : ENNReal) ^ (-(d : ℤ)))) *
          Mettapedia.UniversalAI.UniversalPrediction.conditionalENN
            (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
              (U := V) ν)
            hyp ctx ≤
        Mettapedia.UniversalAI.UniversalPrediction.conditionalENN
          (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
            (U := U) ν)
          hyp ctx := by
  classical
  obtain ⟨c, hc⟩ :=
    Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure_mul_le_of_invariance
      (U := U) (V := V) ν
  obtain ⟨d, hd⟩ :=
    Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure_mul_le_of_invariance
      (U := V) (V := U) ν
  refine ⟨c, d, ?_⟩
  intro ctx hyp
  let a : ENNReal := (2 : ENNReal) ^ (-(c : ℤ))
  let b : ENNReal := (2 : ENNReal) ^ (-(d : ℤ))
  let μU : Mettapedia.UniversalAI.UniversalPrediction.Semimeasure :=
    Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure (U := U) ν
  let μV : Mettapedia.UniversalAI.UniversalPrediction.Semimeasure :=
    Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure (U := V) ν
  have hnum : a * μV (ctx ++ hyp) ≤ μU (ctx ++ hyp) := by
    simpa [a, μU, μV] using hc (ctx ++ hyp)
  have hden : b * μU ctx ≤ μV ctx := by
    simpa [b, μU, μV] using hd ctx
  have hb0 : b ≠ 0 := by
    exact (ENNReal.zpow_pos (a := (2 : ENNReal)) (by norm_num)
      (by simp) (-(d : ℤ))).ne'
  have hbTop : b ≠ ⊤ := by
    exact ENNReal.zpow_ne_top (a := (2 : ENNReal)) (by norm_num)
      (by simp) (-(d : ℤ))
  have hnumB : (a * b) * μV (ctx ++ hyp) ≤ b * μU (ctx ++ hyp) := by
    calc
      (a * b) * μV (ctx ++ hyp) = b * (a * μV (ctx ++ hyp)) := by
        ac_rfl
      _ ≤ b * μU (ctx ++ hyp) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_left hnum b
  have hdiv := ENNReal.div_le_div hnumB hden
  have hright :
      (b * μU (ctx ++ hyp)) / (b * μU ctx) =
        μU (ctx ++ hyp) / μU ctx := by
    simpa using
      (ENNReal.mul_div_mul_left
        (a := μU (ctx ++ hyp)) (b := μU ctx) (c := b) hb0 hbTop)
  calc
    (a * b) *
        Mettapedia.UniversalAI.UniversalPrediction.conditionalENN μV hyp ctx
        = ((a * b) * μV (ctx ++ hyp)) / μV ctx := by
            simp [Mettapedia.UniversalAI.UniversalPrediction.conditionalENN,
              div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ (b * μU (ctx ++ hyp)) / (b * μU ctx) := hdiv
    _ = μU (ctx ++ hyp) / μU ctx := hright
    _ = Mettapedia.UniversalAI.UniversalPrediction.conditionalENN μU hyp ctx := by
        simp [Mettapedia.UniversalAI.UniversalPrediction.conditionalENN]

/-- A semimeasure conditional is always bounded above by `1`. -/
theorem conditionalENN_le_one
    (μ : Mettapedia.UniversalAI.UniversalPrediction.Semimeasure)
    (ctx hyp : Mettapedia.UniversalAI.UniversalPrediction.BinString) :
    Mettapedia.UniversalAI.UniversalPrediction.conditionalENN μ hyp ctx ≤ 1 := by
  by_cases hctx : μ ctx = 0
  · simp [Mettapedia.UniversalAI.UniversalPrediction.conditionalENN_eq_zero_of_eq_zero
      μ ctx hyp hctx]
  · have hctxTop : μ ctx ≠ ⊤ :=
      Mettapedia.UniversalAI.UniversalPrediction.semimeasure_ne_top μ ctx
    unfold Mettapedia.UniversalAI.UniversalPrediction.conditionalENN
    rw [ENNReal.div_le_iff hctx hctxTop]
    simpa using μ.mono_append ctx hyp

/-- A semimeasure conditional never evaluates to `∞`. -/
theorem conditionalENN_ne_top
    (μ : Mettapedia.UniversalAI.UniversalPrediction.Semimeasure)
    (ctx hyp : Mettapedia.UniversalAI.UniversalPrediction.BinString) :
    Mettapedia.UniversalAI.UniversalPrediction.conditionalENN μ hyp ctx ≠ ⊤ := by
  exact ne_top_of_le_ne_top (by simp) (conditionalENN_le_one μ ctx hyp)

/-- Real-valued multiplicative factor obtained from two prefix-complexity
invariance constants. -/
noncomputable def xiKpfMachineFactor (c d : ℕ) : ℝ :=
  (((2 : ENNReal) ^ (-(c : ℤ))).toReal *
    ((2 : ENNReal) ^ (-(d : ℤ))).toReal)

/-- The real machine factor is strictly positive. -/
theorem xiKpfMachineFactor_pos (c d : ℕ) :
    0 < xiKpfMachineFactor c d := by
  unfold xiKpfMachineFactor
  have hc0 : (2 : ENNReal) ^ (-(c : ℤ)) ≠ 0 :=
    (ENNReal.zpow_pos (a := (2 : ENNReal)) (by norm_num)
      (by simp) (-(c : ℤ))).ne'
  have hcTop : (2 : ENNReal) ^ (-(c : ℤ)) ≠ ⊤ :=
    ENNReal.zpow_ne_top (a := (2 : ENNReal)) (by norm_num)
      (by simp) (-(c : ℤ))
  have hd0 : (2 : ENNReal) ^ (-(d : ℤ)) ≠ 0 :=
    (ENNReal.zpow_pos (a := (2 : ENNReal)) (by norm_num)
      (by simp) (-(d : ℤ))).ne'
  have hdTop : (2 : ENNReal) ^ (-(d : ℤ)) ≠ ⊤ :=
    ENNReal.zpow_ne_top (a := (2 : ENNReal)) (by norm_num)
      (by simp) (-(d : ℤ))
  exact mul_pos (ENNReal.toReal_pos hc0 hcTop)
    (ENNReal.toReal_pos hd0 hdTop)

/-- Prefix-complexity universal mixtures give comparable real-valued
conditional priors across universal prefix-free machines.

This is the `priorFromConditional` readout of
`xiKpfConditionalENN_mul_le_of_invariance`, so it is the version consumed by the
real-valued abduction-ranking surface. -/
theorem xiKpfPriorFromConditional_mul_le_of_invariance
    (U V : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine)
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM U]
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM V]
    (ν : Mettapedia.UniversalAI.UniversalPrediction.BinString →
      Mettapedia.UniversalAI.UniversalPrediction.Semimeasure) :
    ∃ c d : ℕ, ∀ ctx hyp : Mettapedia.UniversalAI.UniversalPrediction.BinString,
      xiKpfMachineFactor c d *
          priorFromConditional
            (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
              (U := V) ν)
            ctx hyp ≤
        priorFromConditional
          (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
            (U := U) ν)
          ctx hyp := by
  obtain ⟨c, d, h⟩ := xiKpfConditionalENN_mul_le_of_invariance U V ν
  refine ⟨c, d, ?_⟩
  intro ctx hyp
  have htop :
      Mettapedia.UniversalAI.UniversalPrediction.conditionalENN
          (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
            (U := U) ν)
          hyp ctx ≠ ⊤ :=
    conditionalENN_ne_top
      (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
        (U := U) ν)
      ctx hyp
  have hreal := ENNReal.toReal_mono htop (h ctx hyp)
  simpa [xiKpfMachineFactor, priorFromConditional, ENNReal.toReal_mul,
    mul_assoc, mul_left_comm, mul_comm] using hreal

/-- A robust abduction ranking survives a change of universal prefix-free
machine when the old-machine margin is large enough to absorb the two
machine-invariance factors.

The hypothesis is deliberately stated as a margin condition, not as automatic
ranking invariance: the worse candidate is allowed to grow by the reverse
machine factor, while the better candidate is only protected by the forward
factor.  This is the honest ranking form of
`xiKpfPriorFromConditional_mul_le_of_invariance`. -/
theorem xiKpfAbduction_interval_rank_of_machine_margin
    (U V : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine)
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM U]
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM V]
    (ν : Mettapedia.UniversalAI.UniversalPrediction.BinString →
      Mettapedia.UniversalAI.UniversalPrediction.Semimeasure) :
    ∃ cUV dUV cVU dVU : ℕ,
      ∀ (ctx betterHypothesis worseHypothesis :
          Mettapedia.UniversalAI.UniversalPrediction.BinString)
        (better worse : ITV),
        0 ≤ worse.upper → 0 ≤ better.lower →
        ((priorFromConditional
              (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                (U := V) ν)
              ctx worseHypothesis /
              xiKpfMachineFactor cVU dVU) * worse.upper <
            (xiKpfMachineFactor cUV dUV *
              priorFromConditional
                (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                  (U := V) ν)
                ctx betterHypothesis) * better.lower) →
        universalMixtureAbductionUpper
            (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
              (U := U) ν)
            ctx worseHypothesis worse <
          universalMixtureAbductionLower
            (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
              (U := U) ν)
            ctx betterHypothesis better := by
  obtain ⟨cUV, dUV, hUV⟩ :=
    xiKpfPriorFromConditional_mul_le_of_invariance U V ν
  obtain ⟨cVU, dVU, hVU⟩ :=
    xiKpfPriorFromConditional_mul_le_of_invariance V U ν
  refine ⟨cUV, dUV, cVU, dVU, ?_⟩
  intro ctx betterHypothesis worseHypothesis better worse
    hWorseUpper hBetterLower hMargin
  let ξU := Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
    (U := U) ν
  let ξV := Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
    (U := V) ν
  let fUV := xiKpfMachineFactor cUV dUV
  let fVU := xiKpfMachineFactor cVU dVU
  have hBetterPrior :
      fUV * priorFromConditional ξV ctx betterHypothesis ≤
        priorFromConditional ξU ctx betterHypothesis := by
    simpa [fUV, ξU, ξV] using hUV ctx betterHypothesis
  have hWorsePriorScaled :
      fVU * priorFromConditional ξU ctx worseHypothesis ≤
        priorFromConditional ξV ctx worseHypothesis := by
    simpa [fVU, ξU, ξV] using hVU ctx worseHypothesis
  have hfVUpos : 0 < fVU := by
    simpa [fVU] using xiKpfMachineFactor_pos cVU dVU
  have hWorsePrior :
      priorFromConditional ξU ctx worseHypothesis ≤
        priorFromConditional ξV ctx worseHypothesis / fVU := by
    exact (le_div_iff₀' hfVUpos).2 hWorsePriorScaled
  have hWorseWeighted :
      priorFromConditional ξU ctx worseHypothesis * worse.upper ≤
        (priorFromConditional ξV ctx worseHypothesis / fVU) *
          worse.upper :=
    mul_le_mul_of_nonneg_right hWorsePrior hWorseUpper
  have hBetterWeighted :
      (fUV * priorFromConditional ξV ctx betterHypothesis) *
          better.lower ≤
        priorFromConditional ξU ctx betterHypothesis * better.lower :=
    mul_le_mul_of_nonneg_right hBetterPrior hBetterLower
  unfold universalMixtureAbductionUpper universalMixtureAbductionLower
    priorWeightedUpper priorWeightedLower
  exact lt_of_le_of_lt hWorseWeighted
    (lt_of_lt_of_le (by simpa [fUV, fVU, ξV] using hMargin)
      hBetterWeighted)

/-- Point-readout corollary of
`xiKpfAbduction_interval_rank_of_machine_margin`.

If the old-machine margin is strong enough to survive the universal-machine
distortion constants, then every selected point from the worse new-machine
interval is below every selected point from the better new-machine interval.
This is the downstream search-facing form: point scores may be read out only
after the interval margin has done the real work. -/
theorem xiKpfAbduction_point_rank_of_machine_margin
    (U V : Mettapedia.UniversalAI.SolomonoffPrior.PrefixFreeMachine)
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM U]
    [Mettapedia.UniversalAI.SolomonoffPrior.UniversalPFM V]
    (ν : Mettapedia.UniversalAI.UniversalPrediction.BinString →
      Mettapedia.UniversalAI.UniversalPrediction.Semimeasure) :
    ∃ cUV dUV cVU dVU : ℕ,
      ∀ (ctx betterHypothesis worseHypothesis :
          Mettapedia.UniversalAI.UniversalPrediction.BinString)
        (better worse : ITV) {betterPoint worsePoint : ℝ},
        0 ≤ worse.upper → 0 ≤ better.lower →
        ((priorFromConditional
              (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                (U := V) ν)
              ctx worseHypothesis /
              xiKpfMachineFactor cVU dVU) * worse.upper <
            (xiKpfMachineFactor cUV dUV *
              priorFromConditional
                (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                  (U := V) ν)
                ctx betterHypothesis) * better.lower) →
        better.lower ≤ betterPoint ∧ betterPoint ≤ better.upper →
        worse.lower ≤ worsePoint ∧ worsePoint ≤ worse.upper →
        priorWeightedPoint
            (priorFromConditional
              (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                (U := U) ν)
              ctx worseHypothesis)
            worsePoint <
          priorWeightedPoint
            (priorFromConditional
              (Mettapedia.UniversalAI.UniversalPrediction.xiKpfSemimeasure
                (U := U) ν)
              ctx betterHypothesis)
            betterPoint := by
  obtain ⟨cUV, dUV, cVU, dVU, hRank⟩ :=
    xiKpfAbduction_interval_rank_of_machine_margin U V ν
  refine ⟨cUV, dUV, cVU, dVU, ?_⟩
  intro ctx betterHypothesis worseHypothesis better worse betterPoint worsePoint
    hWorseUpper hBetterLower hMargin hBetter hWorse
  exact universalMixtureAbduction_interval_rank_point_lt
    (hRank ctx betterHypothesis worseHypothesis better worse
      hWorseUpper hBetterLower hMargin)
    hBetter hWorse

/-- Positive canary: an algorithmic prior can reverse point-only abduction and
also justify a robust interval ranking when the prior-weighted intervals are
separated.

Here the simpler candidate has raw point `3/4` and interval `[1/2,1]`; the
more complex candidate has stronger raw point `5/6` and interval `[2/3,1]`.
With description-length priors `2^{-1}` and `2^{-4}`, the simpler explanation
strictly wins after prior weighting. -/
theorem algorithmicPriorAbduction_strict_interval_rank_canary :
    descriptionLengthPrior 1 = (1 / 2 : ℝ) ∧
      descriptionLengthPrior 4 = (1 / 16 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (3 / 4 : ℝ) ∧
      plnAbductionStrength
          (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (5 / 6 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) <
        plnAbductionStrength
          (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) =
        (3 / 8 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 4)
          (plnAbductionStrength
            (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) =
        (5 / 96 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 4)
          (plnAbductionStrength
            (2 / 3 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) <
        priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) ∧
      priorWeightedLower (descriptionLengthPrior 1)
          abductionSearchBetterPointITV =
        (1 / 4 : ℝ) ∧
      priorWeightedUpper (descriptionLengthPrior 1)
          abductionSearchBetterPointITV =
        (1 / 2 : ℝ) ∧
      priorWeightedLower (descriptionLengthPrior 4)
          abductionSearchStrongITV =
        (1 / 24 : ℝ) ∧
      priorWeightedUpper (descriptionLengthPrior 4)
          abductionSearchStrongITV =
        (1 / 16 : ℝ) ∧
      priorWeightedIntervalStrictlyRanks
        (descriptionLengthPrior 1) (descriptionLengthPrior 4)
        abductionSearchBetterPointITV abductionSearchStrongITV := by
  norm_num [descriptionLengthPrior, priorWeightedPoint, priorWeightedLower,
    priorWeightedUpper, priorWeightedIntervalStrictlyRanks,
    abductionSearchBetterPointITV, abductionSearchStrongITV,
    plnAbductionCredalStrengthITV, deductionCredalStrengthITV,
    deductionCredalStrengthLower, deductionCredalStrengthUpper,
    deductionCredalJointLower, deductionCredalJointUpper,
    deductionBBranchLower, deductionBBranchUpper,
    deductionNotBBranchLower, deductionNotBBranchUpper,
    deductionJointAB, deductionJointBC, bayesInversion, plnAbductionStrength,
    plnDeductionStrength]

/-- Negative canary: a description-length prior may flip point scores while
the prior-weighted intervals still overlap.  In that case the system should
record ambiguity, not a robust best explanation. -/
theorem algorithmicPriorAbduction_point_flip_not_interval_rank_canary :
    plnAbductionStrength
        (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) =
      (1 / 2 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) =
        (3 / 4 : ℝ) ∧
      plnAbductionStrength
          (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) <
        plnAbductionStrength
          (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)) =
        (1 / 4 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 2)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) =
        (3 / 16 : ℝ) ∧
      priorWeightedPoint (descriptionLengthPrior 2)
          (plnAbductionStrength
            (1 / 2 : ℝ) (2 / 3 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (3 / 4 : ℝ)) <
        priorWeightedPoint (descriptionLengthPrior 1)
          (plnAbductionStrength
            (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
      priorWeightedIntervalsOverlap
        (descriptionLengthPrior 1) (descriptionLengthPrior 2)
        abductionSearchOpenITV abductionSearchBetterPointITV ∧
      ¬ priorWeightedIntervalStrictlyRanks
        (descriptionLengthPrior 1) (descriptionLengthPrior 2)
        abductionSearchOpenITV abductionSearchBetterPointITV ∧
      ¬ priorWeightedIntervalStrictlyRanks
        (descriptionLengthPrior 2) (descriptionLengthPrior 1)
        abductionSearchBetterPointITV abductionSearchOpenITV := by
  norm_num [descriptionLengthPrior, priorWeightedPoint, priorWeightedLower,
    priorWeightedUpper, priorWeightedIntervalsOverlap,
    priorWeightedIntervalStrictlyRanks, abductionSearchOpenITV,
    abductionSearchBetterPointITV, plnAbductionCredalStrengthITV,
    deductionCredalStrengthITV, deductionCredalStrengthLower,
    deductionCredalStrengthUpper, deductionCredalJointLower,
    deductionCredalJointUpper, deductionBBranchLower, deductionBBranchUpper,
    deductionNotBBranchLower, deductionNotBBranchUpper, deductionJointAB,
    deductionJointBC, bayesInversion, plnAbductionStrength,
    plnDeductionStrength]

end Mettapedia.PLN.RuleFamilies.FirstOrder
