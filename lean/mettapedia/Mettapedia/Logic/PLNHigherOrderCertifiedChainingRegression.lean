import Mathlib.Tactic
import Mettapedia.Logic.PLNGWASHigherOrderBridge
import Mettapedia.Logic.PLNHigherOrderCalibrationContracts
import Mettapedia.Logic.PLNVarianceChainNoGo

/-!
# Higher-Order Certified Chaining Regression

Concrete canaries for the certified 2nd/3rd-order chaining layer.

The point is to show that the new certified-estimate / chain-bound / decision
theorems land on actual finite examples:

- a certified continuation example,
- a reveal-preference example,
- a fallback-preference example,
- an abstention example,
- and one GWAS-shaped higher-order example.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNRegimeMixtureTheorems

/-! ## Small finite regime canary -/

inductive DemoRegime where
  | focused
  | alternate
  deriving DecidableEq, Fintype, Repr

theorem demoRegime_univ :
    (Finset.univ : Finset DemoRegime) = {DemoRegime.focused, DemoRegime.alternate} := by
  ext r
  cases r <;> simp

noncomputable def demoPosterior : CertifiedRegimePosterior DemoRegime where
  weights
    | .focused => 3 / 4
    | .alternate => 1 / 4
  valid := by
    constructor
    · intro r
      cases r <;> norm_num
    · rw [demoRegime_univ]
      simp
      norm_num
  uncertaintyRadius := 1 / 20
  uncertaintyRadius_nonneg := by norm_num

def demoBranchValues : DemoRegime → ℝ
  | .focused => 1
  | .alternate => 0

noncomputable def continueAdmissibility : CertifiedAdmissibilityEstimate where
  lower := 4 / 5
  upper := 9 / 10
  coverage := 19 / 20
  errorBound := 1 / 50
  lower_nonneg := by norm_num
  upper_le_one := by norm_num
  lower_le_upper := by norm_num
  coverage_nonneg := by norm_num
  coverage_le_one := by norm_num
  errorBound_nonneg := by norm_num

noncomputable def continueTrust : CertifiedTrustEstimate where
  lower := 9 / 10
  upper := 1
  coverage := 19 / 20
  disagreementPenalty := 1 / 100
  fragilityPenalty := 1 / 100
  lower_nonneg := by norm_num
  upper_le_one := by norm_num
  lower_le_upper := by norm_num
  coverage_nonneg := by norm_num
  coverage_le_one := by norm_num
  disagreementPenalty_nonneg := by norm_num
  fragilityPenalty_nonneg := by norm_num

noncomputable def continueChainStep : CertifiedChainStep DemoRegime where
  admissibility := continueAdmissibility
  trust := continueTrust
  posterior := demoPosterior
  branchValues := demoBranchValues

noncomputable def continueRealizedStep : RealizedCertifiedChainStep DemoRegime where
  admissibility := continueAdmissibility
  trust := continueTrust
  posterior := demoPosterior
  branchValues := demoBranchValues
  actualError := 1 / 100
  actualError_nonneg := by norm_num
  actualError_le_effectiveBound := by
    norm_num [CertifiedChainStep.effectiveErrorBound, continueAdmissibility, continueTrust]

theorem certifiedChaining_regression_continue_sound :
    chainActualError [continueRealizedStep] ≤ 1 / 10 := by
  apply continueSound_if_chainBound_le_tolerance
  norm_num [chainCertifiedErrorBoundFromRealized, CertifiedChainStep.effectiveErrorBound,
    continueAdmissibility, continueTrust, continueRealizedStep]

theorem certifiedChaining_regression_continue_action :
    chooseHigherOrderAction
      (actionSummaryOfCertifiedChain [continueChainStep] (1 / 10) 1 1 (1 / 10)) = .continue := by
  apply continuePreferred_if_chainBound_le_tolerance
  norm_num [actionSummaryOfCertifiedChain, chainCertifiedErrorBound,
    CertifiedChainStep.effectiveErrorBound, continueAdmissibility, continueTrust,
    continueChainStep]

noncomputable def revealAdmissibility : CertifiedAdmissibilityEstimate where
  lower := 3 / 10
  upper := 7 / 10
  coverage := 4 / 5
  errorBound := 1 / 4
  lower_nonneg := by norm_num
  upper_le_one := by norm_num
  lower_le_upper := by norm_num
  coverage_nonneg := by norm_num
  coverage_le_one := by norm_num
  errorBound_nonneg := by norm_num

noncomputable def revealTrust : CertifiedTrustEstimate where
  lower := 4 / 5
  upper := 1
  coverage := 4 / 5
  disagreementPenalty := 1 / 20
  fragilityPenalty := 0
  lower_nonneg := by norm_num
  upper_le_one := by norm_num
  lower_le_upper := by norm_num
  coverage_nonneg := by norm_num
  coverage_le_one := by norm_num
  disagreementPenalty_nonneg := by norm_num
  fragilityPenalty_nonneg := by norm_num

noncomputable def revealChainStep : CertifiedChainStep DemoRegime where
  admissibility := revealAdmissibility
  trust := revealTrust
  posterior := demoPosterior
  branchValues := demoBranchValues

theorem certifiedChaining_regression_revealVariance_eq :
    certifiedVariance revealChainStep = 3 / 16 := by
  have hmix :
      mixtureValue demoPosterior.weights demoBranchValues = 3 / 4 := by
    rw [mixtureValue, demoRegime_univ]
    simp [demoPosterior, demoBranchValues]
  unfold certifiedVariance mixtureVariance expectedSquaredLoss
  change
    ∑ r : DemoRegime,
        demoPosterior.weights r * (mixtureValue demoPosterior.weights demoBranchValues - demoBranchValues r) ^ 2 =
      3 / 16
  rw [hmix, demoRegime_univ]
  simp [demoPosterior, demoBranchValues]
  norm_num

theorem certifiedChaining_regression_reveal_action :
    chooseHigherOrderAction
      (actionSummaryOfCertifiedChain [revealChainStep] (1 / 10) (1 / 10) 1 (1 / 10)) = .reveal := by
  apply revealPreferred_if_cost_lt_headCertifiedVariance
  · norm_num [chainCertifiedErrorBound, CertifiedChainStep.effectiveErrorBound,
      actionSummaryOfCertifiedChain, revealAdmissibility, revealTrust, revealChainStep]
  · simpa [certifiedChaining_regression_revealVariance_eq] using
      (show (1 / 10 : ℝ) < 3 / 16 by norm_num)

noncomputable def fallbackSummary : CertifiedActionSummary where
  continueBound := 3 / 10
  tolerance := 1 / 10
  revealCost := 1
  revealVariance := 1 / 10
  fallbackBound := 1 / 50
  fallbackTolerance := 1 / 10

theorem certifiedChaining_regression_fallback_action :
    chooseHigherOrderAction fallbackSummary = .fallback := by
  apply fallbackPreferred_if_continueBound_gt_fallbackThreshold
  · norm_num [fallbackSummary]
  · norm_num [fallbackSummary]
  · norm_num [fallbackSummary]

noncomputable def abstainSummary : CertifiedActionSummary where
  continueBound := 3 / 10
  tolerance := 1 / 10
  revealCost := 1
  revealVariance := 1 / 10
  fallbackBound := 1 / 5
  fallbackTolerance := 1 / 10

theorem certifiedChaining_regression_abstain_action :
    chooseHigherOrderAction abstainSummary = .abstain := by
  apply abstainPreferred_if_no_action_certified
  · norm_num [abstainSummary]
  · norm_num [abstainSummary]
  · norm_num [abstainSummary]

/-! ## GWAS-shaped canary -/

def gwasFocusedRegime : GWASLatentRegime where
  fineMapping := .singleSignal
  tissue := .tissueSpecific
  mechanism := .regulatory

def gwasFocusedPosterior : CertifiedRegimePosterior GWASLatentRegime where
  weights r := if r = gwasFocusedRegime then 1 else 0
  valid := by
    constructor
    · intro r
      by_cases h : r = gwasFocusedRegime <;> simp [h]
    · simp [gwasFocusedRegime]
  uncertaintyRadius := 0
  uncertaintyRadius_nonneg := by norm_num

noncomputable def gwasFocusedProfile : GWASHigherOrderProfile where
  posterior := gwasFocusedPosterior
  trustEstimate := continueTrust
  trustRegime := .calibrated

noncomputable def gwasFocusedQuery : GWASLatentRegime → ℝ
  | r => if r = gwasFocusedRegime then 3 / 5 else 0

def gwasFocusedHypothesis : GWASHypothesis where
  locus := "chr16:fto"
  gene := "FTO"
  mechanism := "regulatory"
  phenotype := "obesity"

theorem certifiedChaining_regression_gwas_broadSupport_eq :
    gwasBroadSupport gwasFocusedProfile gwasFocusedQuery = 3 / 5 := by
  simp [gwasBroadSupport, gwasFocusedProfile, gwasFocusedPosterior,
    gwasFocusedQuery, gwasFocusedRegime, mixtureValue]

theorem certifiedChaining_regression_gwas_revealTissue_extends_context :
    (revealTissue gwasFocusedHypothesis .crossTissue).context =
      [GWASContextAtom.tissue .crossTissue] := by
  simp [gwasFocusedHypothesis, revealTissue]

/-! ## Non-degenerate GWAS canary: exercises the reveal pathway -/

/-- A second GWAS regime: multi-signal, cross-tissue, pathway-mediated. -/
def gwasMultiRegime : GWASLatentRegime where
  fineMapping := .multiSignal
  tissue := .crossTissue
  mechanism := .pathwayMediated

/-- The two benchmark regimes are distinct. -/
theorem gwasFocusedRegime_ne_gwasMultiRegime :
    gwasFocusedRegime ≠ gwasMultiRegime := by decide

/-- Non-degenerate posterior: 3/4 weight on focused, 1/4 on multi, 0 elsewhere. -/
noncomputable def gwasMixedPosterior : CertifiedRegimePosterior GWASLatentRegime where
  weights r :=
    if r = gwasFocusedRegime then 3 / 4
    else if r = gwasMultiRegime then 1 / 4
    else 0
  valid := by
    have hne : gwasFocusedRegime ≠ gwasMultiRegime := gwasFocusedRegime_ne_gwasMultiRegime
    constructor
    · intro r
      -- The if-chain must be unfolded explicitly before split_ifs can act.
      show (0:ℝ) ≤ if r = gwasFocusedRegime then 3/4 else if r = gwasMultiRegime then 1/4 else 0
      split_ifs <;> norm_num
    · -- Rewrite the two-branch if as a sum of two single-indicator functions,
      -- then apply Finset.sum_ite_eq for each indicator.
      have hrewrite : ∀ r : GWASLatentRegime,
          (if r = gwasFocusedRegime then (3:ℝ) / 4
           else if r = gwasMultiRegime then 1 / 4
           else 0) =
          (if r = gwasFocusedRegime then (3:ℝ) / 4 else 0) +
          (if r = gwasMultiRegime then 1 / 4 else 0) := by
        intro r
        by_cases h1 : r = gwasFocusedRegime
        · subst h1; simp [hne]
        · by_cases h2 : r = gwasMultiRegime
          · subst h2; simp [Ne.symm hne]
          · simp only [if_neg h1, if_neg h2, add_zero]
      have hsumFocused :
          ∑ r : GWASLatentRegime,
              (if r = gwasFocusedRegime then (3 : ℝ) / 4 else 0) = 3 / 4 := by
        simp [Finset.mem_univ]
      have hsumMulti :
          ∑ r : GWASLatentRegime,
              (if r = gwasMultiRegime then (1 : ℝ) / 4 else 0) = 1 / 4 := by
        simp [Finset.mem_univ]
      calc
        ∑ r : GWASLatentRegime,
            (if r = gwasFocusedRegime then (3 : ℝ) / 4
             else if r = gwasMultiRegime then 1 / 4
             else 0)
            =
            ∑ r : GWASLatentRegime,
              ((if r = gwasFocusedRegime then (3 : ℝ) / 4 else 0) +
               (if r = gwasMultiRegime then 1 / 4 else 0)) := by
              simp_rw [hrewrite]
        _ =
            (∑ r : GWASLatentRegime, (if r = gwasFocusedRegime then (3 : ℝ) / 4 else 0)) +
            (∑ r : GWASLatentRegime, (if r = gwasMultiRegime then 1 / 4 else 0)) := by
              rw [Finset.sum_add_distrib]
        _ = 1 := by
              rw [hsumFocused, hsumMulti]
              norm_num
  uncertaintyRadius := 0
  uncertaintyRadius_nonneg := by norm_num

/-- Query with distinct values on the two regimes: 4/5 on focused, 1/5 on multi. -/
noncomputable def gwasMixedQuery : GWASLatentRegime → ℝ
  | r => if r = gwasFocusedRegime then 4 / 5 else if r = gwasMultiRegime then 1 / 5 else 0

noncomputable def gwasMixedProfile : GWASHigherOrderProfile where
  posterior := gwasMixedPosterior
  trustEstimate := continueTrust
  trustRegime := .calibrated

/-- The certified variance is strictly positive for the non-degenerate mixed posterior. -/
theorem certifiedChaining_regression_gwas_mixed_variance_pos :
    0 < gwasCertifiedVariance gwasMixedProfile gwasMixedQuery := by
  -- gwasCertifiedVariance unfolds to mixtureVariance on gwasMixedPosterior.weights
  show 0 < mixtureVariance gwasMixedPosterior.weights gwasMixedQuery
  apply PLNVarianceChainNoGo.mixtureVariance_pos_of_nondegen
      gwasMixedPosterior.weights gwasMixedQuery gwasMixedPosterior.valid
      gwasFocusedRegime gwasMultiRegime
      gwasFocusedRegime_ne_gwasMultiRegime
  · -- 0 < w focused = 3/4
    have : gwasMixedPosterior.weights gwasFocusedRegime = 3 / 4 := by
      simp [gwasMixedPosterior]
    linarith
  · -- 0 < w multi = 1/4
    have : gwasMixedPosterior.weights gwasMultiRegime = 1 / 4 := by
      simp [gwasMixedPosterior, gwasFocusedRegime_ne_gwasMultiRegime.symm]
    linarith
  · -- q focused = 4/5 ≠ 1/5 = q multi
    have h1 : gwasMixedQuery gwasFocusedRegime = 4 / 5 := by simp [gwasMixedQuery]
    have h2 : gwasMixedQuery gwasMultiRegime = 1 / 5 := by
      simp [gwasMixedQuery, gwasFocusedRegime_ne_gwasMultiRegime.symm]
    rw [h1, h2]; norm_num

/-- With continueBound > tolerance and zero reveal cost, action chooser selects `.reveal`. -/
theorem certifiedChaining_regression_gwas_mixed_reveal_at_zero_cost :
    chooseHigherOrderAction
      (gwasActionSummary gwasMixedProfile gwasMixedQuery 1 (1/2) 0 1 1) = .reveal := by
  apply gwas_revealTissuePreferred_if_cost_lt_variance
  · norm_num
  · exact certifiedChaining_regression_gwas_mixed_variance_pos

/-! ## Calibration and enriched-reveal canaries -/

noncomputable def demoConformalCertificate : ConformalCertificate where
  alpha := 1 / 10
  alpha_nonneg := by norm_num
  alpha_lt_one := by norm_num
  quantile := 1 / 20
  quantile_nonneg := by norm_num

noncomputable def demoConformalAdmissibility :
    CertifiedAdmissibilityEstimate :=
  conformalToAdmissibility (modelOutput := 4 / 5)
    (by constructor <;> norm_num) demoConformalCertificate

theorem certifiedChaining_regression_conformal_coverage :
    demoConformalAdmissibility.coverage = 9 / 10 := by
  norm_num [demoConformalAdmissibility, conformalToAdmissibility,
    conformalCoverage, demoConformalCertificate]

theorem certifiedChaining_regression_conformal_errorBound :
    demoConformalAdmissibility.errorBound = 1 / 20 := by
  norm_num [demoConformalAdmissibility, conformalToAdmissibility,
    demoConformalCertificate]

noncomputable def gwasMixedEnrichedProfile : GWASEnrichedHigherOrderProfile where
  posterior := gwasMixedPosterior
  trustEstimate := continueTrust
  trustRegime := .calibrated
  branchValues := gwasMixedQuery
  withinVariance
    | r =>
        if r = gwasFocusedRegime then 1 / 20
        else if r = gwasMultiRegime then 1 / 10
        else 0
  withinVariance_nonneg := by
    intro r
    by_cases h₁ : r = gwasFocusedRegime
    · simp [h₁]
    · by_cases h₂ : r = gwasMultiRegime
      · simp [h₂, Ne.symm gwasFocusedRegime_ne_gwasMultiRegime]
      · simp [h₁, h₂]

theorem certifiedChaining_regression_gwas_total_variance_law :
    gwasTotalVariance gwasMixedEnrichedProfile =
      gwasBetweenVariance gwasMixedEnrichedProfile +
        gwasExpectedWithinVariance gwasMixedEnrichedProfile := by
  exact gwasLawOfTotalVariance gwasMixedEnrichedProfile

theorem certifiedChaining_regression_gwas_reveal_reduces_variance :
    gwasExpectedPostRevealVariance gwasMixedEnrichedProfile ≤
      gwasTotalVariance gwasMixedEnrichedProfile := by
  exact gwasExpectedPostRevealVariance_le_totalVariance gwasMixedEnrichedProfile

noncomputable def gwasFocusedLikelihood : GWASLatentRegime → ℝ
  | r => if r = gwasFocusedRegime then 2 else 1

theorem gwasFocusedLikelihood_nonneg (r : GWASLatentRegime) :
    0 ≤ gwasFocusedLikelihood r := by
  by_cases h : r = gwasFocusedRegime <;> simp [gwasFocusedLikelihood, h]

theorem gwasFocusedLikelihood_norm_pos :
    0 <
      (∑ r : GWASLatentRegime,
        gwasMixedEnrichedProfile.posterior.weights r * gwasFocusedLikelihood r) := by
  let tailSum : ℝ :=
    Finset.sum (Finset.univ.erase gwasFocusedRegime) fun r =>
      gwasMixedEnrichedProfile.posterior.weights r * gwasFocusedLikelihood r
  have hpos :
      0 <
        gwasMixedEnrichedProfile.posterior.weights gwasFocusedRegime *
          gwasFocusedLikelihood gwasFocusedRegime := by
    have hw : gwasMixedEnrichedProfile.posterior.weights gwasFocusedRegime = 3 / 4 := by
      simp [gwasMixedEnrichedProfile, gwasMixedPosterior]
    have hl : gwasFocusedLikelihood gwasFocusedRegime = 2 := by
      simp [gwasFocusedLikelihood]
    rw [hw, hl]
    norm_num
  have hnonneg : 0 ≤ tailSum := by
    unfold tailSum
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg
        (CertifiedRegimePosterior.weights_nonneg gwasMixedEnrichedProfile.posterior r)
        (gwasFocusedLikelihood_nonneg r)
  have hsplit :
      (∑ r : GWASLatentRegime,
          gwasMixedEnrichedProfile.posterior.weights r * gwasFocusedLikelihood r) =
        gwasMixedEnrichedProfile.posterior.weights gwasFocusedRegime *
            gwasFocusedLikelihood gwasFocusedRegime + tailSum := by
    unfold tailSum
    calc
      (∑ r : GWASLatentRegime,
          gwasMixedEnrichedProfile.posterior.weights r * gwasFocusedLikelihood r)
          =
          Finset.sum (Finset.univ.erase gwasFocusedRegime) (fun r =>
            gwasMixedEnrichedProfile.posterior.weights r * gwasFocusedLikelihood r) +
          gwasMixedEnrichedProfile.posterior.weights gwasFocusedRegime *
            gwasFocusedLikelihood gwasFocusedRegime := by
              exact
                (Finset.sum_erase_add
                  (s := Finset.univ)
                  (a := gwasFocusedRegime)
                  (f := fun r =>
                    gwasMixedEnrichedProfile.posterior.weights r * gwasFocusedLikelihood r)
                  (by simp)).symm
      _ =
          gwasMixedEnrichedProfile.posterior.weights gwasFocusedRegime *
              gwasFocusedLikelihood gwasFocusedRegime +
            Finset.sum (Finset.univ.erase gwasFocusedRegime) (fun r =>
              gwasMixedEnrichedProfile.posterior.weights r * gwasFocusedLikelihood r) := by
                rw [add_comm]
  rw [hsplit]
  exact add_pos_of_pos_of_nonneg hpos hnonneg

noncomputable def gwasPosteriorUpdatedToFocused : GWASEnrichedHigherOrderProfile :=
  gwasBayesianUpdateProfile
    gwasMixedEnrichedProfile
    gwasFocusedLikelihood
    gwasFocusedLikelihood_nonneg
    gwasFocusedLikelihood_norm_pos

theorem certifiedChaining_regression_gwas_update_valid :
    ValidRegimeWeights gwasPosteriorUpdatedToFocused.posterior.weights := by
  exact gwasBayesianUpdatePosterior_valid
    gwasMixedEnrichedProfile
    gwasFocusedLikelihood
    gwasFocusedLikelihood_nonneg
    gwasFocusedLikelihood_norm_pos

theorem certifiedChaining_regression_gwas_update_focuses :
    bayesianUpdateWeights
        gwasMixedEnrichedProfile.posterior
        gwasFocusedLikelihood
        gwasFocusedLikelihood_nonneg
        gwasFocusedLikelihood_norm_pos
        gwasMultiRegime
      ≤
      bayesianUpdateWeights
        gwasMixedEnrichedProfile.posterior
        gwasFocusedLikelihood
        gwasFocusedLikelihood_nonneg
        gwasFocusedLikelihood_norm_pos
        gwasFocusedRegime := by
  have hden : 0 <
      (∑ r : GWASLatentRegime,
        gwasMixedEnrichedProfile.posterior.weights r * gwasFocusedLikelihood r) :=
    gwasFocusedLikelihood_norm_pos
  have hnum :
      gwasMixedEnrichedProfile.posterior.weights gwasMultiRegime *
          gwasFocusedLikelihood gwasMultiRegime ≤
        gwasMixedEnrichedProfile.posterior.weights gwasFocusedRegime *
          gwasFocusedLikelihood gwasFocusedRegime := by
    have hwMulti :
        gwasMixedEnrichedProfile.posterior.weights gwasMultiRegime = 1 / 4 := by
      simp [gwasMixedEnrichedProfile, gwasMixedPosterior,
        gwasFocusedRegime_ne_gwasMultiRegime.symm]
    have hwFocus :
        gwasMixedEnrichedProfile.posterior.weights gwasFocusedRegime = 3 / 4 := by
      simp [gwasMixedEnrichedProfile, gwasMixedPosterior]
    have hlMulti : gwasFocusedLikelihood gwasMultiRegime = 1 := by
      simp [gwasFocusedLikelihood, gwasFocusedRegime_ne_gwasMultiRegime.symm]
    have hlFocus : gwasFocusedLikelihood gwasFocusedRegime = 2 := by
      simp [gwasFocusedLikelihood]
    rw [hwMulti, hwFocus, hlMulti, hlFocus]
    norm_num
  unfold bayesianUpdateWeights
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden)

end Mettapedia.Logic
