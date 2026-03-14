import Mathlib.Tactic
import Mettapedia.Logic.PLNHigherOrderDecisionTheorems
import Mettapedia.Logic.PLNHigherOrderPosteriorUpdate

/-!
# GWAS Higher-Order Bridge

This module gives the upcoming GWAS benchmark family a theorem-facing higher-
order shape without committing Lean to particular public datasets or pipelines.

The key idea is to make the latent coordinates explicit:

- fine-mapping regime
- tissue / cell-type regime
- mechanism-family regime
- trust / calibration regime

and then reuse the certified higher-order chaining / decision theory on top of
those latent coordinates.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNRegimeMixtureTheorems

/-- Coarse fine-mapping regimes for GWAS hypotheses. -/
inductive GWASFineMappingRegime where
  | singleSignal
  | multiSignal
  | diffuseCredibleSet
  deriving DecidableEq, Fintype, Repr

/-- Coarse tissue or cell-type regimes. -/
inductive GWASTissueRegime where
  | tissueSpecific
  | crossTissue
  | unknownTissue
  deriving DecidableEq, Fintype, Repr

/-- Coarse mechanism-family regimes. -/
inductive GWASMechanismRegime where
  | coding
  | regulatory
  | splicing
  | pathwayMediated
  deriving DecidableEq, Fintype, Repr

/-- Trust / calibration regimes for the evidence-integration layer. -/
inductive GWASTrustRegime where
  | calibrated
  | uncertain
  | weaklySupported
  deriving DecidableEq, Fintype, Repr

/-- Explicit latent regime for broad GWAS mechanistic reasoning. -/
structure GWASLatentRegime where
  fineMapping : GWASFineMappingRegime
  tissue : GWASTissueRegime
  mechanism : GWASMechanismRegime
  deriving DecidableEq, Fintype, Repr

/-- Explicit refinement atoms that can be revealed during mechanistic search. -/
inductive GWASContextAtom where
  | fineMapping (regime : GWASFineMappingRegime)
  | tissue (regime : GWASTissueRegime)
  | mechanism (regime : GWASMechanismRegime)
  deriving DecidableEq, Repr

/-- Abstract GWAS mechanistic hypothesis object. -/
structure GWASHypothesis where
  locus : String
  gene : String
  mechanism : String
  phenotype : String
  context : List GWASContextAtom := []
  deriving Repr

/-- Theorem-facing higher-order profile for a GWAS hypothesis. -/
structure GWASHigherOrderProfile where
  posterior : CertifiedRegimePosterior GWASLatentRegime
  trustEstimate : CertifiedTrustEstimate
  trustRegime : GWASTrustRegime

/-- Enriched GWAS profile with within-regime uncertainty for reveal/update
analysis. -/
structure GWASEnrichedHigherOrderProfile extends GWASHigherOrderProfile where
  branchValues : GWASLatentRegime → ℝ
  withinVariance : GWASLatentRegime → ℝ
  withinVariance_nonneg : ∀ r, 0 ≤ withinVariance r

/-- Broad-query mechanistic support is the regime-mixture expectation. -/
def gwasBroadSupport
    (profile : GWASHigherOrderProfile)
    (q : GWASLatentRegime → ℝ) : ℝ :=
  mixtureValue profile.posterior.weights q

/-- Variance of the unresolved mechanistic broad query. -/
def gwasCertifiedVariance
    (profile : GWASHigherOrderProfile)
    (q : GWASLatentRegime → ℝ) : ℝ :=
  mixtureVariance profile.posterior.weights q

/-- Reveal a concrete tissue/context regime. -/
def revealTissue
    (hyp : GWASHypothesis)
    (tissue : GWASTissueRegime) : GWASHypothesis :=
  { hyp with context := hyp.context ++ [GWASContextAtom.tissue tissue] }

/-- Reveal a concrete fine-mapping regime. -/
def revealFineMapping
    (hyp : GWASHypothesis)
    (fine : GWASFineMappingRegime) : GWASHypothesis :=
  { hyp with context := hyp.context ++ [GWASContextAtom.fineMapping fine] }

/-- Reveal a concrete mechanism-family regime. -/
def revealMechanism
    (hyp : GWASHypothesis)
    (mech : GWASMechanismRegime) : GWASHypothesis :=
  { hyp with context := hyp.context ++ [GWASContextAtom.mechanism mech] }

/-- Decision summary induced by a GWAS higher-order profile. -/
def gwasActionSummary
    (profile : GWASHigherOrderProfile)
    (q : GWASLatentRegime → ℝ)
    (continueBound tolerance revealCost fallbackBound fallbackTolerance : ℝ) :
    CertifiedActionSummary where
  continueBound := continueBound
  tolerance := tolerance
  revealCost := revealCost
  revealVariance := gwasCertifiedVariance profile q
  fallbackBound := fallbackBound
  fallbackTolerance := fallbackTolerance

theorem gwasPosterior_valid
    (profile : GWASHigherOrderProfile) :
    ValidRegimeWeights profile.posterior.weights := by
  exact profile.posterior.valid

theorem gwasBroadSupport_nonneg_of_unit_interval
    (profile : GWASHigherOrderProfile)
    {q : GWASLatentRegime → ℝ}
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) :
    0 ≤ gwasBroadSupport profile q := by
  exact CertifiedRegimePosterior.mixtureValue_nonneg_of_unit_interval
    profile.posterior hq

theorem gwasBroadSupport_le_one_of_unit_interval
    (profile : GWASHigherOrderProfile)
    {q : GWASLatentRegime → ℝ}
    (hq : ∀ r, 0 ≤ q r ∧ q r ≤ 1) :
    gwasBroadSupport profile q ≤ 1 := by
  exact CertifiedRegimePosterior.mixtureValue_le_one_of_unit_interval
    profile.posterior hq

theorem gwasCertifiedVariance_nonneg
    (profile : GWASHigherOrderProfile)
    (q : GWASLatentRegime → ℝ) :
    0 ≤ gwasCertifiedVariance profile q := by
  unfold gwasCertifiedVariance mixtureVariance expectedSquaredLoss
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg
      (CertifiedRegimePosterior.weights_nonneg profile.posterior r)
      (sq_nonneg _)

theorem revealTissue_extends_context
    (hyp : GWASHypothesis)
    (tissue : GWASTissueRegime) :
    (revealTissue hyp tissue).context = hyp.context ++ [GWASContextAtom.tissue tissue] := by
  rfl

theorem revealFineMapping_extends_context
    (hyp : GWASHypothesis)
    (fine : GWASFineMappingRegime) :
    (revealFineMapping hyp fine).context =
      hyp.context ++ [GWASContextAtom.fineMapping fine] := by
  rfl

theorem revealMechanism_extends_context
    (hyp : GWASHypothesis)
    (mech : GWASMechanismRegime) :
    (revealMechanism hyp mech).context =
      hyp.context ++ [GWASContextAtom.mechanism mech] := by
  rfl

theorem gwas_revealTissuePreferred_if_cost_lt_variance
    (profile : GWASHigherOrderProfile)
    (q : GWASLatentRegime → ℝ)
    (continueBound tolerance revealCost fallbackBound fallbackTolerance : ℝ)
    (hcontinue : ¬ continueBound ≤ tolerance)
    (hreveal : revealCost < gwasCertifiedVariance profile q) :
    chooseHigherOrderAction
      (gwasActionSummary profile q
        continueBound tolerance revealCost fallbackBound fallbackTolerance) = .reveal := by
  exact revealPreferred_if_cost_lt_certifiedVariance
    (gwasActionSummary profile q
      continueBound tolerance revealCost fallbackBound fallbackTolerance)
    hcontinue
    hreveal

theorem gwasRevealGain_positive_if_cost_lt_variance
    (profile : GWASHigherOrderProfile)
    (q : GWASLatentRegime → ℝ)
    {c : ℝ}
    (hc : c < gwasCertifiedVariance profile q) :
    0 < revealGain profile.posterior.weights q c := by
  simpa [gwasCertifiedVariance] using
    revealPreferred_if_cost_lt_variance
      (w := profile.posterior.weights)
      (q := q)
      hc

/-- Convert the enriched GWAS profile into the generic enriched higher-order
step used by the variance/update theorems. -/
def GWASEnrichedHigherOrderProfile.toEnrichedChainStep
    (profile : GWASEnrichedHigherOrderProfile) :
    EnrichedChainStep GWASLatentRegime where
  posterior := profile.posterior
  branchValues := profile.branchValues
  withinVariance := profile.withinVariance
  withinVariance_nonneg := profile.withinVariance_nonneg

def gwasBetweenVariance
    (profile : GWASEnrichedHigherOrderProfile) : ℝ :=
  betweenVariance profile.toEnrichedChainStep

def gwasExpectedWithinVariance
    (profile : GWASEnrichedHigherOrderProfile) : ℝ :=
  expectedWithinVariance profile.toEnrichedChainStep

def gwasTotalVariance
    (profile : GWASEnrichedHigherOrderProfile) : ℝ :=
  totalVariance profile.toEnrichedChainStep

def gwasExpectedPostRevealVariance
    (profile : GWASEnrichedHigherOrderProfile) : ℝ :=
  expectedPostRevealVariance profile.toEnrichedChainStep

def gwasRevealVarianceReduction
    (profile : GWASEnrichedHigherOrderProfile) : ℝ :=
  revealVarianceReduction profile.toEnrichedChainStep

noncomputable def gwasBayesianUpdateProfile
    (profile : GWASEnrichedHigherOrderProfile)
    (likelihood : GWASLatentRegime → ℝ)
    (hlik_nonneg : ∀ r, 0 ≤ likelihood r)
    (hnorm : 0 < ∑ r, profile.posterior.weights r * likelihood r) :
    GWASEnrichedHigherOrderProfile where
  posterior := bayesianUpdatePosterior profile.posterior likelihood hlik_nonneg hnorm
  trustEstimate := profile.trustEstimate
  trustRegime := profile.trustRegime
  branchValues := profile.branchValues
  withinVariance := profile.withinVariance
  withinVariance_nonneg := profile.withinVariance_nonneg

theorem gwasLawOfTotalVariance
    (profile : GWASEnrichedHigherOrderProfile) :
    gwasTotalVariance profile =
      gwasBetweenVariance profile + gwasExpectedWithinVariance profile := by
  exact lawOfTotalVariance profile.toEnrichedChainStep

theorem gwasExpectedPostRevealVariance_eq_expectedWithinVariance
    (profile : GWASEnrichedHigherOrderProfile) :
    gwasExpectedPostRevealVariance profile =
      gwasExpectedWithinVariance profile := by
  exact expectedPostRevealVariance_eq_expectedWithinVariance
    profile.toEnrichedChainStep

theorem gwasExpectedPostRevealVariance_le_totalVariance
    (profile : GWASEnrichedHigherOrderProfile) :
    gwasExpectedPostRevealVariance profile ≤ gwasTotalVariance profile := by
  exact expectedPostRevealVariance_le_totalVariance
    profile.toEnrichedChainStep

theorem gwasRevealVarianceReduction_eq_betweenVariance
    (profile : GWASEnrichedHigherOrderProfile) :
    gwasRevealVarianceReduction profile = gwasBetweenVariance profile := by
  exact revealVarianceReduction_eq_betweenVariance
    profile.toEnrichedChainStep

theorem gwasRevealPreferred_if_cost_lt_betweenVariance
    (profile : GWASEnrichedHigherOrderProfile)
    {cost : ℝ}
    (hcost : cost < gwasBetweenVariance profile) :
    cost < gwasRevealVarianceReduction profile := by
  exact revealPreferred_if_cost_lt_betweenVariance
    (step := profile.toEnrichedChainStep)
    hcost

theorem gwasBayesianUpdatePosterior_valid
    (profile : GWASEnrichedHigherOrderProfile)
    (likelihood : GWASLatentRegime → ℝ)
    (hlik_nonneg : ∀ r, 0 ≤ likelihood r)
    (hnorm : 0 < ∑ r, profile.posterior.weights r * likelihood r) :
    ValidRegimeWeights
      (gwasBayesianUpdateProfile profile likelihood hlik_nonneg hnorm).posterior.weights := by
  exact bayesianUpdate_valid profile.posterior likelihood hlik_nonneg hnorm

theorem gwasExpectedPosteriorVariance_le_priorVariance
    (profile : GWASEnrichedHigherOrderProfile) :
    gwasExpectedPostRevealVariance profile ≤ gwasTotalVariance profile := by
  exact expectedPosteriorVariance_le_priorVariance profile.toEnrichedChainStep

theorem gwasExpectedPosteriorVariance_drop_eq_betweenVariance
    (profile : GWASEnrichedHigherOrderProfile) :
    gwasTotalVariance profile - gwasExpectedPostRevealVariance profile =
      gwasBetweenVariance profile := by
  exact expectedPosteriorVariance_drop_eq_betweenVariance
    profile.toEnrichedChainStep

end Mettapedia.Logic
