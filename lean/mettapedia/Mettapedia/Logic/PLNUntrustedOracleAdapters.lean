import Mettapedia.Logic.PLNHigherOrderCalibrationContracts
import Mettapedia.Logic.PLNHigherOrderInformationSets

/-!
# Untrusted Oracle Adapters

This module formalizes the theorem-facing adapter layer between blind-time
features and the certified higher-order objects consumed by the chaining
theorems.

The point is not to trust learned models as semantics.  The point is to require
that anything learned be wrapped in certified interfaces before it can influence
certified chaining decisions.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNRegimeMixtureTheorems

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- Promotion status for an estimator lane that proposes higher-order values. -/
inductive OracleAdapterStatus where
  | promotableExact
  | certifiedApproximate
  | approximateOperational
  deriving DecidableEq, Repr

/-- Exactly the statuses that are allowed to feed the certified theorem lane. -/
def OracleAdapterStatus.supportsCertifiedConsumption :
    OracleAdapterStatus → Prop
  | .promotableExact => True
  | .certifiedApproximate => True
  | .approximateOperational => False

theorem OracleAdapterStatus.promotableExact_supportsCertifiedConsumption :
    OracleAdapterStatus.supportsCertifiedConsumption .promotableExact := by
  trivial

theorem OracleAdapterStatus.certifiedApproximate_supportsCertifiedConsumption :
    OracleAdapterStatus.supportsCertifiedConsumption .certifiedApproximate := by
  trivial

theorem OracleAdapterStatus.approximateOperational_not_supportsCertifiedConsumption :
    ¬ OracleAdapterStatus.supportsCertifiedConsumption .approximateOperational := by
  simp [OracleAdapterStatus.supportsCertifiedConsumption]

/-- A theorem-facing adapter: it consumes only blind-time features and produces
certified higher-order objects.  This is the clean interface through which
learned or heuristic estimators may enter the higher-order PLN theorem layer. -/
structure CertifiedBlindOracleAdapter (R : Type*) [Fintype R] [DecidableEq R] where
  status : OracleAdapterStatus
  status_supportsCertified :
    OracleAdapterStatus.supportsCertifiedConsumption status
  admissibilityOf : BlindFeatures → CertifiedAdmissibilityEstimate
  posteriorOf : BlindFeatures → CertifiedRegimePosterior R
  trustOf : BlindFeatures → CertifiedTrustEstimate

theorem CertifiedBlindOracleAdapter.status_ne_approximateOperational
    (adapter : CertifiedBlindOracleAdapter R) :
    adapter.status ≠ .approximateOperational := by
  cases adapter with
  | mk status hs _ _ _ =>
      cases status with
      | promotableExact =>
          intro hstatus
          cases hstatus
      | certifiedApproximate =>
          intro hstatus
          cases hstatus
      | approximateOperational =>
          exact False.elim hs

/-- Package one blind-time adapter output as a certified chain step. -/
def CertifiedBlindOracleAdapter.toCertifiedChainStep
    (adapter : CertifiedBlindOracleAdapter R)
    (blind : BlindFeatures)
    (branchValues : R → ℝ) : CertifiedChainStep R where
  admissibility := adapter.admissibilityOf blind
  trust := adapter.trustOf blind
  posterior := adapter.posteriorOf blind
  branchValues := branchValues

/-- Produce the theorem-facing action summary used by certified chaining
decisions from a blind-time adapter. -/
def CertifiedBlindOracleAdapter.toCertifiedActionSummary
    (adapter : CertifiedBlindOracleAdapter R)
    (blind : BlindFeatures)
    (branchValues : R → ℝ)
    (continueBound tolerance revealCost fallbackBound fallbackTolerance : ℝ) :
    CertifiedActionSummary where
  continueBound := continueBound
  tolerance := tolerance
  revealCost := revealCost
  revealVariance := certifiedVariance (adapter.toCertifiedChainStep blind branchValues)
  fallbackBound := fallbackBound
  fallbackTolerance := fallbackTolerance

/-- The blind-time decision induced by a certified adapter. -/
noncomputable def CertifiedBlindOracleAdapter.toBlindPolicy
    (adapter : CertifiedBlindOracleAdapter R)
    (branchValues : R → ℝ)
    (continueBound tolerance revealCost fallbackBound fallbackTolerance : ℝ) :
    BlindPolicy :=
  fun blind =>
    chooseHigherOrderAction
      (adapter.toCertifiedActionSummary blind branchValues
        continueBound tolerance revealCost fallbackBound fallbackTolerance)

/-- Oracle evaluation of an adapter-derived blind policy remains oracle
independent by construction. -/
noncomputable def CertifiedBlindOracleAdapter.evaluateBlindDecision
    (adapter : CertifiedBlindOracleAdapter R)
    (branchValues : R → ℝ)
    (continueBound tolerance revealCost fallbackBound fallbackTolerance : ℝ)
    (blind : BlindFeatures)
    (oracle : OracleFeatures) :
    HigherOrderDecision :=
  evaluateBlindPolicy
    (adapter.toBlindPolicy branchValues
      continueBound tolerance revealCost fallbackBound fallbackTolerance)
    blind oracle

theorem CertifiedBlindOracleAdapter.blindDecision_independent_of_oracle
    (adapter : CertifiedBlindOracleAdapter R)
    (branchValues : R → ℝ)
    (continueBound tolerance revealCost fallbackBound fallbackTolerance : ℝ)
    (blind : BlindFeatures)
    (oracle₁ oracle₂ : OracleFeatures) :
    adapter.evaluateBlindDecision branchValues
      continueBound tolerance revealCost fallbackBound fallbackTolerance
      blind oracle₁ =
    adapter.evaluateBlindDecision branchValues
      continueBound tolerance revealCost fallbackBound fallbackTolerance
      blind oracle₂ := by
  exact blindPolicy_independent_of_oracle
    (adapter.toBlindPolicy branchValues
      continueBound tolerance revealCost fallbackBound fallbackTolerance)
    blind oracle₁ oracle₂

theorem CertifiedBlindOracleAdapter.blindDecision_eq_policy
    (adapter : CertifiedBlindOracleAdapter R)
    (branchValues : R → ℝ)
    (continueBound tolerance revealCost fallbackBound fallbackTolerance : ℝ)
    (blind : BlindFeatures)
    (oracle : OracleFeatures) :
    adapter.evaluateBlindDecision branchValues
      continueBound tolerance revealCost fallbackBound fallbackTolerance
      blind oracle =
    chooseHigherOrderAction
      (adapter.toCertifiedActionSummary blind branchValues
        continueBound tolerance revealCost fallbackBound fallbackTolerance) := by
  rfl

theorem CertifiedBlindOracleAdapter.chainStep_trustAdjustedLower_nonneg
    (adapter : CertifiedBlindOracleAdapter R)
    (blind : BlindFeatures)
    (branchValues : R → ℝ) :
    0 ≤ (adapter.toCertifiedChainStep blind branchValues).trustAdjustedLower := by
  unfold CertifiedChainStep.trustAdjustedLower
  exact trustAdjustedLowerBound_nonneg
    (adapter.admissibilityOf blind) (adapter.trustOf blind)

theorem CertifiedBlindOracleAdapter.chainStep_effectiveErrorBound_nonneg
    (adapter : CertifiedBlindOracleAdapter R)
    (blind : BlindFeatures)
    (branchValues : R → ℝ) :
    0 ≤ (adapter.toCertifiedChainStep blind branchValues).effectiveErrorBound := by
  exact (adapter.toCertifiedChainStep blind branchValues).effectiveErrorBound_nonneg

theorem CertifiedBlindOracleAdapter.actionSummary_revealVariance_nonneg
    (adapter : CertifiedBlindOracleAdapter R)
    (blind : BlindFeatures)
    (branchValues : R → ℝ)
    (continueBound tolerance revealCost fallbackBound fallbackTolerance : ℝ) :
    0 ≤
      (adapter.toCertifiedActionSummary blind branchValues
        continueBound tolerance revealCost fallbackBound fallbackTolerance).revealVariance := by
  unfold CertifiedBlindOracleAdapter.toCertifiedActionSummary
  exact certifiedVariance_nonneg (adapter.toCertifiedChainStep blind branchValues)

/-- A calibrated scalar admissibility oracle can be promoted into the certified
adapter interface when paired with certified regime/trust producers. -/
structure CalibratedBlindAdmissibilityOracle where
  predict : BlindFeatures → ℝ
  predict_unit : ∀ blind, 0 ≤ predict blind ∧ predict blind ≤ 1
  certificate : ConformalCertificate

noncomputable def CalibratedBlindAdmissibilityOracle.toCertifiedEstimate
    (oracle : CalibratedBlindAdmissibilityOracle)
    (blind : BlindFeatures) : CertifiedAdmissibilityEstimate :=
  conformalToAdmissibility
    (oracle.predict blind)
    (oracle.predict_unit blind)
    oracle.certificate

noncomputable def adapterOfCalibratedAdmissibility
    (oracle : CalibratedBlindAdmissibilityOracle)
    (posteriorOf : BlindFeatures → CertifiedRegimePosterior R)
    (trustOf : BlindFeatures → CertifiedTrustEstimate)
    (status : OracleAdapterStatus)
    (hstatus : OracleAdapterStatus.supportsCertifiedConsumption status) :
    CertifiedBlindOracleAdapter R where
  status := status
  status_supportsCertified := hstatus
  admissibilityOf := oracle.toCertifiedEstimate
  posteriorOf := posteriorOf
  trustOf := trustOf

noncomputable def adapterOfCalibratedAdmissibilityCertifiedApproximate
    (oracle : CalibratedBlindAdmissibilityOracle)
    (posteriorOf : BlindFeatures → CertifiedRegimePosterior R)
    (trustOf : BlindFeatures → CertifiedTrustEstimate) :
    CertifiedBlindOracleAdapter R :=
  adapterOfCalibratedAdmissibility
    (R := R)
    oracle posteriorOf trustOf
    .certifiedApproximate
    OracleAdapterStatus.certifiedApproximate_supportsCertifiedConsumption

theorem adapterOfCalibratedAdmissibility_status_ne_approximateOperational
    (oracle : CalibratedBlindAdmissibilityOracle)
    (posteriorOf : BlindFeatures → CertifiedRegimePosterior R)
    (trustOf : BlindFeatures → CertifiedTrustEstimate)
    (status : OracleAdapterStatus)
    (hstatus : OracleAdapterStatus.supportsCertifiedConsumption status) :
    (adapterOfCalibratedAdmissibility (R := R)
      oracle posteriorOf trustOf status hstatus).status ≠ .approximateOperational := by
  exact CertifiedBlindOracleAdapter.status_ne_approximateOperational _

end Mettapedia.Logic
