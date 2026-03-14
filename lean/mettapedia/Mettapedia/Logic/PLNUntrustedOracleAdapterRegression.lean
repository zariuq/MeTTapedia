import Mathlib.Tactic
import Mettapedia.Logic.PLNUntrustedOracleAdapters
import Mettapedia.Logic.PLNHigherOrderCertifiedChainingRegression

/-!
# Untrusted Oracle Adapter Regression

Concrete canaries for the theorem-facing untrusted-oracle adapter layer.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.PLNRegimeMixtureTheorems

noncomputable def uaDemoConformalCertificate : ConformalCertificate where
  alpha := 1 / 10
  quantile := 1 / 20
  alpha_nonneg := by norm_num
  alpha_lt_one := by norm_num
  quantile_nonneg := by norm_num

noncomputable def uaDemoBlindFeatures : BlindFeatures where
  topologyScore := 3 / 5
  sigmaCoverage := 4 / 5
  regimeEntropy := 1 / 4
  missingContextBurden := 1 / 5

noncomputable def uaDemoOracleFeatures₁ : OracleFeatures where
  exactValue := 9 / 10
  conditioningResidual := 1 / 20
  baseDependence := 1 / 10

noncomputable def uaDemoOracleFeatures₂ : OracleFeatures where
  exactValue := 1 / 10
  conditioningResidual := 3 / 10
  baseDependence := 1 / 5

noncomputable def uaDemoBlindAdmissibilityOracle : CalibratedBlindAdmissibilityOracle where
  predict _ := 4 / 5
  predict_unit := by
    intro _
    constructor <;> norm_num
  certificate := uaDemoConformalCertificate

noncomputable def uaDemoCertifiedAdapter :
    CertifiedBlindOracleAdapter DemoRegime :=
  adapterOfCalibratedAdmissibilityCertifiedApproximate
    (R := DemoRegime)
    uaDemoBlindAdmissibilityOracle
    (fun _ => demoPosterior)
    (fun _ => continueTrust)

theorem uaDemoCertifiedAdapter_status_ne_approximateOperational :
    uaDemoCertifiedAdapter.status ≠ .approximateOperational := by
  exact uaDemoCertifiedAdapter.status_ne_approximateOperational

theorem uaDemoCertifiedAdapter_blindDecision_independent_of_oracle :
    uaDemoCertifiedAdapter.evaluateBlindDecision demoBranchValues
      (1 / 20) (1 / 10) 1 1 (1 / 10) uaDemoBlindFeatures uaDemoOracleFeatures₁ =
    uaDemoCertifiedAdapter.evaluateBlindDecision demoBranchValues
      (1 / 20) (1 / 10) 1 1 (1 / 10) uaDemoBlindFeatures uaDemoOracleFeatures₂ := by
  exact uaDemoCertifiedAdapter.blindDecision_independent_of_oracle
    demoBranchValues (1 / 20) (1 / 10) 1 1 (1 / 10)
    uaDemoBlindFeatures uaDemoOracleFeatures₁ uaDemoOracleFeatures₂

theorem uaDemoCertifiedAdapter_continue_action :
    uaDemoCertifiedAdapter.evaluateBlindDecision demoBranchValues
      0 1 1 1 (1 / 10) uaDemoBlindFeatures uaDemoOracleFeatures₁ = .continue := by
  unfold CertifiedBlindOracleAdapter.evaluateBlindDecision evaluateBlindPolicy
  apply continuePreferred_if_chainBound_le_tolerance
  simp [CertifiedBlindOracleAdapter.toCertifiedActionSummary]

theorem uaDemoCertifiedAdapter_revealVariance_nonneg :
    0 ≤
      (uaDemoCertifiedAdapter.toCertifiedActionSummary uaDemoBlindFeatures demoBranchValues
        (1 / 20) (1 / 10) 1 1 (1 / 10)).revealVariance := by
  exact uaDemoCertifiedAdapter.actionSummary_revealVariance_nonneg
    uaDemoBlindFeatures demoBranchValues (1 / 20) (1 / 10) 1 1 (1 / 10)

end Mettapedia.Logic
