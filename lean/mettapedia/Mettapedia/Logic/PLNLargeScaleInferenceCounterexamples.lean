import Mettapedia.Logic.PLNInclusionExclusionIdentifiability
import Mettapedia.Logic.PLNTrailFreeDynamicsCounterexample
import Mettapedia.Logic.PremiseSelectionExternalBayesianity
import Mettapedia.Logic.PremiseSelectionCoverageCounterexamples

/-!
# Large-Scale Inference Counterexample Index

This module provides a clean theorem-facing surface for the Chapter-9 counterexample-first
track. It re-exports stable aliases for the main negative and corrected-positive results:

- Inclusion-exclusion identifiability limits (first two terms are insufficient).
- Trail-free protocol non-convergence (deterministic 2-cycle witness).
- Pooling-axiom non-uniqueness (max-pool counterexample), plus corrected uniqueness under
  explicit total-additivity.

The intent is navigational stability for paper/theorem-index references.
-/

namespace Mettapedia.Logic.PLNLargeScaleInferenceCounterexamples

open Mettapedia.Logic.PLNInclusionExclusionIdentifiability
open Mettapedia.Logic.PLNTrailFreeDynamicsCounterexample
open Mettapedia.Logic.PremiseSelection
open Mettapedia.Logic.EvidenceQuantale

theorem ch9_ie_sameFirstTwo_differentUnion :
    ieTerm1 A1 B1 C1 = ieTerm1 A2 B2 C2
      ∧ ieTerm2 A1 B1 C1 = ieTerm2 A2 B2 C2
      ∧ unionCard A1 B1 C1 ≠ unionCard A2 B2 C2 :=
  same_first_two_terms_different_union

theorem ch9_ie_noUniversalPredictor :
    ¬ ∃ F : Nat → Nat → Nat,
        ∀ A B C : Finset Omega, unionCard A B C = F (ieTerm1 A B C) (ieTerm2 A B C) :=
  no_universal_union_predictor_from_first_two_terms

theorem ch9_ie_noSingleAdditiveCorrection :
    ¬ ∃ xi : Nat,
        unionCard A1 B1 C1 = ieTwoTermApprox A1 B1 C1 + xi
          ∧ unionCard A2 B2 C2 = ieTwoTermApprox A2 B2 C2 + xi :=
  no_single_additive_correction_for_both_models

theorem ch9_trailFree_notEventualConstant (x0 : TVState) :
    ¬ EventuallyConstant x0 :=
  orbit_not_eventually_constant x0

theorem ch9_poolingAxioms_notUnique
    {Goal Fact : Type*} [Nonempty Goal] [Nonempty Fact] :
    (maxPoolingOperator (Goal := Goal) (Fact := Fact)).pool ≠ fuse :=
  maxPoolingOperator_ne_fuse

theorem ch9_poolingUnique_of_externalBayes_totalAdd
    (poolE : Mettapedia.Logic.EvidenceQuantale.Evidence →
      Mettapedia.Logic.EvidenceQuantale.Evidence →
      Mettapedia.Logic.EvidenceQuantale.Evidence)
    (hexBayes : ∀ x y ℓ, poolE (x * ℓ) (y * ℓ) = poolE x y * ℓ)
    (htotal : ∀ x y, (poolE x y).total = x.total + y.total) :
    ∀ x y, poolE x y = x + y :=
  poolE_eq_hplus_of_externalBayes_totalAdd poolE hexBayes htotal

theorem ch9_coverageCard_not_sufficient_for_risk :
    dependencyCoverage D_cov S_cov_lowRisk = dependencyCoverage D_cov S_cov_highRisk
      ∧ S_cov_lowRisk.card = S_cov_highRisk.card
      ∧ falsePositiveRisk D_cov S_cov_lowRisk ≠ falsePositiveRisk D_cov S_cov_highRisk :=
  sameCoverageAndCard_differentFalsePositiveRisk

theorem ch9_noUniversalRiskPredictor_fromCoverageCard :
    ¬ ∃ F : Nat → Nat → Nat,
        ∀ S : Finset Fact3,
          falsePositiveRisk D_cov S = F (dependencyCoverage D_cov S) S.card :=
  no_universal_risk_predictor_from_coverage_and_card

end Mettapedia.Logic.PLNLargeScaleInferenceCounterexamples
