import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelITV
import Mettapedia.Logic.PLNWorldModelITVHypercube
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNWMOSLFBridgeITV
import Mettapedia.Logic.PLNXiRuleRegistry
import Mettapedia.Logic.PLNXiCarrierScreening
import Mettapedia.Logic.PLNXiDerivedBNRules
import Mettapedia.Logic.PLNIntensionalWorldModel
import Mettapedia.Logic.IntensionalInheritanceSolomonoffBridge
import Mettapedia.Logic.PLNInferenceControlCore
import Mettapedia.Logic.PLNInferenceControlAlgorithms
import Mettapedia.Logic.PLNInferenceControlChainer
import Mettapedia.Logic.PLNInferenceControlExamples
import Mettapedia.Logic.PLNGuardedHigherOrderSemantics
import Mettapedia.Logic.PLNMixedModeChainComposition
import Mettapedia.Logic.PLNProbHOLPlannerBridge
import Mettapedia.Logic.PLNRegimeMixtureBenchmarkBridge
import Mettapedia.Logic.PLNRegimeMixtureRegression
import Mettapedia.Logic.PLNHigherOrderChainingTheorems
import Mettapedia.Logic.PLNHigherOrderChainingRegression
import Mettapedia.Logic.PLNHigherOrderCertifiedEstimates
import Mettapedia.Logic.PLNUntrustedOracleAdapters
import Mettapedia.Logic.PLNUntrustedOracleAdapterRegression
import Mettapedia.Logic.PLNHigherOrderChainBounds
import Mettapedia.Logic.PLNHigherOrderDecisionTheorems
import Mettapedia.Logic.PLNGWASHigherOrderBridge
import Mettapedia.Logic.PLNHigherOrderCertifiedChainingRegression
import Mettapedia.Logic.PLNTopologyCPTNoGo
import Mettapedia.Logic.PLNVarianceChainNoGo
import Mettapedia.Logic.PLNHigherOrderNoGoBridge
import Mettapedia.Logic.PLNMarkovLogicAbstract
import Mettapedia.Logic.PLNMarkovLogicCountable
import Mettapedia.Logic.PLNMarkovLogicFiniteRestriction
import Mettapedia.Logic.PLNMarkovLogicFactorGraph
import Mettapedia.Logic.PLNMarkovLogicWorldModel
import Mettapedia.Logic.PLNMarkovLogicRegression
import Mettapedia.Logic.PLNMarkovLogicClauseSemantics
import Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph
import Mettapedia.Logic.PLNMarkovLogicClauseWorldModel
import Mettapedia.Logic.PLNMarkovLogicClauseRegression
import Mettapedia.Logic.PLNProbabilisticEventCalculus
import Mettapedia.Logic.PLNColliderSingletonBridge
import Mettapedia.Logic.PLNErrorMagnificationGrounding
import Mettapedia.Logic.HigherOrder.PLNKyburgReduction
import Mettapedia.Logic.PLNNARSRuleCorrespondence
import Mettapedia.Logic.PLNEndToEnd
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.EvidenceSTVBridge
import Mettapedia.Logic.SufficientStatisticSurface
import Mettapedia.Logic.GenericWorldModelForgetting
import Mettapedia.Logic.PLNWorldModelOverlap
import Mettapedia.Logic.PLNWorldModelSupportForgetting
import Mettapedia.Logic.PLNWorldModelConservationPack
import Mettapedia.Logic.PLNWorldModelOrderCostBounds
import Mettapedia.Logic.PLNWorldModelOrderCostAuditCertificate
import Mettapedia.Logic.PLNWorldModelOrderCostProvenanceDemo
import Mettapedia.Logic.PLNWorldModelOrderCostWeightedDemo
import Mettapedia.Logic.PLNWorldModelOrderCostGasPolicyDemo
import Mettapedia.Logic.PLNWorldModelAudit
import Mettapedia.Logic.PLNSemitopology
import Mettapedia.Logic.PLNProvenanceWMSupportBridge
import Mettapedia.Logic.PLNSemitopologyProvenanceBridge
import Mettapedia.Logic.PLNFirstOrder.InfiniteSoundness
import Mettapedia.Logic.PLNFirstOrder.InfiniteCanary
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSoundnessInf
import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSpecialization
import Mettapedia.Logic.PLNFirstOrder.FuzzyDomainQuantifiers
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemanticsFin
import Mettapedia.Logic.HOL
import Mettapedia.Logic.PLNWorldModelHOL
import Mettapedia.Logic.PLNWorldModelHOLCompleteness
import Mettapedia.Logic.PLNWorldModelHOLConsequence
import Mettapedia.Logic.PLNWorldModelHOLSetBridge
import Mettapedia.Logic.PLNHigherOrderHOL
import Mettapedia.Logic.PLNWorldModelPredCodeConsequence
import Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness
import Mettapedia.Logic.PLNWorldModelPreorder
import Mettapedia.Logic.PLNGaussianEMExtension

/-!
# PLN Canonical API (Lean)

Facade module exposing recommended, semantically grounded entry points:

- Strength formulas from `PLNDerivation` (deduction, induction, abduction)
- WM-calculus types from `PLNWorldModelCalculus` (query equivalence, rewrite rules)
- Sort-indexed WM layer (`WorldModelSigma`) from `PLNWorldModel`
- ITV semantics/query layer from `PLNWorldModelITV` + `PLNWorldModelITVHypercube`
- OSLF bridge: `XiPLN`, `XiPLNSigma`, atom semantics (`PLNWMOSLFBridge`)
- ITV threshold transport + quantale coherence (`PLNWMOSLFBridgeITV`)
- End-to-end rewrite/query/threshold bundles (interval-indexed)
- PLN↔NARS rule correspondence package (`PLNNARSRuleCorrespondence`)
- Schema templates in `Schema` namespace (building blocks for new derived rules)
- MeTTa integration: type-of-based query builders (`PLNWMOSLFBridgeTyped.MeTTaTypeOf`)
- Documentation index for derived BN rules, exactness matrix, end-to-end theorems
- Real HOL, direct `Set -> HOL -> WM`, higher-order PLN, and the
  logical-induction-ready HOL belief/process layer
- Planner-facing higher-order belief shadows derived from semantic `ProbHOL`
- Finite regime-mixture theorem layer for direct/soft/reveal higher-order
  continuation criteria
- Infinite-first MLN semantics plus finite-support factor-graph / WM
  subsumption

BN-topology-specific endpoints (chain/fork/collider) and sort-variant
specializations are available directly from `PLNXiDerivedBNRules` and
`PLNWMOSLFBridgeITV` — this facade re-exports only the generic layer.

This file is intentionally lightweight: it is an index with stable names, not a new semantics layer.

Important status boundary:

- the mature higher-order surface here is the HOL core, the HOL/WM bridge,
  HO-PLN consequence/rewrite transport, and the semantic `ProbHOL` layer;
- the logical-induction-style belief/process exports and planner-shadow exports are
  experimental overlays and should not be read as a completed higher-order
  metatheory or a full belief-market semantics;
- no HOL completeness claim is licensed by this file.
-/

namespace Mettapedia.Logic.PLNCanonical

open Mettapedia.Logic
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNBNCompilation
open Mettapedia.Logic.PLNBNCompilation.BNWorldModel
open Mettapedia.Logic.PLNXiDerivedBNRules
open Mettapedia.Logic.PLNXiDerivedBNRules.Typed
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

/-! ## Canonical Evidence Carriers -/

/-- Canonical evidence carrier for PLN in this repository. -/
abbrev Evidence := EvidenceQuantale.Evidence

/-- Canonical STV record used by rule-level formulas. -/
abbrev STV := PLNDeduction.STV

/-- Distributional STV view (kept for compatibility). -/
abbrev DistributionalSTV := PLN.Distributional.SimpleTruthValue

/-- Proven STV isomorphism between distributional and deduction views. -/
abbrev stvIso := EvidenceSTVBridge.stvEquiv

/-! ## Guarded Admissibility Endpoints -/

abbrev PLNGuardSemanticStatus :=
  Mettapedia.Logic.PLNGuardedHigherOrderSemantics.GuardSemanticStatus

abbrev PLNHigherOrderGuardPayload :=
  Mettapedia.Logic.PLNGuardedHigherOrderSemantics.HigherOrderGuardPayload

abbrev PLNGuardedSemanticQuery :=
  Mettapedia.Logic.PLNGuardedHigherOrderSemantics.SemanticProbGuardedQuery

abbrev PLNMixedModePlan :=
  Mettapedia.Logic.PLNMixedModeChainComposition.MixedModePlan

abbrev PLNBenchmarkPlannerShadow :=
  Mettapedia.Logic.BenchmarkPlannerShadow

abbrev pln_guarded_startPlan :=
  Mettapedia.Logic.PLNMixedModeChainComposition.startPlan

abbrev pln_guarded_applyStep :=
  Mettapedia.Logic.PLNMixedModeChainComposition.applyStep

abbrev pln_guarded_clean_chain_demo :=
  Mettapedia.Logic.PLNMixedModeChainComposition.cleanPlan_D

abbrev pln_guarded_higher_order_demo :=
  Mettapedia.Logic.PLNMixedModeChainComposition.leakyHigherOrderPlan_C

abbrev pln_guarded_bounded_composition_demo :=
  Mettapedia.Logic.PLNMixedModeChainComposition.boundedThenExactPlan_D

noncomputable abbrev pln_guarded_benchmarkPlannerShadow :=
  @_root_.Mettapedia.Logic.benchmarkPlannerShadow

noncomputable abbrev pln_guarded_leakyHigherOrderPlannerShadow :=
  @_root_.Mettapedia.Logic.leakyHigherOrderPlannerShadow

/-! ## Chapter-7 Distributional / Kyburg Endpoints -/

abbrev ch7_strengthWith_eq_beta_posterior_meanENN :=
  Mettapedia.Logic.PLNKyburgReduction.strengthWith_eq_beta_posterior_meanENN

abbrev ch7_evidence_encodes_beta_parameters :=
  Mettapedia.Logic.PLNKyburgReduction.evidence_encodes_beta_parameters

abbrev ch7_hplus_is_bayesian_update :=
  Mettapedia.Logic.PLNKyburgReduction.hplus_is_bayesian_update

abbrev ch7_evidence_aggregation_is_conjugate_update :=
  Mettapedia.Logic.PLNKyburgReduction.evidence_aggregation_is_conjugate_update

abbrev ch7_pln_is_bayes_optimal_for_exchangeable :=
  Mettapedia.Logic.PLNKyburgReduction.pln_is_bayes_optimal_for_exchangeable

abbrev ch7_kyburg_flattening :=
  @Mettapedia.Logic.PLNKyburgReduction.kyburg_flattening

abbrev ch7_expectation_consistency :=
  @Mettapedia.Logic.PLNKyburgReduction.expectation_consistency

abbrev ch7_kyburg_no_advantage :=
  @Mettapedia.Logic.PLNKyburgReduction.kyburg_no_advantage

abbrev ch7_flatten_is_monad_multiplication :=
  @Mettapedia.Logic.PLNKyburgReduction.flatten_is_monad_multiplication

abbrev ch7_flatten_associativity :=
  @Mettapedia.Logic.PLNKyburgReduction.flatten_associativity

abbrev ch7_flatten_associativity_kernel :=
  @Mettapedia.Logic.PLNKyburgReduction.flatten_associativity_kernel

abbrev ch7_kyburg_no_advantage_via_monad :=
  @Mettapedia.Logic.PLNKyburgReduction.kyburg_no_advantage_via_monad

abbrev ch7_deFinetti_flatten_apply_singleton :=
  Mettapedia.Logic.PLNKyburgReduction.deFinetti_flatten_apply_singleton

abbrev ch7_worked_example_strength_uniform_3_1 :=
  Mettapedia.Logic.PLNKyburgReduction.chapter7_worked_example_strength_uniform_3_1

abbrev ch7_distributional_kyburg_bridge_available :=
  Mettapedia.Logic.PLNKyburgReduction.chapter7_distributional_kyburg_bridge_available

/-! ## Arbitrary-Domain Quantifier Semantics Endpoints -/

abbrev PLNWeightFunctionInf :=
  Mettapedia.Logic.PLNFirstOrder.Infinite.WeightFunctionInf

abbrev PLNSatisfyingSetInf :=
  Mettapedia.Logic.PLNFirstOrder.Infinite.SatisfyingSetInf

noncomputable abbrev pln_forAllEvalInf :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.forAllEvalInf

noncomputable abbrev pln_thereExistsEvalInf :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.thereExistsEvalInf

noncomputable abbrev pln_forAllEvalExtInf :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.forAllEvalExtInf

noncomputable abbrev pln_thereExistsEvalExtInf :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.thereExistsEvalExtInf

abbrev pln_deMorgan_inf :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.deMorgan_inf

abbrev pln_weaknessInf_mono :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.weaknessInf_mono

abbrev pln_weaknessInf_mono_subset :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.weaknessInf_mono_subset

abbrev pln_forAllEvalInf_is_weakness :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.main_theorem_1_forAll_is_weakness_inf

abbrev pln_forAllEvalInf_mono_weights :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.main_theorem_2_monotonicity_inf

abbrev pln_thereExistsEvalInf_deMorgan :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.main_theorem_3_de_morgan_inf

abbrev pln_forAllEvalInf_functoriality :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.main_theorem_5_functoriality_inf

abbrev pln_forAllEvalInf_constantTrue_eq_sup_all :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.forAllEvalInf_constantTrue_eq_sup_all

abbrev pln_forAllEvalInf_constantFalse_eq_bot :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.forAllEvalInf_constantFalse_eq_bot

abbrev pln_forAllEvalExtInf_le_thereExistsEvalExtInf :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.forAllEvalExtInf_le_thereExistsEvalExtInf

abbrev pln_forAllEvalExtInf_eq_top_of_isEmpty :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.forAllEvalExtInf_eq_top_of_isEmpty

abbrev pln_thereExistsEvalExtInf_eq_bot_of_isEmpty :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.thereExistsEvalExtInf_eq_bot_of_isEmpty

abbrev pln_SatisfyingSetInf_ofFinitary :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.SatisfyingSetInf.ofFinitary

abbrev pln_WeightFunctionInf_ofFinitary :=
  @Mettapedia.Logic.PLNFirstOrder.Infinite.WeightFunctionInf.ofFinitary

/-! ## Arbitrary-Domain Fuzzy Quantifier Endpoints -/

abbrev PLNFuzzyQuantifierParamsInf :=
  Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParamsInf

abbrev PLNFuzzyProfile :=
  Mettapedia.Logic.PLNFirstOrder.FuzzyProfile

abbrev PLNFuzzyCapacity :=
  Mettapedia.Logic.PLNFirstOrder.FuzzyCapacity

abbrev pln_nearOneInf :=
  @Mettapedia.Logic.PLNFirstOrder.nearOneInf

abbrev pln_nearZeroInf :=
  @Mettapedia.Logic.PLNFirstOrder.nearZeroInf

/-! ## Real HOL Endpoints -/

abbrev PLNHOLTy := Mettapedia.Logic.HOL.Ty

abbrev PLNHOLTerm := @Mettapedia.Logic.HOL.Term

abbrev PLNHOLClosedFormula := @_root_.Mettapedia.Logic.HOL.ClosedFormula

abbrev PLNHenkinModel := @_root_.Mettapedia.Logic.HOL.HenkinModel

abbrev PLNHOLDerivation := @_root_.Mettapedia.Logic.HOL.Derivation

abbrev pln_hol_models := @_root_.Mettapedia.Logic.HOL.HenkinModel.models

abbrev pln_hol_theorem_sound := @_root_.Mettapedia.Logic.HOL.Soundness.theorem_sound

abbrev pln_hol_embedSentence := @_root_.Mettapedia.Logic.HOL.Embedding.FirstOrder.embedSentence

abbrev PLNHOLQuery := @_root_.Mettapedia.Logic.PLNWorldModelHOL.HOLQuery

abbrev PLNHOLState := @_root_.Mettapedia.Logic.PLNWorldModelHOL.HOLState

abbrev pln_hol_singleton_adequacy_strength_one :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOL.singleton_adequacy_strength_one

abbrev pln_hol_pointwiseImplies_iff_singletonConsequence :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLCompleteness.pointwiseImplies_iff_singletonConsequence

abbrev pln_hol_pointwiseIff_iff_queryEq :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLCompleteness.pointwiseIff_iff_queryEq

abbrev pln_hol_wmConsequenceRuleOn_of_pointwise :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLConsequence.wmConsequenceRuleOn_of_pointwise

/-! ## Direct Set-Semantics -> HOL -> WM Endpoints -/

abbrev PLNSetHOLQuery :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.SetHOLQuery

abbrev PLNSetHOLState :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.SetState

abbrev PLNSetHOLModel :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.SetHOLModel

abbrev pln_setHol_denote_embedSentence_iff :=
  @_root_.Mettapedia.Logic.HOL.Semantics.SetBased.pointed_denote_embedSentence_iff

abbrev pln_setHol_singleton_adequacy_strength_one :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.singleton_adequacy_strength_one

abbrev pln_setHol_pointwiseImplies_iff_singletonStrengthLE :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.pointwiseImplies_iff_singletonStrengthLE

abbrev pln_setHol_queryEq_of_pointwiseIff :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.queryEq_of_pointwiseIff

abbrev pln_setHol_pointwiseIff_iff_queryEq :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.pointwiseIff_iff_queryEq

abbrev pln_setHol_queryStrength_eq_of_pointwiseIff :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.queryStrength_eq_of_pointwiseIff

abbrev pln_setHol_evidence_eq_of_mutual_consequence_embed :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.setHolEvidence_eq_of_mutual_consequence_embed

abbrev pln_setHol_evidence_eq_of_mutual_provable_imp_embed :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.setHolEvidence_eq_of_mutual_provable_imp_embed

abbrev pln_setHol_queryStrength_eq_of_mutual_consequence_embed :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.queryStrength_eq_of_mutual_consequence_embed

abbrev pln_setHol_queryStrength_eq_of_mutual_provable_imp_embed :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.queryStrength_eq_of_mutual_provable_imp_embed

abbrev pln_setHol_queryStrength_embedSentence_eq_setQueryStrength :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.queryStrength_embedSentence_eq_setQueryStrength

abbrev pln_setHol_consequence_iff_singletonStrengthLEOnTheory_embed :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.consequence_iff_singletonStrengthLEOnTheory_embed

abbrev pln_setHol_provable_imp_iff_singletonStrengthLEOnTheory_embed :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.provable_imp_iff_singletonStrengthLEOnTheory_embed

abbrev pln_setHol_wmConsequenceRuleOn_of_provable_imp_embed :=
  @_root_.Mettapedia.Logic.PLNWorldModelHOLSetBridge.wmConsequenceRuleOn_of_provable_imp_embed

/-! ## Higher-Order PLN Endpoints -/

abbrev PLNHigherOrderHOLQuery :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLCore.HOLQuery

abbrev PLNHigherOrderHOLState :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLCore.HOLState

abbrev pln_higherOrderHOLProvable :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable

abbrev pln_higherOrderHOLProvImp :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvImp

abbrev pln_higherOrderHOLProvEq :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvEq

abbrev pln_higherOrderHOLProvIff :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.HOLProvIff

abbrev pln_higherOrderHOLProvPointwiseEq :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.HOLProvPointwiseEq

abbrev pln_higherOrderHOLProvImp_refl :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_refl

abbrev pln_higherOrderHOLProvImp_top :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_top

abbrev pln_higherOrderHOLProvImp_trans :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLCore.holProvImp_trans

abbrev pln_higherOrderHOLProvIff_refl :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_refl

abbrev pln_higherOrderHOLProvIff_symm :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_symm

abbrev pln_higherOrderHOLProvIff_trans :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_trans

abbrev pln_higherOrderHOLProvImp_and_mono :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_and_mono

abbrev pln_higherOrderHOLProvImp_or_mono :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_or_mono

abbrev pln_higherOrderHOLProvImp_and_left :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_and_left

abbrev pln_higherOrderHOLProvImp_and_right :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_and_right

abbrev pln_higherOrderHOLProvImp_and_intro :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_and_intro

abbrev pln_higherOrderHOLProvImp_or_intro_left :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_or_intro_left

abbrev pln_higherOrderHOLProvImp_or_intro_right :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_or_intro_right

abbrev pln_higherOrderHOLProvImp_or_elim :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_or_elim

abbrev pln_higherOrderHOLProvImp_not_of :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_not_of

abbrev pln_higherOrderHOLProvImp_imp_mono :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_imp_mono

abbrev pln_higherOrderHOLProvIff_and_mono :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_and_mono

abbrev pln_higherOrderHOLProvIff_or_mono :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_or_mono

abbrev pln_higherOrderHOLProvIff_not :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_not

abbrev pln_higherOrderHOLProvIff_imp_mono :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_imp_mono

abbrev pln_higherOrderHOLProvIff_and_comm :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_and_comm

abbrev pln_higherOrderHOLProvIff_or_comm :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_or_comm

abbrev pln_higherOrderHOLProvable_models :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvable_models

abbrev pln_higherOrderHOLProvImp_implies_pointwise :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_pointwise

abbrev pln_higherOrderHOLProvImp_implies_singletonConsequence :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_singletonConsequence

abbrev pln_higherOrderHOLProvImp_implies_multisetConsequence :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_multisetConsequence

abbrev pln_higherOrderHOLEq_models :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvEq_models

abbrev pln_higherOrderHOLProvIff_implies_queryEq :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_queryEq

abbrev pln_higherOrderHOLProvIff_implies_strengthEq :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_strengthEq

noncomputable abbrev pln_higherOrderHOL_wmConsequenceRule_of_holProvImp :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLConsequence.wmConsequenceRule_of_holProvImp

noncomputable abbrev pln_higherOrderHOL_wmConsequenceRuleOn_of_holProvImp :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLConsequence.wmConsequenceRuleOn_of_holProvImp

noncomputable abbrev pln_higherOrderHOL_wmRewriteRule_of_holProvIff :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLConsequence.wmRewriteRule_of_holProvIff

abbrev pln_higherOrderHOL_holdsLinkWM :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLLinkBridge.holdsLinkWM

abbrev pln_higherOrderHOL_holdsLinkWM_mono_of_holProvImp :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLLinkBridge.holdsLinkWM_mono_of_holProvImp

abbrev pln_higherOrderHOL_holdsTermWM_transport_of_holProvIff :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLLinkBridge.holdsTermWM_transport_of_holProvIff

abbrev pln_higherOrderHOL_holdsLinkWM_of_holProvIff_left :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLLinkBridge.holdsLinkWM_of_holProvIff_left

abbrev pln_higherOrderHOL_holdsLinkWM_of_holProvIff_right :=
  @_root_.Mettapedia.Logic.PLNHigherOrderHOLLinkBridge.holdsLinkWM_of_holProvIff_right

/-! ## Semantic Probabilistic HOL Endpoints -/

abbrev PLNProbHOLModelSpace :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.ModelSpace

noncomputable abbrev pln_probHol_sentenceProb :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.sentenceProb

abbrev pln_probHol_sentenceProb_top_eq_one :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.sentenceProb_top_eq_one

abbrev pln_probHol_sentenceProb_bot_eq_zero :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.sentenceProb_bot_eq_zero

abbrev pln_probHol_sentenceProb_mono_of_pointwiseImplies :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.sentenceProb_mono_of_pointwiseImplies

abbrev pln_probHol_sentenceProb_eq_of_pointwiseIff :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.sentenceProb_eq_of_pointwiseIff

noncomputable abbrev pln_probHol_probEvidence :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.probEvidence

noncomputable abbrev pln_probHol_probQueryStrength :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.probQueryStrength

abbrev pln_probHol_probQueryStrength_eq_sentenceProb :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.probQueryStrength_eq_sentenceProb

abbrev pln_probHol_probQueryStrength_mono_of_pointwiseImplies :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.probQueryStrength_mono_of_pointwiseImplies

abbrev pln_probHol_probQueryStrength_eq_of_pointwiseIff :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.probQueryStrength_eq_of_pointwiseIff

abbrev pln_probHol_empiricalSentenceProb_eq_staticQueryStrength :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.empiricalSentenceProb_eq_staticQueryStrength

abbrev pln_probHol_empiricalProbQueryStrength_eq_staticQueryStrength :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.empiricalProbQueryStrength_eq_staticQueryStrength

abbrev PLNHierarchicalProbHOLState :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.HierarchicalState

noncomputable abbrev pln_probHol_hierarchicalSentenceProb :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalSentenceProb

abbrev pln_probHol_hierarchicalSentenceProb_eq_flat_sentenceProb :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalSentenceProb_eq_flat_sentenceProb

abbrev pln_probHol_hierarchicalSentenceProb_eq_integral_componentSentenceProb :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalSentenceProb_eq_integral_componentSentenceProb

abbrev pln_probHol_hierarchicalSentenceProb_mono_of_pointwiseImplies :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalSentenceProb_mono_of_pointwiseImplies

abbrev pln_probHol_hierarchicalSentenceProb_eq_of_pointwiseIff :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalSentenceProb_eq_of_pointwiseIff

noncomputable abbrev pln_probHol_hierarchicalProbEvidence :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalProbEvidence

noncomputable abbrev pln_probHol_hierarchicalProbQueryStrength :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalProbQueryStrength

abbrev pln_probHol_hierarchicalProbQueryStrength_eq_sentenceProb :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalProbQueryStrength_eq_sentenceProb

abbrev pln_probHol_hierarchicalProbQueryStrength_mono_of_pointwiseImplies :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalProbQueryStrength_mono_of_pointwiseImplies

abbrev pln_probHol_hierarchicalProbQueryStrength_eq_of_pointwiseIff :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchicalProbQueryStrength_eq_of_pointwiseIff

abbrev pln_probHol_hierarchical_regression_empirical_probStrength_eq_static :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.hierarchical_regression_empirical_probStrength_eq_static

abbrev PLNBeliefDayTracksSentenceProb :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.BeliefDayTracksSentenceProb

abbrev PLNBeliefDayTracksSentenceProbOn :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.BeliefDayTracksSentenceProbOn

abbrev PLNBeliefDayTracksHierarchicalProb :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.BeliefDayTracksHierarchicalProb

abbrev PLNBeliefDayTracksHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.BeliefDayTracksHierarchicalProbOn

abbrev PLNBeliefProcessEventuallyTracksSentenceProbOn :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.BeliefProcessEventuallyTracksSentenceProbOn

abbrev PLNBeliefProcessEventuallyTracksHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.BeliefProcessEventuallyTracksHierarchicalProbOn

abbrev pln_probHol_beliefDayTracksSentenceProbOn_singleton :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.beliefDayTracksSentenceProbOn_singleton

abbrev pln_probHol_beliefDayTracksHierarchicalProbOn_singleton :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.beliefDayTracksHierarchicalProbOn_singleton

abbrev pln_probHol_guardedBenchmark_componentSentenceProb_eq_branchMass :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.componentSentenceProb_eq_branchMass

abbrev pln_probHol_guardedBenchmark_hierarchicalSentenceProb_eq_integral_branchMass :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkHierarchicalSentenceProb_eq_integral_branchMass

abbrev pln_probHol_guardedBenchmark_hierarchicalSentenceProb_eq_higherOrderSemanticValue :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkHierarchicalSentenceProb_eq_higherOrderSemanticValue

noncomputable abbrev pln_probHol_guardedBenchmark_defaultBenchmarkLatentProfile :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.defaultBenchmarkLatentProfile

noncomputable abbrev pln_probHol_guardedBenchmark_benchmarkLatentHierarchicalState :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkLatentHierarchicalState

abbrev pln_probHol_guardedBenchmark_benchmarkLatentHierarchicalSentenceProb_eq_benchmarkHierarchicalSentenceProb :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkLatentHierarchicalSentenceProb_eq_benchmarkHierarchicalSentenceProb

abbrev pln_probHol_guardedBenchmark_benchmarkLatentHierarchicalSentenceProb_eq_higherOrderSemanticValue :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkLatentHierarchicalSentenceProb_eq_higherOrderSemanticValue

abbrev pln_probHol_guardedBenchmark_benchmarkLatentHierarchicalProbQueryStrength_eq_higherOrderSemanticValue :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkLatentHierarchicalProbQueryStrength_eq_higherOrderSemanticValue

noncomputable abbrev pln_probHol_guardedBenchmark_benchmarkBeliefPrice :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefPrice

noncomputable abbrev pln_probHol_guardedBenchmark_benchmarkBeliefDay :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefDay

abbrev pln_probHol_guardedBenchmark_benchmarkBeliefDay_tracks_benchmarkHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefDay_tracks_benchmarkHierarchicalProbOn

abbrev pln_probHol_guardedBenchmark_benchmarkBeliefDay_tracks_benchmarkLatentHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefDay_tracks_benchmarkLatentHierarchicalProbOn

abbrev pln_probHol_guardedBenchmark_benchmarkBeliefProcess_eventuallyTracks_benchmarkHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefProcess_eventuallyTracks_benchmarkHierarchicalProbOn

abbrev pln_probHol_guardedBenchmark_benchmarkBeliefProcess_eventuallyTracks_benchmarkLatentHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefProcess_eventuallyTracks_benchmarkLatentHierarchicalProbOn

abbrev pln_probHol_guardedBenchmark_benchmarkBeliefDay_not_tracks_benchmarkHierarchicalProbOn_with_top :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefDay_not_tracks_benchmarkHierarchicalProbOn_with_top

abbrev pln_probHol_guardedBenchmark_benchmarkBeliefDay_not_tracks_benchmarkLatentHierarchicalProbOn_with_top :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.benchmarkBeliefDay_not_tracks_benchmarkLatentHierarchicalProbOn_with_top

abbrev pln_probHol_guardedBenchmark_higherOrderSemanticContraction_value_eq_benchmarkBeliefPrice :=
  @_root_.Mettapedia.Logic.HOL.Probabilistic.higherOrderSemanticContraction_value_eq_benchmarkBeliefPrice

abbrev pln_probHolPlanner_benchmarkPlannerShadow_carried_value_eq_benchmarkBeliefPrice :=
  @_root_.Mettapedia.Logic.benchmarkPlannerShadow_carried_value_eq_benchmarkBeliefPrice

abbrev pln_probHolPlanner_benchmarkPlannerShadow_process_tracks_hierarchicalProbOn :=
  @_root_.Mettapedia.Logic.benchmarkPlannerShadow_process_tracks_hierarchicalProbOn

abbrev pln_probHolPlanner_benchmarkPlannerShadow_day_tracks_benchmarkLatentHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.benchmarkPlannerShadow_day_tracks_benchmarkLatentHierarchicalProbOn

abbrev pln_probHolPlanner_benchmarkPlannerShadow_process_tracks_benchmarkLatentHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.benchmarkPlannerShadow_process_tracks_benchmarkLatentHierarchicalProbOn

abbrev pln_probHolPlanner_benchmarkPlannerShadow_day_not_tracks_benchmarkLatentExpandedSample :=
  @_root_.Mettapedia.Logic.benchmarkPlannerShadow_day_not_tracks_benchmarkLatentExpandedSample

abbrev pln_probHolPlanner_leakyHigherOrderPayload_valid01 :=
  @_root_.Mettapedia.Logic.leakyHigherOrderPayload_valid01

abbrev pln_probHolPlanner_leakyHigherOrderPlan_C_current_value_eq_benchmarkBeliefPrice :=
  @_root_.Mettapedia.Logic.leakyHigherOrderPlan_C_current_value_eq_benchmarkBeliefPrice

abbrev pln_probHolPlanner_leakyHigherOrderPlan_C_current_gateConfidence_eq_higherOrderGuardConfidence :=
  @_root_.Mettapedia.Logic.leakyHigherOrderPlan_C_current_gateConfidence_eq_higherOrderGuardConfidence

abbrev pln_probHolPlanner_leakyHigherOrderPlan_C_current_records_payload :=
  @_root_.Mettapedia.Logic.leakyHigherOrderPlan_C_current_records_payload

abbrev pln_probHolPlanner_leakyHigherOrderPlannerShadow_process_tracks_defaultBenchmarkLatentHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.leakyHigherOrderPlannerShadow_process_tracks_defaultBenchmarkLatentHierarchicalProbOn

/-! ## Finite Regime-Mixture Endpoints -/

abbrev PLNRegimeMixtureValidWeights :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.ValidRegimeWeights

noncomputable abbrev pln_regimeMixture_mixtureValue :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.mixtureValue

noncomputable abbrev pln_regimeMixture_branchRadius :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.branchRadius

noncomputable abbrev pln_regimeMixture_expectedSquaredLoss :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.expectedSquaredLoss

noncomputable abbrev pln_regimeMixture_mixtureVariance :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.mixtureVariance

noncomputable abbrev pln_regimeMixture_revealGain :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.revealGain

abbrev pln_regimeMixture_directApprox_error_le_residualMass_mul_branchRadius :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.directApprox_error_le_residualMass_mul_branchRadius

abbrev pln_regimeMixture_expectedSquaredLoss_decomposition :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.expectedSquaredLoss_decomposition

abbrev pln_regimeMixture_expectedSquaredLoss_mixture_le :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.expectedSquaredLoss_mixture_le

abbrev pln_regimeMixture_revealPreferred_if_cost_lt_variance :=
  @_root_.Mettapedia.Logic.PLNRegimeMixtureTheorems.revealPreferred_if_cost_lt_variance

abbrev pln_regimeMixture_benchmarkMixtureValue_eq_higherOrderSemanticValue :=
  @_root_.Mettapedia.Logic.benchmarkMixtureValue_eq_higherOrderSemanticValue

abbrev pln_regimeMixture_benchmarkMixtureValue_eq_benchmarkBeliefPrice :=
  @_root_.Mettapedia.Logic.benchmarkMixtureValue_eq_benchmarkBeliefPrice

abbrev pln_regimeMixture_benchmarkDirectApprox_exactBranch_bound :=
  @_root_.Mettapedia.Logic.benchmarkDirectApprox_exactBranch_bound

abbrev pln_regimeMixture_benchmarkMixtureSquaredLoss_le_exactBranchRisk :=
  @_root_.Mettapedia.Logic.benchmarkMixtureSquaredLoss_le_exactBranchRisk

abbrev pln_regimeMixture_benchmarkRevealPreferred_if_cost_lt_variance :=
  @_root_.Mettapedia.Logic.benchmarkRevealPreferred_if_cost_lt_variance

abbrev pln_regimeMixture_regression_leaky_value_eq_concrete :=
  @_root_.Mettapedia.Logic.regimeMixture_regression_leaky_value_eq_concrete

abbrev pln_regimeMixture_regression_leaky_mixtureVariance_le_exactBranchRisk :=
  @_root_.Mettapedia.Logic.regimeMixture_regression_leaky_mixtureVariance_le_exactBranchRisk

abbrev pln_regimeMixture_regression_leaky_reveal_preferred_at_zero_cost :=
  @_root_.Mettapedia.Logic.regimeMixture_regression_leaky_reveal_preferred_at_zero_cost

abbrev pln_regimeMixture_regression_leaky_reveal_not_preferred_at_cost_one :=
  @_root_.Mettapedia.Logic.regimeMixture_regression_leaky_reveal_not_preferred_at_cost_one

abbrev pln_regimeMixture_regression_sameWM_differentRegimes_differentAdmissibleDiscoveries :=
  @_root_.Mettapedia.Logic.regimeMixture_regression_sameWM_differentRegimes_differentAdmissibleDiscoveries

/-! ## Higher-Order Chaining Endpoints -/

abbrev pln_higherOrderChaining_continue_preserves_semanticStatus :=
  @_root_.Mettapedia.Logic.higherOrder_continue_preserves_semanticStatus

abbrev pln_higherOrderChaining_continue_accumulatedBound_eq_combineBounds :=
  @_root_.Mettapedia.Logic.higherOrder_continue_accumulatedBound_eq_combineBounds

abbrev pln_higherOrderChaining_continue_keeps_query_when_not_reveal :=
  @_root_.Mettapedia.Logic.higherOrder_continue_keeps_query_when_not_reveal

abbrev pln_higherOrderChaining_reveal_sets_queryChanged :=
  @_root_.Mettapedia.Logic.higherOrder_reveal_sets_queryChanged

abbrev pln_higherOrderChaining_continue_current_value_eq_benchmarkBeliefPrice :=
  @_root_.Mettapedia.Logic.higherOrder_continue_current_value_eq_benchmarkBeliefPrice

abbrev pln_higherOrderChaining_continue_current_value_eq_plannerShadow_carried_value :=
  @_root_.Mettapedia.Logic.higherOrder_continue_current_value_eq_plannerShadow_carried_value

abbrev pln_higherOrderChaining_continue_plannerShadow_process_tracks_benchmarkLatentHierarchicalProbOn :=
  @_root_.Mettapedia.Logic.higherOrder_continue_plannerShadow_process_tracks_benchmarkLatentHierarchicalProbOn

abbrev pln_higherOrderChaining_continue_broadQueryError_le_residualMass_mul_branchRadius :=
  @_root_.Mettapedia.Logic.higherOrder_continue_broadQueryError_le_residualMass_mul_branchRadius

abbrev pln_higherOrderChaining_continue_mixtureSquaredLoss_le_exactBranchRisk :=
  @_root_.Mettapedia.Logic.higherOrder_continue_mixtureSquaredLoss_le_exactBranchRisk

abbrev pln_higherOrderChaining_revealPreferred_for_refinedQuery_if_cost_lt_mixtureVariance :=
  @_root_.Mettapedia.Logic.higherOrder_revealPreferred_for_refinedQuery_if_cost_lt_mixtureVariance

abbrev pln_higherOrderChaining_decision_flattening_sound :=
  @_root_.Mettapedia.Logic.higherOrder_decision_flattening_sound

abbrev pln_higherOrderChaining_regression_leaky_continue_preserves_semanticStatus :=
  @_root_.Mettapedia.Logic.higherOrderChaining_regression_leaky_continue_preserves_semanticStatus

abbrev pln_higherOrderChaining_regression_leaky_continue_accumulatedBound_eq :=
  @_root_.Mettapedia.Logic.higherOrderChaining_regression_leaky_continue_accumulatedBound_eq

abbrev pln_higherOrderChaining_regression_leaky_continue_value_eq_benchmarkBeliefPrice :=
  @_root_.Mettapedia.Logic.higherOrderChaining_regression_leaky_continue_value_eq_benchmarkBeliefPrice

abbrev pln_higherOrderChaining_regression_leaky_broadQueryError_le_residualMass_mul_branchRadius :=
  @_root_.Mettapedia.Logic.higherOrderChaining_regression_leaky_broadQueryError_le_residualMass_mul_branchRadius

abbrev pln_higherOrderChaining_regression_leaky_reveal_preferred_at_zero_cost :=
  @_root_.Mettapedia.Logic.higherOrderChaining_regression_leaky_reveal_preferred_at_zero_cost

abbrev pln_higherOrderChaining_regression_reveal_sets_queryChanged :=
  @_root_.Mettapedia.Logic.higherOrderChaining_regression_reveal_sets_queryChanged

/-! ## Certified Higher-Order Chaining Endpoints -/

abbrev PLNCertifiedAdmissibilityEstimate :=
  @_root_.Mettapedia.Logic.CertifiedAdmissibilityEstimate

abbrev PLNCertifiedTrustEstimate :=
  @_root_.Mettapedia.Logic.CertifiedTrustEstimate

abbrev PLNCertifiedRegimePosterior :=
  @_root_.Mettapedia.Logic.CertifiedRegimePosterior

abbrev PLNCertifiedChainStep :=
  @_root_.Mettapedia.Logic.CertifiedChainStep

abbrev PLNRealizedCertifiedChainStep :=
  @_root_.Mettapedia.Logic.RealizedCertifiedChainStep

abbrev PLNHigherOrderDecision :=
  @_root_.Mettapedia.Logic.HigherOrderDecision

abbrev PLNCertifiedActionSummary :=
  @_root_.Mettapedia.Logic.CertifiedActionSummary

abbrev pln_higherOrderCertified_trustAdjustedLowerBound :=
  @_root_.Mettapedia.Logic.trustAdjustedLowerBound

abbrev pln_higherOrderCertified_chainAdmissibilityIndependent :=
  @_root_.Mettapedia.Logic.chainAdmissibilityIndependent

abbrev pln_higherOrderCertified_chainAdmissibilityBottleneck :=
  @_root_.Mettapedia.Logic.chainAdmissibilityBottleneck

abbrev pln_higherOrderCertified_chainAdmissibilityTrustWeighted :=
  @_root_.Mettapedia.Logic.chainAdmissibilityTrustWeighted

abbrev pln_higherOrderCertified_chainCertifiedErrorBound :=
  @_root_.Mettapedia.Logic.chainCertifiedErrorBound

abbrev pln_higherOrderCertified_continueSound_if_chainBound_le_tolerance :=
  @_root_.Mettapedia.Logic.continueSound_if_chainBound_le_tolerance

abbrev pln_higherOrderCertified_continuePreferred_if_chainBound_le_tolerance :=
  @_root_.Mettapedia.Logic.continuePreferred_if_chainBound_le_tolerance

abbrev pln_higherOrderCertified_revealPreferred_if_cost_lt_certifiedVariance :=
  @_root_.Mettapedia.Logic.revealPreferred_if_cost_lt_certifiedVariance

abbrev pln_higherOrderCertified_fallbackPreferred_if_continueBound_gt_fallbackThreshold :=
  @_root_.Mettapedia.Logic.fallbackPreferred_if_continueBound_gt_fallbackThreshold

abbrev pln_higherOrderCertified_abstainPreferred_if_no_action_certified :=
  @_root_.Mettapedia.Logic.abstainPreferred_if_no_action_certified

abbrev pln_higherOrderCertified_higherOrder_action_flattening_sound :=
  @_root_.Mettapedia.Logic.higherOrder_action_flattening_sound

/-! ## Untrusted Oracle Adapter Endpoints -/

abbrev PLNOracleAdapterStatus :=
  @_root_.Mettapedia.Logic.OracleAdapterStatus

abbrev PLNCertifiedBlindOracleAdapter :=
  @_root_.Mettapedia.Logic.CertifiedBlindOracleAdapter

abbrev PLNCalibratedBlindAdmissibilityOracle :=
  @_root_.Mettapedia.Logic.CalibratedBlindAdmissibilityOracle

abbrev pln_oracleAdapter_supportsCertifiedConsumption :=
  @_root_.Mettapedia.Logic.OracleAdapterStatus.supportsCertifiedConsumption

abbrev pln_oracleAdapter_toCertifiedChainStep :=
  @_root_.Mettapedia.Logic.CertifiedBlindOracleAdapter.toCertifiedChainStep

abbrev pln_oracleAdapter_toCertifiedActionSummary :=
  @_root_.Mettapedia.Logic.CertifiedBlindOracleAdapter.toCertifiedActionSummary

noncomputable abbrev pln_oracleAdapter_toBlindPolicy :=
  @_root_.Mettapedia.Logic.CertifiedBlindOracleAdapter.toBlindPolicy

noncomputable abbrev pln_oracleAdapter_evaluateBlindDecision :=
  @_root_.Mettapedia.Logic.CertifiedBlindOracleAdapter.evaluateBlindDecision

noncomputable abbrev pln_oracleAdapter_adapterOfCalibratedAdmissibility :=
  @_root_.Mettapedia.Logic.adapterOfCalibratedAdmissibility

abbrev pln_oracleAdapter_blindDecision_independent_of_oracle :=
  @_root_.Mettapedia.Logic.CertifiedBlindOracleAdapter.blindDecision_independent_of_oracle

abbrev pln_oracleAdapter_chainStep_trustAdjustedLower_nonneg :=
  @_root_.Mettapedia.Logic.CertifiedBlindOracleAdapter.chainStep_trustAdjustedLower_nonneg

abbrev pln_oracleAdapter_actionSummary_revealVariance_nonneg :=
  @_root_.Mettapedia.Logic.CertifiedBlindOracleAdapter.actionSummary_revealVariance_nonneg

abbrev pln_oracleAdapter_regression_status_ne_approximateOperational :=
  @_root_.Mettapedia.Logic.uaDemoCertifiedAdapter_status_ne_approximateOperational

abbrev pln_oracleAdapter_regression_blindDecision_independent_of_oracle :=
  @_root_.Mettapedia.Logic.uaDemoCertifiedAdapter_blindDecision_independent_of_oracle

abbrev pln_oracleAdapter_regression_continue_action :=
  @_root_.Mettapedia.Logic.uaDemoCertifiedAdapter_continue_action

/-! ## Certified Chaining No-Go Endpoints -/

abbrev PLNBoolBNBinaryEdgeWitness :=
  @_root_.Mettapedia.Logic.PLNTopologyCPTNoGo.BoolBNBinaryEdgeWitness

abbrev PLNVarianceChainAction :=
  @_root_.Mettapedia.Logic.PLNVarianceChainNoGo.VarianceChainAction

abbrev PLNVarianceChainStep :=
  @_root_.Mettapedia.Logic.PLNVarianceChainNoGo.VarianceChainStep

abbrev pln_noGo_same_topology_different_residual_of_binary_edge_fragment :=
  @_root_.Mettapedia.Logic.PLNTopologyCPTNoGo.same_topology_different_residual_of_binary_edge_fragment

abbrev pln_noGo_topology_bound_not_tight_of_binary_edge_fragment :=
  @_root_.Mettapedia.Logic.PLNTopologyCPTNoGo.topology_bound_not_tight_of_binary_edge_fragment

abbrev pln_noGo_topology_function_bound_is_trivial_of_binary_edge_fragment :=
  @_root_.Mettapedia.Logic.PLNTopologyCPTNoGo.topology_function_bound_is_trivial_of_binary_edge_fragment

abbrev pln_noGo_residual_separation_of_binary_edge_fragment :=
  @_root_.Mettapedia.Logic.PLNTopologyCPTNoGo.residual_separation_of_binary_edge_fragment

abbrev pln_noGo_variance_accumulation_along_unrevealed_chain :=
  @_root_.Mettapedia.Logic.PLNVarianceChainNoGo.variance_accumulation_along_unrevealed_chain

abbrev pln_noGo_reveal_resets_variance_accumulation :=
  @_root_.Mettapedia.Logic.PLNVarianceChainNoGo.reveal_resets_variance_accumulation

abbrev pln_noGo_fallback_resets_variance_accumulation :=
  @_root_.Mettapedia.Logic.PLNVarianceChainNoGo.fallback_resets_variance_accumulation

abbrev pln_noGo_variance_accumulation_between_resets :=
  @_root_.Mettapedia.Logic.PLNVarianceChainNoGo.variance_accumulation_between_resets

abbrev pln_noGo_topologyOnlyProxy_not_certifying :=
  @_root_.Mettapedia.Logic.topologyOnlyProxy_not_certifying

abbrev pln_noGo_unrevealedHigherOrderChain_requires_varianceBudget :=
  @_root_.Mettapedia.Logic.unrevealedHigherOrderChain_requires_varianceBudget

abbrev PLNGWASHypothesis :=
  @_root_.Mettapedia.Logic.GWASHypothesis

abbrev PLNGWASHigherOrderProfile :=
  @_root_.Mettapedia.Logic.GWASHigherOrderProfile

abbrev pln_gwasHigherOrder_gwasBroadSupport :=
  @_root_.Mettapedia.Logic.gwasBroadSupport

abbrev pln_gwasHigherOrder_gwasCertifiedVariance :=
  @_root_.Mettapedia.Logic.gwasCertifiedVariance

abbrev pln_gwasHigherOrder_revealTissue :=
  @_root_.Mettapedia.Logic.revealTissue

abbrev pln_gwasHigherOrder_revealFineMapping :=
  @_root_.Mettapedia.Logic.revealFineMapping

abbrev pln_gwasHigherOrder_revealMechanism :=
  @_root_.Mettapedia.Logic.revealMechanism

abbrev pln_gwasHigherOrder_revealTissuePreferred_if_cost_lt_variance :=
  @_root_.Mettapedia.Logic.gwas_revealTissuePreferred_if_cost_lt_variance

abbrev pln_gwasHigherOrder_revealGain_positive_if_cost_lt_variance :=
  @_root_.Mettapedia.Logic.gwasRevealGain_positive_if_cost_lt_variance

abbrev pln_higherOrderCertified_regression_continue_sound :=
  @_root_.Mettapedia.Logic.certifiedChaining_regression_continue_sound

abbrev pln_higherOrderCertified_regression_continue_action :=
  @_root_.Mettapedia.Logic.certifiedChaining_regression_continue_action

abbrev pln_higherOrderCertified_regression_reveal_action :=
  @_root_.Mettapedia.Logic.certifiedChaining_regression_reveal_action

abbrev pln_higherOrderCertified_regression_fallback_action :=
  @_root_.Mettapedia.Logic.certifiedChaining_regression_fallback_action

abbrev pln_higherOrderCertified_regression_abstain_action :=
  @_root_.Mettapedia.Logic.certifiedChaining_regression_abstain_action

abbrev pln_higherOrderCertified_regression_gwas_broadSupport_eq :=
  @_root_.Mettapedia.Logic.certifiedChaining_regression_gwas_broadSupport_eq

abbrev pln_higherOrderCertified_regression_gwas_revealTissue_extends_context :=
  @_root_.Mettapedia.Logic.certifiedChaining_regression_gwas_revealTissue_extends_context

/-! ## Clause-Native MLN Endpoints (primary MLN→WM result)

The clause-native lane is the canonical MLN subsumption result.
Grounded clauses with explicit atom-scope factor graphs compile to
a `ValuationWorldModel` state whose `queryStrength` equals the MLN `queryProb`.

**Important distinction:** MLN theory combination (adding clauses to a
ground MLN) is NOT the same operation as WM additive revision (adding
evidence sources). The subsumption theorem says that *each* ground MLN
compiles to a single WM evidence source; it does not claim that merging
two MLN knowledge bases corresponds to WM revision of their compiled states. -/

-- Types
abbrev PLNAtomValuation :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseSemantics.AtomValuation

abbrev PLNLiteral :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseSemantics.Literal

abbrev PLNGroundClause :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseSemantics.GroundClause

abbrev PLNWeightedGroundClause :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseSemantics.WeightedGroundClause

abbrev PLNGroundMLN :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseSemantics.GroundMLN

abbrev PLNClassicalGroundMLN :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseSemantics.ClassicalGroundMLN

abbrev PLNConstraintQuery :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph.ConstraintQuery

-- Core bridge
noncomputable abbrev pln_mln_clause_compiledClauseFactorGraph :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph.GroundMLN.compiledClauseFactorGraph

noncomputable abbrev pln_mln_clause_clauseWMState :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseWorldModel.clauseWMState

noncomputable abbrev pln_mln_clause_clauseMassSemantics :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseWorldModel.clauseMassSemantics

-- Main theorem
abbrev pln_mln_clause_queryStrength_eq_queryProb :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseWorldModel.clauseWM_queryStrength_eq_queryProb

-- Bridge lemmas
abbrev pln_mln_clause_weight_eq_queryMass :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseWorldModel.clauseWM_weight_eq_queryMass

abbrev pln_mln_clause_total_eq_totalMass :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseWorldModel.clauseWM_total_eq_totalMass

abbrev pln_mln_clause_evidence_eq_evidenceOfMasses :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseWorldModel.clauseWM_evidence_eq_evidenceOfMasses

-- Factor graph bridge
abbrev pln_mln_clause_unnormalizedJoint_eq_worldWeight :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph.GroundMLN.compiledClauseFactorGraph_unnormalizedJoint_eq_worldWeight

abbrev pln_mln_clause_weightOfConstraints_eq_queryMass :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph.GroundMLN.weightOfConstraints_eq_queryMass

abbrev pln_mln_clause_partitionFunction_eq_totalMass :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph.GroundMLN.partitionFunction_eq_totalMass

-- Classical MLN bridge
abbrev pln_mln_clause_worldWeight_eq_gibbsProduct :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseSemantics.ClassicalGroundMLN.worldWeight_eq_gibbsProduct

-- Regression canaries
abbrev pln_mln_clause_regression_sigmoid_queryStrength_eq_three_fourths :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseRegression.sigmoid_queryStrength_true_eq_three_fourths

abbrev pln_mln_clause_regression_conflicting_queryStrength_eq_three_fifths :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseRegression.conflicting_queryStrength_true_eq_three_fifths

abbrev pln_mln_clause_regression_hardZero_queryStrength_eq_zero :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseRegression.hardZero_queryStrength_false_eq_zero

abbrev pln_mln_clause_regression_conflicting_not_entailed :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicClauseRegression.conflicting_true_not_entailed_by_live_worlds

/-! ## Abstract MLN Endpoints (infinite-first, abstract world/query types) -/

abbrev PLNAbstractMLNSemantics :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicAbstract.AbstractMLNSemantics

abbrev PLNMLNMassSemantics :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicAbstract.MassSemantics

abbrev PLNMLNMassState :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicAbstract.MassState

abbrev PLNCountableMLNSemantics :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicCountable.CountableMLNSemantics

abbrev PLNFiniteSupportWitness :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicFiniteRestriction.FiniteSupportWitness

abbrev PLNRestrictedMLNWorld :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicFiniteRestriction.RestrictedWorld

abbrev pln_mln_queryStrength_eq_queryProb_of_evidence_eq :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicAbstract.queryStrength_eq_queryProb_of_evidence_eq

noncomputable abbrev pln_mln_logWeightPotential :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicCountable.logWeightPotential

abbrev pln_mln_restricted_queryProb_eq_full_queryProb_of_finite_support :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicFiniteRestriction.restricted_queryProb_eq_full_queryProb_of_finite_support

abbrev pln_mln_compiledJoint_eq_restrictedWorldWeight :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicFactorGraph.compiledJoint_eq_restrictedWorldWeight

abbrev pln_mln_compiledQueryMass_eq_restrictedQueryMass :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicFactorGraph.compiledQueryMass_eq_restrictedQueryMass

abbrev pln_mln_compiledPartition_eq_restrictedTotalMass :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicFactorGraph.compiledPartition_eq_restrictedTotalMass

abbrev pln_mln_wm_queryStrength_eq_restricted_queryProb :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicWorldModel.wm_queryStrength_eq_restricted_queryProb

abbrev pln_mln_wm_queryStrength_eq_full_queryProb_of_finite_support :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicWorldModel.wm_queryStrength_eq_full_queryProb_of_finite_support

abbrev pln_mln_regression_demo_compiledPartition_eq_three :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicRegression.demo_compiledPartition_eq_three

abbrev pln_mln_regression_wm_queryStrength_ideal_eq_two_thirds :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicRegression.wm_queryStrength_ideal_eq_two_thirds

abbrev pln_mln_regression_wm_queryStrength_reachable_eq_one :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicRegression.wm_queryStrength_reachable_eq_one

abbrev pln_mln_regression_wm_queryStrength_impossible_eq_zero :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicRegression.wm_queryStrength_impossible_eq_zero

abbrev pln_mln_regression_additive_revision_changes_evidence :=
  @_root_.Mettapedia.Logic.PLNMarkovLogicRegression.additive_revision_changes_evidence

/-! ## Logical-Induction-Ready HOL Belief Endpoints -/

abbrev PLNHOLClosedFormulaCode :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.ClosedFormulaCode

abbrev PLNHOLDeductiveProcess :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.DeductiveProcess

abbrev PLNHOLPrice01 :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.Price01

abbrev PLNHOLBeliefDay :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.BeliefDay

abbrev PLNHOLBeliefProcess :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.BeliefProcess

abbrev PLNHOLTrader :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.Trader

abbrev PLNHOLTheoryExtension :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.TheoryExtension

abbrev pln_hol_encodeClosedFormula :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.encodeClosedFormula

abbrev pln_hol_decodeClosedFormula :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.decodeClosedFormula

abbrev pln_hol_eventuallyProves :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.DeductiveProcess.eventuallyProves

noncomputable abbrev pln_hol_extendByAxioms :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.DeductiveProcess.extendByAxioms

abbrev pln_hol_LogicalInductionCriterion :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.LogicalInductionCriterion

noncomputable abbrev pln_hol_forceAxiomsAtOne :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.forceAxiomsAtOne

abbrev pln_hol_RespectsTheoryExtension :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.RespectsTheoryExtension

abbrev pln_hol_PreservesOutsideAxioms :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.PreservesOutsideAxioms

abbrev pln_hol_TrustsVisibleTheorems :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.TrustsVisibleTheorems

abbrev pln_hol_TimelyLearnsAtOne :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.TimelyLearnsAtOne

abbrev pln_hol_EventuallyExactOnFiniteSample :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.EventuallyExactOnFiniteSample

noncomputable abbrev pln_hol_beliefEvidence :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.beliefEvidence

noncomputable abbrev pln_hol_dayQueryStrength :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.dayQueryStrength

noncomputable abbrev pln_hol_empiricalBeliefDay :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.empiricalBeliefDay

abbrev pln_hol_empiricalDayStrength_eq_staticQueryStrength :=
  @_root_.Mettapedia.Logic.HOL.LogicalInduction.empiricalDayStrength_eq_staticQueryStrength

/-! ## Predicate-Code Legacy Endpoints -/

abbrev PLNPredCodeQuery := _root_.Mettapedia.Logic.PLNWorldModelPredCode.PredCodeQuery

abbrev PLNPredCodeState := _root_.Mettapedia.Logic.PLNWorldModelPredCode.PredCodeState

abbrev PLNPredCodeInfQuery :=
  _root_.Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.PredCodeInfQuery

abbrev pln_predCode_pointwiseImplies_iff_singletonConsequence :=
  @_root_.Mettapedia.Logic.PLNWorldModelPredCodeCompleteness.pointwiseImplies_iff_singletonConsequence

abbrev pln_predCodeInf_wmConsequenceRule_of_pointwise :=
  @_root_.Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness.wmConsequenceRule_of_pointwise

noncomputable abbrev pln_sugenoIntegral :=
  @Mettapedia.Logic.PLNFirstOrder.FuzzyCapacity.sugenoIntegral

abbrev pln_nearOneMassInf :=
  @Mettapedia.Logic.PLNFirstOrder.nearOneMassInf

abbrev pln_nearZeroMassInf :=
  @Mettapedia.Logic.PLNFirstOrder.nearZeroMassInf

abbrev pln_fuzzyExistsScoreInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyExistsScoreInf

abbrev pln_fuzzyIntervalHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyIntervalHoldsInf

abbrev pln_fuzzyForAllHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf

abbrev pln_fuzzyThereExistsHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyThereExistsHoldsInf

noncomputable abbrev pln_sugenoScoreInf :=
  @Mettapedia.Logic.PLNFirstOrder.sugenoScoreInf

noncomputable abbrev pln_choquetIntegral :=
  @Mettapedia.Logic.PLNFirstOrder.FuzzyCapacity.choquetIntegral

abbrev PLNGradedQuantifierSemantics :=
  _root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics

abbrev pln_gradedIntervalHolds :=
  @_root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics.intervalHolds

abbrev pln_gradedForAllHolds :=
  @_root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics.forAllHolds

abbrev pln_gradedThereExistsHolds :=
  @_root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics.thereExistsHolds

abbrev pln_gradedScoreOnDomain :=
  @_root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics.scoreOnDomain

abbrev pln_gradedIntervalOnDomainHolds :=
  @_root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics.intervalOnDomainHolds

abbrev pln_gradedForAllOnDomainHolds :=
  @_root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics.forAllOnDomainHolds

abbrev pln_gradedThereExistsOnDomainHolds :=
  @_root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics.thereExistsOnDomainHolds

abbrev pln_sugenoGradedQuantifierSemantics :=
  @Mettapedia.Logic.PLNFirstOrder.sugenoGradedQuantifierSemantics

noncomputable abbrev pln_choquetGradedQuantifierSemantics :=
  @Mettapedia.Logic.PLNFirstOrder.choquetGradedQuantifierSemantics

noncomputable abbrev pln_choquetScoreInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetScoreInf

abbrev pln_choquetIntervalHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetIntervalHoldsInf

abbrev pln_choquetForAllHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetForAllHoldsInf

abbrev pln_choquetThereExistsHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetThereExistsHoldsInf

abbrev pln_domainRestrict :=
  @Mettapedia.Logic.PLNFirstOrder.domainRestrict

abbrev pln_eqOnDomain :=
  @Mettapedia.Logic.PLNFirstOrder.eqOnDomain

abbrev pln_fuzzyExistsOnDomainScoreInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyExistsOnDomainScoreInf

abbrev pln_fuzzyIntervalOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyIntervalOnDomainHoldsInf

abbrev pln_fuzzyForAllOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyForAllOnDomainHoldsInf

abbrev pln_fuzzyThereExistsOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyThereExistsOnDomainHoldsInf

abbrev pln_fuzzyAllOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyAllOnDomainHoldsInf

abbrev pln_fuzzySomeOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzySomeOnDomainHoldsInf

noncomputable abbrev pln_choquetOnDomainScoreInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetOnDomainScoreInf

abbrev pln_choquetIntervalOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetIntervalOnDomainHoldsInf

abbrev pln_choquetForAllOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetForAllOnDomainHoldsInf

abbrev pln_choquetThereExistsOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetThereExistsOnDomainHoldsInf

abbrev pln_choquetAllOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetAllOnDomainHoldsInf

abbrev pln_choquetSomeOnDomainHoldsInf :=
  @Mettapedia.Logic.PLNFirstOrder.choquetSomeOnDomainHoldsInf

abbrev pln_fuzzyExists_is_nearOneMassInf :=
  @Mettapedia.Logic.PLNFirstOrder.main_theorem_1_fuzzy_exists_is_nearOneMass_inf

abbrev pln_fuzzyMonotonicityInf :=
  @Mettapedia.Logic.PLNFirstOrder.main_theorem_2_fuzzy_monotonicity_inf

abbrev pln_fuzzyComplementTransportInf :=
  @Mettapedia.Logic.PLNFirstOrder.main_theorem_3_fuzzy_complement_transport_inf

abbrev pln_fuzzySignatureInvarianceInf :=
  @Mettapedia.Logic.PLNFirstOrder.main_theorem_4_fuzzy_signature_invariance_inf

abbrev pln_sugenoMonotonicityInf :=
  @Mettapedia.Logic.PLNFirstOrder.main_theorem_5_sugeno_monotonicity_inf

abbrev pln_nearOneMassInf_constantOne_eq_one :=
  @Mettapedia.Logic.PLNFirstOrder.nearOneMassInf_constantOne_eq_one

abbrev pln_sugenoScoreInf_constantOne_eq_one :=
  @Mettapedia.Logic.PLNFirstOrder.sugenoScoreInf_constantOne_eq_one

abbrev pln_choquetScoreInf_mono :=
  @Mettapedia.Logic.PLNFirstOrder.choquetScoreInf_mono

abbrev pln_choquetScoreInf_constantOne_eq_one :=
  @Mettapedia.Logic.PLNFirstOrder.choquetScoreInf_constantOne_eq_one

abbrev pln_fuzzyExistsOnDomainScoreInf_eq_of_eqOnDomain :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyExistsOnDomainScoreInf_eq_of_eqOnDomain

abbrev pln_fuzzyForAllOnDomainHoldsInf_iff_of_eqOnDomain :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyForAllOnDomainHoldsInf_iff_of_eqOnDomain

abbrev pln_fuzzyAllOnDomainHoldsInf_relativized :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyAllOnDomainHoldsInf_relativized

abbrev pln_choquetOnDomainScoreInf_eq_of_eqOnDomain :=
  @Mettapedia.Logic.PLNFirstOrder.choquetOnDomainScoreInf_eq_of_eqOnDomain

abbrev pln_choquetForAllOnDomainHoldsInf_iff_of_eqOnDomain :=
  @Mettapedia.Logic.PLNFirstOrder.choquetForAllOnDomainHoldsInf_iff_of_eqOnDomain

abbrev pln_choquetAllOnDomainHoldsInf_relativized :=
  @Mettapedia.Logic.PLNFirstOrder.choquetAllOnDomainHoldsInf_relativized

abbrev pln_gradedScoreOnDomain_eq_of_eqOnDomain :=
  @_root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics.scoreOnDomain_eq_of_eqOnDomain

abbrev pln_gradedForAllOnDomainHolds_mono_of_pointwise :=
  @_root_.Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSemantics.forAllOnDomainHolds_mono_of_pointwise

/-! ## Finite/Counting Fuzzy Quantifier Endpoints -/

abbrev PLNFuzzyQuantifierParamsFin :=
  Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParamsFin

abbrev pln_fuzzyParamsFin_toInf :=
  @Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierParams.toInf

noncomputable abbrev pln_witnessCountFin :=
  @Mettapedia.Logic.PLNFirstOrder.witnessCountFin

noncomputable abbrev pln_witnessFractionFin :=
  @Mettapedia.Logic.PLNFirstOrder.witnessFractionFin

noncomputable abbrev pln_nearOneFractionFin :=
  @Mettapedia.Logic.PLNFirstOrder.nearOneFractionFin

noncomputable abbrev pln_nearZeroFractionFin :=
  @Mettapedia.Logic.PLNFirstOrder.nearZeroFractionFin

noncomputable abbrev pln_fuzzyExistsScoreFin :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyExistsScoreFin

abbrev pln_fuzzyIntervalHoldsFin :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyIntervalHoldsFin

abbrev pln_fuzzyForAllHoldsFin :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsFin

abbrev pln_fuzzyThereExistsHoldsFin :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyThereExistsHoldsFin

noncomputable abbrev pln_countingCapacity :=
  @Mettapedia.Logic.PLNFirstOrder.FuzzyCapacity.countingCapacity

abbrev pln_boundedProfileFinToInf :=
  @Mettapedia.Logic.PLNFirstOrder.boundedProfileFinToInf

abbrev pln_nearOneMassInf_counting_eq_nearOneFractionFin :=
  @Mettapedia.Logic.PLNFirstOrder.nearOneMassInf_counting_eq_nearOneFractionFin

abbrev pln_nearZeroMassInf_counting_eq_nearZeroFractionFin :=
  @Mettapedia.Logic.PLNFirstOrder.nearZeroMassInf_counting_eq_nearZeroFractionFin

abbrev pln_fuzzyExistsScoreInf_counting_eq_fuzzyExistsScoreFin :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyExistsScoreInf_counting_eq_fuzzyExistsScoreFin

abbrev pln_fuzzyIntervalHoldsInf_counting_iff_fuzzyIntervalHoldsFin :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyIntervalHoldsInf_counting_iff_fuzzyIntervalHoldsFin

abbrev pln_fuzzyForAllHoldsInf_counting_iff_fuzzyForAllHoldsFin :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyForAllHoldsInf_counting_iff_fuzzyForAllHoldsFin

abbrev pln_fuzzyThereExistsHoldsInf_counting_iff_fuzzyThereExistsHoldsFin :=
  @Mettapedia.Logic.PLNFirstOrder.fuzzyThereExistsHoldsInf_counting_iff_fuzzyThereExistsHoldsFin

/-! ## Additive WM Singleton-Surface Endpoints -/

abbrev wm_multiset_singletonSurface :=
  @Mettapedia.Logic.SufficientStatisticSurface.singletonSurface

abbrev wm_multiset_additive_evidence_eq_aggregate :=
  @Mettapedia.Logic.SufficientStatisticSurface.evidence_eq_aggregate_singletonSurface_of_zero

abbrev wm_multiset_additive_extension_unique :=
  @Mettapedia.Logic.SufficientStatisticSurface.existsUnique_additiveExtension_of_singletonSurface_zero

/-! ## Forgetting Endpoints -/

abbrev WMZeroPreserving :=
  @Mettapedia.Logic.GenericWorldModelZeroPreserving

abbrev WMForgettingLayer :=
  Mettapedia.Logic.ForgettingLayer

abbrev wm_no_exactInverse_revision_of_nonzero_outside_scope :=
  @Mettapedia.Logic.ForgettingLayer.no_exactInverse_revision_of_nonzero_outside_scope

abbrev WMOutsideLeakageBudget :=
  @Mettapedia.Logic.OutsideLeakageBudget

abbrev wm_antiHallucination_outsideScope_of_exactInverse :=
  @Mettapedia.Logic.antiHallucination_outsideScope_of_exactInverse

abbrev wm_outsideScopeEvidence_conserved_of_exactInverse :=
  @Mettapedia.Logic.outsideScopeEvidence_conserved_of_exactInverse

abbrev wm_outsideLeakageCount_zero_of_exactInverse :=
  @Mettapedia.Logic.outsideLeakageCount_zero_of_exactInverse

abbrev wm_outsideLeakageBudget_zero_of_exactInverse :=
  @Mettapedia.Logic.outsideLeakageBudget_zero_of_exactInverse

abbrev wm_outsideLeakageBudget_of_exactInverse :=
  @Mettapedia.Logic.outsideLeakageBudget_of_exactInverse

abbrev WMEvidenceConservationPack :=
  @Mettapedia.Logic.EvidenceConservationPack

abbrev wm_evidenceConservationPack_of_forgetting :=
  @Mettapedia.Logic.evidenceConservationPack_of_forgetting

/-! ## Non-Additive Perimeter Endpoints -/

abbrev WMOverlapLayer :=
  Mettapedia.Logic.OverlapLayer

abbrev WMSupportTrackedForgettingLayer :=
  Mettapedia.Logic.SupportTrackedForgettingLayer

abbrev wm_overlap_additive_of_independent :=
  @Mettapedia.Logic.OverlapLayer.additive_of_independent'

abbrev wm_exactInverse_of_supported :=
  @Mettapedia.Logic.SupportTrackedForgettingLayer.exactInverse_revision_of_support_subset

abbrev wm_exactInverse_supported_outside_zero :=
  @Mettapedia.Logic.SupportTrackedForgettingLayer.exactInverse_revision_supported_outside_zero

abbrev WMNoHallucinationOutsideScope :=
  @Mettapedia.Logic.NoHallucinationOutsideScope

abbrev wm_noHallucinationOutsideScope_of_exactInverse :=
  @Mettapedia.Logic.noHallucinationOutsideScope_of_exactInverse

abbrev wm_zeroLeakageOutsideScope_of_exactInverse :=
  @Mettapedia.Logic.zeroLeakageOutsideScope_of_exactInverse

abbrev WMSwapDefect :=
  @Mettapedia.Logic.SwapDefect

abbrev WMOrderSensitive :=
  @Mettapedia.Logic.OrderSensitive

abbrev wm_not_orderSensitive_of_commutativeMergeEvidence :=
  @Mettapedia.Logic.not_orderSensitive_of_commutativeMergeEvidence

noncomputable abbrev WMSwapAnomalyCount :=
  @Mettapedia.Logic.SwapAnomalyCount

abbrev WMSwapAnomalyBound :=
  @Mettapedia.Logic.SwapAnomalyBound

abbrev wm_swapAnomalyCount_zero_of_commutativeMergeEvidence :=
  @Mettapedia.Logic.swapAnomalyCount_zero_of_commutativeMergeEvidence

abbrev wm_swapAnomalyBound_of_pairwise_bounds :=
  @Mettapedia.Logic.swapAnomalyBound_of_pairwise_bounds

noncomputable abbrev WMScheduleErrorCount :=
  @Mettapedia.Logic.scheduleErrorCount

abbrev WMScheduleErrorBound :=
  @Mettapedia.Logic.scheduleErrorBound

abbrev wm_scheduleErrorBound_of_pairwise_bounds :=
  @Mettapedia.Logic.scheduleErrorBound_of_pairwise_bounds

noncomputable abbrev wm_swapStepAnomalyCount :=
  @Mettapedia.Logic.swapStepAnomalyCount

abbrev wm_swapStepAnomalyBound :=
  @Mettapedia.Logic.swapStepAnomalyBound

abbrev wm_scheduleError_twoStep_eq_swapStepAnomalyCount :=
  @Mettapedia.Logic.scheduleError_twoStep_eq_swapStepAnomalyCount

abbrev wm_scheduleErrorBound_twoStep_of_swapStepBound :=
  @Mettapedia.Logic.scheduleErrorBound_twoStep_of_swapStepBound

/-! ## Order-Cost Audit Certificate Endpoints -/

abbrev WMRuntimePairwiseOrderCheck :=
  @Mettapedia.Logic.RuntimePairwiseOrderCheck

abbrev WMRuntimeBudgetPolicyPass :=
  @Mettapedia.Logic.RuntimeBudgetPolicyPass

abbrev wm_runtimePairwiseOrderCheck_certifies_scheduleErrorBound :=
  @Mettapedia.Logic.runtimePairwiseOrderCheck_certifies_scheduleErrorBound

abbrev wm_runtimePairwiseOrderCheck_certifies_policyThreshold :=
  @Mettapedia.Logic.runtimePairwiseOrderCheck_certifies_policyThreshold

abbrev WMRuntimeSwapStepCheck :=
  @Mettapedia.Logic.RuntimeSwapStepCheck

abbrev wm_runtimeSwapStepCheck_certifies_twoStepPolicyThreshold :=
  @Mettapedia.Logic.runtimeSwapStepCheck_certifies_twoStepPolicyThreshold

/-! ## Weighted Numeric Order-Cost Demo Endpoints -/

abbrev wm_weightedRightBiasMerge :=
  @Mettapedia.Logic.weightedRightBiasMerge

noncomputable abbrev wm_weightedRightBiasOverlapLayer :=
  @Mettapedia.Logic.weightedRightBiasOverlapLayer

noncomputable abbrev wm_weightedSwapAnomalyCount :=
  @Mettapedia.Logic.weightedSwapAnomalyCount

noncomputable abbrev wm_weightedScheduleErrorCount :=
  @Mettapedia.Logic.weightedScheduleErrorCount

abbrev wm_weightedScheduleErrorBound :=
  @Mettapedia.Logic.weightedScheduleErrorBound

abbrev wm_weightedSwapAnomalyCount_eq_zero_of_query_eq :=
  @Mettapedia.Logic.weightedSwapAnomalyCount_eq_zero_of_query_eq

abbrev wm_weightedSwapAnomalyCount_eq_weight_of_zero_then_single :=
  @Mettapedia.Logic.weightedSwapAnomalyCount_eq_weight_of_zero_then_single

abbrev wm_weightedScheduleErrorCount_twoStep_eq_weight_of_zero_then_single :=
  @Mettapedia.Logic.weightedScheduleErrorCount_twoStep_eq_weight_of_zero_then_single

abbrev wm_weightedScheduleErrorBound_twoStep_weight_of_zero_then_single :=
  @Mettapedia.Logic.weightedScheduleErrorBound_twoStep_weight_of_zero_then_single

abbrev wm_weightedScheduleErrorBound_twoStep_not_zero_of_pos_weight :=
  @Mettapedia.Logic.weightedScheduleErrorBound_twoStep_not_zero_of_pos_weight

/-! ## Provenance Order-Cost Demo Endpoints -/

noncomputable abbrev wm_whichTopCountConjugateEvidence :=
  @Mettapedia.Logic.whichTopCountConjugateEvidence

abbrev wm_provenanceRightBiasMerge :=
  @Mettapedia.Logic.provenanceRightBiasMerge

noncomputable abbrev wm_provenanceRightBiasOverlapLayer :=
  @Mettapedia.Logic.provenanceRightBiasOverlapLayer

noncomputable abbrev wm_provenanceSwapAnomalyCount :=
  @Mettapedia.Logic.provenanceSwapAnomalyCount

noncomputable abbrev wm_provenanceScheduleErrorCount :=
  @Mettapedia.Logic.provenanceScheduleErrorCount

abbrev wm_provenanceScheduleErrorBound :=
  @Mettapedia.Logic.provenanceScheduleErrorBound

abbrev wm_provenanceSwapAnomalyCount_eq_zero_of_query_eq :=
  @Mettapedia.Logic.provenanceSwapAnomalyCount_eq_zero_of_query_eq

abbrev wm_provenanceSwapAnomalyCount_eq_top_of_zero_then_nonzero :=
  @Mettapedia.Logic.provenanceSwapAnomalyCount_eq_top_of_zero_then_nonzero

abbrev wm_provenanceScheduleErrorCount_twoStep_eq_top_of_zero_then_nonzero :=
  @Mettapedia.Logic.provenanceScheduleErrorCount_twoStep_eq_top_of_zero_then_nonzero

abbrev wm_provenanceScheduleErrorBound_twoStep_top_of_zero_then_nonzero :=
  @Mettapedia.Logic.provenanceScheduleErrorBound_twoStep_top_of_zero_then_nonzero

abbrev wm_provenanceScheduleErrorBound_twoStep_not_zero_of_zero_then_nonzero :=
  @Mettapedia.Logic.provenanceScheduleErrorBound_twoStep_not_zero_of_zero_then_nonzero

/-! ## Gas-Lane Order-Budget Policy Endpoints -/

noncomputable abbrev wm_gasAdditiveOverlapLayer :=
  @Mettapedia.Logic.gasAdditiveOverlapLayer

noncomputable abbrev wm_gasScheduleErrorCount :=
  @Mettapedia.Logic.gasScheduleErrorCount

abbrev wm_gasScheduleErrorBound :=
  @Mettapedia.Logic.gasScheduleErrorBound

abbrev wm_gasOrderBudgetPolicy :=
  @Mettapedia.Logic.gasOrderBudgetPolicy

abbrev wm_gasScheduleErrorCount_batchSwap_eq_zero :=
  @Mettapedia.Logic.gasScheduleErrorCount_batchSwap_eq_zero

abbrev wm_gasRuntimePairwiseOrderCheck_batchSwap_zero :=
  @Mettapedia.Logic.gasRuntimePairwiseOrderCheck_batchSwap_zero

abbrev wm_gasOrderBudgetPolicy_batchSwap_zero_via_runtimeCertificate :=
  @Mettapedia.Logic.gasOrderBudgetPolicy_batchSwap_zero_via_runtimeCertificate

abbrev wm_gasPolicy_zeroThreshold_ethanol :=
  @Mettapedia.Logic.gasPolicy_zeroThreshold_ethanol

abbrev wm_gasPolicy_zeroThreshold_ammonia :=
  @Mettapedia.Logic.gasPolicy_zeroThreshold_ammonia

abbrev wm_gasPolicy_zeroThreshold_toluene :=
  @Mettapedia.Logic.gasPolicy_zeroThreshold_toluene

/-! ## Coalition / Semitopology Endpoints -/

abbrev WMSemitopology :=
  Mettapedia.Logic.Semitopology

abbrev WMCoalitionTopology :=
  Mettapedia.Logic.CoalitionTopology

abbrev wm_topological_of_intersection_closed :=
  @Mettapedia.Logic.Semitopology.topological_of_intersection_closed

abbrev wm_local_consensus_of_constant_on_actionable :=
  @Mettapedia.Logic.Semitopology.local_consensus_of_constant_on_actionable

abbrev wm_discontinuity_of_conflicting_actionable_values :=
  @Mettapedia.Logic.Semitopology.discontinuity_of_conflicting_actionable_values

abbrev wm_overlap_additive_of_semitopologyIndependent :=
  @Mettapedia.Logic.Semitopology.additive_of_semitopologyIndependent

abbrev wm_exactInverse_of_supportedInActionableScope :=
  @Mettapedia.Logic.Semitopology.exactInverse_of_supportedInActionableScope

/-! ## Provenance→WM Support Bridge Endpoints -/

abbrev wm_whichSupport :=
  @Mettapedia.Logic.whichSupport

abbrev wm_whichSupport_add_union :=
  @Mettapedia.Logic.whichSupport_add_union

abbrev wm_exactInverse_supported_outside_zero_which :=
  @Mettapedia.Logic.exactInverse_supported_outside_zero_of_whichSupport

abbrev wm_whichSupportTagged :=
  @Mettapedia.Logic.whichSupportTagged

noncomputable abbrev wm_whichEmptyScopeForgettingLayer :=
  @Mettapedia.Logic.whichEmptyScopeForgettingLayer

abbrev wm_whichEmptyScope_exactInverse_of_supported :=
  @Mettapedia.Logic.whichEmptyScope_exactInverse_of_supported

abbrev wm_whichEmptyScope_revision_zero_of_supported :=
  @Mettapedia.Logic.whichEmptyScope_revision_zero_of_supported

abbrev wm_trackedWhichState :=
  Mettapedia.Logic.TrackedWhichState

abbrev wm_tracked_exactInverse_of_trackedRevision :=
  @Mettapedia.Logic.tracked_exactInverse_of_trackedRevision

abbrev wm_forgetWhichSupportBy :=
  @Mettapedia.Logic.forgetWhichSupportBy

abbrev wm_whichSupport_forgetWhichSupportBy :=
  @Mettapedia.Logic.whichSupport_forgetWhichSupportBy

abbrev wm_whichSupport_forgetWhichOverlap_add :=
  @Mettapedia.Logic.whichSupport_forgetWhichOverlap_add

abbrev wm_semitopologyIndependent_remainders_after_forgetting_overlap :=
  @Mettapedia.Logic.semitopologyIndependent_remainders_after_forgetting_overlap

abbrev wm_scopedTrackedWhichState :=
  Mettapedia.Logic.ScopedTrackedWhichState

abbrev wm_forgetScopedByScope :=
  @Mettapedia.Logic.forgetScopedByScope

abbrev wm_scopedTracked_exactInverse_of_supported_of_clean :=
  @Mettapedia.Logic.forgetScopedByScope_exactInverse_of_supported_of_clean

abbrev wm_trackedOverlapFootprint :=
  @Mettapedia.Logic.scopedOverlapFootprint

abbrev wm_additive_recovery_after_forgetting_nonactionable_overlap :=
  @Mettapedia.Logic.additive_recovery_after_forgetting_nonactionable_overlap

abbrev WMOverlapSeparatedAudit :=
  @Mettapedia.Logic.OverlapSeparatedAudit

abbrev wm_semitopologyIndependent_of_overlapSeparatedAudit :=
  @Mettapedia.Logic.semitopologyIndependent_of_overlapSeparatedAudit

abbrev wm_additiveRecovery_of_overlapSeparatedAudit :=
  @Mettapedia.Logic.additiveRecovery_of_overlapSeparatedAudit

/-! ## View-Induced Preorder Endpoints -/

abbrev wm_selectorPreorder :=
  @Mettapedia.Logic.PLNWorldModelPreorder.selectorPreorder

abbrev wm_selectorProductPreorder :=
  @Mettapedia.Logic.PLNWorldModelPreorder.selectorProductPreorder

noncomputable abbrev wm_supportConfidencePreorder :=
  Mettapedia.Logic.PLNWorldModelPreorder.supportConfidencePreorder

/-! ## Advanced Gaussian / One-Step EM Endpoints -/

abbrev advancedWeightedNormalGammaEvidence :=
  Mettapedia.Logic.WeightedNormalGammaEvidence

abbrev advancedWeightedNormalGammaPrior :=
  Mettapedia.Logic.WeightedNormalGammaPrior

abbrev advancedGaussianMixtureState :=
  Mettapedia.Logic.GaussianMixtureState

abbrev ch7_weightedGaussianStatistic :=
  @Mettapedia.Logic.SufficientStatisticSurface.weightedGaussianStatistic

abbrev ch7_hardLabelWeightedAggregate_eq_gaussianFilter :=
  @Mettapedia.Logic.SufficientStatisticSurface.indicatorGaussianStatistic_aggregate_eq_ofDiscrete_filter

abbrev ch7_hardLabelWeightedPosterior_eq_gaussianFilter :=
  @Mettapedia.Logic.SufficientStatisticSurface.indicatorGaussianStatistic_posterior_eq_gaussian_filter

abbrev ch7_gaussianEM_unit_mStep_eq_gaussian :=
  @Mettapedia.Logic.PLNGaussianEM.GaussianMixtureState.mStepPosterior_unit_eq_gaussian

/-! ## PLN↔NARS Rule Correspondence canonical aliases -/

abbrev PLNNARSRuleBridgeBundle :=
  Mettapedia.Logic.PLNNARSRuleCorrespondence.PLNNARSRuleBridgeBundle

abbrev plnNarsRuleBridgeBundle :=
  Mettapedia.Logic.PLNNARSRuleCorrespondence.plnNarsRuleBridgeBundle

abbrev NARSTruthValue :=
  Mettapedia.Logic.NARSPLNGaloisConnection.NARSTruthValue

abbrev NARSPLNBelief :=
  Mettapedia.Logic.NARSPLNGaloisConnection.PLNBelief

noncomputable abbrev L_narsToPln :=
  Mettapedia.Logic.NARSPLNGaloisConnection.L

noncomputable abbrev U_plnToNars :=
  Mettapedia.Logic.NARSPLNGaloisConnection.U

abbrev L_le_iff_le_U_nars_pln :=
  @Mettapedia.Logic.NARSPLNGaloisConnection.L_le_iff_le_U

abbrev galoisConnection_L_U_finite_nars_pln :=
  @Mettapedia.Logic.NARSPLNGaloisConnection.galoisConnection_L_U_finite

abbrev narsToPLNTV :=
  Mettapedia.Logic.PLNNARSRuleCorrespondence.narsToPLNTV

abbrev plnToNARSTV :=
  Mettapedia.Logic.PLNNARSRuleCorrespondence.plnToNARSTV

/-! ## Chapter-13 Inference-Control Core Endpoints -/

noncomputable abbrev ch13ScorePooled :=
  @Mettapedia.Logic.PLNInferenceControlCore.ch13ScorePooled

noncomputable abbrev ch13ScoreTwoStage :=
  @Mettapedia.Logic.PLNInferenceControlCore.ch13ScoreTwoStage

abbrev ch13_selector_default_ranking_iff :=
  @Mettapedia.Logic.PLNInferenceControlCore.ch13_selector_default_ranking_iff

abbrev ch13_stable_pooled_of_twoStage :=
  @Mettapedia.Logic.PLNInferenceControlCore.ch13_stable_pooled_of_twoStage

abbrev ch13_inferenceControl_end_to_end :=
  @Mettapedia.Logic.PLNInferenceControlCore.ch13_inferenceControl_end_to_end

noncomputable abbrev ch13_greedyPick? :=
  @Mettapedia.Logic.PLNInferenceControlAlgorithms.greedyPick?

noncomputable abbrev ch13_greedySelect :=
  @Mettapedia.Logic.PLNInferenceControlAlgorithms.greedySelect

abbrev ch13_greedySelect_chain_of_le_card :=
  @Mettapedia.Logic.PLNInferenceControlAlgorithms.greedySelect_chain_of_le_card

abbrev ch13_inferenceControl_end_to_end_algorithmic :=
  @Mettapedia.Logic.PLNInferenceControlAlgorithms.ch13_inferenceControl_end_to_end_algorithmic

noncomputable abbrev ch13_forwardStep :=
  @Mettapedia.Logic.PLNInferenceControlChainer.forwardStep

noncomputable abbrev ch13_forwardSearch :=
  @Mettapedia.Logic.PLNInferenceControlChainer.forwardSearch

noncomputable abbrev ch13_backwardStep :=
  @Mettapedia.Logic.PLNInferenceControlChainer.backwardStep

noncomputable abbrev ch13_backwardSearch :=
  @Mettapedia.Logic.PLNInferenceControlChainer.backwardSearch

noncomputable abbrev ch13_boundedSearch :=
  @Mettapedia.Logic.PLNInferenceControlChainer.boundedSearch

abbrev ch13_forwardSearch_chain_of_le_card :=
  @Mettapedia.Logic.PLNInferenceControlChainer.forwardSearch_chain_of_le_card

abbrev ch13_forwardSearch_one_minus_exp_bound_of_le_card :=
  @Mettapedia.Logic.PLNInferenceControlChainer.forwardSearch_one_minus_exp_bound_of_le_card

abbrev ch13_boundedSearch_eq_forwardSearch_of_card_le_topK :=
  @Mettapedia.Logic.PLNInferenceControlChainer.boundedSearch_eq_forwardSearch_of_card_le_topK

abbrev ch13_bool_end_to_end_algorithmic :=
  Mettapedia.Logic.PLNInferenceControlExamples.ch13_bool_end_to_end_algorithmic

abbrev ch13_bool_coverage_exact_one :=
  Mettapedia.Logic.PLNInferenceControlExamples.ch13_bool_coverage_exact_one

abbrev ch13_fin3_end_to_end_algorithmic_topK2 :=
  Mettapedia.Logic.PLNInferenceControlExamples.ch13_fin3_end_to_end_algorithmic_topK2

abbrev ch13_fin3_coverage_exact_two :=
  Mettapedia.Logic.PLNInferenceControlExamples.ch13_fin3_coverage_exact_two

/-! ## Canonical rule-strength names -/

noncomputable abbrev deductionStrength := PLN.plnDeductionStrength
noncomputable abbrev inductionStrength := PLN.plnInductionStrength
noncomputable abbrev abductionStrength := PLN.plnAbductionStrength

noncomputable abbrev sourceRuleStrength := PLN.plnSourceRuleStrength
noncomputable abbrev sinkRuleStrength := PLN.plnSinkRuleStrength

theorem sourceRule_eq_induction (s_BA s_BC s_A s_B s_C : ℝ) :
    sourceRuleStrength s_BA s_BC s_A s_B s_C =
      inductionStrength s_BA s_BC s_A s_B s_C := rfl

theorem sinkRule_eq_abduction (s_AB s_CB s_A s_B s_C : ℝ) :
    sinkRuleStrength s_AB s_CB s_A s_B s_C =
      abductionStrength s_AB s_CB s_A s_B s_C := rfl

/-! ## WM-calculus canonical type aliases -/

abbrev WMQueryEq {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WMQueryEq (State := State) (Query := Query)

abbrev WMEvidenceLE {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WMEvidenceLE (State := State) (Query := Query)

abbrev WMViewEq {State Query : Type*} {α : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WMViewEq (State := State) (Query := Query) (α := α)

abbrev WMRewriteRule (State Query : Type*)
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WMRewriteRule State Query

abbrev WMQueryEqSigma {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.WMQueryEqSigma
    (State := State) (Srt := Srt) (Query := Query)

abbrev WMEvidenceLESigma {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.WMEvidenceLESigma
    (State := State) (Srt := Srt) (Query := Query)

abbrev WMViewEqSigma {State Srt : Type*} {Query : Srt → Type*} {α : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.WMViewEqSigma
    (State := State) (Srt := Srt) (Query := Query) (α := α)

abbrev WorldModelSigma (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceClass.EvidenceType State] :=
  PLNWorldModel.WorldModelSigma State Srt Query

abbrev WMRewriteRuleSigma (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query

abbrev WMStrengthRuleSigma (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.WMStrengthRuleSigma State Srt Query

/-! ## WM-Core View Aliases (Strength/Confidence/Interpretation) -/

/-  Naming convention:
`wmQuery*` aliases expose ENNReal-valued core views (not the Chapter-8 `Real` wrappers).
Use `wmQueryEq*_to_*` aliases for transport/equivalence lemmas on those core views. -/

noncomputable abbrev wmQueryStrengthWith {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WorldModel.queryStrengthWith (State := State) (Query := Query)

noncomputable abbrev wmQueryConfidenceENN {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WorldModel.queryConfidence (State := State) (Query := Query)

abbrev wmQueryInterpret {State Query : Type*} {Ctx Val : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    [EvidenceClass.InterpretableEvidence Ctx Evidence Val] :=
  PLNWorldModel.WorldModel.queryInterpret
    (State := State) (Query := Query) (Ctx := Ctx) (Val := Val)

noncomputable abbrev wmQueryStrengthWithSigma {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.queryStrengthWith
    (State := State) (Srt := Srt) (Query := Query)

noncomputable abbrev wmQueryConfidenceSigmaENN {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.queryConfidence
    (State := State) (Srt := Srt) (Query := Query)

abbrev wmQueryInterpretSigma {State Srt : Type*} {Query : Srt → Type*} {Ctx Val : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    [EvidenceClass.InterpretableEvidence Ctx Evidence Val] :=
  PLNWorldModel.WorldModelSigma.queryInterpret
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx) (Val := Val)

abbrev wmQueryEq_to_queryStrengthWith :=
  @PLNWorldModel.WMQueryEq.to_queryStrengthWith

abbrev wmQueryEq_to_queryStrengthWith_threshold :=
  @PLNWorldModel.WMQueryEq.to_queryStrengthWith_threshold

abbrev wmQueryEq_to_queryConfidenceENN :=
  @PLNWorldModel.WMQueryEq.to_queryConfidence

abbrev wmQueryEq_to_queryConfidenceENN_threshold :=
  @PLNWorldModel.WMQueryEq.to_queryConfidence_threshold

abbrev wmQueryEq_to_queryInterpret :=
  @PLNWorldModel.WMQueryEq.to_queryInterpret

abbrev wmQueryEqSigma_to_queryStrengthWith :=
  @PLNWorldModel.WorldModelSigma.WMQueryEqSigma.to_queryStrengthWith

abbrev wmQueryEqSigma_to_queryStrengthWith_threshold :=
  @PLNWorldModel.WorldModelSigma.WMQueryEqSigma.to_queryStrengthWith_threshold

abbrev wmQueryEqSigma_to_queryConfidenceENN :=
  @PLNWorldModel.WorldModelSigma.WMQueryEqSigma.to_queryConfidence

abbrev wmQueryEqSigma_to_queryConfidenceENN_threshold :=
  @PLNWorldModel.WorldModelSigma.WMQueryEqSigma.to_queryConfidence_threshold

abbrev wmQueryEqSigma_to_queryInterpret :=
  @PLNWorldModel.WorldModelSigma.WMQueryEqSigma.to_queryInterpret

/-! ## Error-Magnification Grounding Aliases -/

noncomputable abbrev queryConfidence {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  @PLNErrorMagnificationGrounding.queryConfidence

noncomputable abbrev queryConfidenceSigma {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  @PLNErrorMagnificationGrounding.queryConfidenceSigma

noncomputable abbrev thresholdAtomSemOfWMQConfidence {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  @PLNErrorMagnificationGrounding.thresholdAtomSemOfWMQConfidence

noncomputable abbrev thresholdAtomSemOfWMQSigmaConfidence {State Srt : Type*}
    {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  @PLNErrorMagnificationGrounding.thresholdAtomSemOfWMQSigmaConfidence

abbrev wmRewriteRule_threshold_atom_confidence :=
  @PLNErrorMagnificationGrounding.wmRewriteRule_threshold_atom_confidence

abbrev wmRewriteRuleSigma_threshold_atom_confidence :=
  @PLNErrorMagnificationGrounding.wmRewriteRuleSigma_threshold_atom_confidence

abbrev rewrite_then_queryEq_threshold_atom_confidence_sigma :=
  @PLNErrorMagnificationGrounding.rewrite_then_queryEq_threshold_atom_confidence_sigma

abbrev double_damping_underestimates_of_queries :=
  @PLNErrorMagnificationGrounding.double_damping_underestimates_of_queries

abbrev threshold_gap_of_double_damping_of_queries :=
  @PLNErrorMagnificationGrounding.threshold_gap_of_double_damping_of_queries

/-! ## ITV semantics canonical aliases -/

abbrev ITV := PLNIndefiniteTruth.ITV

abbrev ITVSemantics (Ctx : Type*) := PLNWorldModel.ITVSemantics Ctx

abbrev BinaryContext := EvidenceClass.BinaryContext

abbrev IDMPredictiveContext := PLNWorldModel.IDMPredictiveContext

noncomputable abbrev queryITV {State Query Ctx : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WorldModel.queryITV (State := State) (Query := Query) (Ctx := Ctx)

noncomputable abbrev queryITVSigma {State Srt Ctx : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.queryITV
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)

abbrev WMITVJudgment {State Query Ctx : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WorldModel.WMITVJudgment
    (State := State) (Query := Query) (Ctx := Ctx)

abbrev WMITVJudgmentCtx {State Query Ctx : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WorldModel.WMITVJudgmentCtx
    (State := State) (Query := Query) (Ctx := Ctx)

abbrev WMITVJudgmentSigma {State Srt Ctx : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.WMITVJudgmentSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)

abbrev WMITVJudgmentCtxSigma {State Srt Ctx : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.WMITVJudgmentCtxSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)

noncomputable def queryITVSigmaBayes95 {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : EvidenceClass.BinaryContext) (W : State) (q : Sigma Query) : ITV :=
  queryITVSigma (State := State) (Srt := Srt) (Query := Query) (Ctx := EvidenceClass.BinaryContext)
    PLNWorldModel.ITVSemantics.bayesCredible95 ctx W q

noncomputable def queryITVSigmaBayes90 {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : EvidenceClass.BinaryContext) (W : State) (q : Sigma Query) : ITV :=
  queryITVSigma (State := State) (Srt := Srt) (Query := Query) (Ctx := EvidenceClass.BinaryContext)
    PLNWorldModel.ITVSemantics.bayesCredible90 ctx W q

noncomputable def queryITVSigmaBayesExact95 {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : EvidenceClass.BinaryContext) (W : State) (q : Sigma Query) : ITV :=
  queryITVSigma (State := State) (Srt := Srt) (Query := Query) (Ctx := EvidenceClass.BinaryContext)
    PLNWorldModel.ITVSemantics.bayesCredibleExact95 ctx W q

noncomputable def queryITVSigmaBayesExact90 {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : EvidenceClass.BinaryContext) (W : State) (q : Sigma Query) : ITV :=
  queryITVSigma (State := State) (Srt := Srt) (Query := Query) (Ctx := EvidenceClass.BinaryContext)
    PLNWorldModel.ITVSemantics.bayesCredibleExact90 ctx W q

noncomputable def queryITVSigmaWalleyIDM {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : IDMPredictiveContext) (W : State) (q : Sigma Query) : ITV :=
  queryITVSigma (State := State) (Srt := Srt) (Query := Query) (Ctx := IDMPredictiveContext)
    PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q

noncomputable def queryITVSigmaBayes95Jeffreys {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (W : State) (q : Sigma Query) : ITV :=
  queryITVSigmaBayes95 (State := State) (Srt := Srt) (Query := Query)
    EvidenceClass.BinaryContext.jeffreys W q

noncomputable def queryITVSigmaBayesExact95Jeffreys {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (W : State) (q : Sigma Query) : ITV :=
  queryITVSigmaBayesExact95 (State := State) (Srt := Srt) (Query := Query)
    EvidenceClass.BinaryContext.jeffreys W q

noncomputable def queryITVSigmaWalleyIDMDefault {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (W : State) (q : Sigma Query) : ITV :=
  queryITVSigmaWalleyIDM (State := State) (Srt := Srt) (Query := Query)
    PLNWorldModel.IDMPredictiveContext.default W q

theorem queryITVWalley_width_add_credibility
    {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (ctx : IDMPredictiveContext) (W : State) (q : Query) :
    PLNWorldModel.WorldModel.queryITVWidth
      (State := State) (Query := Query)
      PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      +
      PLNWorldModel.WorldModel.queryITVCredibility
        (State := State) (Query := Query)
        PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      = 1 :=
  PLNWorldModel.WorldModel.queryITVWidth_add_queryITVCredibility_walley
    (State := State) (Query := Query) ctx W q

theorem queryITVWalley_width_eq_one_sub_credibility
    {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (ctx : IDMPredictiveContext) (W : State) (q : Query) :
    PLNWorldModel.WorldModel.queryITVWidth
      (State := State) (Query := Query)
      PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      =
      1 -
      PLNWorldModel.WorldModel.queryITVCredibility
        (State := State) (Query := Query)
        PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q :=
  PLNWorldModel.WorldModel.queryITVWidth_eq_one_sub_queryITVCredibility_walley
    (State := State) (Query := Query) ctx W q

theorem queryITVSigmaWalley_width_add_credibility
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : IDMPredictiveContext) (W : State) (q : Sigma Query) :
    PLNWorldModel.WorldModelSigma.queryITVWidth
      (State := State) (Srt := Srt) (Query := Query)
      PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      +
      PLNWorldModel.WorldModelSigma.queryITVCredibility
        (State := State) (Srt := Srt) (Query := Query)
        PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      = 1 :=
  PLNWorldModel.WorldModelSigma.queryITVWidth_add_queryITVCredibility_walley
    (State := State) (Srt := Srt) (Query := Query) ctx W q

theorem queryITVSigmaWalley_width_eq_one_sub_credibility
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : IDMPredictiveContext) (W : State) (q : Sigma Query) :
    PLNWorldModel.WorldModelSigma.queryITVWidth
      (State := State) (Srt := Srt) (Query := Query)
      PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      =
      1 -
      PLNWorldModel.WorldModelSigma.queryITVCredibility
        (State := State) (Srt := Srt) (Query := Query)
        PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q :=
  PLNWorldModel.WorldModelSigma.queryITVWidth_eq_one_sub_queryITVCredibility_walley
    (State := State) (Srt := Srt) (Query := Query) ctx W q

/-! ## ITV Hypercube canonical aliases -/

abbrev WMIntervalSemantics :=
  Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics

abbrev CtxOfInterval := PLNWorldModelITVHypercube.CtxOfInterval
abbrev CtxOfVertex := PLNWorldModelITVHypercube.CtxOfVertex

noncomputable abbrev semanticsOfInterval :=
  PLNWorldModelITVHypercube.semanticsOfInterval

noncomputable abbrev queryITVSigmaOfInterval {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModelITVHypercube.queryITVSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query)

noncomputable abbrev queryITVAtVertex {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModelITVHypercube.queryITVAtVertex
    (State := State) (Srt := Srt) (Query := Query)

abbrev WMITVThresholdJudgmentSigma {State Srt Ctx : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWorldModel.WorldModelSigma.WMITVThresholdJudgmentSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)

abbrev queryEq_to_queryITVSigmaOfInterval :=
  @PLNWorldModelITVHypercube.WMQueryEqSigma.to_queryITVSigmaOfInterval

abbrev queryEq_to_queryITVSigma_bayesExact :=
  @PLNWorldModelITVHypercube.WMQueryEqSigma.to_queryITVSigma_bayesExact

abbrev queryEq_to_queryITVSigma_walley :=
  @PLNWorldModelITVHypercube.WMQueryEqSigma.to_queryITVSigma_walley

abbrev queryEq_to_WMITVJudgmentSigmaOfInterval :=
  @PLNWorldModelITVHypercube.WMQueryEqSigma.to_WMITVJudgmentSigmaOfInterval

abbrev queryEq_to_WMITVJudgmentSigma_bayesExact :=
  @PLNWorldModelITVHypercube.WMQueryEqSigma.to_WMITVJudgmentSigma_bayesExact

abbrev queryEq_to_WMITVJudgmentSigma_walley :=
  @PLNWorldModelITVHypercube.WMQueryEqSigma.to_WMITVJudgmentSigma_walley

abbrev queryEq_to_WMITVThresholdJudgmentSigmaOfInterval :=
  @PLNWorldModelITVHypercube.WMQueryEqSigma.to_WMITVThresholdJudgmentSigmaOfInterval

abbrev queryEq_to_WMITVThresholdJudgmentSigma_bayesExact :=
  @PLNWorldModelITVHypercube.WMQueryEqSigma.to_WMITVThresholdJudgmentSigma_bayesExact

abbrev queryEq_to_WMITVThresholdJudgmentSigma_walley :=
  @PLNWorldModelITVHypercube.WMQueryEqSigma.to_WMITVThresholdJudgmentSigma_walley

abbrev applyITV_ofInterval :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITV_ofInterval

abbrev applyITVThreshold_ofInterval :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_ofInterval

abbrev applyITV_bayesExact_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITV_bayesExact_selector

abbrev applyITV_walley_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITV_walley_selector

abbrev applyITVThreshold_bayesExact_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_bayesExact_selector

abbrev applyITVThreshold_walley_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_walley_selector

abbrev applyITVThreshold_bayesExact_lower_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_bayesExact_lower_selector

abbrev applyITVThreshold_bayesExact_upper_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_bayesExact_upper_selector

abbrev applyITVThreshold_bayesExact_credibility_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_bayesExact_credibility_selector

abbrev applyITVThreshold_bayesExact_width_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_bayesExact_width_selector

abbrev applyITVThreshold_bayesExact_strength_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_bayesExact_strength_selector

abbrev applyITVThreshold_walley_lower_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_walley_lower_selector

abbrev applyITVThreshold_walley_upper_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_walley_upper_selector

abbrev applyITVThreshold_walley_credibility_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_walley_credibility_selector

abbrev applyITVThreshold_walley_width_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_walley_width_selector

abbrev applyITVThreshold_walley_strength_selector :=
  @PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_walley_strength_selector

/-! ## OSLF/GSLT Hypercube canonical aliases -/

abbrev vertexLanguageDef :=
  Mettapedia.OSLF.Framework.VertexRewriteRules.vertexLanguageDef

abbrev gslt_forward_transport :=
  @Mettapedia.OSLF.Framework.HypercubeGSLTFunctor.gslt_forward_transport

abbrev vertexTemporalLanguageDef :=
  Mettapedia.OSLF.Framework.VertexTemporalRewriteRules.vertexTemporalLanguageDef

abbrev gslt_temporal_forward_transport :=
  @Mettapedia.OSLF.Framework.HypercubeTemporalGSLTFunctor.gslt_temporal_forward_transport

abbrev hypercube_forward_quantale_coherence_bundle :=
  @Mettapedia.OSLF.Framework.QuantaleCoherence.hypercube_forward_quantale_coherence_bundle

abbrev hypercube_forward_quantale_coherence_bundle_temporal :=
  @Mettapedia.OSLF.Framework.QuantaleCoherence.hypercube_forward_quantale_coherence_bundle_temporal

/-- One-call Bayes-exact threshold transport:
rewrite-preservation followed by typed query-equivalence transport. -/
theorem applyITVThreshold_then_queryEq_transport_bayesExact
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {r : WMRewriteRuleSigma State Srt Query} {W : State} {q : Sigma Query}
    (ctx : CtxOfInterval .bayesExact)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesExact).eval ctx (r.derive W)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) r.conclusion q) :
    WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := CtxOfInterval .bayesExact)
      (semanticsOfInterval .bayesExact) ctx W q coord tau := by
  exact queryEq_to_WMITVThresholdJudgmentSigma_bayesExact
    (State := State) (Srt := Srt) (Query := Query)
    (q₁ := r.conclusion) (q₂ := q)
    hEq ctx coord tau
    (applyITVThreshold_bayesExact_selector
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) ctx coord tau hSide hW hTau)

/-- One-call Bayes-normal threshold transport:
rewrite-preservation followed by typed query-equivalence transport. -/
theorem applyITVThreshold_then_queryEq_transport_bayesNormal
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {r : WMRewriteRuleSigma State Srt Query} {W : State} {q : Sigma Query}
    (ctx : CtxOfInterval .bayesNormal)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesNormal).eval ctx (r.derive W)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) r.conclusion q) :
    WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := CtxOfInterval .bayesNormal)
      (semanticsOfInterval .bayesNormal) ctx W q coord tau := by
  exact queryEq_to_WMITVThresholdJudgmentSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query)
    (q₁ := r.conclusion) (q₂ := q)
    hEq .bayesNormal ctx coord tau
    (applyITVThreshold_ofInterval
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) .bayesNormal ctx coord tau hSide hW hTau)

/-- One-call Walley threshold transport:
rewrite-preservation followed by typed query-equivalence transport. -/
theorem applyITVThreshold_then_queryEq_transport_walley
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {r : WMRewriteRuleSigma State Srt Query} {W : State} {q : Sigma Query}
    (ctx : CtxOfInterval .walleyIDM)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W)
    (hTau : tau ≤ coord ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) r.conclusion q) :
    WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := CtxOfInterval .walleyIDM)
      (semanticsOfInterval .walleyIDM) ctx W q coord tau := by
  exact queryEq_to_WMITVThresholdJudgmentSigma_walley
    (State := State) (Srt := Srt) (Query := Query)
    (q₁ := r.conclusion) (q₂ := q)
    hEq ctx coord tau
    (applyITVThreshold_walley_selector
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) ctx coord tau hSide hW hTau)

/-- End-to-end Bayes-exact bundle:
rewrite/query transport + quantale/selector coherence in one call. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bayesExact
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval .bayesExact).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
          PLNWorldModel.ITVSemantics.bayesCredibleExact95 ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  have hThresh :=
    applyITVThreshold_then_queryEq_transport_bayesExact
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) (q := queryOfAtom₁ a0 p)
      ctx coord tau hSide hW hTau hEq
  rcases hThresh with ⟨_hWq, hTauQ⟩
  have hTauP :
      tau ≤ coord (PLNWorldModel.ITVSemantics.bayesCredibleExact95.eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
    simpa [PLNWorldModel.WorldModelSigma.queryITV, semanticsOfInterval,
      PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
  exact
    PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := coord) (tau := tau)
      (hVal := hVal)
      (pick := fun _ : Unit => p)
      (hReach := by
        intro _u
        exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
      (H := H)
      (hTau := by
        intro _u
        simpa using hTauP)

/-- End-to-end Bayes-normal bundle:
rewrite/query transport + quantale/selector coherence in one call. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bayesNormal
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : BinaryContext)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval .bayesNormal).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query) (Ctx := BinaryContext)
          PLNWorldModel.ITVSemantics.bayesCredible95 ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  have hThresh :=
    applyITVThreshold_then_queryEq_transport_bayesNormal
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) (q := queryOfAtom₁ a0 p)
      ctx coord tau hSide hW hTau hEq
  rcases hThresh with ⟨_hWq, hTauQ⟩
  have hTauP :
      tau ≤ coord (PLNWorldModel.ITVSemantics.bayesCredible95.eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
    simpa [PLNWorldModel.WorldModelSigma.queryITV, semanticsOfInterval,
      PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
  exact
    PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m)
      (itvSem := PLNWorldModel.ITVSemantics.bayesCredible95) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := coord) (tau := tau)
      (hVal := hVal)
      (pick := fun _ : Unit => p)
      (hReach := by
        intro _u
        exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
      (H := H)
      (hTau := by
        intro _u
        simpa using hTauP)

/-- End-to-end Walley bundle:
rewrite/query transport + quantale/selector coherence in one call. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_walley
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : IDMPredictiveContext)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query) (Ctx := IDMPredictiveContext)
          PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  have hThresh :=
    applyITVThreshold_then_queryEq_transport_walley
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) (q := queryOfAtom₁ a0 p)
      ctx coord tau hSide hW hTau hEq
  rcases hThresh with ⟨_hWq, hTauQ⟩
  have hTauP :
      tau ≤ coord (PLNWorldModel.ITVSemantics.walleyIDMPredictive.eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
    simpa [PLNWorldModel.WorldModelSigma.queryITV, semanticsOfInterval,
      PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
  exact
    PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := coord) (tau := tau)
      (hVal := hVal)
      (pick := fun _ : Unit => p)
      (hReach := by
        intro _u
        exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
      (H := H)
      (hTau := by
        intro _u
        simpa using hTauP)

/-- Interval-indexed one-call bundle:
hypercube selector transport + rewrite/query transport + quantale coherence. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_of_interval
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query)
          (Ctx := CtxOfInterval i)
          (semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  cases i with
  | bayesNormal =>
      simpa [WMIntervalSemantics, CtxOfInterval, semanticsOfInterval] using
        (end_to_end_quantale_selector_rewrite_query_threshold_bayesNormal
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (r := r) (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (p := p) (coord := coord) (tau := tau)
          hSide hW hTau hEq hVal H)
  | bayesExact =>
      simpa [WMIntervalSemantics, CtxOfInterval, semanticsOfInterval] using
        (end_to_end_quantale_selector_rewrite_query_threshold_bayesExact
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (r := r) (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (p := p) (coord := coord) (tau := tau)
          hSide hW hTau hEq hVal H)
  | walleyIDM =>
      simpa [WMIntervalSemantics, CtxOfInterval, semanticsOfInterval] using
        (end_to_end_quantale_selector_rewrite_query_threshold_walley
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (r := r) (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (p := p) (coord := coord) (tau := tau)
          hSide hW hTau hEq hVal H)

/-- Interval-indexed one-call bundle for genuinely dependent query families.
This composes rewrite/query ITV transport and quantale coherence in one theorem. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_of_interval_dep
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query)
          (Ctx := CtxOfInterval i)
          (semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  cases i with
  | bayesNormal =>
      have hThresh :=
        applyITVThreshold_then_queryEq_transport_bayesNormal
          (State := State) (Srt := Srt) (Query := Query)
          (r := r) (q := queryOfAtom₁ a0 p)
          ctx coord tau hSide hW hTau hEq
      rcases hThresh with ⟨_hWq, hTauQ⟩
      have hTauP :
          tau ≤ coord (PLNWorldModel.ITVSemantics.bayesCredible95.eval ctx
            (PLNWMOSLFBridgeITVTyped.wmPatternValuation
              (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
        simpa [PLNWorldModel.WorldModelSigma.queryITV, semanticsOfInterval,
          PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
      exact
        PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesNormal_id
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (coord := coord) (tau := tau)
          (hVal := hVal)
          (pick := fun _ : Unit => p)
          (hReach := by
            intro _u
            exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
          (H := H)
          (hTau := by
            intro _u
            simpa using hTauP)
  | bayesExact =>
      have hThresh :=
        applyITVThreshold_then_queryEq_transport_bayesExact
          (State := State) (Srt := Srt) (Query := Query)
          (r := r) (q := queryOfAtom₁ a0 p)
          ctx coord tau hSide hW hTau hEq
      rcases hThresh with ⟨_hWq, hTauQ⟩
      have hTauP :
          tau ≤ coord (PLNWorldModel.ITVSemantics.bayesCredibleExact95.eval ctx
            (PLNWMOSLFBridgeITVTyped.wmPatternValuation
              (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
        simpa [PLNWorldModel.WorldModelSigma.queryITV, semanticsOfInterval,
          PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
      exact
        PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (coord := coord) (tau := tau)
          (hVal := hVal)
          (pick := fun _ : Unit => p)
          (hReach := by
            intro _u
            exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
          (H := H)
          (hTau := by
            intro _u
            simpa using hTauP)
  | walleyIDM =>
      have hThresh :=
        applyITVThreshold_then_queryEq_transport_walley
          (State := State) (Srt := Srt) (Query := Query)
          (r := r) (q := queryOfAtom₁ a0 p)
          ctx coord tau hSide hW hTau hEq
      rcases hThresh with ⟨_hWq, hTauQ⟩
      have hTauP :
          tau ≤ coord (PLNWorldModel.ITVSemantics.walleyIDMPredictive.eval ctx
            (PLNWMOSLFBridgeITVTyped.wmPatternValuation
              (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
        simpa [PLNWorldModel.WorldModelSigma.queryITV, semanticsOfInterval,
          PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
      exact
        PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (coord := coord) (tau := tau)
          (hVal := hVal)
          (pick := fun _ : Unit => p)
          (hReach := by
            intro _u
            exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
          (H := H)
          (hTau := by
            intro _u
            simpa using hTauP)

/-- Canonical structured output type for one-call end-to-end transport/coherence. -/
abbrev EndToEndQuantaleSelectorRewriteQueryThresholdBundle
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (H : Finset (Unit × Unit)) : Prop :=
  (∀ _ : Unit,
    Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
  Mettapedia.Algebra.QuantaleWeakness.weakness
    (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
      (PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
      (fun _ : Unit => p)) H =
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
        m.mapTerm (fun _ : Unit => p)) H ∧
  (∀ u : Unit,
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
      (.atom a0) (m.mapTerm ((fun _ : Unit => p) u)))

/-- Bundle endpoint:
interval-indexed one-call transport from selector + rewrite/query + quantale coherence. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdBundle
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H := by
  exact end_to_end_quantale_selector_rewrite_query_threshold_of_interval
    (State := State) (Srt := Srt) (Query := Query)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Bundle endpoint for genuinely dependent query families. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval_dep
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdBundle
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H := by
  exact end_to_end_quantale_selector_rewrite_query_threshold_of_interval_dep
    (State := State) (Srt := Srt) (Query := Query)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Record-valued end-to-end artifact (not a conjunction):
selector transport + rewrite/query transport + quantale coherence. -/
structure EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (H : Finset (Unit × Unit)) : Type where
  reachability :
    ∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)
  quantale_coherence :
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H
  truth_transport :
    ∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query)
          (Ctx := CtxOfInterval i)
          (semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))

/-- Final one-call record-valued endpoint (interval-indexed). -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H := by
  rcases end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal H with ⟨hReach, hRest⟩
  rcases hRest with ⟨hWeak, hTruth⟩
  exact
    { reachability := hReach
      quantale_coherence := hWeak
      truth_transport := hTruth }

/-- Final one-call record-valued endpoint for dependent query families. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval_dep
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H := by
  rcases end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval_dep
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal H with ⟨hReach, hRest⟩
  rcases hRest with ⟨hWeak, hTruth⟩
  exact
    { reachability := hReach
      quantale_coherence := hWeak
      truth_transport := hTruth }

/-! ## Chapter-8 style threshold-acceptance endpoint -/

/-- Chapter-8 style threshold acceptance on the target side:
OSLF threshold-atom truth after WM rewrite + quantale/coherence transport. -/
def ch8ThresholdAccepted
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    (W₂ : State)
    (queryOfAtom₂ : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ) : Prop :=
  Mettapedia.OSLF.Formula.sem R
    (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
      (State := State) (Srt := Srt) (Query := Query)
      (Ctx := CtxOfInterval i)
      (semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
    (.atom a0) (m.mapTerm p)

/-- Any final-bundle witness gives Chapter-8 threshold acceptance directly. -/
theorem ch8_thresholdAccepted_of_finalBundle
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (H : Finset (Unit × Unit))
    (bundle :
      EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
        (State := State) (Srt := Srt) (Query := Query)
        (i := i) (R := R) (m := m) (ctx := ctx)
        W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H) :
    ch8ThresholdAccepted
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₂ queryOfAtom₂ a0 p coord tau := by
  simpa [ch8ThresholdAccepted] using bundle.truth_transport ()

/-- Single Chapter-8 one-call endpoint:
WM rewrite + OSLF transport + threshold acceptance as one theorem. -/
theorem ch8_wm_rewrite_oslf_threshold_acceptance_of_interval
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    ch8ThresholdAccepted
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₂ queryOfAtom₂ a0 p coord tau := by
  exact ch8_thresholdAccepted_of_finalBundle
    (State := State) (Srt := Srt) (Query := Query)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
    (a0 := a0) (p := p) (coord := coord) (tau := tau) (H := H)
    (end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal H)

/-! ## Chapter-9 positive composition endpoint (selector + rewrite + threshold) -/

/-- One-call composed endpoint for non-counterexample Chapter-9 development:
combine Chapter-13 algorithmic selector guarantees with Chapter-8
rewrite→OSLF→threshold acceptance.

The selector output `G` is mapped into the hypercube witness carrier via
`selectorWitness`, making the composition explicit while keeping the two
semantic layers modular. -/
theorem ch9_selector_rewrite_threshold_end_to_end_of_interval
    {Goal Fact Bin : Type*} [Fintype Fact] [DecidableEq Fact]
    (A : Mettapedia.Logic.PremiseSelection.PriorNBAssumptionChecklist Goal Fact Bin)
    (η : Fact → ℝ)
    (globalPrior localPrior likelihood : Mettapedia.Logic.PremiseSelection.Scorer Goal Fact)
    (g : Goal)
    (hLocal : A.localExchangeabilityInBin)
    (δ : Fact → ℝ) (ε : ℝ)
    (hTwoStage :
      Mettapedia.Logic.PremiseSelectionOptimality.BayesOptimalRanking η
        (ch13ScoreTwoStage globalPrior localPrior likelihood g))
    (hbound : ∀ x, |δ x| ≤ ε)
    (hmargin : ∀ x y, η x < η y →
      ch13ScorePooled globalPrior localPrior likelihood g y
        - ch13ScorePooled globalPrior localPrior likelihood g x > 2 * ε)
    (htie : ∀ x y, η x = η y → δ x = δ y)
    (D : Finset Fact)
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (selectorWitness : Finset Fact → Finset (Unit × Unit)) :
    let G := PLNInferenceControlAlgorithms.greedySelect D A.topK
    (A.topK ≤ Fintype.card Fact
      ∧ (∀ g' f',
          0 ≤ (Mettapedia.Logic.PremiseSelection.selectorDefaults_halfGate Goal Fact).gate g' f'
            ∧ (Mettapedia.Logic.PremiseSelection.selectorDefaults_halfGate Goal Fact).gate g' f' ≤ 1)
      ∧ Mettapedia.Logic.PremiseSelectionOptimality.BayesOptimalRanking η
          (Mettapedia.Logic.PremiseSelectionOptimality.perturbedScore
            (ch13ScorePooled globalPrior localPrior likelihood g) δ)
      ∧ (1 - Real.exp (-1)) * (Nat.min A.topK D.card : ℝ) ≤
          Mettapedia.Logic.PremiseSelection.dependencyCoverage D G)
      ∧ ch8ThresholdAccepted
          (State := State) (Srt := Srt) (Query := Query)
          (i := i) (R := R) (m := m) (ctx := ctx)
          W₂ queryOfAtom₂ a0 p coord tau := by
  intro G
  refine ⟨?_, ?_⟩
  · simpa [G] using
      (ch13_inferenceControl_end_to_end_algorithmic
        (A := A) (η := η)
        (globalPrior := globalPrior) (localPrior := localPrior)
        (likelihood := likelihood) (g := g)
        hLocal (δ := δ) (ε := ε) hTwoStage hbound hmargin htie
        (D := D))
  · exact ch8_wm_rewrite_oslf_threshold_acceptance_of_interval
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal (selectorWitness G)

/-! ## Intensional Inheritance (Chapter 12) canonical endpoints -/

abbrev InheritanceSort :=
  PLNIntensionalWorldModel.InheritanceSort

abbrev InheritanceQueryFamily :=
  PLNIntensionalWorldModel.InheritanceQueryFamily

abbrev InheritanceQueryBuilder :=
  PLNIntensionalWorldModel.InheritanceQueryBuilder

/-- Universal-mixture prior `Pξ(W|x)` used by intensional inheritance bridges. -/
noncomputable abbrev priorFromConditional :=
  Mettapedia.Logic.IntensionalInheritance.priorFromConditional

/-- Universal-mixture extensional term `Pξ(W|F,x)` used by intensional bridges. -/
noncomputable abbrev extensionalFromConditional :=
  Mettapedia.Logic.IntensionalInheritance.extensionalFromConditional

/-- Universal-mixture intensional term `log₂(Pξ(W|F,x)/Pξ(W|x))`. -/
noncomputable abbrev intensionalFromConditional :=
  Mettapedia.Logic.IntensionalInheritance.intensionalFromConditional

abbrev intensionalFromConditional_eq_log2_ratio :=
  @Mettapedia.Logic.IntensionalInheritance.intensionalFromConditional_eq_log2_ratio

abbrev intensionalFromXiSemimeasure_eq_log2_ratio :=
  @Mettapedia.Logic.IntensionalInheritance.intensionalFromXiSemimeasure_eq_log2_ratio

abbrev intensionalFromXiGeom_eq_log2_ratio :=
  @Mettapedia.Logic.IntensionalInheritance.intensionalFromXiGeom_eq_log2_ratio

/-- Pattern-level mixed inheritance atom-query encoder. -/
def patternInheritanceQueryOfAtom_mixed
    {Query : Type}
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query) :
    String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma (InheritanceQueryFamily Query) :=
  fun a p => PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedQ enc
    (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a) p

/-- Mixed (extensional+ASSOC) rewrite-to-threshold endpoint under selected ITV semantics. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (Side : Prop)
    (hSound : Side →
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedPolicyAssoc
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : Side)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  simpa [patternInheritanceQueryOfAtom_mixed] using
    (PLNWMOSLFBridgeITVTyped.wmRewriteRuleSigma_itv_threshold_atom
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
      (Ctx := CtxOfInterval i)
      R (semanticsOfInterval i) ctx tau coord
      (r := PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query)
        enc combine Side hSound (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
      hSide W
      (queryOfAtom := patternInheritanceQueryOfAtom_mixed enc)
      (a := a0) (p := p) (hEnc := rfl) hTau)

/-- Composed endpoint: Solomonoff log-ratio bridge + mixed-ASSOC threshold transport. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (Side : Prop)
    (hSound : Side →
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedPolicyAssoc
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : Side)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (liftScore : ℝ → Evidence)
    (hAssocLift :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) W enc
        (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
      liftScore (intensionalFromConditional ξ x F Wc))
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (liftScore
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  have hLog :
      intensionalFromConditional ξ x F Wc =
        Real.log
          (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
        Real.log 2 :=
    intensionalFromConditional_eq_log2_ratio ξ x F Wc hPrior hExt
  have hTau' :
      tau ≤ coord ((semanticsOfInterval i).eval ctx
        (combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))) := by
    simpa [hAssocLift, hLog] using hTau
  exact intensional_mixed_assoc_threshold_atom_of_interval
    (State := State) (Query := Query)
    i R ctx enc combine Side hSound W a0 p coord tau hSide hTau'

/-- Semantic form of the Solomonoff-composed endpoint:
consumes ASSOC-score correspondences instead of a direct `hAssocLift`. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  have hSound :
      True →
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedPolicyAssoc
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine := by
    intro _
    exact
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedPolicyAssoc_of_assocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence hMixed hAssoc
  have hAssocLift :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) W enc
        (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
      scoreToEvidence (intensionalFromConditional ξ x F Wc) := by
    exact
      PLNIntensionalWorldModel.InheritanceQueryBuilder.assocEvidence_eq_scoreToEvidence_of_assocScore_eq
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence hAssoc
        (W := W) (a := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (b := p)
        hAssocScore
  exact intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff
    (State := State) (Query := Query)
    i R ctx enc combine True hSound W a0 p coord tau trivial
    ξ x F Wc scoreToEvidence hAssocLift hPrior hExt hTau

/-- Canonical score-model alias for intensional inheritance channels. -/
abbrev InheritanceIntensionalScoreModel
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query) :=
  PLNIntensionalWorldModel.InheritanceQueryBuilder.IntensionalScoreModel
    (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (Query := Query) enc

/-- Structured Solomonoff context used to tie query-level ASSOC scores to
universal-mixture intensional inheritance. -/
structure SolomonoffAssocContext where
  x : Mettapedia.Logic.SolomonoffPrior.BinString
  F : Mettapedia.Logic.SolomonoffPrior.BinString
  Wc : Mettapedia.Logic.SolomonoffPrior.BinString

/-- Canonical model eliminating ad hoc per-query ASSOC-score bridge assumptions. -/
structure SolomonoffAssocLinkedModel
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query) where
  scoreModel : InheritanceIntensionalScoreModel (State := State) (Query := Query) enc
  contextOf : State → String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
    Mettapedia.Logic.SolomonoffInduction.Semimeasure → SolomonoffAssocContext
  assocScore_context :
    ∀ (W : State) (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure),
      scoreModel.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ
          (contextOf W a0 p ξ).x
          (contextOf W a0 p ξ).F
          (contextOf W a0 p ξ).Wc

/-- Strong linked Solomonoff model:
extends `SolomonoffAssocLinkedModel` by internalizing mixed-channel and positivity
obligations, removing common Chapter-12 call-site hypotheses. -/
structure SolomonoffAssocLinkedModelStrong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query) where
  linked : SolomonoffAssocLinkedModel (State := State) (Query := Query) enc
  combine : Evidence → Evidence → Evidence
  mixed_sound :
    PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
      (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (Query := Query) enc combine
      linked.scoreModel.assocScore linked.scoreModel.scoreToEvidence
  prior_pos :
    ∀ (W : State) (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure),
      0 < priorFromConditional ξ
        (linked.contextOf W a0 p ξ).x
        (linked.contextOf W a0 p ξ).Wc
  ext_pos :
    ∀ (W : State) (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure),
      0 < extensionalFromConditional ξ
        (linked.contextOf W a0 p ξ).x
        (linked.contextOf W a0 p ξ).F
        (linked.contextOf W a0 p ξ).Wc

/-- Model-based semantic Solomonoff endpoint:
same theorem as `..._semantic`, but consumes a canonical score model. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_model
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (model : InheritanceIntensionalScoreModel (State := State) (Query := Query) enc)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine model.assocScore model.scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      model.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine model.assocScore model.scoreToEvidence
    hMixed model.assoc_sound
    W a0 p coord tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Linked semantic Solomonoff endpoint with no explicit per-query
`hAssocScore` argument: the context linker carries that law canonically. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (model : SolomonoffAssocLinkedModel (State := State) (Query := Query) enc)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine
        model.scoreModel.assocScore model.scoreModel.scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hPrior : 0 < priorFromConditional ξ
      (model.contextOf W a0 p ξ).x
      (model.contextOf W a0 p ξ).Wc)
    (hExt : 0 < extensionalFromConditional ξ
      (model.contextOf W a0 p ξ).x
      (model.contextOf W a0 p ξ).F
      (model.contextOf W a0 p ξ).Wc)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.contextOf W a0 p ξ).x
              (model.contextOf W a0 p ξ).F
              (model.contextOf W a0 p ξ).Wc /
             priorFromConditional ξ
              (model.contextOf W a0 p ξ).x
              (model.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  let c := model.contextOf W a0 p ξ
  have hAssocScore :
      model.scoreModel.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ c.x c.F c.Wc := by
    simpa [c] using model.assocScore_context W a0 p ξ
  have hPrior' : 0 < priorFromConditional ξ c.x c.Wc := by
    simpa [c] using hPrior
  have hExt' : 0 < extensionalFromConditional ξ c.x c.F c.Wc := by
    simpa [c] using hExt
  have hTau' : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ c.x c.F c.Wc / priorFromConditional ξ c.x c.Wc) /
            Real.log 2)))) := by
    simpa [c] using hTau
  exact intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_model
    (State := State) (Query := Query)
    i R ctx enc combine model.scoreModel hMixed
    W a0 p coord tau ξ c.x c.F c.Wc hAssocScore hPrior' hExt' hTau'

/-- Strong linked endpoint:
same as `..._semantic_linked`, but mixed-channel and positivity obligations are
carried by `SolomonoffAssocLinkedModelStrong`. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked_strong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).F
              (model.linked.contextOf W a0 p ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked
    (State := State) (Query := Query)
    i R ctx enc model.combine model.linked model.mixed_sound
    W a0 p coord tau ξ
    (model.prior_pos W a0 p ξ)
    (model.ext_pos W a0 p ξ)
    hTau

/-- Bayes-normal selector wrapper for the strong linked semantic endpoint. -/
theorem intensional_mixed_assoc_threshold_atom_bayesNormal_of_solomonoff_semantic_linked_strong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval .bayesNormal)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesNormal).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).F
              (model.linked.contextOf W a0 p ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval .bayesNormal)
        (semanticsOfInterval .bayesNormal) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked_strong
    (State := State) (Query := Query)
    .bayesNormal R ctx enc model W a0 p coord tau ξ hTau

/-- Bayes-exact selector wrapper for the strong linked semantic endpoint. -/
theorem intensional_mixed_assoc_threshold_atom_bayesExact_of_solomonoff_semantic_linked_strong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval .bayesExact)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesExact).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).F
              (model.linked.contextOf W a0 p ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval .bayesExact)
        (semanticsOfInterval .bayesExact) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked_strong
    (State := State) (Query := Query)
    .bayesExact R ctx enc model W a0 p coord tau ξ hTau

/-- Walley-IDM selector wrapper for the strong linked semantic endpoint. -/
theorem intensional_mixed_assoc_threshold_atom_walley_of_solomonoff_semantic_linked_strong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval .walleyIDM)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hTau : tau ≤ coord ((semanticsOfInterval .walleyIDM).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).F
              (model.linked.contextOf W a0 p ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval .walleyIDM)
        (semanticsOfInterval .walleyIDM) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked_strong
    (State := State) (Query := Query)
    .walleyIDM R ctx enc model W a0 p coord tau ξ hTau

/-- Bayes-normal selector wrapper for semantic Solomonoff-composed intensional threshold transport. -/
theorem intensional_mixed_assoc_threshold_atom_bayesNormal_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval .bayesNormal)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesNormal).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval .bayesNormal)
        (semanticsOfInterval .bayesNormal) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    .bayesNormal R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p coord tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Bayes-exact selector wrapper for semantic Solomonoff-composed intensional threshold transport. -/
theorem intensional_mixed_assoc_threshold_atom_bayesExact_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval .bayesExact)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesExact).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval .bayesExact)
        (semanticsOfInterval .bayesExact) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    .bayesExact R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p coord tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Walley selector wrapper for semantic Solomonoff-composed intensional threshold transport. -/
theorem intensional_mixed_assoc_threshold_atom_walley_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval .walleyIDM)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((semanticsOfInterval .walleyIDM).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval .walleyIDM)
        (semanticsOfInterval .walleyIDM) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    .walleyIDM R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p coord tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Lower-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_lower_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2)))).lower) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau (fun itv => itv.lower)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.lower) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Upper-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_upper_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2)))).upper) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau (fun itv => itv.upper)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.upper) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Credibility-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_credibility_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2)))).credibility) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau (fun itv => itv.credibility)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.credibility) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Width-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_width_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2)))).width) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau (fun itv => itv.width)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.width) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Strength-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_strength_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.Logic.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < priorFromConditional ξ x Wc)
    (hExt : 0 < extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ x F Wc / priorFromConditional ξ x Wc) /
            Real.log 2)))).strength) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        (Ctx := CtxOfInterval i)
        (semanticsOfInterval i) ctx W tau (fun itv => itv.strength)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.strength) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Inheritance-sort one-call bundle endpoint (generic query encoder). -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bundle_inheritance_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State InheritanceSort (InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H := by
  exact end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval
    (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom) (queryOfAtom₂ := queryOfAtom)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Inheritance-sort one-call final-bundle endpoint (generic query encoder). -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State InheritanceSort (InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
    (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom) (queryOfAtom₂ := queryOfAtom)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Inheritance-sort final-bundle endpoint specialized to Bayes normal semantics. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_bayesNormal
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State InheritanceSort (InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval .bayesNormal)
    {r : WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesNormal).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      (i := .bayesNormal) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_of_interval
    (State := State) (i := .bayesNormal) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom := queryOfAtom) (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Inheritance-sort final-bundle endpoint specialized to Bayes exact semantics. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_bayesExact
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State InheritanceSort (InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval .bayesExact)
    {r : WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesExact).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      (i := .bayesExact) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_of_interval
    (State := State) (i := .bayesExact) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom := queryOfAtom) (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Inheritance-sort final-bundle endpoint specialized to Walley IDM semantics. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_walley
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State InheritanceSort (InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval .walleyIDM)
    {r : WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((semanticsOfInterval .walleyIDM).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Pattern)
      (i := .walleyIDM) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_of_interval
    (State := State) (i := .walleyIDM) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom := queryOfAtom) (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- One-call final-bundle endpoint for linked semantic Solomonoff intensional inheritance.

This endpoint composes:
1. rewrite/query/quantale transport via the generic final-bundle API, and
2. truth transport from the linked semantic Solomonoff theorem family.
-/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linked_of_interval
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Evidence → Evidence → Evidence)
    (model : SolomonoffAssocLinkedModel (State := State) (Query := Query) enc)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine
        model.scoreModel.assocScore model.scoreModel.scoreToEvidence)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hPrior : 0 < priorFromConditional ξ
      (model.contextOf W₁ a0 p ξ).x
      (model.contextOf W₁ a0 p ξ).Wc)
    (hExt : 0 < extensionalFromConditional ξ
      (model.contextOf W₁ a0 p ξ).x
      (model.contextOf W₁ a0 p ξ).F
      (model.contextOf W₁ a0 p ξ).Wc)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.contextOf W₁ a0 p ξ).x
              (model.contextOf W₁ a0 p ξ).F
              (model.contextOf W₁ a0 p ξ).Wc /
             priorFromConditional ξ
              (model.contextOf W₁ a0 p ξ).x
              (model.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hPriorTarget : 0 < priorFromConditional ξ
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).x
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).Wc)
    (hExtTarget : 0 < extensionalFromConditional ξ
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).x
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).F
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).Wc)
    (hTauTarget : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             priorFromConditional ξ
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H := by
  letI : PLNWorldModel.WorldModelSigma State InheritanceSort (InheritanceQueryFamily Query) :=
    PLNIntensionalWorldModel.worldModelSigmaInheritanceFromUntyped
      (State := State) (Query := Query)
  let r :
      WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Query) :=
    PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_assocSemantic
      (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (Query := Query)
      enc combine model.scoreModel.assocScore model.scoreModel.scoreToEvidence
      hMixed model.scoreModel.assoc_sound
      (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p
  let c₁ := model.contextOf W₁ a0 p ξ
  have hAssocLift₁ :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query)
        W₁ enc (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
      model.scoreModel.scoreToEvidence
        (Real.log
          (extensionalFromConditional ξ c₁.x c₁.F c₁.Wc / priorFromConditional ξ c₁.x c₁.Wc) /
          Real.log 2) := by
    have hAssocScore₁ :
        model.scoreModel.assocScore W₁
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
          intensionalFromConditional ξ c₁.x c₁.F c₁.Wc := by
      simpa [c₁] using model.assocScore_context W₁ a0 p ξ
    have hLog₁ :
        intensionalFromConditional ξ c₁.x c₁.F c₁.Wc =
          Real.log
            (extensionalFromConditional ξ c₁.x c₁.F c₁.Wc / priorFromConditional ξ c₁.x c₁.Wc) /
          Real.log 2 :=
      intensionalFromConditional_eq_log2_ratio ξ c₁.x c₁.F c₁.Wc
        (by simpa [c₁] using hPrior)
        (by simpa [c₁] using hExt)
    calc
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query)
          W₁ enc (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p
          = model.scoreModel.scoreToEvidence
              (model.scoreModel.assocScore W₁
                (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p) :=
            model.scoreModel.assoc_sound W₁ (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p
      _ = model.scoreModel.scoreToEvidence (intensionalFromConditional ξ c₁.x c₁.F c₁.Wc) := by
            rw [hAssocScore₁]
      _ = model.scoreModel.scoreToEvidence
            (Real.log
              (extensionalFromConditional ξ c₁.x c₁.F c₁.Wc / priorFromConditional ξ c₁.x c₁.Wc) /
              Real.log 2) := by
            rw [hLog₁]
  have hTauScore :
      tau ≤ coord ((semanticsOfInterval i).eval ctx
        (combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
          (model.scoreModel.scoreToEvidence
            (Real.log
              (extensionalFromConditional ξ c₁.x c₁.F c₁.Wc / priorFromConditional ξ c₁.x c₁.Wc) /
              Real.log 2)))) := by
    simpa [c₁] using hTau
  have hTauAssoc :
      tau ≤ coord ((semanticsOfInterval i).eval ctx
        (combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))) := by
    simpa [hAssocLift₁] using hTauScore
  have hDerive :
      r.derive W₁ =
        combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p) := by
    simp [r, PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_assocSemantic,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc]
  have hTau' :
      tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)) := by
    simpa [hDerive] using hTauAssoc
  have hSide : r.side := by
    simp [r,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_assocSemantic,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc]
  have hEq :
      WMQueryEqSigma
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        r.conclusion ((patternInheritanceQueryOfAtom_mixed enc) a0 p) := by
    simpa [r, patternInheritanceQueryOfAtom_mixed,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_assocSemantic,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc] using
      (PLNWorldModel.WorldModelSigma.WMQueryEqSigma.refl
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        ((patternInheritanceQueryOfAtom_mixed enc) a0 p))
  have hBase :=
    end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := patternInheritanceQueryOfAtom_mixed enc)
      (queryOfAtom₂ := patternInheritanceQueryOfAtom_mixed enc)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau' hEq hVal H
  have hTruthTarget :
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
          (Ctx := CtxOfInterval i)
          (semanticsOfInterval i) ctx W₂ tau coord
          (patternInheritanceQueryOfAtom_mixed enc))
        (.atom a0) (m.mapTerm p) :=
    intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked
      (State := State) (Query := Query)
      i R ctx enc combine model hMixed
      W₂ a0 (m.mapTerm p) coord tau ξ hPriorTarget hExtTarget hTauTarget
  exact
    { reachability := hBase.reachability
      quantale_coherence := hBase.quantale_coherence
      truth_transport := by
        intro u
        cases u
        simpa using hTruthTarget }

/-- Strong linked one-call final bundle for Chapter-12 intensional inheritance.

This variant consumes `SolomonoffAssocLinkedModelStrong`, so mixed-channel and
positivity obligations are internalized in the model object. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_of_interval
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).F
              (model.linked.contextOf W₁ a0 p ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hTauTarget : tau ≤ coord ((semanticsOfInterval i).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linked_of_interval
    (State := State) (Query := Query)
    (i := i) (R := R) (m := m) (ctx := ctx)
    enc model.combine model.linked model.mixed_sound
    (W₁ := W₁) (W₂ := W₂) (a0 := a0) (p := p)
    (coord := coord) (tau := tau) (ξ := ξ)
    hW hVal
    (model.prior_pos W₁ a0 p ξ)
    (model.ext_pos W₁ a0 p ξ)
    hTau
    (model.prior_pos W₂ a0 (m.mapTerm p) ξ)
    (model.ext_pos W₂ a0 (m.mapTerm p) ξ)
    hTauTarget
    H

/-- Bayes-normal selector wrapper for strong linked Chapter-12 final-bundle endpoint. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_bayesNormal
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval .bayesNormal)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesNormal).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).F
              (model.linked.contextOf W₁ a0 p ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hTauTarget : tau ≤ coord ((semanticsOfInterval .bayesNormal).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
      (i := .bayesNormal) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_of_interval
    (State := State) (Query := Query)
    (i := .bayesNormal) (R := R) (m := m) (ctx := ctx)
    enc model
    (W₁ := W₁) (W₂ := W₂) (a0 := a0) (p := p)
    (coord := coord) (tau := tau) (ξ := ξ)
    hW hVal hTau hTauTarget H

/-- Bayes-exact selector wrapper for strong linked Chapter-12 final-bundle endpoint. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_bayesExact
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval .bayesExact)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hTau : tau ≤ coord ((semanticsOfInterval .bayesExact).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).F
              (model.linked.contextOf W₁ a0 p ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hTauTarget : tau ≤ coord ((semanticsOfInterval .bayesExact).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
      (i := .bayesExact) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_of_interval
    (State := State) (Query := Query)
    (i := .bayesExact) (R := R) (m := m) (ctx := ctx)
    enc model
    (W₁ := W₁) (W₂ := W₂) (a0 := a0) (p := p)
    (coord := coord) (tau := tau) (ξ := ξ)
    hW hVal hTau hTauTarget H

/-- Walley-IDM selector wrapper for strong linked Chapter-12 final-bundle endpoint. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_walley
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval .walleyIDM)
    (enc : InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.Logic.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hTau : tau ≤ coord ((semanticsOfInterval .walleyIDM).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).F
              (model.linked.contextOf W₁ a0 p ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hTauTarget : tau ≤ coord ((semanticsOfInterval .walleyIDM).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (extensionalFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             priorFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := InheritanceSort) (Query := InheritanceQueryFamily Query)
      (i := .walleyIDM) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_of_interval
    (State := State) (Query := Query)
    (i := .walleyIDM) (R := R) (m := m) (ctx := ctx)
    enc model
    (W₁ := W₁) (W₂ := W₂) (a0 := a0) (p := p)
    (coord := coord) (tau := tau) (ξ := ξ)
    hW hVal hTau hTauTarget H

/-! ## Event Calculus (Chapter 14) canonical endpoints -/

abbrev EventCalcSort :=
  PLNProbabilisticEventCalculus.EventCalcSort

abbrev PatternEventQueryFamily :=
  PLNProbabilisticEventCalculus.PatternEventQueryFamily

abbrev patternEventQueryOfAtom_holds :=
  PLNProbabilisticEventCalculus.patternEventQueryOfAtom_holds

abbrev patternEventQueryOfAtom_initiated :=
  PLNProbabilisticEventCalculus.patternEventQueryOfAtom_initiated

abbrev patternEventQueryOfAtom_terminated :=
  PLNProbabilisticEventCalculus.patternEventQueryOfAtom_terminated

/-- Event-calculus one-call bundle endpoint (generic query encoder). -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bundle_event_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State EventCalcSort PatternEventQueryFamily]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State EventCalcSort PatternEventQueryFamily} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma PatternEventQueryFamily)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma
      (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdBundle
      (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H := by
  exact end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval
    (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom) (queryOfAtom₂ := queryOfAtom)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Event-calculus one-call final-bundle endpoint (generic query encoder). -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_event_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State EventCalcSort PatternEventQueryFamily]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : CtxOfInterval i)
    {r : WMRewriteRuleSigma State EventCalcSort PatternEventQueryFamily} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma PatternEventQueryFamily)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : WMQueryEqSigma
      (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
    (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom) (queryOfAtom₂ := queryOfAtom)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Temporal-hypercube one-call bundle for event queries:
composes GSLT forward transport on `vertexTemporalLanguageDef`, quantale
coherence transport, and ITV-threshold atom truth transport. -/
theorem end_to_end_temporal_hypercube_event_threshold_bundle_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State EventCalcSort PatternEventQueryFamily]
    {v w : Mettapedia.ProbabilityTheory.Hypercube.ProbabilityVertex}
    (hvw : v ≤ w)
    (f : Mettapedia.Algebra.QuantaleWeakness.QuantaleHom
      (Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics.semanticsOfVertex w).Q
      (Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics.semanticsOfVertex v).Q)
    (srcVal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      (Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics.semanticsOfVertex w).Q)
    (dstVal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      (Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics.semanticsOfVertex v).Q)
    (hValWeak : ∀ p, dstVal p = f (srcVal p))
    {U : Type*} [Fintype U]
    (pick : U → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    {p₀ : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (hReach : ∀ u,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar
        (vertexTemporalLanguageDef w) p₀ (pick u))
    (H : Finset (U × U))
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (i : WMIntervalSemantics)
    (ctx : CtxOfInterval i)
    (W₁ W₂ : State)
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma PatternEventQueryFamily)
    (a0 : String)
    (coord : ITV → ℝ) (tau : ℝ)
    (hITV : ∀ p,
      (semanticsOfInterval i).eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
          W₂ queryOfAtom a0 p) =
      (semanticsOfInterval i).eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
          W₁ queryOfAtom a0 p))
    (hTau : ∀ u,
      tau ≤ coord ((semanticsOfInterval i).eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
          W₁ queryOfAtom a0 (pick u)))) :
    (∀ u,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar
        (vertexTemporalLanguageDef v) p₀ (pick u)) ∧
    f (Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight srcVal pick) H) =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight dstVal id pick) H ∧
    (∀ u,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
          (Ctx := CtxOfInterval i)
          (semanticsOfInterval i) ctx W₂ tau coord queryOfAtom)
        (.atom a0) (pick u)) := by
  rcases hypercube_forward_quantale_coherence_bundle_temporal
      (v := v) (w := w)
      hvw f srcVal dstVal hValWeak pick (p₀ := p₀) hReach H with ⟨hForward, hWeak⟩
  refine ⟨hForward, hWeak, ?_⟩
  intro u
  have hEq : (semanticsOfInterval i).eval ctx
      (PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        W₂ queryOfAtom a0 (pick u)) =
    (semanticsOfInterval i).eval ctx
      (PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
        W₁ queryOfAtom a0 (pick u)) := hITV (pick u)
  have hTauW₂ :
      tau ≤ coord ((semanticsOfInterval i).eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := EventCalcSort) (Query := PatternEventQueryFamily)
          W₂ queryOfAtom a0 (pick u))) := by
    simpa [hEq] using hTau u
  simpa [Mettapedia.OSLF.Formula.sem,
    PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma,
    PLNWMOSLFBridgeITVTyped.wmITVAtomSemQSigma] using hTauW₂


/-! ## OSLF Bridge canonical aliases -/

abbrev XiPLN {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWMOSLFBridge.XiPLN (State := State) (Query := Query)

noncomputable abbrev wmEvidenceAtomSemQ {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWMOSLFBridge.wmEvidenceAtomSemQ (State := State) (Query := Query)

abbrev XiPLNSigma {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWMOSLFBridgeTyped.XiPLNSigma (State := State) (Srt := Srt) (Query := Query)

noncomputable abbrev wmEvidenceAtomSemQSigma {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWMOSLFBridgeTyped.wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query)

noncomputable abbrev wmITVAtomSemQSigma {State Srt Ctx : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWMOSLFBridgeITVTyped.wmITVAtomSemQSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)

noncomputable abbrev thresholdAtomSemOfWMITVQSigma
    {State Srt Ctx : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query] :=
  PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
    (State := State) (Srt := Srt) (Query := Query) (Ctx := Ctx)


/-! ## MeTTa integration aliases -/

abbrev MeTTaTypeOfSortTag :=
  Mettapedia.Logic.PLNWMOSLFBridgeTyped.MeTTaTypeOf.SortTag

abbrev ThreeNativeTaggedQueryFamily :=
  PLNXiDerivedBNRules.Typed.ThreeNativeTaggedQueryFamily

abbrev MeTTaTypeMarkers :=
  Mettapedia.Logic.PLNWMOSLFBridgeTyped.MeTTaTypeOf.SortTypeMarkers

abbrev MeTTaTypeMarkersDefault :=
  Mettapedia.Logic.PLNWMOSLFBridgeTyped.MeTTaTypeOf.defaultMarkers

abbrev MeTTaQueryBuilder :=
  Mettapedia.Logic.PLNWMOSLFBridgeTyped.MeTTaTypeOf.QueryBuilder

abbrev queryOfAtomFromTypeOf :=
  @Mettapedia.Logic.PLNWMOSLFBridgeTyped.MeTTaTypeOf.queryOfAtomFromTypeOf

abbrev queryOfAtomFromTypeOfWith :=
  @Mettapedia.Logic.PLNWMOSLFBridgeTyped.MeTTaTypeOf.queryOfAtomFromTypeOfWith

abbrev xiPLNSigmaOfTypeOf :=
  @Mettapedia.Logic.PLNWMOSLFBridgeTyped.MeTTaTypeOf.xiPLNSigmaOfTypeOf


/-! ## Derived BN Rules (canonical — no free side-condition hypotheses)

Fully derived PLN inference rules for BN structures. All side conditions
are derived from local Markov + d-separation — no free `hSO` arguments.

Import `Mettapedia.Logic.PLNXiDerivedBNRules` and use directly:

### Deduction: Chain BN (A→B→C) — §1

**Tier A**: BN-PLN (structural, d-sep + local Markov → admissible rewrite)
- `ChainBNLocalMarkovAll` — type alias for the local Markov hypothesis
- `xi_deduction_rewrite_of_chainBN` — WMRewriteRule (NO free hSO)
- `xi_deduction_admissible_of_chainBN` — query judgment from derivable WM state
- `xi_deduction_semE_atom_of_chainBN` — OSLF evidence = derived evidence
- `xi_deduction_threshold_of_chainBN` — threshold Prop from strength bound
- `xi_deduction_strength_eq_of_chainBN` — linkCond strength = link strength

**Tier A→B Composition** (end-to-end queryStrength → plnDeductionStrength)
- `xi_deduction_queryStrength_eq_plnDeduction_of_chainBN` — for singleton CPT state:
  `(queryStrength {cpt} (link A C)).toReal = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))`
  Consumes: singleton bridge + VEBridge + Tier B.

**Tier B**: Bernoulli-PLN (measure → formula bridge)
- `toStrength_evidenceOfProb` — `Evidence.toStrength ∘ evidenceOfProb = id` (for p ≤ 1)
- `xi_deduction_plnStrength_exact_of_chainBN` — P(C|A) = plnDeductionStrength(...)

**Tier C**: Beta-Bernoulli (computable from evidence counts)
- `plnStrength_lt_one` — `s_B < 1` when `nB_neg ≠ 0` (denominator safety)
- `plnDeductionStrength_denom_pos` — `0 < 1 - s_B` (denominator positivity)
- `plnDeductionStrength_of_plnStrength` — unfolds plnStrength in deduction formula
- `plnDeductionStrength_of_plnStrength_full` — all four arguments unfolded
- `evidence_hplus_is_conjugate` — Beta conjugate update for evidence aggregation

**Guardrail**: Beta is a modeling choice, not forced by exchangeability.
See `EvidenceBeta.not_beta_from_exchangeability_example`.

### Source Rule (Induction): Fork BN (A←B→C) — §4

**Tier A**: BN-PLN (structural, d-sep + local Markov → admissible rewrite)
- `ForkBNLocalMarkovAll` — type alias for the local Markov hypothesis
- `xi_sourceRule_rewrite_of_forkBN` — WMRewriteRule (NO free hSO)
- `xi_sourceRule_admissible_of_forkBN` — query judgment from derivable WM state
- `xi_sourceRule_semE_atom_of_forkBN` — OSLF evidence = derived evidence
- `xi_sourceRule_threshold_of_forkBN` — threshold Prop from strength bound
- `xi_sourceRule_strength_eq_of_forkBN` — linkCond strength = link strength

The fork BN has edges B→A and B→C. The source rule derives link A→C from
links B→A and B→C via the same conditional independence A ⊥ C | B. The
screening-off WMQueryEq has the same form as the chain BN deduction case;
the structural difference is the BN graph topology.

**Tier A→B Composition** (end-to-end queryStrength → plnInductionStrength)
- `xi_source_queryStrength_eq_plnInduction_of_forkBN` — for singleton CPT state:
  `(queryStrength {cpt} (link A C)).toReal = plnInductionStrength(P(A|B), P(C|B), P(A), P(B), P(C))`
  Uses `bayesInversion(P(A|B), P(A), P(B)) = P(B|A)` + fork screening-off + PLN deduction formula.
  Consumes: `forkBN_plnDeductionStrength_exact` (PLNBayesNetFastRules).

**Tier B**: Bernoulli-PLN (measure → formula bridge)
- `forkBN_plnDeductionStrength_exact` — P(C|A) = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))
  from CondIndepVertices (local Markov at C). ~30 lines vs ~900 for chain case.
- `forkBN_pos_screeningOff` / `forkBN_neg_screeningOff` — screening-off from CondIndepVertices
  via `condIndep_eventEq_mul_cond` + `real_ratio_of_ennreal_mul_eq`

### Sink Rule (Abduction): Collider BN (A→C←B) — §5

**Tier A**: BN-PLN (structural, d-sep + local Markov → admissible rewrite)
- `ColliderBNLocalMarkovAll` — type alias for the local Markov hypothesis
- `xi_sinkRule_rewrite_of_colliderBN` — WMRewriteRule (NO free hSO)
- `xi_sinkRule_admissible_of_colliderBN` — query judgment from derivable WM state
- `xi_sinkRule_semE_atom_of_colliderBN` — OSLF evidence = derived evidence
- `xi_sinkRule_threshold_of_colliderBN` — threshold Prop from strength bound
- `xi_sinkRule_strength_eq_of_colliderBN` — link strength = prop strength

The collider BN has edges A→C and B→C. The sink rule derives link A→B from
links A→C and B→C. The side condition is marginal independence A ⊥ B | ∅,
which holds because A and B have no active path when C is not conditioned on.

Variable mapping: (A_rule, B_rule, C_rule) = (Three.A, Three.C, Three.B).
Sink center = Three.C. The WMQueryEq rewrites `link ⟨A,valA⟩ ⟨B,valB⟩`
to `prop ⟨B,valB⟩` (marginal independence: P(B|A) = P(B)).

These require BN instances (Fintype, DecidableEq, etc.) which are
provided by `open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples`.

**Tier A→B Composition: NOT EXACT (approximation)**
- `plnAbductionStrength_not_exact_collider` — counterexample showing PLN abduction
  formula gives 2/3 ≠ 1/2 for an OR-gate collider. The PLN abduction formula
  requires B ⊥ A | C, but conditioning on the collider C *opens* the explaining-away
  path, making A and B dependent given C.

### Generic tools (§6)

- `real_ratio_of_ennreal_mul_eq` — convert ENNReal multiplicative screening-off
  `a * d = b * c` to `.real` ratio form `a/b = c/d` (PLNBayesNetFastRules)
- `eventEq_false_eq_compl_true_of_bool` — Bool complement bridge for event sets (EventSets) -/

/-! ## Schema namespace

Rule templates parameterized by abstract side conditions. These are building
blocks for constructing new derived rules from other BN structures (fork,
collider, etc.), NOT standalone inference rules.

To build a derived rule from a schema template:
1. Prove the side condition from your model semantics
2. Instantiate the schema with the proved side condition
3. Add admissibility + OSLF bridge theorems
4. Export the derived rule (not the schema) as canonical -/

namespace Schema

/-! ### Screening-off side condition templates -/

abbrev DeductionScreeningOff {Atom State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State (PLNWorldModel.PLNQuery Atom)] :=
  PLNXiRuleRegistry.DeductionScreeningOff (Atom := Atom) (State := State)

abbrev SourceRuleScreeningOff {Atom State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State (PLNWorldModel.PLNQuery Atom)] :=
  PLNXiRuleRegistry.SourceRuleScreeningOff (Atom := Atom) (State := State)

abbrev SinkRuleScreeningOff {Atom State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State (PLNWorldModel.PLNQuery Atom)] :=
  PLNXiRuleRegistry.SinkRuleScreeningOff (Atom := Atom) (State := State)

/-! ### Carrier family template -/

abbrev CarrierFamily {Atom State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State (PLNWorldModel.PLNQuery Atom)] :=
  PLNXiCarrierScreening.CarrierFamily (Atom := Atom) (State := State)

end Schema

/-! ## Exactness Matrix

Summary of formula-level exactness across BN topologies:

| Rule | BN Topology | Tier A (WM/OSLF) | Tier A→B (formula) | Notes |
|------|-------------|-------------------|---------------------|-------|
| Deduction | Chain A→B→C | exact | exact | `plnDeductionStrength` via total probability + C ⊥ A given B |
| Source/Induction | Fork A←B→C | exact | exact | `plnInductionStrength` = Bayes inversion + deduction; C ⊥ A given B holds |
| Sink/Abduction | Collider A→C←B | exact (marginal) | **NOT exact** | Structural: P(B given A) = P(B); formula: explaining-away violates B ⊥ A given C |

### Key theorems

- Chain exact: `chainBN_plnDeductionStrength_exact` (`PLNBayesNetFastRules`)
- Fork exact (measure): `forkBN_plnDeductionStrength_exact` (`PLNBayesNetFastRules`)
- Fork exact (queryStrength): `xi_source_queryStrength_eq_plnInduction_of_forkBN` (`PLNXiDerivedBNRules`)
- Collider structural exact: `xi_sinkRule_strength_eq_of_colliderBN` (`PLNXiDerivedBNRules`)
- Collider .toReal exact: `xi_sink_queryStrength_toReal_eq_of_colliderBN` (`PLNXiDerivedBNRules`)
- Collider singleton short-name re-exports:
  `sinkLinkEqPropToReal`, `singletonPropToReal` (`PLNColliderSingletonBridge`)
- Collider formula counterexample: `plnAbductionStrength_not_exact_collider` (`PLNXiDerivedBNRules`)
- Error framework: `Comparison/ErrorCharacterization.lean` (decomposition + bounds + decision criteria)

### When is a PLN rule exact?

A PLN rule is exact when its internal screening-off assumption holds:
- **Deduction/Source**: requires C ⊥ A | B (holds in chain and fork by d-separation)
- **Abduction**: requires B ⊥ A | C (FAILS in collider: conditioning on C opens the explaining-away path)

The `ErrorCharacterization` module provides quantitative bounds on the error when
screening-off is violated (`error_bound_by_max_violation`, `conservative_estimate_is_bound`).

### Collider singleton composition pattern

Use this exact two-step composition:
```lean
have h1 := PLNColliderSingletonBridge.sinkLinkEqPropToReal
  valA valB hPos hLMarkov hDSep ({cpt} : BNWorldModel.State (bn := colliderBN))
have h2 := PLNColliderSingletonBridge.singletonPropToReal
  cpt Three.B valB
exact Eq.trans h1 h2
```
-/

/-! ## End-to-End Theorems (BN → WM → OSLF)

`PLNEndToEnd` is intentionally a stable, thin surface over proved theorems.
It avoids heavyweight wrapper statements that can trigger elaboration timeouts.

### Formula exactness
- `PLNEndToEnd.chainFormulaExact`
- `PLNEndToEnd.forkFormulaExact`

### Admissibility + OSLF bridge
- `PLNEndToEnd.chainAdmissible`, `PLNEndToEnd.chainOSLFEvidence`, `PLNEndToEnd.chainOSLFThreshold`
- `PLNEndToEnd.forkAdmissible`, `PLNEndToEnd.forkOSLFEvidence`, `PLNEndToEnd.forkOSLFThreshold`
- `PLNEndToEnd.colliderAdmissible`, `PLNEndToEnd.colliderOSLFEvidence`, `PLNEndToEnd.colliderOSLFThreshold`

### Collider split
- `PLNEndToEnd.colliderStructural`, `PLNEndToEnd.colliderStructuralToReal`
- `PLNEndToEnd.colliderNotExact`
- `PLNEndToEnd.colliderExactWhenScreeningOff`
- Singleton composition helpers: `PLNColliderSingletonBridge.sinkLinkEqPropToReal`,
  `PLNColliderSingletonBridge.singletonPropToReal`

### Generic context lifts
- `PLNEndToEnd.wmRewriteRuleCtx`
- `PLNWMOSLFBridge.xiDerivesAtomEvidence_sound_ctx`
- `PLNWMOSLFBridge.xiDerivesAtomStrength_threshold_sound_ctx`
- `PLNWMOSLFBridge.xi_atom_revision_ctx`
-/

end Mettapedia.Logic.PLNCanonical
