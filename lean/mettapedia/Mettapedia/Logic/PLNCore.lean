import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.CompletePLN
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelPureKernelBridge
import Mettapedia.Logic.PLNWorldModelInstitution
import Mettapedia.Logic.PLNWorldModelHyperdoctrine
import Mettapedia.Logic.PLNWorldModelCategoricalBridge
import Mettapedia.Logic.PLNJointEvidence
import Mettapedia.Logic.PLNJointEvidenceProbability
import Mettapedia.Logic.PLNBayesNetWorldModel
import Mettapedia.Logic.PLNBayesNetInference
import Mettapedia.Logic.PLNLinkCalculus
import Mettapedia.Logic.PLNLinkCalculusSoundness
import Mettapedia.Logic.PLNBayesNetFastRules
import Mettapedia.Logic.PLNBNCompilation
import Mettapedia.Logic.PremiseSelectionKNN
import Mettapedia.Logic.PremiseSelectionKNN_PLNBridge
import Mettapedia.Logic.PremiseSelectionFusion
import Mettapedia.Logic.PremiseSelectionOptimality
import Mettapedia.Logic.PremiseSelectionCoverage
import Mettapedia.Logic.PremiseSelectionExternalBayesianity
import Mettapedia.Logic.PremiseSelectionLocalMixtureBridge
import Mettapedia.Logic.PremiseSelectionOperatorRoles
import Mettapedia.Logic.PremiseSelectionPriorNB
import Mettapedia.Logic.PremiseSelectionPUCalibration
import Mettapedia.Logic.PremiseSelectionRankingStability
import Mettapedia.Logic.PremiseSelectionSelectorSpec
import Mettapedia.Logic.PremiseSelectionPartitionedPriorNB
import Mettapedia.Logic.PremiseSelectionBestPLNDraft
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
import Mettapedia.Logic.PLNHigherOrderChainBounds
import Mettapedia.Logic.PLNHigherOrderDecisionTheorems
import Mettapedia.Logic.PLNGWASHigherOrderBridge
import Mettapedia.Logic.PLNHigherOrderCertifiedChainingRegression
import Mettapedia.Logic.PLNUntrustedOracleAdapterRegression
import Mettapedia.Logic.PLNTopologyCPTNoGo
import Mettapedia.Logic.PLNVarianceChainNoGo
import Mettapedia.Logic.PLNHigherOrderNoGoBridge
import Mettapedia.Logic.MarkovLogicRegression
import Mettapedia.Logic.MarkovLogicClauseSemantics
import Mettapedia.Logic.MarkovLogicClauseFactorGraph
import Mettapedia.Logic.MarkovLogicClauseWorldModel
import Mettapedia.Logic.MarkovLogicClauseRegression
import Mettapedia.Logic.SoundnessCompleteness
import Mettapedia.Logic.PLNErrorMagnificationGrounding
import Mettapedia.Logic.PLNCanonicalAPI
import Mettapedia.Logic.PLNFirstOrder.InfiniteRegression
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierRegressionInf
import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierRegression
import Mettapedia.Logic.PLNFirstOrder.FuzzyDomainQuantifierRegression
import Mettapedia.Logic.PLNFirstOrder.FuzzySyllogismRegressionFin
import Mettapedia.Logic.PLNWorldModelHOLSetBridge
import Mettapedia.Logic.PLNHigherOrderHOLRegression
import Mettapedia.Logic.SufficientStatisticSurface
import Mettapedia.Logic.GenericWorldModelForgetting
import Mettapedia.Logic.PLNSemitopology
import Mettapedia.Logic.PLNSemitopologyProvenanceBridge
import Mettapedia.Logic.PLNWorldModelAudit
import Mettapedia.Logic.PLNWorldModelPreorder
import Mettapedia.Logic.PLNGaussianEMExtension
import Mettapedia.Logic.HigherOrder.PLNKyburgReduction
import Mettapedia.Logic.PLNIntensionalWorldModel
import Mettapedia.Logic.IntensionalInheritanceSolomonoffBridge
import Mettapedia.Logic.PLNNARSRuleCorrespondence
import Mettapedia.Logic.PLNTemporalCausalInference
import Mettapedia.Logic.PLNProbabilisticEventCalculus
import Mettapedia.Logic.SemanticsDecisionTree
import Mettapedia.Logic.PLNLargeScaleInferenceCounterexamples
import Mettapedia.Logic.PLNMultideductionResidual
import Mettapedia.Logic.PLNTrailFreeDampedConvergence
import Mettapedia.Logic.PremiseSelectionBRGI

/-!
# PLN Core (Curated, theorem-complete entrypoint)

This module is a curated import surface for the currently theorem-complete PLN stack:

- Core derivation formulas (`PLNDerivation`)
- Complete/joint evidence world-model semantics (`CompletePLN`, `PLNJointEvidence*`)
- Distributional-to-Kyburg higher-order reduction bridge
  (`HigherOrder/PLNKyburgReduction`)
- WM rewrite layer and BN compilation bridge (`PLNWorldModel*`, `PLNBNCompilation`)
- BN fast-rule exactness results: chain + fork measure-level exact (`PLNBayesNetFastRules`)
- Derived BN rules: deduction (chain) + source/induction (fork) + sink/abduction (collider)
  5-shape blocks (`PLNXiDerivedBNRules` — 0 sorry, no free screening-off hypotheses)
- Tier A→B composition: chain + fork (exact), collider (counterexample: approximate)
  (`xi_source_queryStrength_eq_plnInduction_of_forkBN`, `plnAbductionStrength_not_exact_collider`)
- Premise-selection bridges and optimality transfer (`PremiseSelection*`)
- Premise-selection coverage/submodularity surrogate (`PremiseSelectionCoverage`)
- Premise-selection external-Bayesian commutation (`PremiseSelectionExternalBayesianity`)
- Chapter-13 composed inference-control core (selector defaults + stability + coverage)
  (`PLNInferenceControlCore`)
- Chapter-13 executable greedy selector + algorithmic end-to-end bridge
  (`PLNInferenceControlAlgorithms`)
- Chapter-13 forward/backward/bounded chainer operator interfaces
  (`PLNInferenceControlChainer`)
- Chapter-13 worked finite fixtures and instantiated end-to-end theorem
  (`PLNInferenceControlExamples`)
- Pooling non-uniqueness counterexample + corrected uniqueness with total-additivity
  (`maxPoolingOperator_ne_fuse`, `poolE_eq_hplus_of_externalBayes_totalAdd`)
- Finite de Finetti local-mixture bridge (`PremiseSelectionLocalMixtureBridge`)
- Quantitative TV bridge forms (coarse unconditional + tight unconditional forms)
  (`l1_iid_inj_le_choose2`, `finite_statistic_tv_mixture_bound`,
   `finite_statistic_tv_mixture_bound_choose2`,
   `finite_statistic_tv_mixture_bound_m16_R4551`)
- Operator-role checklist for prior/revision/tensor composition (`PremiseSelectionOperatorRoles`)
- Concrete normalized role-model witness (`negOnlyOperatorRoleTheoryNormalized`)
  showing role-class realizability with normalization closure
- Concrete Prior-NB role/commutation theorems (`PremiseSelectionPriorNB`)
- Core PLN rule aliases:
  (`PLN_ContextualPriorRevision`, `PLN_NormalizedPriorLikelihoodTensor`,
   `PLN_PriorNBRankingTransfer`)
- Bridge alias families (classical-method correspondence, non-breaking):
  (`PLN_tensorStrength_eq_nbPosterior`, `PLN_hplusPos_eq_knnRelevance`,
   `PLN_revisionStrength_eq_linearPool`)
- Regraduation odds/log-odds power laws in the evidence carrier
  (`BinaryEvidence.toOdds_power_rpow`, `BinaryEvidence.toLogOdds_power_mul`)
- PU-style weak-negative calibration lemmas (`PremiseSelectionPUCalibration`)
- Ranking-stability theorems under bounded perturbations (`PremiseSelectionRankingStability`)
- Selector-spec defaults linked to checklist assumptions (`PremiseSelectionSelectorSpec`)
- Partitioned normalized Prior-NB composition and TV-bound aggregation
  (`PremiseSelectionPartitionedPriorNB`)
- Draft "best-PLN" composition module (global prior + partitioned local prior +
  normalized sequential tensor update) with role/ranking wrappers
  (`PremiseSelectionBestPLNDraft`)
- Soundness/completeness tradeoff characterization (`SoundnessCompleteness`)
- Error-magnification grounding across WM calculus, OSLF atom semantics, and
  evidence-derived confidence transport (`PLNErrorMagnificationGrounding`)
- Canonical API with 3-tier theorem index (`PLNCanonicalAPI`)
- Arbitrary-domain PLN first-order quantifier surface
  (`PLNFirstOrder.InfiniteRegression`, plus canonical aliases in `PLNCanonicalAPI`)
- Arbitrary-domain fuzzy first-order quantifier surface
  (`PLNFirstOrder.FuzzyQuantifierRegressionInf`, plus canonical aliases in `PLNCanonicalAPI`)
- Choquet-style arbitrary-domain fuzzy first-order branch
  (`PLNFirstOrder.ChoquetQuantifierRegression`, plus canonical aliases in `PLNCanonicalAPI`)
- Fuzzy-domain arbitrary-domain first-order branch
  (`PLNFirstOrder.FuzzyDomainQuantifierRegression`, plus canonical aliases in `PLNCanonicalAPI`)
- Finite/counting fuzzy Chapter-11 syllogism surface
  (`PLNFirstOrder.FuzzySyllogismRegressionFin`)
- Higher-order PLN layer over real Church/Henkin HOL plus the real HOL WM bridge
  (`PLNHigherOrderHOLRegression`, plus canonical aliases in `PLNCanonicalAPI`)
- Direct set-semantics to HOL grounding and public `Set -> HOL -> WM` bridge,
  together with comparison theorems against the older FOL-routed set bridge
  (`HOL.Semantics.SetBased`, `PLNWorldModelHOLSetBridge`, plus canonical aliases in
  `PLNCanonicalAPI`)
- Infinitary semantic probabilistic HOL over measurable indexed spaces of
  pointed Henkin models, together with the theorem that the existing empirical
  HOL↔WM semantics is a special case
  (`HOL.Probabilistic`, plus canonical aliases in `PLNCanonicalAPI`)
- Logical-induction-ready dynamic belief/process infrastructure over closed HOL
  formulas, kept strictly separate from Henkin truth and the static HOL↔WM lens
  (`HOL.LogicalInduction`, plus canonical aliases in `PLNCanonicalAPI`)
- Planner-facing higher-order belief shadows derived from semantic `ProbHOL`,
  so benchmark/control layers can consume theorem-backed prices and tracking
  results without becoming the canonical semantics
  (`PLNProbHOLPlannerBridge`, plus canonical aliases in `PLNCanonicalAPI`)
- Finite regime-mixture theorems and benchmark regressions for direct
  continuation approximation, soft-mixture squared-loss optimality, and
  reveal/value-of-information criteria in the higher-order Chapter-11 lane
  (`PLNRegimeMixtureBenchmarkBridge`, `PLNRegimeMixtureRegression`, plus
  canonical aliases in `PLNCanonicalAPI`)
- Clause-native MLN subsumption (primary MLN result): grounded clause semantics,
  clause-scope factor-graph compilation, ValuationWorldModel bridge, and
  `queryStrength = queryProb` with three regression canaries (3/4, 3/5, 0)
  (`MarkovLogicClause*`, canonical aliases in `PLNCanonicalAPI`)
- Abstract infinite-first MLN semantics over countable worlds (supporting infrastructure),
  with finite-support restriction, extensional factor-graph specialization, and
  abstract MassState WM bridge
  (`MarkovLogic{Abstract,Countable,FiniteRestriction,FactorGraph,BinaryWorldModel}`,
  regression canary in `MarkovLogicRegression`)
- Additive multiset WM singleton-surface classification / uniqueness
  (`SufficientStatisticSurface`)
- Forgetting layer with scope invariance and scoped no-go for exact inverse forgetting
  (`GenericWorldModelForgetting`)
- Coalition/semitopology layer for quorum/actionable-coalition reasoning with
  local-consensus/conflict lemmas and bridges into overlap/support forgetting
  (`PLNSemitopology`)
- Provenance-backed tracked forgetting and overlap-remainder support recovery
  for the non-additive perimeter (`PLNSemitopologyProvenanceBridge`)
- Runtime-audit oriented WM wrappers for conservation/order-cost/overlap-separation
  signals (`PLNWorldModelAudit`)
- Scope-labelled tracked provenance state with non-empty-scope exact forgetting
  under support containment plus clean-base hypotheses
  (`PLNScopedTrackedWhichState`)
- Selector-induced evidence/view preorders (`PLNWorldModelPreorder`)
- Advanced weighted Gaussian / one-step E/M extension with hard-label reduction
  (`PLNGaussianEMExtension`)
- PLN↔NARS rule correspondence package (rule-level bridge + informativeness adjunction)
  (`PLNNARSRuleCorrespondence`)
- Chapter-14 temporal/causal relationship layer
  (`PLNTemporalCausalInference`)
- Probabilistic event-calculus WM/rewrite grounding
  (`PLNProbabilisticEventCalculus`)
- Semantics decision gate (probability vs evidence/interval/NARS mirror)
  with weaker-than-KS references (`SemanticsDecisionTree`)
- Large-scale inference counterexample index:
  inclusion-exclusion identifiability no-go, trail-free non-stabilization witness,
  pooling non-uniqueness/corrected-uniqueness aliases, plus
  coverage/cardinality insufficiency for risk-sensitive selection
  (`PLNLargeScaleInferenceCounterexamples`)
- Multideduction positive residual decomposition + indexed agreement endpoint
  (`PLNMultideductionResidual`)
- Indexed n-way multideduction residual decomposition + indexed agreement family
  (`PLNMultideductionResidual`)
- Damped SP/SPN constructive convergence endpoint under eventual fresh evidence
  (`PLNTrailFreeDampedConvergence`)
- Damped SP/SPN bounded-gap fairness reset bounds with explicit time windows
  (`PLNTrailFreeDampedConvergence`)
- Finite BRGI object with policy-sensitive optimum characterization
  (`PremiseSelectionBRGI`)
- Graph-level BRGI object/refinement wrappers preserving finite-set optimality
  (`PremiseSelectionBRGI`)

## Where are the Lean proofs that PLN covers NB and k-NN?

See `Mettapedia/Logic/README.md` § "Where are the Lean proofs for PLN covering NB and k-NN?"
for exact file/line references. The key theorems are:

- **NB bridge**: `PLN_tensorStrength_eq_nbPosterior` (`PLNBayesNetInference:296`)
- **k-NN bridge**: `PLN_hplusPos_eq_knnRelevance` (`PremiseSelectionKNN_PLNBridge:111`)
- **Ranking transfer**: `pln_inherits_nb_optimal`, `pln_inherits_nb_ranking`,
  `pln_inherits_knn_ranking`, `pln_knn_ranking_eq` (`PremiseSelectionOptimality:333–369`)

All are fully proved (0 sorry).

Files with active proof debt are intentionally *not* re-exported here; those are grouped in
`PLNExperimental`.
-/

namespace Mettapedia.Logic.PLNCore

end Mettapedia.Logic.PLNCore
