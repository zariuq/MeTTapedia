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
import Mettapedia.Logic.SoundnessCompleteness
import Mettapedia.Logic.PLNErrorMagnificationGrounding
import Mettapedia.Logic.PLNCanonicalAPI
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
  (`Evidence.toOdds_power_rpow`, `Evidence.toLogOdds_power_mul`)
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
