import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.Languages.MeTTa.SpaceRefinement
import Mettapedia.GSLT.Core.WeightedMuScheduler
import Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler
import Mettapedia.Languages.MeTTa.Prime.TypedScheduler
import Mettapedia.Logic.ModalQuantaleSemantics
import Mettapedia.Order.FiniteSetFixedPoints
#eval List.insertionSort (fun _ _ : Nat => False) [1, 2, 3]
#eval List.insertionSort (fun _ _ : Nat => True) [1, 2, 3]
#print List.orderedInsert
#print List.insertionSort
#check List.orderedInsert_of_le

#print axioms Mettapedia.Languages.MeTTa.SpaceRefinement.check_holds_iff
#print axioms Mettapedia.Languages.MeTTa.SpaceRefinement.check_holds_iff_nonempty_evidence
#print axioms Mettapedia.Languages.MeTTa.SpaceRefinement.duplicate_occurrences_are_distinct
#print axioms Mettapedia.GSLT.Core.WeightedMuScheduler.QuantalePolicy.run_sound
#print axioms Mettapedia.GSLT.Core.WeightedMuScheduler.QuantalePolicy.completed_policies_bag_agree
#print axioms Mettapedia.GSLT.Core.WeightedMuScheduler.TemporalObjective.no_negativeObjective
#print axioms Mettapedia.GSLT.Core.WeightedMuScheduler.weightedGood_winning
#print axioms Mettapedia.GSLT.Core.WeightedMuScheduler.weightedOddLoop_has_no_certificate
#print axioms Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler.fusedScorer_grade_mul
#print axioms Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler.propensity_eq_strength_mul_confidence
#print axioms Mettapedia.PLN.Bridges.GSLT.EvidenceWeightedScheduler.internalNeedEvidencePolicy_apply
#print axioms Mettapedia.Logic.ModalMuCalculus.satisfies_congr
#print axioms Mettapedia.Logic.ModalMuCalculus.EvaluationGame.Program.graphValid_eq_true
#print axioms Mettapedia.Languages.MeTTa.Prime.TypedScheduler.TemporalObjective.evaluationProgram_denotes_iff
#print axioms Mettapedia.Languages.MeTTa.Prime.TypedScheduler.TemporalObjective.recurringSingleton_denotes
#print axioms Mettapedia.Languages.MeTTa.Prime.TypedScheduler.TemporalObjective.recurringStrategy_winning
#print axioms Mettapedia.Order.FiniteSetFixedPoints.monotone_chain_stabilizes_at_card
#print axioms Mettapedia.Order.FiniteSetFixedPoints.antitone_chain_stabilizes_at_card
#print axioms Mettapedia.Order.FiniteSetFixedPoints.lfp_eq_iterate_empty
#print axioms Mettapedia.Order.FiniteSetFixedPoints.gfp_eq_iterate_univ
#print axioms Mettapedia.Logic.ModalQuantaleSemantics.Boolean.qSatisfies_iff_satisfies
#print axioms Mettapedia.Logic.ModalQuantaleSemantics.Boolean.satisfies_mono_env
#print axioms Mettapedia.Logic.ModalQuantaleSemantics.Boolean.satisfies_mu_iff_mem_lfp
#print axioms Mettapedia.Logic.ModalQuantaleSemantics.Boolean.satisfies_nu_iff_mem_gfp
#print axioms Mettapedia.Logic.ModalQuantaleSemantics.Boolean.satisfies_mu_iff_mem_iterate_empty
#print axioms Mettapedia.Logic.ModalQuantaleSemantics.Boolean.satisfies_nu_iff_mem_iterate_univ
