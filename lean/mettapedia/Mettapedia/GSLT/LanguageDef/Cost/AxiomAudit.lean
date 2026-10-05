import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationBinding
import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra
import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingCongruence
import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientModel
import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientSubstitution
import Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation
import Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues
import Mettapedia.GSLT.LanguageDef.Cost.CodeAuthority
import Mettapedia.GSLT.LanguageDef.Cost.Elaboration.FibreReplayKey
import Mettapedia.GSLT.LanguageDef.Cost.Elaboration.ReplayKey
import Mettapedia.GSLT.LanguageDef.Cost.FiniteActivePair
import Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls
import Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionInstantiation
import Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation
import Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction
import Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingControls
import Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingExtension
import Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingModel
import Mettapedia.GSLT.LanguageDef.Cost.FundedWriter
import Mettapedia.GSLT.LanguageDef.Cost.InteractionCoverage
import Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
import Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary
import Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation
import Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension
import Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws
import Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport
import Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation
import Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns
import Mettapedia.GSLT.LanguageDef.HistoryKeyObstruction
import Mettapedia.GSLT.LanguageDef.Cost.ScheduleWriter
import Mettapedia.GSLT.LanguageDef.Cost.SourceAccountSubstitution
import Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage
import Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement
import Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentPrefixRefinement
import Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement
import Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement
import Mettapedia.GSLT.LanguageDef.Cost.StaticSpineHeadRefinement
import Mettapedia.GSLT.LanguageDef.CostScheduleObservation
/-!
# Axioms of the generic Cost construction

Every statement listed here depends only on `propext`, `Classical.choice` and
`Quot.sound`.  The sources carry the statements; this file prints their axioms.
-/

-- GSLT.LanguageDef.Continued.ContinuationDecorationBinding
#print axioms Mettapedia.GSLT.LanguageDef.WellSorted.HasType.instantiateBVarAt
#print axioms Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.mapContractum_instantiateBVarAt
#print axioms Mettapedia.GSLT.LanguageDef.continuation_substitution_avoids_capture

-- GSLT.LanguageDef.Cost.AccountBindingAlgebra
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.modelCategory
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.forget
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.pure_forget
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.fibre
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.fibre_forget
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.accountSubstitution_identity
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.accountSubstitution_comp
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.fibreSubstitution
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.fibreSubstitutionObserved
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.fibreSubstitution_comp_apply
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.OccurrenceMarker.instantiateHom
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.OccurrenceMarker.comparison
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.OccurrenceMarker.comparison_fibre_nontrivial
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.RhoSourceComparison.source_equations
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.RhoSourceComparison.observe_source
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.RhoSourceComparison.canonical_source_observation_act
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.RhoSourceComparison.marked_input_source
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.RhoSourceComparison.marked_body_instantiation
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.RhoSourceComparison.action_nontrivial
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.RhoSourceComparison.comparison_loses_account_order
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.LambdaBindingComparison.marked_self_application_source
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingAlgebra.LambdaBindingComparison.marked_self_application_keeps_occurrence

-- GSLT.LanguageDef.Cost.AccountBindingCongruence
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingCongruence.equation_sound
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingCongruence.derivation_sound
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingCongruence.derivation_observe
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingCongruence.setoid

-- GSLT.LanguageDef.Cost.AccountBindingQuotientModel
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientModel.operation_project
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientModel.project_substituteArguments
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientModel.operation_substitute
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientModel.algebra

-- GSLT.LanguageDef.Cost.AccountBindingQuotientSubstitution
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientSubstitution.substituteRaw_environment_congr
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientSubstitution.substitute_comp
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientSubstitution.algebra
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientSubstitution.liftEnvironment_represented

-- GSLT.LanguageDef.Cost.AtomicSignatureInterpretation
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation.decodeNatKey_encodeNatKey
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation.canonical_eq_iff
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation.committed_accounts_injective
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation.commitLiteral_typed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.AtomicSignatureInterpretation.signature_syntax_readout

-- GSLT.LanguageDef.Cost.BoundaryOccurrenceValues
#print axioms Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues.get
#print axioms Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues.set
#print axioms Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues.get_set
#print axioms Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues.set_get
#print axioms Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues.get_set_other
#print axioms Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues.set_commute
#print axioms Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues.getTree
#print axioms Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues.setTree
#print axioms Mettapedia.GSLT.LanguageDef.Cost.BoundaryOccurrenceValues.setTree_packedChildren

-- GSLT.LanguageDef.Cost.CodeAuthority
#print axioms Mettapedia.GSLT.LanguageDef.Cost.typed_code_instantiateBVar
#print axioms Mettapedia.GSLT.LanguageDef.Cost.prior_layer_funding_is_code
#print axioms Mettapedia.GSLT.LanguageDef.Cost.wrapped_typing_does_not_imply_code

-- GSLT.LanguageDef.Cost.Elaboration.FibreReplayKey
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.compactFibreKey_hasRealization_iff_constant
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.compactFibreKey_supports_iff_constant
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.provenanceKey_isExact

-- GSLT.LanguageDef.Cost.Elaboration.ReplayKey
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.ReplayKey.hasRealization_iff_supports_of_split
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.ReplayKey.isExact_iff_hasIdentityRealization
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.ReplayKey.Examples.collapsed_not_exact
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Elaboration.ReplayKey.Examples.retained_strictlyRefines_collapsed

-- GSLT.LanguageDef.Cost.FiniteActivePair
#print axioms Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.costActivePairRedex_hasType
#print axioms Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.costActivePairContractum_hasType

-- GSLT.LanguageDef.Cost.FiniteInteractionControls
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls.lambda_core_valid
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls.asynchronous_core_valid
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls.synchronous_core_valid
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls.synchronous_contractum_in_core
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls.FundedSynchronous.fires
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls.FundedSynchronous.reducts_exact
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls.FundedSynchronous.empty_stack_no_step
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteInteractionControls.FundedSynchronous.mismatched_head_no_step

-- GSLT.LanguageDef.Cost.FiniteInteractionInstantiation
#print axioms Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.costWholeRedex_instances_typed

-- GSLT.LanguageDef.Cost.FiniteLambdaActivation
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation.language_valid
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation.funded_local_beta_typed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation.funded_identity_fires
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation.unfunded_identity_no_step
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation.mismatched_identity_no_step
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FiniteLambdaActivation.local_body_not_closed_assignment

-- GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction.free
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction.adjunction
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction.accountMonad
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction.multiplication_account
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction.multiplication_substitute
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction.multiplication_not_injective

-- GSLT.LanguageDef.Cost.FreeAccountBindingControls
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingControls.Lambda.self_application_nontrivial
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingControls.Lambda.full_environment_is_essential
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingControls.Lambda.multiplication_noninjective
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingControls.Lambda.inside_binder_not_root_action
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingControls.Rho.input_source
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingControls.Rho.input_nontrivial

-- GSLT.LanguageDef.Cost.FreeAccountBindingExtension
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingExtension.extendCloneHom
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingExtension.extend
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingExtension.extend_unique
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingExtension.homEquiv

-- GSLT.LanguageDef.Cost.FreeAccountBindingModel
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingModel.observationHom
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingModel.act_substitute
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingModel.model
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingModel.generatorHom
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingModel.unit

-- GSLT.LanguageDef.Cost.FundedWriter
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FundedWriter.interpret_pure
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FundedWriter.interpret_map
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FundedWriter.interpret_bind
#print axioms Mettapedia.GSLT.LanguageDef.Cost.FundedWriter.interpret_endomorphism

-- GSLT.LanguageDef.Cost.InteractionCoverage
#print axioms Mettapedia.GSLT.LanguageDef.Cost.InteractionCoverage.rho_base_rules
#print axioms Mettapedia.GSLT.LanguageDef.Cost.InteractionCoverage.synchronous_base_rules
#print axioms Mettapedia.GSLT.LanguageDef.Cost.InteractionCoverage.rho_not_all_rules_selected

-- GSLT.LanguageDef.Cost.Layer.Operational
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.Realization.realizePath_append
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.Realization.workSpan_append
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.Realization.compact_key_requires_injectivity
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.OperationalSchedule.workSpan_append
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.OperationalSchedule.workSpan_ofIndexed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.OperationalSchedule.receipt_ofIndexed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.OperationalSchedule.count_ofIndexed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.OperationalSchedule.waves_ofIndexed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.NormalizationEvent.erases_equivalent
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.oneWave_workSpan
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.oneWave_ne_serial_of_wide

-- GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary
#print axioms Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary.source_self_application_typed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary.literal_base_translation_not_typed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary.signed_literal_translation_not_typed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary.wrapped_variable_not_base
#print axioms Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary.two_environment_application_typed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary.two_binder_abstraction_not_typed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary.identity_adapter_typed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary.adapter_not_source_equivalent_to_variable
#print axioms Mettapedia.GSLT.LanguageDef.Cost.LiteralLambdaTranslationBoundary.adapter_requires_funded_activation

-- GSLT.LanguageDef.Cost.OperationalValuation
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.scheduleGrade_append
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.scheduleGrade_workSpan
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.chronology_historyGrade
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.scheduleGrade_chronology
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.scheduleGrade_withWorkSpan
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.erase_total_coordinate_recovers_workSpan
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.annotateSchedule_erases_to_eventBag
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.filterAnnotatedSchedule_eq_authoredSemanticFilter
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.no_history_recovery_of_workSpan_collision
#print axioms Mettapedia.GSLT.LanguageDef.Cost.OperationalValuation.readout_eq_of_history_eq

-- GSLT.LanguageDef.Cost.RawAccountBindingExtension
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension.observe_interpret
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension.interpret_substitute_variable
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension.interpret_gen_operation
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension.interpret_gen_substitute
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension.account_word_injective
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension.interpretMap
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingExtension.constructorMap_unique

-- GSLT.LanguageDef.Cost.RawAccountBindingLaws
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws.interpret_liftEnvironment
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws.interpret_substituteArguments
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws.substitute_identity_sound
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws.substitute_comp_sound
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws.substitute_operation_sound
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RawAccountBindingLaws.substitute_account_sound

-- GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport.transport
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport.transport_packedChildren
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport.append
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport.append_packedChildren
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport.argumentTail_packedChildren
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedBoundaryOriginTransport.elementTail_packedChildren

-- GSLT.LanguageDef.Cost.RetainedSourceObservation
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation.sourceSkeletonInventoryTree_eq_of_rel
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation.distinct_fvars_same_inventory
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation.sourceSkeletonInventory_eq_of_equivalent
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation.sourceSkeletonInventory_normalizeTerm
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation.normalizeObservedFibre
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation.normalizeAccountFibre
#print axioms Mettapedia.GSLT.LanguageDef.Cost.RetainedSourceObservation.normalize_account_transport

-- GSLT.LanguageDef.Cost.ScheduleWriter
#print axioms Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational.OperationalSchedule.receipt_append
#print axioms Mettapedia.GSLT.LanguageDef.Cost.ScheduleWriter.interpret_nil
#print axioms Mettapedia.GSLT.LanguageDef.Cost.ScheduleWriter.interpret_append
#print axioms Mettapedia.GSLT.LanguageDef.Cost.ScheduleWriter.interpret_ofIndexed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.ScheduleWriter.interpret_oneWave

-- GSLT.LanguageDef.Cost.SourceAccountSubstitution
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceAccountSubstitution.substitute_identity
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceAccountSubstitution.substitute_comp
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceAccountSubstitution.substitute_length
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceAccountSubstitution.map_substitute
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceAccountSubstitution.swap_changes_account_atom

-- GSLT.LanguageDef.Cost.SourceIndexedSemanticImage
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage.insert
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage.eraseColor_compile
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage.compile_injective
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage.normalize
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage.sourceKey_ofSource_eq_iff
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage.normalizeObservedImage

-- GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement.argumentPlan
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement.plan
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement.refined_term_typed
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement.frame
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement.plan_boundaryPacket
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement.children
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticArgumentBoundaryRefinement.semanticTree

-- GSLT.LanguageDef.Cost.StaticArgumentPrefixRefinement
#print axioms Mettapedia.GSLT.LanguageDef.CostStaticArgumentPlan.reprefix
#print axioms Mettapedia.GSLT.LanguageDef.CostStaticArgumentPlan.reprefix_abstractPatterns
#print axioms Mettapedia.GSLT.LanguageDef.CostStaticArgumentPlan.reprefix_entries
#print axioms Mettapedia.GSLT.LanguageDef.CostStaticElementPlan.reprefix
#print axioms Mettapedia.GSLT.LanguageDef.CostStaticElementPlan.reprefix_abstractPatterns
#print axioms Mettapedia.GSLT.LanguageDef.CostStaticElementPlan.reprefix_entries

-- GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement.boundary_certifies
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement.replacementChildren
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement.replacement_restore
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement.replacement_recontextualize
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticLeafBoundaryRefinement.replacement_rigid_leaf_changed

-- GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Argument.plan
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Argument.entries
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Argument.abstractPatterns
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Argument.children
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Argument.children_packedChildren
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Element.plan
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Element.entries
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Element.abstractPatterns
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Element.children
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineEnclosingRefinement.Element.children_packedChildren

-- GSLT.LanguageDef.Cost.StaticSpineHeadRefinement
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineHeadRefinement.plan
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineHeadRefinement.entries
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineHeadRefinement.abstractPatterns
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineHeadRefinement.children
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineHeadRefinement.children_packedChildren
#print axioms Mettapedia.GSLT.LanguageDef.Cost.StaticSpineHeadRefinement.occurrences

-- GSLT.LanguageDef.CostScheduleObservation
#print axioms Mettapedia.GSLT.LanguageDef.CostScheduleObservation.Schedule.events_append
#print axioms Mettapedia.GSLT.LanguageDef.CostScheduleObservation.Schedule.eventReceipt_events
#print axioms Mettapedia.GSLT.LanguageDef.CostScheduleObservation.Schedule.collect_events
#print axioms Mettapedia.GSLT.LanguageDef.CostScheduleObservation.Schedule.observed_append
#print axioms Mettapedia.GSLT.LanguageDef.CostScheduleObservation.Schedule.observed_ofIndexed
#print axioms Mettapedia.GSLT.LanguageDef.CostScheduleObservation.Schedule.observed_receipt_ofIndexed
#print axioms Mettapedia.GSLT.LanguageDef.CostScheduleObservation.Schedule.observed_wave_count_ofIndexed
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.fires_target_unique
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.target_eq_of_pathEntries_eq
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.fires_pathEntries
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.exists_path_of_fires
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.instanceValuation_onPath
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.exists_path_of_stepEnables
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.product_path_parts
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.product_part_valuation
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.funded_path_parts
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.joint_path_left
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.joint_path_left_ledger
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.joint_path_left_parts
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.RunControls.two_orders_same_payment
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.RunControls.zero_price_still_works
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.runPayment_eq_receipt
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.observations_of_entries
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.length_le_runPayment_card
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.unpaid_run
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.matching_run
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.wave_run
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.eq_of_receipt_eq_zero
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.exists_one_wave
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.one_wave_run
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.exists_waveRuns
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.WaveRuns.receipt
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.WaveRuns.payment
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.WaveRuns.work
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.WaveRuns.balance
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.WaveRuns.append
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.WaveRuns.split
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.WaveRuns.append_payment_work
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.paymentTraceAccount_comap
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.paymentAccount_of
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.history_step_iff
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.historyStrip_comp_unit
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.classLabels_total
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.classLabels_namesSource
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.history_unique_parent
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.classHistory_unique_parent
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.MergeControl.base_two_parents
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.MergeControl.history_separates_parents
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.element_eq_of_events
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.toWriter_injective
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.extend_injective
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.eq_origin_or_extend
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.RootedCover.liftPath_append
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.RootedCover.ofElement_extend
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.RootedCover.ofElement_unique
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.historyCover_ofElement
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.forget_injective_iff
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.Erasure.cover_eq_bot
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.Erasure.base_eq_top
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.Erasure.folds_iff_ne_bot
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.Erasure.survives_iff_le_kernel
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.Erasure.descends_iff_trace_le_kernel
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.ErasureControls.grid_trace_folds
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.ErasureControls.trace_ne_base
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.stateRecoverable_iff
#print axioms Mettapedia.GSLT.Causality.HistoryMonad.stateRecoverable_iff_base_le
#print axioms Mettapedia.GSLT.LanguageDef.CIGSLT.no_concatenating_history_monad
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.instanceValuation_onPath_map
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.System.funded_payment_recoverable
#print axioms Mettapedia.GSLT.Causality.ResourceInteraction.RunControls.order_not_recoverable
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.ledger_law
#print axioms Mettapedia.GSLT.LanguageDef.Cost.SchedulePaidRuns.ledger_law_of_no_release
