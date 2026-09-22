import Mettapedia.OSLF.Main
import Mettapedia.OSLF.Framework.GeneratedLayerAdjunction
import Mettapedia.OSLF.Framework.LogicalMetric
import Mettapedia.OSLF.Framework.ScopeStratum
import Mettapedia.OSLF.Framework.ObserverIdempotence
import Mettapedia.OSLF.Framework.TypeFormerExtension
import Mettapedia.OSLF.SourceLedger
import Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
import Mettapedia.GSLT.Examples.AuthoredRuleSorting
import Mettapedia.GSLT.Meredith.Bisimulation
import Mettapedia.GSLT.Logic.HigherOrderBisimulation
import Mettapedia.GSLT.Logic.HigherOrderContextClosureControls
import Mettapedia.OSLF.Syntax.OperatorInterpretationRegression
import Mettapedia.OSLF.Framework.ContextualModalSignatureTransport

/-!
# Referenced constructions and their axiom trails

Each named reference below checks that a construction is available through
the imported modules, and makes a rename or removal break this inventory.
The `#print axioms` commands display dependency trails at build time; they do
not themselves reject an unexpected axiom.

This module proves neither completeness of the development nor fidelity to a
source theorem. Such claims require auditing the actual statements, explicit
hypotheses, instances, negative controls and operational correspondence.
-/

namespace Mettapedia.OSLF.DeliverableAudit

open Mettapedia.OSLF.Framework
open Mettapedia.GSLT

/-! ## Composable transport and its interpretation boundary -/

example := @Mettapedia.OSLF.Binding.RewriteMor.EnvCovering.ident
example := @Mettapedia.OSLF.Binding.RewriteMor.EnvCovering.comp
example := @Mettapedia.OSLF.Binding.RewriteMor.EnvCovering.ident_comp
example := @Mettapedia.OSLF.Binding.RewriteMor.EnvCovering.comp_ident
example := @Mettapedia.OSLF.Binding.RewriteMor.EnvCovering.comp_assoc
example := @Mettapedia.OSLF.Binding.RewriteMor.relyPossibly_transport_comp
example := @Mettapedia.OSLF.Binding.OperatorInterpretationRegression.inspect_bind
example := @Mettapedia.OSLF.Binding.OperatorInterpretationRegression.no_postcomposition_operation
example := @ContextualModalSignature.parametersFor_map
example := @ContextualModalSignatureCompiler.modalTerm_map
example := @ContextualModalSignatureCompiler.runFrom_extension_map
example := @ContextualModalSignatureCompiler.definition_map
example := @ContextualModalSignatureCompiler.continuationExtension_map
example := @ContextualModalTransportCanary.source_carrier_really_changes
example := @ContextualModalTransportCanary.contextual_row_still_has_three_parameters
example := @ContextualModalTransportCanary.chronological_rows_transport
example := @ContextualModalTransportCanary.reversed_dependencies_change_row
example := @ContextualModalTransportCanary.dropped_dependency_changes_row

#print axioms Mettapedia.OSLF.Binding.RewriteMor.EnvCovering.comp_assoc
#print axioms Mettapedia.OSLF.Binding.RewriteMor.relyPossibly_transport_comp
#print axioms Mettapedia.OSLF.Binding.OperatorInterpretationRegression.no_postcomposition_operation
#print axioms ContextualModalSignatureCompiler.definition_map

/-! ## 1. Redex-position generator, with the rho square as its gate -/

example := @GeneratedModality.relyPossibly_intro
example := @GeneratedModality.relyPossibly_step
example := @GeneratedModality.relyPossibly_elim
example := @GeneratedHypercubeInstances.rhoCommPaper_square_card
example := @GeneratedHypercubeInstances.rhoCommPaper_square_is_face
example := @GeneratedHypercubeInstances.rhoComm_square_needs_two_conditions

/-! ## 2. Labels: least enabling contexts and the class-relative congruence -/

example := @RedexRelativeCongruence.actIPO_context_replay
example := @RedexRelativeCongruence.contextRules_locally_respectful
example := @RedexRelativeCongruence.ipoBisimilar_comp
example := @RedexRelativeCongruence.class_eq_iff
example := @RedexRelativeCongruence.contextClassMap_toClass
example := @RedexRelativeCongruence.classFunctor
example := @RedexRelativeCongruence.InterfaceControls.interface_changing_step
example := @RedexRelativeCongruence.InterfaceControls.payloads_are_distinct
example := @RedexRelativeCongruence.InterfaceControls.shared_context_is_not_least
example := @RedexRelativeEnabling.Congruence.distinct_agents_same_class
example := @RedexRelativeEnabling.Congruence.active_and_idle_classes_distinct
example := @RedexRelativeEnabling.Congruence.context_map_changes_class
example := @HigherOrderBisimulation.System.progress_mono
example := @HigherOrderBisimulation.System.bisimilar_unfold
example := @HigherOrderBisimulation.System.bisimilar_trans
example := @HigherOrderBisimulation.System.class_eq_iff
example := @HigherOrderBisimulation.System.labelClass_eq_iff
example := @HigherOrderBisimulation.System.quotientStep_from_class_iff
example := @HigherOrderBisimulation.ipo_bisimilar_iff
example := @HigherOrderBisimulation.System.bisimilar_of_literal
example := @HigherOrderBisimulation.System.bisimilar_classLabel_iff
example := @HigherOrderBisimulation.PayloadControls.nested_payloads_are_bisimilar
example := @HigherOrderBisimulation.PayloadControls.nested_payloads_are_not_equal
example := @HigherOrderBisimulation.PayloadControls.literal_matching_is_stricter
example := @HigherOrderBisimulation.PayloadControls.different_channels_are_distinguished
example := @HigherOrderBisimulation.PayloadControls.observed_payloads_are_distinguished
example := @HigherOrderBisimulation.PayloadControls.class_step_needs_label_class
example := @HigherOrderBisimulation.TypedPayloadControls.false_computes_zero
example := @HigherOrderBisimulation.TypedPayloadControls.true_computes_one
example := @HigherOrderBisimulation.TypedPayloadControls.wrong_input_is_rejected
example := @HigherOrderBisimulation.TypedPayloadControls.wrong_output_is_rejected
example := @HigherOrderBisimulation.TypedPayloadControls.constant_result_is_rejected
example := @HigherOrderBisimulation.TypedPayloadControls.successor_classes_are_distinct
example := @Mettapedia.Logic.FinitaryClosure.respectful
example := @Mettapedia.Logic.FinitaryClosure.close_gfp_le
example := @Mettapedia.Logic.FinitaryClosure.coinduction_up_to
example := @Mettapedia.Logic.FinitaryClosure.certificate_sound_up_to
example := @HigherOrderBisimulation.System.gfp_iff_bisimilar
example := @HigherOrderBisimulation.System.finite_closure_bisimilar
example := @HigherOrderBisimulation.System.certificate_bisimilar
example := @HigherOrderBisimulation.ContextClosureControls.locally_respectful
example := @HigherOrderBisimulation.ContextClosureControls.seeds_advance
example := @HigherOrderBisimulation.ContextClosureControls.nested_certificate_bisimilar
example := @HigherOrderBisimulation.ContextClosureControls.wrong_channel_rejected
example := @HigherOrderBisimulation.ContextClosureControls.missing_child_rejected
example := @HigherOrderBisimulation.ContextClosureControls.wrong_child_rejected
example := @HigherOrderBisimulation.ContextClosureControls.unchecked_constructor_is_not_respectful
example := @BagRelativePushout.congruence
example := @Languages.ProcessCalculi.RhoCalculus.PlatformLabels.platform_congruence
example := @Languages.ProcessCalculi.RhoCalculus.PlatformLabels.platform_hasRelativePushouts
example := @Languages.ProcessCalculi.RhoCalculus.AdmissibleContexts.quoteFreePath_of_parallelPath
example := @Languages.ProcessCalculi.RhoCalculus.AdmissibleContexts.quoting_context_separates
example := @IPOBox.bisimilar_ipoSystem_iff
example := @IPOBox.bisimilar_ipoSystem_comp
example := @IPOBox.backwardImageFiniteModulo_of_cancel
example := @Languages.ProcessCalculi.RhoCalculus.PlatformLabels.platform_backwardImageFiniteModulo
example := @Languages.ProcessCalculi.RhoCalculus.PlatformLabels.platform_backward_adequacy
example := @ParallelLeastEnablerFails.least_enabler_exists
example := @ParallelLeastEnablerFails.redex_isLeastEnabler_beside_bystander
example := @ParallelLeastEnablerFails.composed_not_isLeastEnabler
example := @ParallelLeastEnablerFails.leastEnablerComposes_fails

/-! ## 3. The setoid at the entry, and the cut as a separating conjunction -/

example := @Languages.ProcessCalculi.RhoCalculus.PlatformEquations.platform_satisfiesModuloOver_cut
example := @Mettapedia.OSLF.StructuralModal.AdmissibleEquations.Admissible.leanInduction

/-! ## 4. Fixpoints, generated scopes, and the tube specimen -/

example := @GeneratedScopeRho.inScope_iff
example := @TubeShape.tube_separates
example := @TubeShape.formula_separates

/-! ## 5. The observer extension and its instrument index -/

example := @ObserverExtension.step_mono
example := @ObserverExtension.headed_of_openingRule_match
example := @ObserverExtension.openingRule_match_of_headed
example := @ObserverExtension.openingRule_match_iff
example := @ObserverExtension.projectionRule_exposes
example := @ObserverBisimilarity.separates_iff
example := @ObserverReconstruction.step_of_premiseFree_match
example := @ObserverReconstruction.opening_step
example := @ObserverReconstruction.projection_step
example := @ObserverReconstruction.adjoined_match_forces_head
example := @ObserverReconstruction.step_dichotomy
example := @ObserverReconstruction.argsHeaded_target_source
example := @ObserverReconstruction.authored_premiseFree_target_not_argsHeaded
example := @ObserverReconstruction.premisesAt_avoids
example := @ObserverReconstruction.authored_target_not_argsHeaded
example := @ObserverReconstruction.evaluatorAvoids_fails
example := @ObserverReconstruction.evaluatorAvoids_of_env
example := @ObserverReconstruction.stepAt_avoids
example := @ObserverReconstruction.premiseAt_avoids
example := @ObserverReconstruction.authored_step_not_argsHeaded
example := @ObserverReconstruction.Smuggling.reaching_bundle_does_not_determine_head
example := @ObserverReconstruction.Smuggling.carrier_fresh
example := @ObserverReconstruction.reads_head_iff
example := @Languages.ProcessCalculi.RhoCalculus.PlatformLabels.rhoPlatform_tame
example := @ObserverReconstruction.IsInstrumentBisimulation
example := @ObserverReconstruction.head_agreement
example := @ObserverReconstruction.isInstrumentBisimulation_not_total
example := @ObserverReconstruction.Determinacy.projection_response_not_determined
example := @ObserverReconstruction.RigidHeads
example := @Languages.ProcessCalculi.RhoCalculus.PlatformLabels.rhoPlatform_rigidHeads
example := @ObserverReconstruction.ObserverSetting
example := @Languages.ProcessCalculi.RhoCalculus.PlatformLabels.rhoPlatform_observerSetting
example := @ObserverReconstruction.LeftHeadsDeclared
example := @ObserverReconstruction.Citation.rigidity_alone_insufficient
example := @ObserverReconstruction.authored_no_match_adjoined_head
example := @ObserverReconstruction.instrument_step_is_adjoined
example := @ObserverReconstruction.adjoined_projection_match_forces
example := @ObserverReconstruction.projection_step_forces
example := @MeTTaIL.LinearMatch.mergeBindings_subset
example := @MeTTaIL.LinearMatch.matchArgsRel_fvars_inversion
example := @MeTTaIL.ScopedSyntax.bind
example := @MeTTaIL.ScopedSyntax.substFVar
example := @MeTTaIL.ScopedSyntax.untyped_disagrees_with_scoped
example := @ObserverExtension.projectionRule_delivers_of_match
example := @ObserverExtension.openingRule_delivers_of_match
example := @ObserverReconstruction.projection_response
example := @ObserverReconstruction.opening_response
example := @ObserverReconstruction.argument_agreement
example := @ObserverReconstruction.ReadableByKit
example := @ObserverReconstruction.reconstruction
example := @MeTTaIL.OccurringLabels.bindingLabels_relationQueryStep
example := @Languages.ProcessCalculi.RhoCalculus.PlatformLabels.guard_evaluatorAvoids
example := @MeTTaIL.OccurringLabels.bindingLabels_matchPattern
example := @MeTTaIL.OccurringLabels.labels_applyBindings
example := @MeTTaIL.OccurringLabels.labels_instantiateBVar
example := @ObserverReconstruction.Interference.transition_does_not_determine_head
example := @ObserverReconstruction.Interference.absorbing_step_reaches_no_bundle
example := @ObserverReconstruction.Interference.opening_step_reaches_bundle

/-! ## 6. The weighting functor -/

example := @EvidenceWeighting.weightMap_proof_irrelevant
example := @EvidenceWeighting.Adaptation.adaptive_not_perm_invariant
example := @EvidenceWeighting.BinderArity.byBinderArity_separates

/-! ## 7. The platform presentation -/

example := @Languages.ProcessCalculi.RhoCalculus.PlatformSlotLaws.joinRule_slotCount
example := @Languages.ProcessCalculi.RhoCalculus.PlatformSlotLaws.rhoPlatform_labels_nodup
example := @Languages.ProcessCalculi.RhoCalculus.PlatformValidation.rhoPlatform_validate

/-! ## 8. Substitutability parity and the logical metric -/

example := @theorem1_substitutability_forward
example := @Languages.ProcessCalculi.RhoCalculus.PlatformSubstitutability.Enumeration.rank_depends_on_enumeration

/-! ## 9. Observation quotients and coherent positioned-rule transport -/

example := @LogicalMetric.ObservationScheme.quotientReading_injective
example := @LogicalMetric.ObservationScheme.quotient_distance_triangle_nonarch
example := @LogicalMetric.depthScheme_classes_eq_iff_bisimilar
example := @LogicalMetric.no_depthMonotone_surjective_enumeration
example := @Binding.RewriteMor.comp_assoc
example := @Binding.RewriteMor.imgPred_comp

/-! ## 10. Behavioral steps, normalization and erased sequence data -/

example := @GSLT.Meredith.Bisimulation.quotientStep_from_class_iff
example := @GSLT.Meredith.Bisimulation.quotientStep_representative_independent
example := @GSLT.Meredith.Bisimulation.quotientPath_from_class_iff
example := @GSLT.Meredith.Bisimulation.quotientPath_mk_iff
example := @GSLT.Meredith.Bisimulation.QuotientStepControls.quotient_path_does_not_require_exact_target
example := @GSLT.Meredith.Bisimulation.QuotientStepControls.behavioral_morphism_need_not_preserve_quotient_steps
example := @Syntax.NormalFormStrength.Coarser.directed_reaches4
example := @Syntax.NormalFormStrength.Coarser.shifted_representative_reduces
example := @Binding.CollectionRestRepair.erased_splice_with_base_rest_is_not_ground
example := @Binding.CollectionRestRepair.erased_closed_splice_is_ground
example := @Binding.ScopeIndexControls.correct_lift_preserves_ambient_identity
example := @Binding.ScopeIndexControls.scope_types_do_not_force_binder_preservation

/-! ## The axiom trail -/

#print axioms Mettapedia.OSLF.Framework.GeneratedModality.relyPossibly_intro
#print axioms Mettapedia.OSLF.Framework.GeneratedModality.relyPossibly_step
#print axioms Mettapedia.OSLF.Framework.GeneratedModality.relyPossibly_elim
#print axioms Mettapedia.OSLF.Framework.GeneratedHypercubeInstances.rhoCommPaper_square_card
#print axioms Mettapedia.OSLF.Framework.GeneratedHypercubeInstances.rhoCommPaper_square_is_face
#print axioms Mettapedia.OSLF.Framework.GeneratedHypercubeInstances.rhoComm_square_needs_two_conditions
#print axioms Mettapedia.GSLT.RedexRelativeCongruence.actIPO_context_replay
#print axioms Mettapedia.GSLT.RedexRelativeCongruence.contextRules_locally_respectful
#print axioms Mettapedia.GSLT.RedexRelativeCongruence.ipoBisimilar_comp
#print axioms Mettapedia.GSLT.BagRelativePushout.congruence
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.platform_congruence
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.platform_hasRelativePushouts
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.AdmissibleContexts.quoteFreePath_of_parallelPath
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.AdmissibleContexts.quoting_context_separates
#print axioms Mettapedia.GSLT.IPOBox.bisimilar_ipoSystem_iff
#print axioms Mettapedia.GSLT.IPOBox.bisimilar_ipoSystem_comp
#print axioms Mettapedia.GSLT.IPOBox.backwardImageFiniteModulo_of_cancel
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.platform_backwardImageFiniteModulo
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.platform_backward_adequacy
#print axioms Mettapedia.GSLT.ParallelLeastEnablerFails.least_enabler_exists
#print axioms Mettapedia.GSLT.ParallelLeastEnablerFails.redex_isLeastEnabler_beside_bystander
#print axioms Mettapedia.GSLT.ParallelLeastEnablerFails.composed_not_isLeastEnabler
#print axioms Mettapedia.GSLT.ParallelLeastEnablerFails.leastEnablerComposes_fails
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquations.platform_satisfiesModuloOver_cut
#print axioms Mettapedia.OSLF.StructuralModal.AdmissibleEquations.Admissible.leanInduction
#print axioms Mettapedia.OSLF.Framework.GeneratedScopeRho.inScope_iff
#print axioms Mettapedia.OSLF.Framework.TubeShape.tube_separates
#print axioms Mettapedia.OSLF.Framework.TubeShape.formula_separates
#print axioms Mettapedia.OSLF.Framework.ObserverExtension.step_mono
#print axioms Mettapedia.OSLF.Framework.ObserverExtension.headed_of_openingRule_match
#print axioms Mettapedia.OSLF.Framework.ObserverExtension.openingRule_match_of_headed
#print axioms Mettapedia.OSLF.Framework.ObserverExtension.openingRule_match_iff
#print axioms Mettapedia.OSLF.Framework.ObserverExtension.projectionRule_exposes
#print axioms Mettapedia.OSLF.Framework.ObserverBisimilarity.separates_iff
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.step_of_premiseFree_match
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.opening_step
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.projection_step
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.adjoined_match_forces_head
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.step_dichotomy
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.argsHeaded_target_source
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.authored_premiseFree_target_not_argsHeaded
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.premisesAt_avoids
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.authored_target_not_argsHeaded
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.evaluatorAvoids_fails
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.evaluatorAvoids_of_env
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.stepAt_avoids
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.premiseAt_avoids
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.authored_step_not_argsHeaded
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.Smuggling.reaching_bundle_does_not_determine_head
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.Smuggling.carrier_fresh
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.reads_head_iff
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.rhoPlatform_tame
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.head_agreement
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.isInstrumentBisimulation_not_total
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.Determinacy.projection_response_not_determined
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.rhoPlatform_rigidHeads
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.rhoPlatform_observerSetting
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.Citation.rigidity_alone_insufficient
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.authored_no_match_adjoined_head
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.instrument_step_is_adjoined
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.projection_step_forces
#print axioms Mettapedia.OSLF.MeTTaIL.LinearMatch.mergeBindings_subset
#print axioms Mettapedia.OSLF.MeTTaIL.LinearMatch.matchArgsRel_fvars_inversion
#print axioms Mettapedia.OSLF.MeTTaIL.ScopedSyntax.untyped_disagrees_with_scoped
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.projection_response
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.argument_agreement
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.reconstruction
#print axioms Mettapedia.OSLF.Framework.ObserverExtension.openingRule_delivers_of_match
#print axioms Mettapedia.OSLF.MeTTaIL.OccurringLabels.bindingLabels_relationQueryStep
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.guard_evaluatorAvoids
#print axioms Mettapedia.OSLF.MeTTaIL.OccurringLabels.bindingLabels_matchPattern
#print axioms Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_applyBindings
#print axioms Mettapedia.OSLF.MeTTaIL.OccurringLabels.labels_instantiateBVar
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.Interference.transition_does_not_determine_head
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.Interference.absorbing_step_reaches_no_bundle
#print axioms Mettapedia.OSLF.Framework.ObserverReconstruction.Interference.opening_step_reaches_bundle
#print axioms Mettapedia.GSLT.EvidenceWeighting.weightMap_proof_irrelevant
#print axioms Mettapedia.GSLT.EvidenceWeighting.Adaptation.adaptive_not_perm_invariant
#print axioms Mettapedia.GSLT.EvidenceWeighting.BinderArity.byBinderArity_separates
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSlotLaws.joinRule_slotCount
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSlotLaws.rhoPlatform_labels_nodup
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformValidation.rhoPlatform_validate
#print axioms Mettapedia.OSLF.Framework.theorem1_substitutability_forward
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSubstitutability.Enumeration.rank_depends_on_enumeration
#print axioms Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.quotientReading_injective
#print axioms Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.quotient_distance_triangle_nonarch
#print axioms Mettapedia.OSLF.Framework.LogicalMetric.depthScheme_classes_eq_iff_bisimilar
#print axioms Mettapedia.OSLF.Framework.LogicalMetric.no_depthMonotone_surjective_enumeration
#print axioms Mettapedia.OSLF.Binding.RewriteMor.comp_assoc
#print axioms Mettapedia.OSLF.Binding.RewriteMor.imgPred_comp
#print axioms Mettapedia.GSLT.Meredith.Bisimulation.quotientStep_from_class_iff
#print axioms Mettapedia.GSLT.Meredith.Bisimulation.quotientStep_representative_independent
#print axioms Mettapedia.GSLT.Meredith.Bisimulation.quotientPath_from_class_iff
#print axioms Mettapedia.GSLT.Meredith.Bisimulation.quotientPath_mk_iff
#print axioms Mettapedia.GSLT.Meredith.Bisimulation.QuotientStepControls.quotient_path_does_not_require_exact_target
#print axioms Mettapedia.GSLT.Meredith.Bisimulation.QuotientStepControls.behavioral_morphism_need_not_preserve_quotient_steps
#print axioms Mettapedia.OSLF.Syntax.NormalFormStrength.Coarser.directed_reaches4
#print axioms Mettapedia.OSLF.Syntax.NormalFormStrength.Coarser.shifted_representative_reduces
#print axioms Mettapedia.OSLF.Binding.CollectionRestRepair.erased_splice_with_base_rest_is_not_ground
#print axioms Mettapedia.OSLF.Binding.CollectionRestRepair.erased_closed_splice_is_ground
#print axioms Mettapedia.OSLF.Binding.ScopeIndexControls.correct_lift_preserves_ambient_identity
#print axioms Mettapedia.OSLF.Binding.ScopeIndexControls.scope_types_do_not_force_binder_preservation

/-! ## Authored rules against their own declarations -/

example := @GSLT.LanguageDef.AuthoredRuleSorting.checkRewriteWellSorted_sound
example := @GSLT.LanguageDef.AuthoredRuleSorting.mettaHE_all_rules_sorted
example := @GSLT.LanguageDef.AuthoredRuleSorting.twoSortDependent_sorted_count
example := @GSLT.LanguageDef.AuthoredRuleSorting.rhoCalc_no_rule_sorted
example := @GSLT.LanguageDef.AuthoredRuleSorting.metamathCore_no_rule_sorted
example := @GSLT.LanguageDef.AuthoredRuleSorting.collection_with_rest_never_sorted
example := @GSLT.LanguageDef.AuthoredRuleSorting.subst_never_sorted
example := @GSLT.LanguageDef.AuthoredRuleSorting.undeclared_fvar_never_sorted
example := @GSLT.LanguageDef.AuthoredRuleSorting.hasType_rest_irrelevant
example := @GSLT.LanguageDef.AuthoredRuleSorting.communicationLeft_hasType
example := @GSLT.LanguageDef.AuthoredRuleSorting.hasType_admits_a_wholly_undeclared_rest
example := @GSLT.LanguageDef.AuthoredRuleSorting.rhoComm_left_sorted_without_its_rest
example := @GSLT.LanguageDef.AuthoredRuleSorting.communication_rest_is_undeclared
example := @GSLT.LanguageDef.AuthoredRuleSorting.communication_rest_declared_once_added
example := @GSLT.LanguageDef.AuthoredRuleSorting.metamath_first_rule_sorted_once_declared

#print axioms Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting.checkRewriteWellSorted_sound
#print axioms Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting.communicationLeft_hasType
#print axioms Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting.hasType_rest_irrelevant
#print axioms Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting.collection_with_rest_never_sorted
#print axioms Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting.hasType_admits_a_wholly_undeclared_rest
#print axioms Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting.mettaHE_all_rules_sorted

/-! ## The source ledger, and the obligations closed against it -/

example := @SourceLedger.ledger_integrity
example := @SourceLedger.numbered_entered
example := @SourceLedger.standing_tally
example := @SourceLedger.audit_coverage
example := @SourceLedger.tally_is_total
example := @SourceLedger.refuted_rows_empty
example := @SourceLedger.proposition_19_1_source_proof_not_cited
example := @SourceLedger.proposition_19_1_is_constructed_not_proved

example := @Framework.GeneratedLayerAdjunction.forget_generated
example := @Framework.GeneratedLayerAdjunction.composite_is_identity
example := @Framework.GeneratedLayerAdjunction.forget_is_not_injective
example := @Framework.GeneratedLayerAdjunction.reading_one_extends_nothing

example := @Framework.LogicalMetric.ObservationScheme.distance_triangle_nonarch
example := @Framework.LogicalMetric.ObservationScheme.distance_eq
example := @Framework.LogicalMetric.ObservationScheme.distance_eq_zero_iff
example := @Framework.LogicalMetric.ObservationScheme.distance_lt_of_rank_lt
example := @Framework.LogicalMetric.enumeration_matters

example := @Framework.ScopeStratum.stratum_quote_par
example := @Framework.ScopeStratum.stratum_join_le
example := @Framework.ScopeStratum.join_injective
example := @Framework.ScopeStratum.stratum_tower
example := @Framework.ScopeStratum.stratum_constant
example := @Framework.ScopeStratum.two_pow_le_sizeOf_towerBody
example := @Framework.ScopeStratum.description_is_cheap

example := @Framework.ObserverIdempotence.rewriteAt_eq_of_second_extension
example := @Framework.ObserverIdempotence.rewriteAt_eq_of_two_extensions
example := @Framework.ObserverIdempotence.disjoint_second_round_is_fresh
example := @Framework.ObserverIdempotence.repeating_a_round_is_not_fresh
example := @Framework.ObserverIdempotence.equations_preserved
example := @Framework.ObserverIdempotence.authored_retained

example := @Framework.TypeFormerExtension.authored_retained
example := @Framework.TypeFormerExtension.rewrites_unchanged
example := @Framework.TypeFormerExtension.redexSites_unchanged
example := @Framework.TypeFormerExtension.extends_a_theory_with_a_site
example := @Framework.TypeFormerExtension.rhoCalc_strictly_extended
example := @Framework.TypeFormerExtension.no_formers_without_sites
example := @Framework.TypeFormerExtension.rhoOnce_labels_distinct
example := @Framework.TypeFormerExtension.rhoTwice_labels_collide
example := @Framework.TypeFormerExtension.rhoTwice_not_label_distinct

/-! ## The three rely-possibly carriers, and the scheme they share -/

example := @Framework.RelyPossiblyScheme.diamond_adjunction
example := @Framework.RelyPossiblyScheme.diamond_exists
example := @Framework.RelyPossiblyScheme.RelyFrame.modality_iff_diamond
example := @Framework.RelyPossiblyScheme.RelyFrame.modality_mono_target
example := @Framework.RelyPossiblyScheme.RelyFrame.modality_antitone_rely
example := @Framework.RelyPossiblyScheme.RelyFrame.modality_congr_rely
example := @Framework.RelyPossiblyScheme.RelyFrame.modality_or_rely
example := @Framework.RelyPossiblyScheme.RelyFrame.modality_of_no_admissible
example := @Framework.RelyPossiblyScheme.RelyFrame.not_modality_of_target_empty
example := @Framework.RelyPossiblyScheme.RelyFrame.modality_iff_diamond_of_subsingleton
example := @Framework.RelyPossiblyScheme.categorical_is_instance
example := @Framework.RelyPossiblyScheme.pattern_is_instance
example := @Framework.RelyPossiblyScheme.scoped_is_instance
example := @Framework.RelyPossiblyScheme.categorical_preserves_joins
example := @Framework.RelyPossiblyScheme.join_not_preserved
example := @Framework.RelyPossiblyScheme.target_need_not_be_load_bearing
example := @Framework.RelyPossiblyScheme.FrameMorphism.id
example := @Framework.RelyPossiblyScheme.FrameMorphism.comp
example := @Framework.RelyPossiblyScheme.FrameMorphism.modality_map
example := @Framework.RelyPossiblyScheme.transport_is_directed

#print axioms Mettapedia.OSLF.Framework.TypeFormerExtension.extends_a_theory_with_a_site
#print axioms Mettapedia.OSLF.SourceLedger.ledger_integrity
#print axioms Mettapedia.OSLF.SourceLedger.standing_tally
#print axioms Mettapedia.OSLF.Framework.GeneratedLayerAdjunction.reading_one_extends_nothing
#print axioms Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.distance_triangle_nonarch
#print axioms Mettapedia.OSLF.Framework.ScopeStratum.description_is_cheap
#print axioms Mettapedia.OSLF.Framework.ObserverIdempotence.rewriteAt_eq_of_two_extensions
#print axioms Mettapedia.OSLF.Framework.RelyPossiblyScheme.categorical_is_instance
#print axioms Mettapedia.OSLF.Framework.RelyPossiblyScheme.pattern_is_instance
#print axioms Mettapedia.OSLF.Framework.RelyPossiblyScheme.scoped_is_instance
#print axioms Mettapedia.OSLF.Framework.RelyPossiblyScheme.join_not_preserved
#print axioms Mettapedia.OSLF.Framework.RelyPossiblyScheme.FrameMorphism.modality_map
#print axioms Mettapedia.OSLF.Framework.RelyPossiblyScheme.transport_is_directed

end Mettapedia.OSLF.DeliverableAudit
