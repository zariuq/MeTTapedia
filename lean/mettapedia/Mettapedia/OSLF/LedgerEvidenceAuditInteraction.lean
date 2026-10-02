import Mettapedia.GSLT.Contexts.ConstantMap
import Mettapedia.GSLT.Contexts.ContextMorphism
import Mettapedia.GSLT.Contexts.Controls.ImageAction
import Mettapedia.GSLT.Contexts.TransitionProfile
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.TransitionProfile
import Mettapedia.GSLT.Contexts.ContextTheory
import Mettapedia.GSLT.Contexts.ImageObservation
import Mettapedia.GSLT.Contexts.RelativeEquivalence
import Mettapedia.GSLT.Contexts.Traces
import Mettapedia.GSLT.Core.FunctionalBisimulation
import Mettapedia.GSLT.LanguageDef.BagNormalFormEffective
import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.Branching
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.ConstantMap
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.EquationTransport
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.Hosting
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.LongerRun
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.OverObservation
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.ReductionBisimilarity
import Mettapedia.GSLT.LanguageDef.Contexts.Controls.Renaming
import Mettapedia.GSLT.LanguageDef.Contexts.Interacting
import Mettapedia.GSLT.LanguageDef.Contexts.Invertible
import Mettapedia.GSLT.LanguageDef.Contexts.Presented
import Mettapedia.GSLT.LanguageDef.Contexts.Structural
import Mettapedia.GSLT.LanguageDef.Contexts.TypedLabels
import Mettapedia.GSLT.LanguageDef.Continued.CutShape
import Mettapedia.GSLT.LanguageDef.Continued.Effective
import Mettapedia.GSLT.LanguageDef.Continued.EffectiveInstances
import Mettapedia.GSLT.LanguageDef.Continued.EffectiveIsomorphism
import Mettapedia.GSLT.LanguageDef.Continued.Forget
import Mettapedia.GSLT.LanguageDef.Continued.InstanceTable
import Mettapedia.GSLT.LanguageDef.Continued.NotContinued
import Mettapedia.GSLT.LanguageDef.Continued.NotEssentiallySurjective
import Mettapedia.GSLT.LanguageDef.Continued.NotFull
import Mettapedia.GSLT.LanguageDef.Continued.Presentation
import Mettapedia.GSLT.LanguageDef.Continued.Sections
import Mettapedia.GSLT.LanguageDef.ContinuedCategory
import Mettapedia.GSLT.LanguageDef.EffectiveSection
import Mettapedia.GSLT.LanguageDef.Encodings.PatternShape
import Mettapedia.GSLT.LanguageDef.EquationSimulation
import Mettapedia.GSLT.LanguageDef.Interaction.BaseInteractions
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContactContinued
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContactMorphisms
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContextualOnly
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
import Mettapedia.GSLT.LanguageDef.Interaction.Fire
import Mettapedia.GSLT.LanguageDef.Interaction.FireInstances
import Mettapedia.GSLT.LanguageDef.Interaction.Freeness
import Mettapedia.GSLT.LanguageDef.Interaction.HeterogeneousCut
import Mettapedia.GSLT.LanguageDef.Interaction.Migration
import Mettapedia.GSLT.LanguageDef.Interaction.MigrationInstances
import Mettapedia.GSLT.LanguageDef.Interaction.ObserverStrength
import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.Interaction.Strength
import Mettapedia.GSLT.LanguageDef.Interaction.StrengthInstances
import Mettapedia.GSLT.LanguageDef.Interaction.Surfaces
import Mettapedia.GSLT.LanguageDef.ReactiveContexts
import Mettapedia.Languages.Calculator.Cut
import Mettapedia.Languages.Calculator.EffectiveSection
import Mettapedia.Languages.Calculator.Interaction
import Mettapedia.Languages.Calculator.Section
import Mettapedia.Languages.InteractionCategory.Interaction
import Mettapedia.Languages.PartrecMachine.HistoryContinued
import Mettapedia.Languages.PartrecMachine.HistoryIsomorphism
import Mettapedia.Languages.PartrecMachine.UndecidableEquivalence
import Mettapedia.Languages.ProcessCalculi.Ambient.Continued
import Mettapedia.Languages.ProcessCalculi.Ambient.Interaction
import Mettapedia.Languages.ProcessCalculi.CCS.Continued
import Mettapedia.Languages.ProcessCalculi.CCS.Cut
import Mettapedia.Languages.ProcessCalculi.CCS.Interaction
import Mettapedia.Languages.ProcessCalculi.CCS.Observed
import Mettapedia.Languages.ProcessCalculi.CCS.Section
import Mettapedia.Languages.ProcessCalculi.CCS.Surface
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingEquivariance
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingNotSignatureMap
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingStepRF
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingTransitions
import Mettapedia.Languages.ProcessCalculi.PiCalculus.FullEncodingTransitions
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ProcessContext
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSectionEffective
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SynchronousWrapping
import Mettapedia.Languages.Transducers.ForcedReading
import Mettapedia.Languages.Transducers.NotInteractive
import Mettapedia.Languages.TransitionSystem.Extension
import Mettapedia.Languages.TuringMachine.Hosted
import Mettapedia.Languages.TuringMachine.LanguageDef
import Mettapedia.Languages.TuringMachine.NotInteractive
import Mettapedia.Languages.TuringMachine.OneSort
import Mettapedia.Languages.TuringMachine.Steps
import Mettapedia.OSLF.MeTTaIL.MultiHoleContext
import Mettapedia.OSLF.MeTTaIL.PatternCodeRecursion

/-!
# Declaration anchors for the ledger rows of Chapters 8 to 10

The rows of the source ledger for Chapters 8, 9 and 10, and the rows of
Chapters 6, 17 and 20 that now cite the same development, name their evidence
in strings.  This module checks that the names resolve.  A rename or a removal
breaks the build instead of leaving a row pointing at nothing.

The check is that each name resolves, not that the declaration's type
discharges the obligation of the row that cites it.
-/

namespace Mettapedia.OSLF.LedgerEvidenceAuditInteraction

noncomputable section

example := @Mettapedia.GSLT.ContextMap
example := @Mettapedia.GSLT.ContextMap.Exhausting
example := @Mettapedia.GSLT.ContextMap.Exhausting.bisimilar_targetProbe_iff
example := @Mettapedia.GSLT.ContextMap.Exhausting.bisimilar_targetProbe_iff_source
example := @Mettapedia.GSLT.ContextMap.Exhausting.comp
example := @Mettapedia.GSLT.ContextMap.Exhausting.term_surjective
example := @Mettapedia.GSLT.ContextMap.Faithful
example := @Mettapedia.GSLT.ContextMap.Hosting
example := @Mettapedia.GSLT.ContextMap.Hosting.branches
example := @Mettapedia.GSLT.ContextMap.PreservesTransitions
example := @Mettapedia.GSLT.ContextMap.ReflectsEquations
example := @Mettapedia.GSLT.ContextMap.ReflectsTransitions
example := @Mettapedia.GSLT.ContextMap.apply_equivariant
example := @Mettapedia.GSLT.ContextMap.bisimilar_push_iff_of_transitions
example := @Mettapedia.GSLT.ContextMap.bisimilar_push_of_transitions
example := @Mettapedia.GSLT.ContextMap.context_plug_on_image
example := @Mettapedia.GSLT.ContextMap.exhausting_id
example := @Mettapedia.GSLT.ContextMap.faithful_iff_reflectsEquations
example := @Mettapedia.GSLT.ContextMap.hosting_iff
example := @Mettapedia.GSLT.ContextMap.targetProbe
example := @Mettapedia.GSLT.ContextMap.traceEquivalent_push_iff_of_transitions
example := @Mettapedia.GSLT.ContextMorphism
example := @Mettapedia.GSLT.ContextMap.constant
example := @Mettapedia.GSLT.ContextMap.constant_not_hosting
example := @Mettapedia.GSLT.ContextMorphism.ofTransitions
example := @Mettapedia.GSLT.ContextMorphism.preserves_full
example := @Mettapedia.GSLT.ContextMorphism.preserves_targetProbe
example := @Mettapedia.GSLT.ContextTheory
example := @Mettapedia.GSLT.ContextTheory.Embeds
example := @Mettapedia.GSLT.ContextTheory.Probe
example := @Mettapedia.GSLT.ContextTheory.Probe.Bisimilar
example := @Mettapedia.GSLT.ContextTheory.Probe.Bisimilar.restrict
example := @Mettapedia.GSLT.ContextTheory.Probe.Bisimilar.traceEquivalent
example := @Mettapedia.GSLT.ContextTheory.Probe.HasTrace
example := @Mettapedia.GSLT.ContextTheory.Probe.Path
example := @Mettapedia.GSLT.ContextTheory.Probe.TraceEquivalent
example := @Mettapedia.GSLT.ContextTheory.TraceEmbeds
example := @Mettapedia.GSLT.ContextTheory.Transition
example := @Mettapedia.GSLT.ContextTheory.bisimilar_toGSLT
example := @Mettapedia.GSLT.ContextTheory.constant_fill_equiv
example := @Mettapedia.GSLT.ContextTheory.embeds_and_traceEmbeds_of_hosting
example := @Mettapedia.GSLT.ContextTheory.embeds_refl
example := @Mettapedia.GSLT.ContextTheory.embeds_trans
example := @Mettapedia.GSLT.ContextTheory.endoProbe
example := @Mettapedia.GSLT.ContextTheory.endoProbe_bisimilar_iff_relEquiv
example := @Mettapedia.GSLT.ContextTheory.fill_plug_plug
example := @Mettapedia.GSLT.ContextTheory.fullProbe
example := @Mettapedia.GSLT.ContextTheory.fullProbe_closed
example := @Mettapedia.GSLT.ContextTheory.reductionProbe
example := @Mettapedia.GSLT.ContextTheory.reductionProbe_bisimilar_iff
example := @Mettapedia.GSLT.ContextTheory.reductionProbe_traceEquivalent_iff
example := @Mettapedia.GSLT.ContextTheory.traceEmbeds_refl
example := @Mettapedia.GSLT.ContextTheory.traceEmbeds_trans
example := @Mettapedia.GSLT.GSLT.bisimilar_map_of_zigzag
example := @Mettapedia.GSLT.GSLT.nonempty_hom
example := @Mettapedia.GSLT.GSLT.nonempty_hom_both
example := @Mettapedia.GSLT.LanguageDef.AdmitsInteractivePresentation
example := @Mettapedia.GSLT.LanguageDef.BagNormalForm.bagCanonicalSection
example := @Mettapedia.GSLT.LanguageDef.BagNormalForm.bagCanonicalSection_effective
example := @Mettapedia.GSLT.LanguageDef.BagNormalForm.normalFormCode_primrec
example := @Mettapedia.GSLT.LanguageDef.CIGSLT
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.Morphism.canonicalKeyMap_eq_of_underlying_eq
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.collapse_has_no_lift
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.contractum_head_ne_introductions
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.deep_not_underlying
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.forget
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.forgetUpToTheoryMap
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.forgetUpToTheoryMap_faithful
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.forget_not_essSurj
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.forget_not_faithful
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.forget_not_full
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.lambdaRenamedIdentity_over_identity
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.successor_not_underlying
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.toContinuedPresentation
example := @Mettapedia.GSLT.LanguageDef.CIGSLT.witnesses_outside_essImage
example := @Mettapedia.GSLT.LanguageDef.ComputableCanonicalSection
example := @Mettapedia.GSLT.LanguageDef.ComputableCanonicalSection.Effective
example := @Mettapedia.GSLT.LanguageDef.ComputableCanonicalSection.Effective.computablePred
example := @Mettapedia.GSLT.LanguageDef.ComputableCanonicalSection.ofChoice
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.Branching.early_late_traceEquivalent
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.Branching.traceEquivalent_not_bisimilar
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.EquationTransport.addCommutativity_preservesEquations
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.EquationTransport.collection_unit_metadata_required
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.LongerRun.lengthen_not_reflectsTransitions
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.LongerRun.morphism_need_not_preserve_traces
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.collapseMorphism
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.collapse_not_exhausting
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.collapse_not_hosting
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.constantToCCS
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.constantToCCS_not_hosting
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.constant_does_not_reflect
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.constants_bisimilar
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.faithfulness_does_not_reflect
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.hosting_exhausting_separated
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.images_not_bisimilar
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.images_not_bisimilar_over_image
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.images_not_bisimilar_targetProbe
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.ofIGSLTMorphism
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.ofReflectingIGSLTMorphism
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.over_observation
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.reduction_bisimilarity_insufficient
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.swapMorphism
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.swap_bisimilar_iff
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.swap_hosting_exhausting
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.swap_moves_a_term
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.targetProbe_sees_more
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.testLabel
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.toMarking
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.toMarking_not_contextMorphism
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.toProbingMorphism
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.toProbing_hosting
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.toProbing_not_exhausting
example := @Mettapedia.GSLT.LanguageDef.Contexts.Inverse.embeds
example := @Mettapedia.GSLT.LanguageDef.Contexts.Inverse.exhausting
example := @Mettapedia.GSLT.LanguageDef.Contexts.Inverse.hosting
example := @Mettapedia.GSLT.LanguageDef.Contexts.Inverse.traceEmbeds
example := @Mettapedia.GSLT.LanguageDef.Contexts.Term.map_fill
example := @Mettapedia.GSLT.LanguageDef.Contexts.contextTheory
example := @Mettapedia.GSLT.LanguageDef.Contexts.exists_oneHole_of_label
example := @Mettapedia.GSLT.LanguageDef.Contexts.gslt_bisimilar_iff
example := @Mettapedia.GSLT.LanguageDef.Contexts.labelOfOccurrence
example := @Mettapedia.GSLT.LanguageDef.Contexts.presentedBisimilar_of_fullProbe
example := @Mettapedia.GSLT.LanguageDef.Contexts.preservesEquations_of_fixesUnits
example := @Mettapedia.GSLT.LanguageDef.Contexts.preservesSteps_of_fixesUnits
example := @Mettapedia.GSLT.LanguageDef.Contexts.structuralContextMorphism
example := @Mettapedia.GSLT.LanguageDef.Contexts.structuralContextMorphism_of_reflects
example := @Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan
example := @Mettapedia.GSLT.LanguageDef.ContinuationRetypingPlan.contractum_head_ne_introductions
example := @Mettapedia.GSLT.LanguageDef.ContinuedPresentation
example := @Mettapedia.GSLT.LanguageDef.ContractionSchema.program_released_of_mode_ne_binding
example := @Mettapedia.GSLT.LanguageDef.EquationHeadsAvoid
example := @Mettapedia.GSLT.LanguageDef.EquationSimulation.equationContextStep_map_of_structuralMorphism
example := @Mettapedia.GSLT.LanguageDef.HeterogeneousCutReading
example := @Mettapedia.GSLT.LanguageDef.HeterogeneousCutReading.contractum_reads_environment
example := @Mettapedia.GSLT.LanguageDef.HeterogeneousCutReading.operands_not_both_of_sort
example := @Mettapedia.GSLT.LanguageDef.HeterogeneousCutReading.rule_not_interaction
example := @Mettapedia.GSLT.LanguageDef.IGSLT
example := @Mettapedia.GSLT.LanguageDef.IGSLT.Morphism
example := @Mettapedia.GSLT.LanguageDef.IGSLT.computablePred_of_iso
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.ambient_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.calculatorRewriting_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.calculator_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.ccs_contact_laws
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.ccs_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.interactionCategory_silent_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.interactionCategory_visible_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.lambda_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.migration_spectrum
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.piSync_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.pi_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.rhoSync_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.rho_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.transducer_forced_reading
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.transducer_row
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.turing_row
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.ac_changes_adjacency
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.assoc_changes_adjacency
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.bareContinued
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.bareContinued_forget
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.collapse
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.collapse_forges_contact
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.collapse_identifies
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.collapse_ne_id
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.contactWith
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.free_position_invariant
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.idem_forges_contact
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.inclusion_not_semantic
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact.unit_forges_contact
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.contextualOnly_no_step
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.contextualOnly_not_interactive
example := @Mettapedia.GSLT.LanguageDef.InteractionCutPresentation
example := @Mettapedia.GSLT.LanguageDef.InteractionCutPresentation.migrationMode
example := @Mettapedia.GSLT.LanguageDef.InteractionCutPresentation.operands_of_binary_left
example := @Mettapedia.GSLT.LanguageDef.InteractivePresentation
example := @Mettapedia.GSLT.LanguageDef.InteractivePresentation.RigidContact
example := @Mettapedia.GSLT.LanguageDef.InteractivePresentation.not_everyRuleIsCut_of_heterogeneousReading
example := @Mettapedia.GSLT.LanguageDef.InteractivePresentation.observed_isInteractive
example := @Mettapedia.GSLT.LanguageDef.InteractivePresentation.position_invariant
example := @Mettapedia.GSLT.LanguageDef.IsBaseRewrite
example := @Mettapedia.GSLT.LanguageDef.IsContinued
example := @Mettapedia.GSLT.LanguageDef.IsInteractive
example := @Mettapedia.GSLT.LanguageDef.MigrationMode
example := @Mettapedia.GSLT.LanguageDef.Reactive
example := @Mettapedia.GSLT.LanguageDef.Splitting
example := @Mettapedia.GSLT.LanguageDef.Splitting.ExposesRedex
example := @Mettapedia.GSLT.LanguageDef.Splitting.Fires
example := @Mettapedia.GSLT.LanguageDef.Splitting.FiresTo
example := @Mettapedia.GSLT.LanguageDef.Splitting.context_mem_zippersAt
example := @Mettapedia.GSLT.LanguageDef.Splitting.headed_of_exposesRedex
example := @Mettapedia.GSLT.LanguageDef.Splitting.ofZipper
example := @Mettapedia.GSLT.LanguageDef.WellSorted.TypedAt.map
example := @Mettapedia.GSLT.LanguageDef.ambient_isEffectivelyContinued
example := @Mettapedia.GSLT.LanguageDef.ambient_step_iff_exists_firesTo
example := @Mettapedia.GSLT.LanguageDef.bare_isContinued
example := @Mettapedia.GSLT.LanguageDef.bare_isEffectivelyContinued
example := @Mettapedia.GSLT.LanguageDef.ccs_isEffectivelyContinued
example := @Mettapedia.GSLT.LanguageDef.ccs_sections_differ
example := @Mettapedia.GSLT.LanguageDef.ccs_tracked_codes
example := @Mettapedia.GSLT.LanguageDef.ccs_two_continuedPresentations
example := @Mettapedia.GSLT.LanguageDef.ccs_two_effective_presentations
example := @Mettapedia.GSLT.LanguageDef.contended_one_cut_two_events
example := @Mettapedia.GSLT.LanguageDef.continuedPresentation_underlying_not_injective
example := @Mettapedia.GSLT.LanguageDef.deep_no_cut
example := @Mettapedia.GSLT.LanguageDef.deep_not_continued
example := @Mettapedia.GSLT.LanguageDef.effectivelyContinued_rows
example := @Mettapedia.GSLT.LanguageDef.equationEquiv_binary_iff
example := @Mettapedia.GSLT.LanguageDef.exists_subst_of_bindsInto
example := @Mettapedia.GSLT.LanguageDef.fill_injective
example := @Mettapedia.GSLT.LanguageDef.guarded_exposed_not_available
example := @Mettapedia.GSLT.LanguageDef.handshakeFirst
example := @Mettapedia.GSLT.LanguageDef.handshakeRoot_fires
example := @Mettapedia.GSLT.LanguageDef.handshake_fires_iff
example := @Mettapedia.GSLT.LanguageDef.lambdaCalc_isInteractive
example := @Mettapedia.GSLT.LanguageDef.lambdaCanonicalSection_effective
example := @Mettapedia.GSLT.LanguageDef.lambda_at_both_levels
example := @Mettapedia.GSLT.LanguageDef.lambda_isContinued
example := @Mettapedia.GSLT.LanguageDef.lambda_isEffectivelyContinued
example := @Mettapedia.GSLT.LanguageDef.lambda_migrationMode
example := @Mettapedia.GSLT.LanguageDef.lambda_residual_depends_on_argument
example := @Mettapedia.GSLT.LanguageDef.lambda_section_unique
example := @Mettapedia.GSLT.LanguageDef.lambda_surface_structural
example := @Mettapedia.GSLT.LanguageDef.mapPattern_ne_of_shape_ne
example := @Mettapedia.GSLT.LanguageDef.mettaCalc_no_interactionCut
example := @Mettapedia.GSLT.LanguageDef.not_admitsInteractivePresentation_iff
example := @Mettapedia.GSLT.LanguageDef.isEmpty_retypingPlan_of_contractum_headed_by_program
example := @Mettapedia.GSLT.LanguageDef.not_step_of_rewrites_ask_reduction
example := @Mettapedia.GSLT.LanguageDef.observerExtension_baseRewritesHeaded
example := @Mettapedia.GSLT.LanguageDef.observerExtension_not_everyRuleIsCut
example := @Mettapedia.GSLT.LanguageDef.openingInsideContent_firesTo
example := @Mettapedia.GSLT.LanguageDef.patternShape_mapPattern
example := @Mettapedia.GSLT.LanguageDef.piSync_isEffectivelyContinued
example := @Mettapedia.GSLT.LanguageDef.pi_isEffectivelyContinued
example := @Mettapedia.GSLT.LanguageDef.rhoCalc_isInteractive
example := @Mettapedia.GSLT.LanguageDef.rho_binds_through_substitution
example := @Mettapedia.GSLT.LanguageDef.rho_migrationMode
example := @Mettapedia.GSLT.LanguageDef.rho_pair_swaps
example := @Mettapedia.GSLT.LanguageDef.rho_parCong_not_base
example := @Mettapedia.GSLT.LanguageDef.rho_surface_nominal
example := @Mettapedia.GSLT.LanguageDef.silent_isEffectivelyContinued
example := @Mettapedia.GSLT.LanguageDef.step_iff_baseStep_in_context
example := @Mettapedia.GSLT.LanguageDef.step_iff_exists_firesTo
example := @Mettapedia.GSLT.LanguageDef.successor_legacyRetyping_isEmpty
example := @Mettapedia.GSLT.LanguageDef.table_sections_effective
example := @Mettapedia.GSLT.LanguageDef.turingMachine_second_without_first
example := @Mettapedia.GSLT.LanguageDef.visibleComposition_legacyRetyping_isEmpty
example := @Mettapedia.Languages.Calculator.calculatorRewriting_isInteractive
example := @Mettapedia.Languages.Calculator.calculatorSection
example := @Mettapedia.Languages.Calculator.calculatorSection_effective
example := @Mettapedia.Languages.Calculator.calculator_not_interactive
example := @Mettapedia.Languages.Calculator.successorCut
example := @Mettapedia.Languages.InteractionCategory.silent_migrationMode
example := @Mettapedia.Languages.InteractionCategory.visible_migrationMode
example := @Mettapedia.Languages.PartrecMachine.equivalence_not_computable
example := @Mettapedia.Languages.PartrecMachine.historyTheory_no_effective_section
example := @Mettapedia.Languages.PartrecMachine.history_not_effectivelyContinued
example := @Mettapedia.Languages.PartrecMachine.no_effective_section_of_iso
example := @Mettapedia.Languages.PartrecMachine.not_effectivelyContinued_of_iso
example := @Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.ambient_isContinued
example := @Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.dissolutionCut
example := @Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.dissolutionRetyping_wrappable
example := @Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.dissolution_migrationMode
example := @Mettapedia.Languages.ProcessCalculi.Ambient.Mobile.dissolution_none_without_location
example := @Mettapedia.Languages.ProcessCalculi.CCS.ccsCalc_isInteractive
example := @Mettapedia.Languages.ProcessCalculi.CCS.ccsCanonicalSection
example := @Mettapedia.Languages.ProcessCalculi.CCS.ccsInteractionCut
example := @Mettapedia.Languages.ProcessCalculi.CCS.ccsRetyping_wrappable
example := @Mettapedia.Languages.ProcessCalculi.CCS.ccs_isContinued
example := @Mettapedia.Languages.ProcessCalculi.CCS.ccs_migrationMode
example := @Mettapedia.Languages.ProcessCalculi.CCS.ccs_releases
example := @Mettapedia.Languages.ProcessCalculi.CCS.ccs_surface_nominal
example := @Mettapedia.Languages.ProcessCalculi.CCS.handshake_semantic_step
example := @Mettapedia.Languages.ProcessCalculi.CCS.handshake_swaps
example := @Mettapedia.Languages.ProcessCalculi.CCS.observedCCS_handshake_steps
example := @Mettapedia.Languages.ProcessCalculi.CCS.observedCCS_isInteractive
example := @Mettapedia.Languages.ProcessCalculi.CCS.observedCCS_loses_third_strength
example := @Mettapedia.Languages.ProcessCalculi.CCS.observedCCS_validate_eq_nil
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction.piInteractionCut
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction.pi_migrationMode
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.ProcessContext
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.ProcessContext.encode_comp
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.ProcessContext.encode_fill
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.congruent_sources_separated_by_image
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.contextStep_preserved_rf
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.encode_not_igsltMorphism
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.encode_not_signatureMap
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.fullEncode_nu_step_not_matched
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.listener_step_not_reflected
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.no_parameter_free_translation
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.nu_nil_not_respected
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.restricted_step_not_preserved
example := @Mettapedia.Languages.ProcessCalculi.PiCalculus.step_preserved_rf
example := @Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection.rhoCanonicalSection_effective
example := @Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.rhoSync_not_underlying
example := @Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.rhoSync_not_wrappable
example := @Mettapedia.Languages.Transducers.change_semantic_step
example := @Mettapedia.Languages.Transducers.controlReading
example := @Mettapedia.Languages.Transducers.control_dataMode
example := @Mettapedia.Languages.Transducers.emissionReading
example := @Mettapedia.Languages.Transducers.feed_operands_not_both_configurations
example := @Mettapedia.Languages.Transducers.mealy_contractum_reads_stream
example := @Mettapedia.Languages.Transducers.mealy_dataMode
example := @Mettapedia.Languages.Transducers.mealy_emitted_depends_on_symbol
example := @Mettapedia.Languages.Transducers.moore_dataMode
example := @Mettapedia.Languages.Transducers.moore_emitted_independent_of_stream
example := @Mettapedia.Languages.Transducers.parity_semantic_step
example := @Mettapedia.Languages.Transducers.transducer_no_contact
example := @Mettapedia.Languages.Transducers.transducer_not_interactive
example := @Mettapedia.Languages.TransitionSystem.Table.inclusionMorphism
example := @Mettapedia.Languages.TuringMachine.appendOne_first_step
example := @Mettapedia.Languages.TuringMachine.appendOne_semantic_step
example := @Mettapedia.Languages.TuringMachine.hostingMorphism
example := @Mettapedia.Languages.TuringMachine.hostingMorphism_hosting
example := @Mettapedia.Languages.TuringMachine.hostingMorphism_not_exhausting
example := @Mettapedia.Languages.TuringMachine.oneSortMachine
example := @Mettapedia.Languages.TuringMachine.oneSortMachine_empty_not_interactive
example := @Mettapedia.Languages.TuringMachine.oneSortMachine_isInteractive
example := @Mettapedia.Languages.TuringMachine.oneSortMachine_validate_eq_nil
example := @Mettapedia.Languages.TuringMachine.oneSort_step_iff
example := @Mettapedia.Languages.TuringMachine.presentation_versus_encoding
example := @Mettapedia.Languages.TuringMachine.run_is_not_same_sort_contact
example := @Mettapedia.Languages.TuringMachine.run_is_ordered_binary_contact
example := @Mettapedia.Languages.TuringMachine.step_iff_machineStep
example := @Mettapedia.Languages.TuringMachine.step_sorted
example := @Mettapedia.Languages.TuringMachine.turingMachine
example := @Mettapedia.Languages.TuringMachine.turingMachine_no_contact
example := @Mettapedia.Languages.TuringMachine.turingMachine_not_interactive
example := @Mettapedia.Languages.TuringMachine.turingMachine_validate_eq_nil
example := @Mettapedia.OSLF.MeTTaIL.DerivedContexts.MultiHoleContext
example := @Mettapedia.OSLF.MeTTaIL.DerivedContexts.MultiHoleContext.Linear.plug
example := @Mettapedia.OSLF.MeTTaIL.DerivedContexts.MultiHoleContext.bind_bind
example := @Mettapedia.OSLF.MeTTaIL.DerivedContexts.MultiHoleContext.exists_oneHole
example := @Mettapedia.OSLF.MeTTaIL.DerivedContexts.MultiHoleContext.fill_bind
example := @Mettapedia.OSLF.MeTTaIL.DerivedContexts.MultiHoleContext.not_linear_of_duplicate
example := @Mettapedia.OSLF.MeTTaIL.PatternCode.bottomUpCode
example := @Mettapedia.OSLF.MeTTaIL.PatternCode.bottomUpCode_patternCode
example := @Mettapedia.OSLF.MeTTaIL.PatternCode.bottomUpCode_primrec

end

end Mettapedia.OSLF.LedgerEvidenceAuditInteraction

example := @Mettapedia.GSLT.ContextMap.Hosting.bisimilar_push_iff
example := @Mettapedia.GSLT.ContextMap.Hosting.preservesTraces
example := @Mettapedia.GSLT.ContextTheory.traceEmbeds_iff_embeds
example := @Mettapedia.GSLT.ContextMap.ContextEquivOnImage
example := @Mettapedia.GSLT.ContextMap.context_resp_on_image
example := @Mettapedia.GSLT.ContextMap.preservesTransitions_iff_rewrites
example := @Mettapedia.GSLT.ContextMap.reflectsTransitions_iff_rewrites
example := @Mettapedia.GSLT.ContextMap.preservesNonemptyReduction
example := @Mettapedia.GSLT.ContextMap.atNonemptyReduction_preservesTransitions
example := @Mettapedia.GSLT.ContextMap.constant_requires_self_transition
example := @Mettapedia.GSLT.Contexts.Controls.ImageAction.identity_on_image
example := @Mettapedia.GSLT.Contexts.Controls.ImageAction.identity_not_on_target
example := @Mettapedia.GSLT.Contexts.Controls.ImageAction.identity_map_on_target
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.TransitionProfile.profiles_distinguish_cost
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.TransitionProfile.reply_no_macroStep
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.toMarking_not_hosting
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.LongerRun.lengthen_faithful
example := @Mettapedia.GSLT.LanguageDef.Contexts.Controls.LongerRun.lengthen_not_hosting
example := @Mettapedia.GSLT.LanguageDef.IGSLT.isInteractive
example := @Mettapedia.GSLT.LanguageDef.Interaction.Controls.contextualOnly_not_IGSLT
example := @Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.programAdditional_result
example := @Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.environmentAdditional_result
example := @Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff
example := @Mettapedia.GSLT.LanguageDef.ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff
example := @Mettapedia.GSLT.LanguageDef.InstanceTable.rhoSync_isContinued
example := @Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.communicationDecoration_wrappable
example := @Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous.decoration_separates_two_slots
example := @Mettapedia.Languages.InteractionCategory.decoration_separates_constructor_closure
example := @Mettapedia.Languages.InteractionCategory.visible_isContinued
example := @Mettapedia.Languages.InteractionCategory.visible_isEffectivelyContinued
