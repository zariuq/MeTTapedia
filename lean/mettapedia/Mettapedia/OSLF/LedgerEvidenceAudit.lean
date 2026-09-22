import Mettapedia.OSLF.Main
import Mettapedia.OSLF.DeliverableAudit

/-!
# Declaration anchors for ledger evidence

`SourceLedger` records, for each source obligation, the construction that answers
it, the theorem that discharges it, an inhabited instance and an adversarial
control.  Those fields are strings.  `rowIntegrity` enforces that a row does not
claim a standing without filling them, but nothing checks that what they name
exists.

This module checks selected declaration anchors. A
rename or a removal breaks the build rather than leaving the ledger pointing at
something that is no longer there.

**Why the references are fully qualified.**  Several of the cited names are
ambiguous across the repository -- the rely-possibly modality and its
introduction, step and elimination lemmas each exist under three different
namespaces, on three different carriers. Shared quantifier-scheme equivalences
do not by themselves identify their operational interpretations. A
citation that gives only a bare name silently picks one.  Writing the full name
here fixes which one the ledger means, and would fail if that choice ever stopped
resolving.

These checks establish that the listed names resolve, not that each ledger
string is represented or that the declaration's type proves its cited obligation.
-/

namespace Mettapedia.OSLF.LedgerEvidenceAudit

noncomputable section

example := @Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.platform_congruence
example := @Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformLabels.rhoPlatform_observerSetting
example := @Mettapedia.OSLF.Binding.Fire
example := @Mettapedia.OSLF.Binding.FireSparse.liveCut_fires
example := @Mettapedia.OSLF.Binding.ParallelFragment.SupportedBy
example := @Mettapedia.OSLF.Binding.ParallelFragment.eq_of_countOut_eq
example := @Mettapedia.OSLF.Binding.ParallelFragment.unique_decomposition_of_disjoint_support
example := @Mettapedia.OSLF.Binding.Splitting
example := @Mettapedia.OSLF.Binding.fibreOfPosition_positionOfFibre
example := @Mettapedia.OSLF.Binding.fire_gives_a_step
example := @Mettapedia.OSLF.Binding.fire_source
example := @Mettapedia.OSLF.Binding.plug
example := @Mettapedia.OSLF.Binding.positionOfFibre_fibreOfPosition
example := @Mettapedia.OSLF.Binding.residual
example := @Mettapedia.OSLF.Formula.Adequacy.concreteSystem
example := @Mettapedia.OSLF.Formula.Adequacy.oslfEquivalent_iff_logicallyEquivalent
example := @Mettapedia.OSLF.Formula.Adequacy.toDirectional
example := @Mettapedia.GSLT.HMLFormula
example := @Mettapedia.GSLT.HMLFormula.satisfies
example := @Mettapedia.GSLT.HennessyMilner.sat_toLabeled
example := @Mettapedia.GSLT.HennessyMilner.contextBisimilar_iff_hmlEquiv
example := @Mettapedia.GSLT.HennessyMilner.ReductionBisimilarityCanary.not_hmlEquiv
example := @Mettapedia.GSLT.HennessyMilner.ReductionBisimilarityCanary.reduction_bisimilarity_insufficient
example := @Mettapedia.OSLF.Framework.EnumeratedAdequacy.contextBisimilar_iff_hmlEquiv_of_enumeration
example := @Mettapedia.OSLF.Framework.EnumeratedAdequacy.forwardEquivalent_iff_bisimilar_of_enumeration
example := @Mettapedia.OSLF.Framework.EnumeratedAdequacy.imageFiniteModulo_of_enumeration
example := @Mettapedia.OSLF.Framework.GeneratedHypercube.derivedAdmissible
example := @Mettapedia.OSLF.Framework.GeneratedHypercube.derivedCenter
example := @Mettapedia.OSLF.Framework.GeneratedHypercube.derivedPresentation
example := @Mettapedia.OSLF.Framework.GeneratedHypercubeInstances.rhoCommPaper_square_card
example := @Mettapedia.OSLF.Framework.GeneratedHypercubeInstances.rhoCommPaper_square_is_face
example := @Mettapedia.OSLF.Framework.GeneratedHypercubeInstances.rhoComm_center_card
example := @Mettapedia.OSLF.Framework.GeneratedModalFamily.mem_redexSites_iff
example := @Mettapedia.OSLF.Framework.GeneratedModality.RelyPossibly
example := @Mettapedia.OSLF.Framework.GeneratedModality.relyPossibly_elim
example := @Mettapedia.OSLF.Framework.GeneratedModality.relyPossibly_intro
example := @Mettapedia.OSLF.Framework.GeneratedModality.relyPossibly_step
example := @Mettapedia.OSLF.Framework.GeneratedScope.inScope
example := @Mettapedia.OSLF.Framework.GeneratedScope.scopeStep
example := @Mettapedia.OSLF.Framework.GeneratedScopeRho.no_selfCode_left
example := @Mettapedia.OSLF.Framework.GeneratedScopeRho.no_selfCode_right
example := @Mettapedia.OSLF.Framework.GeneratedScopeRho.quote_par_injective
example := @Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme
example := @Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.distance
example := @Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.reading
example := @Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.separatingRank
example := @Mettapedia.OSLF.Framework.LogicalMetric.cheapFirst
example := @Mettapedia.OSLF.Framework.LogicalMetric.hmlScheme
example := @Mettapedia.OSLF.Framework.TypeFormerExtension.rhoOnce_validate_eq_nil
example := @Mettapedia.OSLF.Framework.TypeFormerExtension.rhoTwice_rejected
example := @Mettapedia.OSLF.Framework.LogicalMetric.hmlScheme_distance_eq_zero_iff_bisimilar
example := @Mettapedia.OSLF.Framework.LogicalMetric.depthScheme_agreement_iff_lt_separatingRank
example := @Mettapedia.OSLF.Framework.LogicalMetric.depthScheme_classes_eq_iff_bisimilar
example := @Mettapedia.OSLF.Framework.LogicalMetric.ObservationScheme.quotientMetricSpace
example := @Mettapedia.OSLF.Framework.ModalHypercube.ModalPresentation
example := @Mettapedia.OSLF.Framework.ModalHypercube.equationalCenter
example := @Mettapedia.OSLF.Framework.ObserverBisimilarity.AgreeingFragment
example := @Mettapedia.OSLF.Framework.ObserverBisimilarity.Instance.readings_agree
example := @Mettapedia.OSLF.Framework.ObserverBisimilarity.Setting
example := @Mettapedia.OSLF.Framework.ObserverBisimilarity.restrict
example := @Mettapedia.OSLF.Framework.ObserverExtension.AdministrativeFresh
example := @Mettapedia.OSLF.Framework.ObserverExtension.Gap.inertPair_conservative
example := @Mettapedia.OSLF.Framework.ObserverExtension.Gap.inertPair_fresh
example := @Mettapedia.OSLF.Framework.ObserverExtension.Gap.inertPair_no_step
example := @Mettapedia.OSLF.Framework.ObserverExtension.ObAdmissible
example := @Mettapedia.OSLF.Framework.ObserverExtension.instrumentRules
example := @Mettapedia.OSLF.Framework.ObserverExtension.mem_terms_of_mem
example := @Mettapedia.OSLF.Framework.ObserverExtension.no_instrument_rules_for_minting
example := @Mettapedia.OSLF.Framework.ObserverExtension.no_opening_for_minting
example := @Mettapedia.OSLF.Framework.ObserverExtension.observerExtension
example := @Mettapedia.OSLF.Framework.ObserverExtension.openedRules_mono
example := @Mettapedia.OSLF.Framework.ObserverExtension.step_mono
example := @Mettapedia.OSLF.Framework.ObserverExtension.step_of_base
example := @Mettapedia.OSLF.Framework.ObserverIdempotence.authored_retained
example := @Mettapedia.OSLF.Framework.ObserverIdempotence.disjoint_second_round_is_fresh
example := @Mettapedia.OSLF.Framework.ObserverIdempotence.equations_preserved
example := @Mettapedia.OSLF.Framework.ObserverIdempotence.rewriteAt_eq_of_second_extension
example := @Mettapedia.OSLF.Framework.ObserverReconstruction.IsInstrumentBisimulation
example := @Mettapedia.OSLF.Framework.ObserverReconstruction.ReadableByKit
example := @Mettapedia.OSLF.Framework.ObserverReconstruction.argument_agreement
example := @Mettapedia.OSLF.Framework.ObserverExtension.openingRule_match_iff
example := @Mettapedia.OSLF.Framework.ObserverReconstruction.projection_response
example := @Mettapedia.OSLF.Framework.ObserverReconstruction.reads_head_iff
example := @Mettapedia.OSLF.Framework.ObserverReconstruction.reconstruction
example := @Mettapedia.OSLF.Framework.RedexPosition.Position
example := @Mettapedia.OSLF.Framework.RedexPosition.children
example := @Mettapedia.OSLF.Framework.RedexPosition.hiddenVars
example := @Mettapedia.OSLF.Framework.RedexPosition.plug
example := @Mettapedia.OSLF.Framework.RedexPosition.positions
example := @Mettapedia.OSLF.Framework.RedexPosition.relyVars
example := @Mettapedia.OSLF.Framework.RedexPosition.slotCount
example := @Mettapedia.OSLF.Framework.RedexPosition.subtermAt
example := @Mettapedia.OSLF.Framework.ScopeStratum.generatorLength
example := @Mettapedia.OSLF.Framework.ScopeStratum.stratum
example := @Mettapedia.OSLF.Framework.ScopeStratum.stratum_tower
example := @Mettapedia.OSLF.Framework.ScopeStratum.towerBody
example := @Mettapedia.OSLF.Framework.ScopeStratum.two_pow_le_sizeOf_towerBody
example := @Mettapedia.OSLF.Framework.TypeFormerExtension.rhoCalc_strictly_extended
example := @Mettapedia.OSLF.Framework.TypeFormerExtension.typeFormerExtension
example := @Mettapedia.OSLF.StructuralModal.AdmissibleEquations.Admissible

end

end Mettapedia.OSLF.LedgerEvidenceAudit
