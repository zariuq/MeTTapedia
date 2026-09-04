import Mettapedia.GSLT.LanguageDef.Cost
import Mettapedia.GSLT.LanguageDef.CostRestorationRelationQuoteArm

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan
open Mettapedia.Algebra

-- ===== QuoteBoundaryDivergence =====
#check @Mettapedia.GSLT.LanguageDef.quoteBoundary_diverges
#check @Mettapedia.GSLT.LanguageDef.canonicalizeByDepths_foreignQuote_preserves_depth
#check @Mettapedia.GSLT.LanguageDef.canonicalizeByDepths_ownQuote_resets_depth
#check @Mettapedia.GSLT.LanguageDef.restorationDepth_ne_keyDepth_at_foreignQuote
#check @Mettapedia.GSLT.LanguageDef.depthDisciplines_agree_iff_same_quote_status

-- ===== ColourTagSeparation =====
#check @Mettapedia.GSLT.LanguageDef.costConstructorTag_distinct
#check @Mettapedia.GSLT.LanguageDef.costConstructorTag_length_distinct
#check @Mettapedia.GSLT.LanguageDef.costConstructorName_distinct
#check @Mettapedia.GSLT.LanguageDef.costStaticReflectivePresentationDecl_mem_profile
#check @Mettapedia.GSLT.LanguageDef.not_quoteStatusAgrees_costStatic
#check @Mettapedia.GSLT.LanguageDef.isQuoteConstructor_costStaticReflectivePresentationDecl
#check @Mettapedia.GSLT.LanguageDef.costStaticReflectivePresentationDecl_quoteConstructor_ne
#check @Mettapedia.GSLT.LanguageDef.hereditaryConstructorImage_disjoint
#check @Mettapedia.GSLT.LanguageDef.not_hereditaryConstructorImage_of_other_colour

-- ===== TwoDepthRestorationApex =====
#check @CostStaticAtomKeyCospan.TwoDepthApex
#check @CostStaticAtomKeyCospan.TwoDepthApexList
#check @CostStaticAtomKeyCospan.QuoteStatusAgrees
#check @CostStaticAtomKeyCospan.apply_depths_coincide_of_agrees
#check @CostStaticAtomKeyCospan.not_quoteStatusAgrees_of_foreignQuote
#check @CostStaticAtomKeyCospan.CommonRestorationApex.toTwoDepth
#check @CostStaticAtomKeyCospan.CommonRestorationApexList.toTwoDepth
#check @CostStaticAtomKeyCospan.twoDepthApex_foreignQuote_descends
#check @CostStaticAtomKeyCospan.twoDepthApex_ownQuote_descends
#check @CostStaticAtomKeyCospan.OrdinaryHeadCondition
#check @CostStaticAtomKeyCospan.ordinaryHeadCondition_of_agrees
#check @CostStaticAtomKeyCospan.agrees_of_ordinaryHeadCondition
#check @CostStaticAtomKeyCospan.not_ordinaryHeadCondition_of_foreignQuote
#check @CostStaticAtomKeyCospan.TwoDepthApex.refl
#check @CostStaticAtomKeyCospan.TwoDepthApex.of_eq
#check @CostStaticAtomKeyCospan.TwoDepthApex.forall_depths_of_leafAligned
#check @CostStaticAtomKeyCospan.TwoDepthApex.reindex
#check @CostStaticAtomKeyCospan.TwoDepthApex.reflList
#check @CostStaticAtomKeyCospan.TwoDepthApex.appendList
#check @CostStaticAtomKeyCospan.TwoDepthApex.parallel_swap_bvars
#check @CostStaticAtomKeyCospan.keyDepthThroughContext
#check @CostStaticAtomKeyCospan.keyDepthThroughContext_eq_restorationDepthThroughContext
#check @CostStaticAtomKeyCospan.keyDepthThroughContext_ne_restorationDepthThroughContext_at_foreignQuote
#check @CostStaticAtomKeyCospan.TwoDepthApexContext
#check @CostStaticAtomKeyCospan.TwoDepthApexContext.refl
#check @CostStaticAtomKeyCospan.TwoDepthApexContext.reindex
#check @CostStaticAtomKeyCospan.TwoDepthPermutation
#check @CostStaticAtomKeyCospan.TwoDepthPermutation.of_endpoint_perms
#check @CostStaticAtomKeyCospan.TwoDepthPermutation.of_canonical_map_perm
#check @CostStaticAtomKeyCospan.TwoDepthApex.parallel_of_permutation
#check @CostStaticAtomKeyCospan.TwoDepthApex.throughContext

-- ===== The zero-consumer quote arm =====
#check @CostStaticAtomKeyCospan.CommonRestorationApex.of_canonicalRootAligned_languageQuoteHead

-- ===== Algebra negatives =====
#check @Mettapedia.Algebra.WorkSpan.ValuedRun
#check @Mettapedia.Algebra.WorkSpan.ForgetsObservation
#check @Mettapedia.Algebra.WorkSpan.workSpan_forgets_any_separating_attribute
#check @Mettapedia.Algebra.WorkSpan.workSpan_forgets_colour
#check @Mettapedia.Algebra.WorkSpan.workSpan_forgets_declaration
#check @Mettapedia.Algebra.WorkSpan.workSpan_forgets_receipt
#check @Mettapedia.Algebra.WorkSpan.workSpan_forgets_causalOrder
#check @Mettapedia.Algebra.WorkSpan.workSpan_forgets_elaborationPath
#check @Mettapedia.Algebra.WorkSpan.work_does_not_determine_span
#check @Mettapedia.Algebra.WorkSpan.span_does_not_determine_work
#check @Mettapedia.Algebra.WorkSpan.sequential_eq_parallel_of_zero_right
#check @Mettapedia.Algebra.WorkSpan.workSpan_forgets_schedule_shape
#check @Mettapedia.Algebra.additiveAlgebra
#check @Mettapedia.Algebra.peakSequential
#check @Mettapedia.Algebra.peakParallel
#check @Mettapedia.Algebra.peakAllocation_violates_lax_interchange
#check @Mettapedia.Algebra.peakAllocation_parallel_strictly_worse
#check @Mettapedia.Algebra.parallelism_improves_span_worsens_allocation
#check @Mettapedia.Algebra.allocationRespecting_scalar_strictMono_at_unitSplit
#check @Mettapedia.Algebra.ReceiptSchema.Schema
#check @Mettapedia.Algebra.ReceiptSchema.Separates
#check @Mettapedia.Algebra.ReceiptSchema.ChecksAsEqual
#check @Mettapedia.Algebra.ReceiptSchema.checksAsEqual_iff_not_separates
#check @Mettapedia.Algebra.ReceiptSchema.omitted_attribute_undetectable
#check @Mettapedia.Algebra.ReceiptSchema.recorded_attribute_detectable
#check @Mettapedia.Algebra.ReceiptSchema.tuple_separates_of_left
#check @Mettapedia.Algebra.ReceiptSchema.tuple_separates_of_right
#check @Mettapedia.Algebra.ReceiptSchema.drop_field_monotone
#check @Mettapedia.Algebra.ReceiptSchema.dropped_field_admits_tamper
#check @Mettapedia.Algebra.OccurrenceIdentity.duplicateFrontier
#check @Mettapedia.Algebra.OccurrenceIdentity.exchange
#check @Mettapedia.Algebra.OccurrenceIdentity.exchange_ne_id
#check @Mettapedia.Algebra.OccurrenceIdentity.occurrence_correspondence_not_determined_by_values
#check @Mettapedia.Algebra.OccurrenceIdentity.value_agreement_does_not_yield_correspondence
#check @Mettapedia.Algebra.OccurrenceIdentity.injective_frontier_forces_identity

-- ===== axioms: the load-bearing ones =====
#print axioms Mettapedia.GSLT.LanguageDef.not_quoteStatusAgrees_costStatic
#print axioms Mettapedia.GSLT.LanguageDef.restorationDepth_ne_keyDepth_at_foreignQuote
#print axioms Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan.CommonRestorationApex.toTwoDepth
#print axioms Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan.TwoDepthPermutation.of_canonical_map_perm
#print axioms Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan.CommonRestorationApex.of_canonicalRootAligned_languageQuoteHead
#print axioms Mettapedia.Algebra.peakAllocation_violates_lax_interchange
#print axioms Mettapedia.Algebra.OccurrenceIdentity.occurrence_correspondence_not_determined_by_values
