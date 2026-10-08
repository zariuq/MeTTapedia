import Mettapedia.OSLF.Framework.InstrumentCutKitEquationComparison
import Mettapedia.OSLF.Framework.InstrumentCutKitControls

/-!
# Complete unit-quotient firing and all-label comparison controls

The independently supplied padded and unpadded constructor terms have
different raw roots. Their actual equation classes induce the same complete
agent and retain the supplied Ask result's two different children. Distinct
hole positions and swapped output children remain distinguishable. The
proper-future separator persists in the actual supported quotient category.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutKitEquationControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.OSLF.SortedConstructors.Padding
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RedexRelativeCongruence
open InstrumentCutContexts InstrumentCutContextControls InstrumentCutKitControls

local instance instrumentCutKitEquationControlsQuiver : Quiver (Srt Symbol arity) := frameQuiver sig

def quotientSource (opened : InstrumentObservations.Policy Symbol)
    (source : InstrumentObservations.Tree Symbol arity) :
    equationKitOrigin arity opened ⟶ equationKitInterface arity opened .base :=
  equationKitValue arity (classOf (embed sig .base (embedSource arity source))) (by
    change KitSupported arity opened (Padding.normalize sig .base (embed sig .base (embedSource arity source)))
    rw [normalize_embed]
    exact embedSource_kitSupported arity opened source)

theorem quotientSource_readout (opened : InstrumentObservations.Policy Symbol)
    (source : InstrumentObservations.Tree Symbol arity) :
    (kitNormalization arity opened).map (quotientSource opened source) = kitSource arity opened source := by
  apply Subtype.ext
  change termArrow sig (Padding.normalize sig .base (embed sig .base (embedSource arity source))) = _
  rw [normalize_embed]
  rfl

theorem ask_body_source_readout : original arity Symbol.cut arguments = embedSource arity properRule.redex := by
  change original arity Symbol.cut arguments =
    original arity Symbol.cut (fun position => embedSource arity ((![sourceLeaf false, sourceLeaf true]) position))
  apply congrArg (original arity Symbol.cut)
  funext position
  fin_cases position
  · exact (source_leaf_readout false).symm
  · exact (source_leaf_readout true).symm

theorem padded_body_source_readout : Padding.normalize sig .base paddedBody = embedSource arity properRule.redex := by
  change Padding.normalize sig .base (pad sig .base (embed sig .base (original arity Symbol.cut arguments))) = _
  rw [normalize_pad, normalize_embed]
  exact ask_body_source_readout

theorem raw_body_source_readout : Padding.normalize sig .base rawBody = embedSource arity properRule.redex := by
  change Padding.normalize sig .base (embed sig .base (original arity Symbol.cut arguments)) = _
  rw [normalize_embed]
  exact ask_body_source_readout

theorem raw_padded_agent_supported : KitSupported arity cutKit (Padding.value sig .base (classOf paddedBody)) := by
  change KitSupported arity cutKit (Padding.normalize sig .base paddedBody)
  rw [padded_body_source_readout]
  exact embedSource_kitSupported arity cutKit properRule.redex

def paddedAgent : equationKitOrigin arity cutKit ⟶ equationKitInterface arity cutKit .base :=
  equationKitValue arity (classOf paddedBody) raw_padded_agent_supported

def unpaddedAgent : equationKitOrigin arity cutKit ⟶ equationKitInterface arity cutKit .base :=
  equationKitValue arity (classOf rawBody) (by
    change KitSupported arity cutKit (Padding.normalize sig .base rawBody)
    rw [raw_body_source_readout]
    exact embedSource_kitSupported arity cutKit properRule.redex)

theorem padded_agent_readout :
    (kitNormalization arity cutKit).map paddedAgent = kitSource arity cutKit properRule.redex := by
  apply Subtype.ext
  exact congrArg (termArrow sig) padded_body_source_readout

theorem unpadded_agent_readout :
    (kitNormalization arity cutKit).map unpaddedAgent = kitSource arity cutKit properRule.redex := by
  apply Subtype.ext
  exact congrArg (termArrow sig) raw_body_source_readout

theorem padded_agents_equal : paddedAgent = unpaddedAgent := by
  apply Subtype.ext
  exact congrArg (classTermArrow sig .base) padding_same_authored_class

theorem different_raw_roots_same_complete_agent : paddedBody ≠ rawBody ∧ paddedAgent = unpaddedAgent :=
  ⟨raw_padding_changes_root, padded_agents_equal⟩

def quotientAsk : equationKitInterface arity cutKit .base ⟶
    equationKitInterface arity cutKit (.arguments Symbol.cut) :=
  equationKitContext arity (contextClassOf (embedContext sig .base (probeContext arity (.ask Symbol.cut)))) (by
    change KitContext arity cutKit (normalizeContext sig .base (embedContext sig .base (probeContext arity (.ask Symbol.cut))))
    rw [normalize_embedContext]
    exact .cons (.nil _) (kit_probeFrame_supported arity cutKit (.ask Symbol.cut) (Or.inr rfl)))

theorem quotientAsk_readout : (kitNormalization arity cutKit).map quotientAsk =
    kitProbeContext arity cutKit (.ask Symbol.cut) (Or.inr rfl) := by
  apply Subtype.ext
  change contextArrow sig (normalizeContext sig .base (embedContext sig .base (probeContext arity (.ask Symbol.cut)))) = _
  rw [normalize_embedContext]
  rfl

theorem arguments_supported (position : Fin 2) : KitSupported arity cutKit (arguments position) := by
  fin_cases position
  · change KitSupported arity cutKit (leaf false)
    exact source_leaf_readout false ▸ embedSource_kitSupported arity cutKit (sourceLeaf false)
  · change KitSupported arity cutKit (leaf true)
    exact source_leaf_readout true ▸ embedSource_kitSupported arity cutKit (sourceLeaf true)

def quotientOutput : equationKitOrigin arity cutKit ⟶
    equationKitInterface arity cutKit (.arguments Symbol.cut) :=
  equationKitValue arity (classOf rawOutput) (by
    change KitSupported arity cutKit (Padding.normalize sig .base (embed sig .base (bundle arity Symbol.cut arguments)))
    rw [normalize_embed]
    exact kitSupported_bundle arity cutKit Symbol.cut (Or.inr rfl) arguments arguments_supported)

theorem quotientOutput_readout : (kitNormalization arity cutKit).map quotientOutput =
    kitValue arity askInstance.output
      (kitSupported_bundle arity cutKit Symbol.cut (Or.inr rfl) arguments arguments_supported) := by
  apply Subtype.ext
  change termArrow sig (Padding.normalize sig .base (embed sig .base (bundle arity Symbol.cut arguments))) =
    termArrow sig (bundle arity Symbol.cut arguments)
  rw [normalize_embed]

theorem supplied_receipt_induces_padded_ask
    (receipt : KitFiringReceipt arity Bool cutKit (.ask Symbol.cut) askInstance.body askInstance.output) :
    ActIPO (equationKitRules arity Bool cutKit (fun rule => rule = properRule)) quotientAsk paddedAgent quotientOutput := by
  apply (equationKit_step_iff arity Bool cutKit _ quotientAsk paddedAgent quotientOutput).mpr
  rw [quotientAsk_readout, padded_agent_readout, quotientOutput_readout]
  apply (kit_category_step_iff arity Bool cutKit _ _ _ _).mpr
  change ActIPO (kitRules arity Bool cutKit (fun rule => rule = properRule))
    (contextArrow sig (probeContext arity (.ask Symbol.cut)))
    (termArrow sig (embedSource arity properRule.redex)) (termArrow sig (bundle arity Symbol.cut arguments))
  rw [← ask_body_source_readout]
  exact receipt.step arity _

theorem padded_ask_actualIPO :
    ActIPO (equationKitRules arity Bool cutKit (fun rule => rule = properRule)) quotientAsk paddedAgent quotientOutput :=
  supplied_receipt_induces_padded_ask firstKitReceipt

theorem different_origins_induce_the_complete_padded_firing :
    firstKitReceipt ≠ secondKitReceipt ∧
      ActIPO (equationKitRules arity Bool cutKit (fun rule => rule = properRule)) quotientAsk paddedAgent quotientOutput :=
  ⟨duplicate_kit_origins_are_retained, supplied_receipt_induces_padded_ask secondKitReceipt⟩

theorem supplied_result_retains_both_children :
    Padding.value sig .base (classOf rawOutput) = bundle arity Symbol.cut arguments ∧
      arguments 0 = leaf false ∧ arguments 1 = leaf true := by
  refine ⟨?_, rfl, rfl⟩
  change Padding.normalize sig .base (embed sig .base (bundle arity Symbol.cut arguments)) = _
  rw [normalize_embed]

theorem raw_output_bundle_readout : rawOutput = rawBundle arity Symbol.cut
    ![embed sig .base (leaf false), embed sig .base (leaf true)] := by
  apply congrArg (Term.node (signature := extended sig .base) (Sum.inl (Constructor.arguments Symbol.cut)))
  funext position
  fin_cases position <;> rfl

theorem swapped_children_are_different_quotient_results :
    classOf rawOutput ≠ classOf (rawBundle arity Symbol.cut
      ![embed sig .base (leaf true), embed sig .base (leaf false)]) := by
  intro same
  rw [raw_output_bundle_readout] at same
  exact swapped_children_fail_equation_bundle_match ((classOf_eq_iff _ _).mp same)

theorem distinct_hole_positions_remain_distinct_classes :
    contextClassOf (embedContext sig .base leftContext) ≠ contextClassOf (embedContext sig .base rightContext) := by
  intro same
  have readout := congrArg (contextValue sig .base) same
  change normalizeContext sig .base (embedContext sig .base leftContext) =
    normalizeContext sig .base (embedContext sig .base rightContext) at readout
  rw [normalize_embedContext, normalize_embedContext] at readout
  exact contexts_differ readout

theorem padded_complete_source_reconstruction (other : InstrumentObservations.Tree Symbol arity) :
    IPOBisimilar (equationKitRules arity Bool cutKit (fun rule => rule = properRule))
      paddedAgent (quotientSource cutKit other) ↔ properRule.redex = other :=
  equationKit_fullyOpened_iff arity Bool cutKit _ paddedAgent (quotientSource cutKit other)
    properRule.redex other padded_agent_readout (quotientSource_readout cutKit other)
    (every_source_fully_opened properRule.redex)

theorem padded_and_unpadded_all_label_bisimilar :
    IPOBisimilar (equationKitRules arity Bool cutKit (fun rule => rule = properRule)) paddedAgent unpaddedAgent := by
  rw [padded_agents_equal]
  exact ipoBisimilar_refl (equationKitRules arity Bool cutKit (fun rule => rule = properRule)) unpaddedAgent

theorem partial_view_converse_still_fails_on_equation_category :
    InstrumentObservations.view falseLeafKit properRule.redex =
        InstrumentObservations.view falseLeafKit (sourceLeaf true) ∧
      ¬ IPOBisimilar (equationKitRules arity Bool falseLeafKit (fun rule => rule = properRule))
        (quotientSource falseLeafKit properRule.redex) (quotientSource falseLeafKit (sourceLeaf true)) := by
  refine ⟨partial_views_same_before_proper_firing, ?_⟩
  intro related
  have normalRelated := (equationKit_bisimilar_iff arity Bool falseLeafKit _ _ _).mp related
  rw [quotientSource_readout, quotientSource_readout] at normalRelated
  exact partial_view_kernel_is_not_full_bisimulation normalRelated

end Mettapedia.OSLF.Framework.InstrumentCutKitEquationControls
