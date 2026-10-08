import Mettapedia.OSLF.Framework.SortedCommutativeSourceFiringComparison
import Mettapedia.OSLF.Framework.SortedCommutativeSourceControls

/-!
# Complete source RPO, firing and hereditary-support controls

Distinct source hole positions share an actual ground filling, and their
whole source RPO is still a RPO against every extended competitor. A genuine
nonidentity constructor label gives a source rule firing whose complete
changed tuple and two independently supplied origins survive the inclusion.

The ask-then-get context is outside the source image. Auxiliary support is
also detected below an ordinary root and in a context sibling. Such a full
result cannot arise from a mapped source rule under a source label; actual
administrative observer firings remain outside this restricted comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeSourceComparisonControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout Mettapedia.GSLT.RedexRelativeCongruence
open SortedCommutativeInstruments Support
open SortedCommutativeInstrumentControls (Symbol arity)
open SortedCommutativeSourceControls (low high firstHole secondHole extraContext)
open scoped BigOperators

abbrev sourceInterface : Source.SourceCategory (arity := arity) := .interface (ULift.up ())

def agent : (.origin : Source.SourceCategory (arity := arity)) ⟶ sourceInterface := RawArrow.value (classOf low)
def firstLabel : sourceInterface ⟶ sourceInterface := RawArrow.context (contextClassOf firstHole)
def secondLabel : sourceInterface ⟶ sourceInterface := RawArrow.context (contextClassOf secondHole)

theorem literal_source_position_labels_differ : firstLabel ≠ secondLabel := by
  intro same
  exact SortedCommutativeSourceControls.original_positions_remain_distinct
    (Quotient.exact (RawArrow.context.inj same))

theorem full_ground_position_collision : agent ≫ firstLabel = agent ≫ secondLabel :=
  congrArg RawArrow.value (congrArg classOf SortedCommutativeSourceControls.source_position_collision)

theorem complete_collision_rpo_in_both_categories :
    ∃ before : Candidate agent agent firstLabel secondLabel,
      IsRelativePushout before ∧ IsRelativePushout (mapCandidate Source.inclusion before) := by
  obtain ⟨before, universal⟩ := Source.source_redex_relativePushouts agent agent
    sourceInterface firstLabel secondLabel full_ground_position_collision
  exact ⟨before, universal, Source.preserves_relativePushout before universal⟩

theorem every_extended_collision_competitor_reconstructs
    (candidate : Candidate (Source.inclusion.map agent) (Source.inclusion.map agent)
      (Source.inclusion.map firstLabel) (Source.inclusion.map secondLabel)) :
    ∃ before : Candidate agent agent firstLabel secondLabel,
      mapCandidate Source.inclusion before = candidate := Source.mapped_candidate_reconstruction candidate

theorem collision_competitor_keeps_all_arrows
    (candidate : Candidate (Source.inclusion.map agent) (Source.inclusion.map agent)
      (Source.inclusion.map firstLabel) (Source.inclusion.map secondLabel)) :
    arrowObserverCount candidate.inl = 0 ∧ arrowObserverCount candidate.inr = 0 ∧
      arrowObserverCount candidate.down = 0 := Source.mapped_candidate_support candidate

def interactionContext : Source.Context (arity := arity) := firstHole.comp (.left rfl .hole high)
def interactionLabel : sourceInterface ⟶ sourceInterface := RawArrow.context (contextClassOf interactionContext)

def selectedRule : ReactionRule (.origin : Source.SourceCategory (arity := arity)) where
  codomain := sourceInterface
  redex := RawArrow.value (classOf (interactionContext.fill low))
  reactum := RawArrow.value (classOf (interactionContext.fill high))

theorem reaction_has_the_actual_original_cut : selectedRule.redex =
    (RawArrow.value (classOf (.cut rfl (firstHole.fill low) high : Source.Value arity)) :
      (.origin : Source.SourceCategory (arity := arity)) ⟶ sourceInterface) := rfl

def declarations (_origin : Nat) : ReactionRule (.origin : Source.SourceCategory (arity := arity)) := selectedRule

def firing (origin : Nat) : Source.FiringEvidence (.origin : Source.SourceCategory (arity := arity)) Nat declarations where
  occurrence := origin
  sourceInterface := sourceInterface
  targetInterface := sourceInterface
  agent := agent
  label := interactionLabel
  reaction := 𝟙 sourceInterface
  square := by exact (Category.comp_id selectedRule.redex).symm
  minimal := raw_right_identity_isIPO interactionLabel (show agent ≫ interactionLabel = selectedRule.redex from rfl)

theorem genuine_source_rule_fires :
    ActIPO (fun rule => ∃ origin, declarations origin = rule) interactionLabel agent (firing 7).result :=
  (firing 7).step

theorem whole_changed_tuple_survives :
    (Source.mapFiring declarations (firing 7)).result =
      (RawArrow.value (classOf (Source.embed (interactionContext.fill high))) :
        (.origin : ContextCategory arity) ⟶ .interface .base) := by
  have resultRead : (firing 7).result = selectedRule.reactum := Category.comp_id selectedRule.reactum
  exact (Source.mapFiring_result declarations (firing 7)).trans (congrArg Source.inclusion.map resultRead)

theorem actual_selected_coordinate_changes_result : selectedRule.reactum ≠ selectedRule.redex := by
  intro same
  have inventories := congrArg inventoryQ (RawArrow.value.inj same)
  change inventoryQ (classCut (signature := Source.signature arity) (Parallel := Source.Parallel arity)
    rfl (classOf (firstHole.fill high)) (classOf high)) =
      inventoryQ (classCut (signature := Source.signature arity) (Parallel := Source.Parallel arity)
        rfl (classOf (firstHole.fill low)) (classOf high)) at inventories
  rw [inventoryQ_classCut, inventoryQ_classCut] at inventories
  have classes := inventoryQ_injective (add_right_cancel inventories)
  change classOf (Term.node (signature := Source.signature arity) (Parallel := Source.Parallel arity) Symbol.pair
    (RawContext.insert Symbol.pair 0 (fun _ _ => low) high)) =
      classOf (Term.node (signature := Source.signature arity) (Parallel := Source.Parallel arity) Symbol.pair
        (RawContext.insert Symbol.pair 0 (fun _ _ => low) low)) at classes
  have picked := (node_class_eq_iff (signature := Source.signature arity) (Parallel := Source.Parallel arity)
    Symbol.pair (RawContext.insert Symbol.pair 0 (fun _ _ => low) high)
      (RawContext.insert Symbol.pair 0 (fun _ _ => low) low)).mp classes 0
  change classOf high = classOf low at picked
  exact SortedCommutativeSourceControls.source_values_are_distinct picked.symm

theorem duplicate_declaration_origins_stay_distinct :
    Source.mapFiring declarations (firing 7) ≠ Source.mapFiring declarations (firing 8) :=
  Source.distinct_origins_keep_distinct_firings declarations (firing 7) (firing 8) (by decide)

theorem complete_firing_context_is_retained :
    (Source.mapFiring declarations (firing 7)).reaction =
      Source.inclusion.map (𝟙 sourceInterface) := Source.mapFiring_reaction declarations (firing 7)

theorem actual_source_rule_step_is_exactly_compared :
    ActIPO (fun rule => ∃ origin, declarations origin = rule) interactionLabel agent (firing 7).result ↔
      ActIPO (Source.mappedRules (fun rule => ∃ origin, declarations origin = rule))
        (Source.inclusion.map interactionLabel) (Source.inclusion.map agent)
          (Source.inclusion.map (firing 7).result) := Source.source_step_iff_mapped _ _ _ _

theorem extra_context_has_four_auxiliary_heads : contextObserverCount extraContext = 4 := by
  change contextObserverCount
    ((probeContext arity (.ask (.ordinary Symbol.pair))).comp
      (probeContext arity (.get (.ordinary Symbol.pair) 0))) = 4
  rw [contextObserverCount_comp]
  rw [contextObserverCount_probeContext, contextObserverCount_probeContext]

def auxiliaryValue : Value arity .base := extraContext.fill (Source.embed low)

theorem auxiliary_value_has_four_auxiliary_heads : observerCount auxiliaryValue = 4 := by
  rw [auxiliaryValue, contextObserverCount_fill, observerCount_embed, Nat.add_zero]
  exact extra_context_has_four_auxiliary_heads

def hiddenInOrdinaryRoot : Value arity .base :=
  Term.node (signature := signature arity) (Constructor.original Symbol.pair)
    (Fin.cases (Source.embed low) (fun _ => auxiliaryValue))

theorem ordinary_root_does_not_hide_auxiliary_support : observerCount hiddenInOrdinaryRoot = 4 := by
  change 0 + (∑ position : Fin 2, observerCount (Fin.cases (Source.embed low) (fun _ => auxiliaryValue) position)) = 4
  rw [Fin.sum_univ_two]
  change 0 + (observerCount (Source.embed low) + observerCount auxiliaryValue) = 4
  rw [observerCount_embed, auxiliary_value_has_four_auxiliary_heads]

def hiddenSiblingContext : RawContext (signature arity) (Parallel arity) .base .base :=
  RawContext.frame (signature := signature arity) (Parallel := Parallel arity)
    (Constructor.original Symbol.pair) 0 (fun _ _ => auxiliaryValue) .hole

theorem full_sibling_support_is_retained : contextObserverCount hiddenSiblingContext = 4 := by
  change 0 + (∑ other : Fin 2, if _absent : other ≠ 0 then observerCount auxiliaryValue else 0) + 0 = 4
  norm_num [siblingCount, Fin.sum_univ_two, auxiliary_value_has_four_auxiliary_heads]

theorem ordinary_root_auxiliary_value_has_no_source_preimage :
    ¬ ∃ before : Source.ValueClass arity, Source.classEmbedding before = classOf hiddenInOrdinaryRoot := by
  rintro ⟨before, same⟩
  have impossible := (classObserverCount_embedding before).symm.trans (congrArg classObserverCount same)
  change 0 = observerCount hiddenInOrdinaryRoot at impossible
  rw [ordinary_root_does_not_hide_auxiliary_support] at impossible
  omega

theorem auxiliary_result_cannot_come_from_any_source_rule
    (sourceRules : ReactionRule (.origin : Source.SourceCategory (arity := arity)) → Prop) :
    ¬ ActIPO (Source.mappedRules sourceRules) (Source.inclusion.map firstLabel) (Source.inclusion.map agent)
      (RawArrow.value (classOf auxiliaryValue)) := by
  intro step
  have pure := Source.source_step_full_target_support sourceRules agent firstLabel _ step
  change observerCount auxiliaryValue = 0 at pure
  rw [auxiliary_value_has_four_auxiliary_heads] at pure
  omega

theorem nonfull_extension_boundary_is_retained : ¬ (Source.inclusion (arity := arity)).Full :=
  SortedCommutativeSourceControls.actual_source_inclusion_is_not_full

theorem empty_origins_supply_no_firing
    (supplied : Source.FiringEvidence (.origin : Source.SourceCategory (arity := arity)) Empty
      (fun impossible => Empty.elim impossible)) : False := Empty.elim supplied.occurrence

theorem administrative_firing_is_real_but_not_pure :
    ActIPO (rules arity Nat) SortedCommutativeInstrumentControls.getSecond.label
      SortedCommutativeInstrumentControls.getSecond.agent SortedCommutativeInstrumentControls.getSecond.target ∧
      arrowObserverCount SortedCommutativeInstrumentControls.getSecond.label ≠ 0 := by
  refine ⟨SortedCommutativeInstrumentControls.getSecond.direct_step, ?_⟩
  change contextObserverCount (probeContext arity (.get .properCut 1)) ≠ 0
  rw [contextObserverCount_probeContext]
  decide

end Mettapedia.OSLF.Framework.SortedCommutativeSourceComparisonControls
