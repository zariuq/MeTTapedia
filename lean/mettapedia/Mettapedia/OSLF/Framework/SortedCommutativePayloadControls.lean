import Mettapedia.OSLF.Framework.SortedCommutativePayloadReconstruction
import Mettapedia.OSLF.Framework.SortedCommutativePayloadContextAction
import Mettapedia.OSLF.Framework.SortedCommutativeCombinedReconstructionControls

/-!
# Actual process payloads and complete administrative successors

Free-frame siblings and parallel residues occupy genuine typed process
positions. The same greatest fixed point that compares successor states
also rejects unequal source payloads at an identical frame shape. AC1
equations preserve payload readings without collapsing ordered ask targets
or independently supplied origins. Unit-rule get competition remains real.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativePayloadControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedCommutativeInstruments Support PayloadLabels
open SortedCommutativeInstrumentControls (Symbol arity ordered reversed firstAsk secondAsk)
open SortedCommutativeSourceControls (low high sourceCut swappedCut)

abbrev sourceRules := SortedCommutativeCombinedReconstructionControls.sourceRules
abbrev system := firingSystem (combinedSourceRules sourceRules Nat)

def pairShape : Skeleton (arity := arity) .base .base :=
  .frame (.original Symbol.pair) 0 .hole

def siblingSlot : Skeleton.Slot pairShape := .inl ⟨1, by decide, rfl⟩

def siblingLabel (supplied : ValueClass arity .base) : Label arity .base .base :=
  frameLabel (.original Symbol.pair) 0 (fun _ _ => supplied) (holeLabel .base)

theorem complete_sibling_readout (supplied : ValueClass arity .base) :
    (siblingLabel supplied).payload siblingSlot = supplied := rfl

theorem actual_context_readout (supplied : ValueClass arity .base) :
    readLabel (siblingLabel supplied) =
      Mettapedia.CategoryTheory.MixedResidue.Context.frame 0
        (Frame.slot (signature := signature arity) (Parallel := Parallel arity)
          (.original Symbol.pair) 0 (fun _ _ => supplied))
        (Mettapedia.CategoryTheory.MixedResidue.Context.parallel 0) :=
  read_frameLabel (.original Symbol.pair) 0 (fun _ _ => supplied) (holeLabel .base)

private theorem sibling_related_iff (first second : ValueClass arity .base) :
    Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates system.Bisimilar
      (siblingLabel first) (siblingLabel second) ↔ system.Bisimilar .base first second := by
  constructor
  · intro related
    cases related with
    | mk shape left right positions => exact positions siblingSlot
  · intro related
    refine Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates.mk
      (vocabulary := vocabulary arity) (State := ValueClass arity)
      (relation := system.Bisimilar) pairShape
      (siblingLabel first).payload (siblingLabel second).payload ?_
    intro slot
    change {other : Fin 2 // other ≠ 0 ∧
      processSort ((signature arity).input (.original Symbol.pair) other) = true} ⊕ PEmpty at slot
    rcases slot with other | absent
    · exact related
    · exact PEmpty.elim absent

theorem same_shape_does_not_replace_payload_matching :
    (siblingLabel (Source.classEmbedding (classOf low))).skeleton =
        (siblingLabel (Source.classEmbedding (classOf high))).skeleton ∧
      ¬Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates system.Bisimilar
        (siblingLabel (Source.classEmbedding (classOf low)))
        (siblingLabel (Source.classEmbedding (classOf high))) := by
  refine ⟨rfl, ?_⟩
  intro related
  have states := (sibling_related_iff _ _).mp related
  exact SortedCommutativeSourceControls.source_values_are_distinct
    ((bisimilar_iff_source_equal sourceRules (Origins := Nat) ⟨7⟩ _ _).mp states)

theorem actual_ac1_payload_equation_is_respected :
    Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates system.Bisimilar
      (siblingLabel (Source.classEmbedding (classOf sourceCut)))
      (siblingLabel (Source.classEmbedding (classOf swappedCut))) := by
  apply (sibling_related_iff _ _).mpr
  exact (raw_bisimilar_iff_source_equation sourceRules (Origins := Nat) ⟨8⟩ _ _).mpr
    SortedCommutativeSourceControls.original_commutative_equation

def residualLabel (supplied : ValueClass arity .base) : Label arity .base .base :=
  parallelLabel rfl supplied (holeLabel .base)

theorem complete_parallel_payload_readout (supplied : ValueClass arity .base) :
    (residualLabel supplied).payload (.inl PUnit.unit) = supplied ∧
      readLabel (residualLabel supplied) =
        (Mettapedia.CategoryTheory.MixedResidue.Context.parallel (valueResidue rfl supplied) :
          MixedContext (signature arity) (Parallel arity) .base .base) := by
  refine ⟨rfl, ?_⟩
  change Mettapedia.CategoryTheory.MixedResidue.Context.parallel
    (valueResidue rfl supplied + 0) = _
  rw [add_zero]

theorem parallel_payload_keeps_multiplicity :
    residualLabel (classOf (.cut rfl (Source.embed low) (Source.embed low))) ≠
      residualLabel (Source.classEmbedding (classOf low)) := by
  intro same
  have readings := congrArg readLabel same
  rw [(complete_parallel_payload_readout _).2, (complete_parallel_payload_readout _).2] at readings
  have bags := Mettapedia.CategoryTheory.MixedResidue.Context.parallel.inj readings
  have payloads := congrArg (residueValue (arity := arity) (sort := .base) rfl) bags
  rw [residueValue_valueResidue, residueValue_valueResidue] at payloads
  change classOf (.cut (signature := signature arity) (Parallel := Parallel arity)
    rfl (Source.embed low) (Source.embed low)) =
    classOf (Source.embed low) at payloads
  have counts := congrArg (fun value => (inventoryQ value).card) payloads
  change (inventory (.cut (signature := signature arity) (Parallel := Parallel arity)
    rfl (Source.embed low) (Source.embed low))).card =
    (inventory (Source.embed low)).card at counts
  rw [SortedCommutativeSourceControls.entire_low_readout] at counts
  simp only [SortedCommutativeInstrumentControls.low, sourceNode, inventory,
    Multiset.card_add, Multiset.card_singleton] at counts
  omega

theorem complete_ordered_ask_targets_remain_nondeterministic :
    (firingSystem (rules arity Nat)).act (PayloadLabels.probeLabel (.ask .properCut))
        (classOf firstAsk.body) (classOf firstAsk.output) ∧
      (firingSystem (rules arity Nat)).act (PayloadLabels.probeLabel (.ask .properCut))
        (classOf firstAsk.body) (classOf secondAsk.output) ∧
      classOf firstAsk.output ≠ classOf secondAsk.output := by
  refine ⟨(directPayloadReceipt firstAsk).step, ?_, ?_⟩
  · have second := (directPayloadReceipt secondAsk).step
    change (firingSystem (rules arity Nat)).act (PayloadLabels.probeLabel (.ask .properCut))
      (classOf (sourceNode arity .properCut reversed))
      (classOf (bundle arity .properCut reversed)) at second
    change (firingSystem (rules arity Nat)).act (PayloadLabels.probeLabel (.ask .properCut))
      (classOf (sourceNode arity .properCut ordered))
      (classOf (bundle arity .properCut reversed))
    rw [← SortedCommutativeInstrumentControls.same_cut_class] at second
    exact second
  · intro same
    exact SortedCommutativeInstrumentControls.different_ordered_ask_targets
      (congrArg RawArrow.value same)

theorem complete_repeated_targets_keep_their_origins :
    (directPayloadReceipt (.get 24 (.ordinary Symbol.pair)
      SortedCommutativeCombinedReconstructionControls.nativeArguments 0 : Occurrence arity Nat)).occurrence.target =
        (directPayloadReceipt (.get 25 (.ordinary Symbol.pair)
          SortedCommutativeCombinedReconstructionControls.nativeArguments 0 : Occurrence arity Nat)).occurrence.target ∧
      directPayloadReceipt (.get 24 (.ordinary Symbol.pair)
        SortedCommutativeCombinedReconstructionControls.nativeArguments 0 : Occurrence arity Nat) ≠
        directPayloadReceipt (.get 25 (.ordinary Symbol.pair)
          SortedCommutativeCombinedReconstructionControls.nativeArguments 0 : Occurrence arity Nat) := by
  refine ⟨rfl, ?_⟩
  intro same
  have origins := congrArg (fun receipt => receipt.occurrence.origin) same
  change (24 : Nat) = 25 at origins
  omega

theorem observer_bearing_child_is_retained :
    (directPayloadReceipt (.get 24 (.ordinary Symbol.pair)
      SortedCommutativeCombinedReconstructionControls.nativeArguments 0 : Occurrence arity Nat)).occurrence.output =
        SortedCommutativeCombinedReconstructionControls.observedChild := rfl

theorem unit_get_competition_remains_actual :
    system.act (PayloadLabels.probeLabel (.get (.ordinary Symbol.pair) 0))
      (classOf (bundle arity (.ordinary Symbol.pair) (fun position => Source.embed
        (SortedCommutativeProbeSourceControls.ordered position))))
      (Source.classEmbedding (classOf low)) ∧
    system.act (PayloadLabels.probeLabel (.get (.ordinary Symbol.pair) 0))
      (classOf (bundle arity (.ordinary Symbol.pair) (fun position => Source.embed
        (SortedCommutativeProbeSourceControls.ordered position))))
      (classOf SortedCommutativeCombinedReconstructionControls.observedChild) ∧
    Source.classEmbedding (classOf low) ≠ classOf SortedCommutativeCombinedReconstructionControls.observedChild := by
  obtain ⟨first, second, distinct⟩ :=
    SortedCommutativeCombinedReconstructionControls.actual_get_results_remain_distinct
  exact ⟨(probe_act_iff _ _ _ _).mpr first, (probe_act_iff _ _ _ _).mpr second,
    fun same => distinct (congrArg RawArrow.value same)⟩

theorem a_foreign_successor_cannot_match_any_source (supplied : Source.ValueClass arity) :
    ¬system.Bisimilar .base (Source.classEmbedding supplied)
      (classOf SortedCommutativeCombinedReconstructionControls.observedChild) := by
  intro related
  have same := (bisimilar_iff_embedded_equal sourceRules (Origins := Nat) ⟨7⟩ supplied _).mp related
  have literal := (combined_observer_bisimilar_iff_embedded_equal sourceRules (Origins := Nat) ⟨7⟩ supplied _).mpr same
  exact SortedCommutativeCombinedReconstructionControls.the_foreign_get_successor_cannot_match_any_pure_source
    supplied literal

theorem missing_origins_remove_actual_ask
    (result : ValueClass arity (.arguments (.ordinary Symbol.pair))) :
    ¬(firingSystem (combinedSourceRules sourceRules Empty)).act
      (PayloadLabels.probeLabel (.ask (.ordinary Symbol.pair)))
      (Source.classEmbedding (classOf low)) result := by
  intro step
  have actual := (probe_act_iff _ _ _ _).mp step
  exact (SortedCommutativeCombinedReconstructionControls.missing_origins_remove_ask_but_not_the_original_get
    (RawArrow.value result)).1 actual

def paddedIdentity : Label arity .base .base :=
  residualLabel (classOf (.zero (signature := signature arity) (Parallel := Parallel arity) rfl))

theorem empty_residue_does_not_invent_an_extra_label :
    encodeContext (readContext paddedIdentity) ≠ paddedIdentity := by
  have empty : valueResidue (arity := arity) (sort := .base) rfl
      (classOf (.zero (signature := signature arity) (Parallel := Parallel arity) rfl)) = 0 := rfl
  have normalized : encodeContext (readContext paddedIdentity) = holeLabel .base := by
    rw [encode_readContext]
    change encodeMixed (readLabel (residualLabel
      (classOf (.zero (signature := signature arity) (Parallel := Parallel arity) rfl)))) = _
    rw [(complete_parallel_payload_readout _).2, empty]
    exact addBag_zero (holeLabel .base)
  intro encoded
  have labels := normalized.symm.trans encoded
  have shapes := congrArg Mettapedia.GSLT.HigherOrderBisimulation.Label.skeleton labels
  cases shapes

theorem an_empty_residue_label_cannot_fire (first last : ValueClass arity .base) :
    ¬system.act paddedIdentity first last := by
  intro step
  exact empty_residue_does_not_invent_an_extra_label ((act_read_iff _ _ _ _).mp step).1

theorem nonidentity_substitution_keeps_the_whole_argument_and_assay :
    (readContext (substituteLabel
      (encodeContext (contextClassOf SortedCommutativeInstrumentControls.firstHole))
      (PayloadLabels.probeLabel (.ask (.ordinary Symbol.pair)))).val).fill
        (Source.classEmbedding (classOf high)) =
      classOf ((probeContext arity (.ask (.ordinary Symbol.pair))).fill
        (SortedCommutativeInstrumentControls.firstHole.fill (Source.embed high))) := by
  rw [substituteLabel_context, read_encodeContext, read_probeLabel, ContextClass.fill_comp]
  rfl

end Mettapedia.OSLF.Framework.SortedCommutativePayloadControls
