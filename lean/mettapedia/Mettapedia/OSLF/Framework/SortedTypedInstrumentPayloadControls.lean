import Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadReconstruction
import Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadContextAction
import Mettapedia.OSLF.Framework.SortedTypedInstrumentCombinedReconstructionControls

/-!
# Same-fixed-point typed payload controls and complete context substitution

Send labels independently retain their process or channel sibling at its
actual sort. Equal skeletons do not replace payload comparison: the same
greatest fixed point separates complete nested channels and multiplicity,
while respecting an actual AC1 swap. Nonidentity context substitution
retains the input, heterogeneous sibling and complete parallel residue.

Actual ordered Cut alternatives, observer-bearing empty-sort coordinates,
unit-get competition and duplicate origins survive the label conversion.
Empty residues cannot introduce additional firing-label presentations.
The source characterization has explicit inhabited administrative origins
and applies to original classes against arbitrary native right values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments SortedTypedInstruments.PayloadLabels
open SortedTypedInstrumentControls SortedTypedInstrumentProbeControls
open SortedTypedInstrumentOriginalProbeControls

abbrev system := firingSystem (combinedSourceRules originalRules Nat)

abbrev ProcessClass := ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.original .process)
abbrev ChannelClass := ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.original .channel)

def sendShape : Skeleton (profile := sourceSignature) (Parallel := sourceParallel)
    (.original .channel) (.original .process) :=
  Skeleton.frame (profile := sourceSignature) (Parallel := sourceParallel) (.original Symbol.send) 0 .hole

def processSibling : Skeleton.Slot sendShape := .inl ⟨1, by decide, rfl⟩

def sendLabel (supplied : ProcessClass) :
    Label sourceSignature sourceParallel (.original .channel) (.original .process) :=
  frameLabel (profile := sourceSignature) (Parallel := sourceParallel) (.original Symbol.send) 0
    (Fin.cases (fun absent => (absent rfl).elim) (fun _ _ => supplied))
    (holeLabel (profile := sourceSignature) (Parallel := sourceParallel) (.original .channel))

def channelShape : Skeleton (profile := sourceSignature) (Parallel := sourceParallel)
    (.original .process) (.original .process) :=
  Skeleton.frame (profile := sourceSignature) (Parallel := sourceParallel) (.original Symbol.send) 1 .hole

def channelSibling : Skeleton.Slot channelShape := .inl ⟨0, by decide, rfl⟩

def channelLabel (supplied : ChannelClass) :
    Label sourceSignature sourceParallel (.original .process) (.original .process) :=
  frameLabel (profile := sourceSignature) (Parallel := sourceParallel) (.original Symbol.send) 1
    (Fin.cases (fun _ => supplied) (fun other absent => by
      have zero : other = 0 := Subsingleton.elim other 0
      subst other
      exact (absent rfl).elim))
        (holeLabel (profile := sourceSignature) (Parallel := sourceParallel) (.original .process))

theorem complete_siblings_have_their_actual_different_sorts
    (process : ProcessClass) (channel : ChannelClass) :
    Skeleton.slotSort sendShape processSibling = .original .process ∧
      Skeleton.slotSort channelShape channelSibling = .original .channel ∧
      (sendLabel process).payload processSibling = process ∧
      (channelLabel channel).payload channelSibling = channel := ⟨rfl, rfl, rfl, rfl⟩

private theorem send_related_iff (first second : ProcessClass) :
    Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates system.Bisimilar
      (sendLabel first) (sendLabel second) ↔ system.Bisimilar (.original .process) first second := by
  constructor
  · intro related
    cases related with
    | mk shape left right positions => exact positions processSibling
  · intro related
    refine Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates.mk
      (vocabulary := vocabulary sourceSignature sourceParallel)
      (State := ValueClass (source := sourceSignature) (Parallel := sourceParallel))
      (relation := system.Bisimilar) sendShape (sendLabel first).payload (sendLabel second).payload ?_
    intro slot
    change {other : Fin 2 // other ≠ 0 ∧
      processSort ((signature sourceSignature sourceParallel).input (.original Symbol.send) other) = true} ⊕
        PEmpty at slot
    rcases slot with other | absent
    · obtain ⟨other, distinct, _process⟩ := other
      fin_cases other
      · exact (distinct rfl).elim
      · exact related
    · exact PEmpty.elim absent

theorem same_shape_cannot_hide_a_changed_nested_channel :
    (sendLabel (classOf (embed (sourcePayload 7)))).skeleton =
        (sendLabel (classOf (embed (sourcePayload 11)))).skeleton ∧
      ¬Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates system.Bisimilar
        (sendLabel (classOf (embed (sourcePayload 7))))
        (sendLabel (classOf (embed (sourcePayload 11)))) := by
  refine ⟨rfl, ?_⟩
  intro related
  have recovered := (bisimilar_iff_embedded_equal originalRules (Origins := Nat) ⟨24⟩
    (classOf (sourcePayload 7)) (classOf (embed (sourcePayload 11)))).mp
      ((send_related_iff _ _).mp related)
  have coordinates := (node_class_eq_iff (signature := signature sourceSignature sourceParallel)
    (Parallel := NativeParallel) (Constructor.original Symbol.send) _ _).mp recovered
  exact different_channel_indices_remain_distinct 7 11 (by omega) (coordinates 0)

theorem the_same_fixed_point_really_separates_multiplicity_one_and_two :
    ¬system.Bisimilar (.original .process) (classOf (embed (sourcePayload 9)))
      (classOf (embed (.cut rfl (sourcePayload 9) (sourcePayload 9)))) := by
  intro related
  have recovered := (bisimilar_iff_source_equal originalRules (Origins := Nat) ⟨24⟩
    (classOf (sourcePayload 9)) (classOf (.cut rfl (sourcePayload 9) (sourcePayload 9)))).mp related
  have counts := congrArg (fun supplied => (inventoryQ supplied).card) recovered
  change 1 = 1 + 1 at counts
  omega

theorem an_actual_ac1_payload_equation_is_respected :
    Mettapedia.GSLT.HigherOrderBisimulation.Label.Relates system.Bisimilar
      (sendLabel (classOf (embed (.cut rfl (sourcePayload 7) (sourcePayload 9)))))
      (sendLabel (classOf (embed (.cut rfl (sourcePayload 9) (sourcePayload 7))))) := by
  apply (send_related_iff _ _).mpr
  exact (raw_bisimilar_iff_source_equation originalRules (Origins := Nat) ⟨24⟩ _ _).mpr
    (Equation.comm (signature := sourceSignature) (Parallel := sourceParallel)
      (sort := .process) rfl (sourcePayload 7) (sourcePayload 9))

def residualLabel (supplied : ProcessClass) :
    Label sourceSignature sourceParallel (.original .process) (.original .process) :=
  parallelLabel (profile := sourceSignature) (Parallel := sourceParallel) rfl supplied
    (holeLabel (profile := sourceSignature) (Parallel := sourceParallel) (.original .process))

theorem complete_parallel_payload_readout (supplied : ProcessClass) :
    (residualLabel supplied).payload (.inl PUnit.unit) = supplied ∧
      readLabel (residualLabel supplied) =
        (Mettapedia.CategoryTheory.MixedResidue.Context.parallel
          (valueResidue (source := sourceSignature) (Parallel := sourceParallel)
            (sort := .original .process) rfl supplied) :
          MixedContext (signature sourceSignature sourceParallel) NativeParallel
            (.original .process) (.original .process)) := by
  refine ⟨rfl, ?_⟩
  change (Mettapedia.CategoryTheory.MixedResidue.Context.parallel
    (valueResidue (source := sourceSignature) (Parallel := sourceParallel)
      (sort := .original .process) rfl supplied + 0) :
      MixedContext (signature sourceSignature sourceParallel) NativeParallel
        (.original .process) (.original .process)) = _
  rw [add_zero]

def paddedIdentity : Label sourceSignature sourceParallel (.original .process) (.original .process) :=
  residualLabel (classOf (.zero rfl))

theorem empty_residue_cannot_create_an_additional_label :
    encodeContext (readContext paddedIdentity) ≠ paddedIdentity := by
  have empty : valueResidue (source := sourceSignature) (Parallel := sourceParallel)
      (sort := .original .process) rfl (classOf (.zero rfl)) = 0 := rfl
  have normalized : encodeContext (readContext paddedIdentity) =
      holeLabel (profile := sourceSignature) (Parallel := sourceParallel) (.original .process) := by
    rw [encode_readContext]
    change encodeMixed (readLabel (residualLabel (classOf (.zero rfl)))) = _
    rw [(complete_parallel_payload_readout _).2, empty]
    exact addBag_zero (holeLabel (profile := sourceSignature) (Parallel := sourceParallel) (.original .process))
  intro encoded
  have shapes := congrArg Mettapedia.GSLT.HigherOrderBisimulation.Label.skeleton
    (normalized.symm.trans encoded)
  cases shapes

theorem an_extra_empty_residue_label_cannot_fire (first last : ProcessClass) :
    ¬system.act paddedIdentity first last := by
  intro step
  exact empty_residue_cannot_create_an_additional_label ((act_read_iff _ _ _ _).mp step).1

theorem actual_ordered_cut_targets_remain_nondeterministic :
    (firingSystem (rules sourceSignature sourceParallel Nat)).act (PayloadLabels.probeLabel (.ask cutHead))
        (classOf (sourceNode cutHead orderedCutArguments)) (classOf (bundle cutHead orderedCutArguments)) ∧
      (firingSystem (rules sourceSignature sourceParallel Nat)).act (PayloadLabels.probeLabel (.ask cutHead))
        (classOf (sourceNode cutHead orderedCutArguments)) (classOf (bundle cutHead exchangedCutArguments)) ∧
      classOf (bundle cutHead orderedCutArguments) ≠ classOf (bundle cutHead exchangedCutArguments) :=
  ⟨(probe_act_iff (rules sourceSignature sourceParallel Nat) (.ask cutHead) _ _).mpr
      actual_cut_ask_keeps_both_ordered_alternatives.1,
    (probe_act_iff (rules sourceSignature sourceParallel Nat) (.ask cutHead) _ _).mpr
      actual_cut_ask_keeps_both_ordered_alternatives.2.1,
    actual_cut_ask_keeps_both_ordered_alternatives.2.2⟩

theorem an_observer_bearing_empty_sort_coordinate_survives :
    (firingSystem (rules sourceSignature sourceParallel Nat)).act
        (PayloadLabels.probeLabel (.get blockedHead 0)) (classOf (bundle blockedHead blockedNativeTuple))
        (classOf observerBearingAbsent) ∧ ¬Nonempty (SourceValue .absent) :=
  ⟨(probe_act_iff (rules sourceSignature sourceParallel Nat) (.get blockedHead 0) _ _).mpr
      whole_inversion_does_not_supply_a_source_inhabitant.1,
    whole_inversion_does_not_supply_a_source_inhabitant.2⟩

theorem the_full_origin_receipt_remains_distinct :
    (directPayloadReceipt (processGet 24 7 (sourcePayload 9))).occurrence.target =
        (directPayloadReceipt (processGet 25 7 (sourcePayload 9))).occurrence.target ∧
      directPayloadReceipt (processGet 24 7 (sourcePayload 9)) ≠
        directPayloadReceipt (processGet 25 7 (sourcePayload 9)) := by
  refine ⟨rfl, ?_⟩
  intro same
  have origins := congrArg (fun receipt => receipt.occurrence.origin) same
  change (24 : Nat) = 25 at origins
  omega

theorem the_competing_original_successor_cannot_match_any_source
    (supplied : Class sourceSignature sourceParallel .process) :
    ¬system.Bisimilar (.original .process) (classEmbedding supplied)
      (classOf (.cut (signature := signature sourceSignature sourceParallel)
        (Parallel := NativeParallel) (sort := .original .process) rfl
        (embed (sourcePayload 11)) (getAssay sendHead (sendArguments 7 (sourcePayload 9)) 1))) := by
  intro related
  have recovered := (bisimilar_iff_embedded_equal originalRules (Origins := Nat) ⟨24⟩ supplied _).mp related
  have counts := congrArg classObserverCount recovered
  rw [classObserverCount_embedding] at counts
  change 0 = arrowObserverCount originalResult at counts
  rw [original_result_has_three_observer_heads] at counts
  omega

theorem complete_nonidentity_substitution_keeps_the_input_sibling_and_residue :
    (readContext (substituteLabel
      (encodeContext (contextClassOf (embedContext
        (SortedTypedInstrumentSourceControls.sendContext (sourcePayload 9)))))
      (encodeContext (contextClassOf (embedContext
        (RawContext.left (signature := sourceSignature) (Parallel := sourceParallel)
          (sort := .process) rfl .hole (sourcePayload 11)))))).val).fill
        (classOf (embed (sourceName 7))) =
      classOf (embed (.cut (signature := sourceSignature) (Parallel := sourceParallel)
        (sort := .process) rfl
        (Term.node (signature := sourceSignature) (Parallel := sourceParallel) Symbol.send
          (Fin.cases (motive := fun position => SourceValue (sourceSignature.input Symbol.send position))
            (sourceName 7) (fun _ => sourcePayload 9))) (sourcePayload 11))) := by
  rw [substituteLabel_complete_value, read_encodeContext, read_encodeContext]
  change classOf ((embedContext (RawContext.left (signature := sourceSignature) (Parallel := sourceParallel)
    (sort := .process) rfl .hole (sourcePayload 11))).fill
      ((embedContext (SortedTypedInstrumentSourceControls.sendContext (sourcePayload 9))).fill
        (embed (sourceName 7)))) = _
  rw [embedContext_fill, embedContext_fill, SortedTypedInstrumentSourceControls.complete_source_filling]
  rfl

end Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadControls
