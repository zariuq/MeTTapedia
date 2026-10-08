import Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeReadout
import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceControls

/-!
# Complete typed probe inversion, AC1 alternatives and empty-sort controls

Send retains its channel and process coordinates through the whole rule
family. Wrong complete get targets are rejected, whereas an actual native
coordinate at an empty source sort is retained. A blocked ask cannot invent
that coordinate from a pure process. Proper Cut has distinct ordered ask
bundles at the same AC1 source class. Nullary probes and duplicate supplied
origins remain real firings rather than uniqueness assumptions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence
open SortedTypedInstruments SortedTypedInstrumentControls

abbrev sendHead : SourceHead sourceSignature sourceParallel := .ordinary .send
abbrev blockedHead : SourceHead sourceSignature sourceParallel := .ordinary .blocked
abbrev cutHead : SourceHead sourceSignature sourceParallel := .properCut .process rfl
abbrev unitHead : SourceHead sourceSignature sourceParallel := .unit .process rfl

theorem complete_channel_get_iff (index : Nat) (payload : SourceValue .process)
    (observed : ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.original .channel)) :
    ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.get sendHead 0))
      (RawArrow.value (classOf (bundle sendHead (sendArguments index payload)))) (RawArrow.value observed) ↔
      observed = classOf (embed (sourceName index)) := by
  exact (get_bundle_step_iff sendHead (sendArguments index payload) 0 observed).trans
    (and_iff_right (show Nonempty Nat from ⟨24⟩))

theorem complete_process_get_iff (index : Nat) (payload : SourceValue .process)
    (observed : ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.original .process)) :
    ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.get sendHead 1))
      (RawArrow.value (classOf (bundle sendHead (sendArguments index payload)))) (RawArrow.value observed) ↔
      observed = classOf (embed payload) := by
  exact (get_bundle_step_iff sendHead (sendArguments index payload) 1 observed).trans
    (and_iff_right (show Nonempty Nat from ⟨24⟩))

theorem actual_wrong_channel_target_is_rejected :
    ¬ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.get sendHead 0))
      (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9)))))
      (RawArrow.value (classOf (embed (sourceName 11)))) := by
  intro step
  have wrong := (complete_channel_get_iff 7 (sourcePayload 9) _).mp step
  exact different_channel_indices_remain_distinct 11 7 (by omega) wrong

private theorem different_payloads (first second : Nat) (different : first ≠ second) :
    classOf (embed (sourcePayload first)) ≠ classOf (embed (sourcePayload second)) := by
  intro same
  have coordinates := (node_class_eq_iff (signature := signature sourceSignature sourceParallel)
    (Parallel := NativeParallel) (Constructor.original Symbol.send) _ _).mp same
  exact different_channel_indices_remain_distinct first second different (coordinates 0)

theorem actual_wrong_nested_payload_is_rejected :
    ¬ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.get sendHead 1))
      (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9)))))
      (RawArrow.value (classOf (embed (sourcePayload 11)))) := by
  intro step
  have wrong := (complete_process_get_iff 7 (sourcePayload 9) _).mp step
  exact different_payloads 11 9 (by omega) wrong

theorem arbitrary_native_absent_get_iff
    (observed : ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.original .absent)) :
    ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.get blockedHead 0))
      (RawArrow.value (classOf (bundle blockedHead blockedNativeTuple))) (RawArrow.value observed) ↔
      observed = classOf observerBearingAbsent := by
  exact (get_bundle_step_iff blockedHead blockedNativeTuple 0 observed).trans
    (and_iff_right (show Nonempty Nat from ⟨41⟩))

theorem whole_inversion_does_not_supply_a_source_inhabitant :
    ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.get blockedHead 0))
      (RawArrow.value (classOf (bundle blockedHead blockedNativeTuple)))
      (RawArrow.value (classOf observerBearingAbsent)) ∧ ¬Nonempty (SourceValue .absent) :=
  ⟨(arbitrary_native_absent_get_iff _).mpr rfl,
    fun ⟨supplied⟩ => no_source_value_at_absent_sort supplied⟩

theorem blocked_ask_cannot_invent_an_absent_coordinate
    (observed : ValueClass (source := sourceSignature) (Parallel := sourceParallel) (.arguments blockedHead)) :
    ¬ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.ask blockedHead))
      (RawArrow.value (classOf (embed (.zero rfl : SourceValue .process)))) (RawArrow.value observed) := by
  intro step
  obtain ⟨_origin, arguments, inputRead, _outputRead⟩ := (ask_step_iff blockedHead _ observed).mp step
  have count := congrArg classObserverCount inputRead
  change 0 = observerCount (sourceNode blockedHead arguments) at count
  rw [observerCount_sourceNode] at count
  have bounded := Finset.single_le_sum
    (fun other _ => Nat.zero_le (observerCount (arguments other))) (Finset.mem_univ (0 : Fin 1))
  have absentPure : observerCount (arguments 0) = 0 := by omega
  obtain ⟨original, _read⟩ := observerCount_zero_original (arguments 0) absentPure
  exact no_source_value_at_absent_sort original

def orderedCutArguments : Arguments cutHead :=
  Fin.cases (embed (sourcePayload 7)) (fun _ => embed (sourcePayload 9))

def exchangedCutArguments : Arguments cutHead :=
  Fin.cases (embed (sourcePayload 9)) (fun _ => embed (sourcePayload 7))

theorem actual_cut_ask_keeps_both_ordered_alternatives :
    ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.ask cutHead))
        (RawArrow.value (classOf (sourceNode cutHead orderedCutArguments)))
        (RawArrow.value (classOf (bundle cutHead orderedCutArguments))) ∧
      ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.ask cutHead))
        (RawArrow.value (classOf (sourceNode cutHead orderedCutArguments)))
        (RawArrow.value (classOf (bundle cutHead exchangedCutArguments))) ∧
      classOf (bundle cutHead orderedCutArguments) ≠ classOf (bundle cutHead exchangedCutArguments) := by
  refine ⟨(ask_step_iff cutHead _ _).mpr ⟨24, orderedCutArguments, rfl, rfl⟩, ?_, ?_⟩
  · apply (ask_step_iff cutHead _ _).mpr
    refine ⟨25, exchangedCutArguments, ?_, rfl⟩
    exact Quotient.sound (Equation.comm (signature := signature sourceSignature sourceParallel)
      (Parallel := NativeParallel) (sort := .original .process) rfl
      (embed (sourcePayload 7)) (embed (sourcePayload 9)))
  · intro same
    have coordinates := (bundle_class_eq_iff cutHead orderedCutArguments exchangedCutArguments).mp same
    exact different_payloads 7 9 (by omega) (coordinates 0)

theorem nullary_unit_ask_has_exact_full_output
    (observed : ValueClass (source := sourceSignature) (Parallel := sourceParallel)
      (.arguments unitHead)) :
    ActIPO (rules sourceSignature sourceParallel Nat) (probeLabel (.ask unitHead))
      (RawArrow.value (classOf (embed (.zero rfl : SourceValue .process)))) (RawArrow.value observed) ↔
      observed = classOf (bundle unitHead (fun position => Fin.elim0 position)) := by
  rw [ask_step_iff]
  constructor
  · rintro ⟨_origin, arguments, _inputRead, outputRead⟩
    have emptyRead : arguments = fun position => Fin.elim0 position := by
      funext position
      exact Fin.elim0 position
    exact outputRead.trans (congrArg (fun tuple => classOf (bundle unitHead tuple)) emptyRead)
  · intro outputRead
    exact ⟨37, (fun position => Fin.elim0 position), rfl, outputRead⟩

theorem actual_empty_origin_get_is_rejected :
    ¬ActIPO (rules sourceSignature sourceParallel Empty) (probeLabel (.get sendHead 0))
      (RawArrow.value (classOf (bundle sendHead (sendArguments 7 (sourcePayload 9)))))
      (RawArrow.value (classOf (embed (sourceName 7)))) :=
  no_probe_step_without_origins _ _ _

theorem exact_probe_inversion_keeps_duplicate_origins :
    ActIPO (rules sourceSignature sourceParallel Nat)
        (processGet 24 7 (sourcePayload 9)).label
        (processGet 24 7 (sourcePayload 9)).agent (processGet 24 7 (sourcePayload 9)).target ∧
      ActIPO (rules sourceSignature sourceParallel Nat)
        (processGet 25 7 (sourcePayload 9)).label
        (processGet 25 7 (sourcePayload 9)).agent (processGet 25 7 (sourcePayload 9)).target ∧
      directReceipt (processGet 24 7 (sourcePayload 9)) ≠
        directReceipt (processGet 25 7 (sourcePayload 9)) :=
  ⟨(processGet 24 7 (sourcePayload 9)).direct_step,
    (processGet 25 7 (sourcePayload 9)).direct_step,
    complete_receipts_do_not_merge_duplicate_origins.2⟩

end Mettapedia.OSLF.Framework.SortedTypedInstrumentProbeControls
