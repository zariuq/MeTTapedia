import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryScope
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemoControls

/-! # Native entry mode, incarnation and state-id controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeEntryCodec NativeTypeEntrySource
open NativeTypeCurrentReader (external currentOps number badValue box)

def source : NativeTypeSourcePorts.Source := TypeReadQueryMemoControls.source
def oldAtom : Atom := box number
def newAtom : Atom := box badValue
def facts : List Atom := [.symbol "Actual"]
def states : States := [facts]
def entry : Entry := ⟨1, 0, 1, modeCode true, 1⟩
def emptyHeap : ShapeTyping.Heap UInt64 := ⟨fun _ => none, fun _ => 0⟩
def heap : ShapeTyping.Heap UInt64 := emptyHeap.step (.alloc 1 oldAtom 1)
def reuse : List (ShapeTyping.HeapOp UInt64) := [.reset 1, .alloc 1 newAtom 1]
def otherArena : List (ShapeTyping.HeapOp UInt64) := [.reset 1, .alloc 1 newAtom 2]

theorem actual_source_record :
    TypeReadQueryMemo.Recorded currentOps source external TypeReadQueryMemoRefinement.completionDepth
      (.infer true oldAtom) facts := by
  refine ⟨by decide, by decide, ⟨⟨[], 0⟩, ?_⟩⟩
  cbv

theorem actual_entry_sound : Sound heap (sourceMeaning currentOps source external) [entry] states := by
  exact record_from_source source external TypeReadQueryMemoControls.source_safe
    TypeNormalizationNames.equality_equivariant id TypeReadQueryRecursiveControls.identity_normalizers
    (fun _ => []) heap [] states (empty_sound heap _ states) entry true oldAtom facts
    (by decide) rfl (by cbv) (by cbv) (by cbv) actual_source_record

theorem positive_native_hit : read [entry] states 1 (modeCode true) 1 0 = some facts := by cbv

/-- The source query is connected through the record/heap invariant, not
only by comparing two worked output literals. -/
theorem positive_hit_is_the_source : sourceMeaning currentOps source external true oldAtom = some facts :=
  source_hit heap _ [entry] states actual_entry_sound 1 true 1 0 oldAtom facts
    (by cbv) (by cbv) positive_native_hit

theorem reset_reuses_address_but_rejects_old_entry :
    (heap.run reuse).cell 1 = some (newAtom, 1) ∧
    (heap.run reuse).epoch 1 = 1 ∧
    read [entry] states 1 (modeCode true) 1 1 = none ∧
    sourceMeaning currentOps source external true newAtom = some [] := by cbv

theorem old_metadata_would_admit_the_stale_payload :
    read [entry] states 1 (modeCode true) 1 0 = some facts ∧
    read [entry] states 1 (modeCode true) 1 1 = none := by cbv

theorem other_arena_with_equal_epoch_is_not_the_old_incarnation :
    (heap.run otherArena).cell 1 = some (newAtom, 2) ∧
    (heap.run otherArena).epoch 2 = 0 ∧
    read [entry] states 1 (modeCode true) 2 0 = none := by cbv

theorem question_codes_cannot_share_one_record :
    read [entry] states 1 (modeCode true) 1 0 = some facts ∧
    read [entry] states 1 (modeCode false) 1 0 = none := by cbv

theorem explicit_mode_has_source_content :
    sourceMeaning currentOps NativeTypeCurrentReader.source external true (box number) ≠
      sourceMeaning currentOps NativeTypeCurrentReader.source external false (box number) := by
  cbv
  simp

theorem zero_and_completed_empty_are_distinct :
    payload [[]] 0 = none ∧ payload [[]] 1 = some [] := by cbv

theorem unsupported_inquiry_is_not_reinterpreted :
    mode 2 = none ∧ inquiryRead [{ entry with question := 2 }] states 1 2 1 0 = none := by cbv

theorem identifier_wrap_is_a_miss_not_state_zero :
    payload [facts] (UInt32.ofNat UInt32.size) = none := by cbv

def latePayload : List Atom := [.symbol "Unrelated"]

theorem state_table_growth_keeps_old_materialization :
    RetainedTypePayloads.intern external (fun _ => 0) latePayload states = some (1, states ++ [latePayload]) ∧
    read [entry] (states ++ [latePayload]) 1 (modeCode true) 1 0 = some facts := by cbv

theorem poisoned_future_id_would_become_a_hit :
    payload [] 1 = none ∧ payload [latePayload] 1 = some latePayload ∧
    ¬ StateIdsPresent [entry] [] := by
  constructor
  · rfl
  constructor
  · cbv
  · intro present
    have required := present entry (by simp) (by cbv)
    rcases required with impossible | ⟨types, impossible⟩
    · cases impossible
    · cases impossible

theorem native_state_ids_are_present : StateIdsPresent [entry] states := by
  intro stored member _
  cases List.mem_singleton.mp member
  exact .inr ⟨facts, by cbv⟩

theorem actual_intern_keeps_sound_entries :
    Sound heap (sourceMeaning currentOps source external) [entry] (states ++ [latePayload]) :=
  sound_after_intern heap _ external (fun _ => 0) latePayload [entry] states 1 (states ++ [latePayload])
    actual_entry_sound native_state_ids_are_present state_table_growth_keeps_old_materialization.1

theorem null_address_is_never_an_occupied_entry :
    find [{ entry with address := 0 }] 0 (modeCode true) = none := by cbv

def image : NativeTypeEntryScope.Image := ⟨[entry], states⟩

theorem unrelated_scope_update_keeps_both_arrays :
    (NativeTypeEntryScope.refreshImage TypeReadScopeMemoControls.warm
      TypeReadScopeMemoControls.unrelated image).entries = [entry] ∧
    (NativeTypeEntryScope.refreshImage TypeReadScopeMemoControls.warm
      TypeReadScopeMemoControls.unrelated image).states = states := by cbv

theorem invalidated_scope_clears_entries_and_payloads :
    (NativeTypeEntryScope.refreshImage TypeReadScopeMemoControls.warm
      TypeReadScopeMemoControls.changedLocal image).entries = [] ∧
    (NativeTypeEntryScope.refreshImage TypeReadScopeMemoControls.warm
      TypeReadScopeMemoControls.changedLocal image).states = [] := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryControls
