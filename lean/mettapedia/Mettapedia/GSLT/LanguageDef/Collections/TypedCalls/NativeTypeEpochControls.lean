import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEpochCache
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEntryControls

/-! # Publication-history and composed raw-source hit controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEpochControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypingScopeEpochs
open NativeTypeEntryCodec NativeTypeEntrySource
open NativeTypeCurrentReader (external currentOps)

def seed : Mettapedia.Machines.IssuedEpochDirectory.State Bool Nat :=
  ⟨100, fun key => if key then ⟨100, 9⟩ else ⟨1, 0⟩⟩

theorem seed_valid : Mettapedia.Machines.IssuedEpochDirectory.Valid seed := by
  intro key
  cases key <;> decide

/-- Advancing a local counter can be hidden behind another member's maximum. -/
def localCounterMutation : Mettapedia.Machines.IssuedEpochDirectory.State Bool Nat :=
  ⟨100, fun key => if key then ⟨100, 9⟩ else ⟨2, 1⟩⟩

theorem local_counter_maximum_misses_a_change :
    Mettapedia.Machines.IssuedEpochDirectory.latest seed [false, true] =
      Mettapedia.Machines.IssuedEpochDirectory.latest localCounterMutation [false, true] ∧
    Mettapedia.Machines.IssuedEpochDirectory.read seed [false, true] ≠
      Mettapedia.Machines.IssuedEpochDirectory.read localCounterMutation [false, true] := by decide

theorem global_publication_cannot_hide_behind_the_maximum :
    Mettapedia.Machines.IssuedEpochDirectory.latest
      (Mettapedia.Machines.IssuedEpochDirectory.publish seed false 1) [false, true] = 101 := by decide

theorem unrelated_publication_preserves_the_selected_read :
    let after := Mettapedia.Machines.IssuedEpochDirectory.publish seed true 20
    Mettapedia.Machines.IssuedEpochDirectory.latest after [false] =
      Mettapedia.Machines.IssuedEpochDirectory.latest seed [false] ∧
    Mettapedia.Machines.IssuedEpochDirectory.read after [false] =
      Mettapedia.Machines.IssuedEpochDirectory.read seed [false] := by decide

theorem unchanged_maximum_is_not_global_injectivity :
    let first := Mettapedia.Machines.IssuedEpochDirectory.initial (fun (_ : Bool) => 0)
    let second := Mettapedia.Machines.IssuedEpochDirectory.initial (fun (_ : Bool) => 1)
    Mettapedia.Machines.IssuedEpochDirectory.latest first [false, true] =
      Mettapedia.Machines.IssuedEpochDirectory.latest second [false, true] ∧
    Mettapedia.Machines.IssuedEpochDirectory.read first [false, true] ≠
      Mettapedia.Machines.IssuedEpochDirectory.read second [false, true] := by decide

theorem changed_read_set_needs_its_own_publication :
    let state := Mettapedia.Machines.IssuedEpochDirectory.initial (fun key : Bool => if key then 1 else 0)
    Mettapedia.Machines.IssuedEpochDirectory.latest state [false] =
      Mettapedia.Machines.IssuedEpochDirectory.latest state [true] ∧
    Mettapedia.Machines.IssuedEpochDirectory.read state [false] ≠
      Mettapedia.Machines.IssuedEpochDirectory.read state [true] := by decide

def wrapSeed : Mettapedia.Machines.IssuedEpochDirectory.State Bool Nat :=
  ⟨UInt64.size + 4, fun _ => ⟨5, 0⟩⟩

theorem unchecked_word_wrap_revives_an_old_code :
    let after := Mettapedia.Machines.IssuedEpochDirectory.publish wrapSeed false 1
    UInt64.ofNat (Mettapedia.Machines.IssuedEpochDirectory.latest after [false]) =
      UInt64.ofNat (Mettapedia.Machines.IssuedEpochDirectory.latest wrapSeed [false]) ∧
    Mettapedia.Machines.IssuedEpochDirectory.read after [false] ≠
      Mettapedia.Machines.IssuedEpochDirectory.read wrapSeed [false] := by decide

def nested : NativeTypingScopeEpochs.State 3 := initial NativeTypingScopeOverlays.Controls.nested

theorem nested_initialized_valid : Valid nested := initial_valid _

theorem inherited_append_outside_ceiling_keeps_compressed_token :
    let after := execute nested [.source (.edit 0 (.append NativeTypingScopeOverlays.Controls.row))]
    check after (token nested) = true ∧
      NativeTypingScopeOverlays.packet after.scope = NativeTypingScopeOverlays.packet nested.scope := by decide

theorem data_only_shift_invalidates_compressed_token :
    let after := execute nested [.source (.edit 0 (.erase 0))]
    check after (token nested) = false ∧
      NativeTypingScopeOverlays.packet after.scope ≠ NativeTypingScopeOverlays.packet nested.scope := by decide

theorem imported_change_invalidates_compressed_token :
    check (execute nested [.source (.edit 2 (.erase 0))]) (token nested) = false := by decide

theorem layer_aba_does_not_revive_compressed_token :
    let after := execute nested [.publish [], .publish nested.scope.layers]
    NativeTypingScopeOverlays.packet after.scope = NativeTypingScopeOverlays.packet nested.scope ∧
      check after (token nested) = false := by decide

theorem import_aba_does_not_revive_compressed_token :
    let after := execute nested [.source (.unlink 0 2), .source (.link 0 2)]
    NativeTypingScopeOverlays.packet after.scope = NativeTypingScopeOverlays.packet nested.scope ∧
      check after (token nested) = false := by decide

theorem retirement_does_not_reuse_the_old_owner :
    check (execute nested [.retire]) (token nested) = false := by decide

def locals : Fin 1 → NativeTypingScopeEdits.State := fun id =>
  ⟨⟨id.val, 0, NativeTypeEntryControls.source.rows⟩, 0, 0⟩

def ownScope : NativeTypingScopeOverlays.State 1 :=
  ⟨NativeTypingScopeImports.initialState 37 locals, 0, [], 81, 0, 0⟩

def own : NativeTypingScopeEpochs.State 1 := initial ownScope
def note : NativeTypingScopeOverlays.Action 1 := .source (.edit 0 (.append (.symbol "note")))
def changed : NativeTypingScopeOverlays.Action 1 := .source (.edit 0 (.replace 0
  (TypeReadQueryMemoControls.row "Box"
    (TypeReadQueryMemoControls.arrow [.symbol "Number"] (.symbol "Changed")))))

theorem snapshot_is_the_actual_entry_source :
    TypeReadScopeMemo.snapshot NativeTypeEntryControls.source own.scope = NativeTypeEntryControls.source := by rfl

theorem own_entry_sound : Sound NativeTypeEntryControls.heap
    (sourceMeaning currentOps (TypeReadScopeMemo.snapshot NativeTypeEntryControls.source own.scope) external)
    NativeTypeEntryControls.image.entries NativeTypeEntryControls.image.states := by
  rw [snapshot_is_the_actual_entry_source]
  exact NativeTypeEntryControls.actual_entry_sound

theorem unrelated_edit_retains_the_native_entry_and_payload :
    NativeTypeEpochCache.bindImage own [note] NativeTypeEntryControls.image = NativeTypeEntryControls.image := by
  rfl

/-- The composed theorem is used here: no fresh-inference output equality
is supplied as a premise. -/
theorem retained_native_hit_answers_the_raw_source_after_edit :
    sourceMeaning currentOps
      (TypeReadScopeMemo.rawSource NativeTypeEntryControls.source (execute own [note]).scope)
      external true NativeTypeEntryControls.oldAtom = some NativeTypeEntryControls.facts := by
  apply NativeTypeEpochCache.raw_source_hit NativeTypeEntryControls.source external id (fun _ => [])
    NativeTypeEntryControls.heap own (initial_valid _) [note] NativeTypeEntryControls.image own_entry_sound
    [] 1 true 1 0 NativeTypeEntryControls.oldAtom NativeTypeEntryControls.facts
  · decide
  · cbv
  · cbv
  · cbv

theorem governing_edit_clears_both_arrays :
    (NativeTypeEpochCache.bindImage own [changed] NativeTypeEntryControls.image).entries = [] ∧
    (NativeTypeEpochCache.bindImage own [changed] NativeTypeEntryControls.image).states = [] := by decide

theorem governing_edit_keeps_the_changed_source_result :
    sourceMeaning currentOps
      (TypeReadScopeMemo.rawSource NativeTypeEntryControls.source (execute own [changed]).scope)
      external true NativeTypeEntryControls.oldAtom = some [.symbol "Changed"] := by cbv

def malformed : NativeTypingScopeEpochs.State 3 := initial
  { NativeTypingScopeOverlays.Controls.nested with layers := [⟨3, ∅, []⟩] }

theorem compressed_check_does_not_remove_the_inherited_bound_obligation :
    let actions := [.source (.edit 0 (.append NativeTypingScopeOverlays.Controls.row))]
    check (execute malformed actions) (token malformed) = true ∧
      NativeTypingScopeOverlays.packet (execute malformed actions).scope ≠
        NativeTypingScopeOverlays.packet malformed.scope ∧
      (NativeTypeEpochCache.bindImage malformed actions NativeTypeEntryControls.image).entries = [] := by decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeEpochControls
