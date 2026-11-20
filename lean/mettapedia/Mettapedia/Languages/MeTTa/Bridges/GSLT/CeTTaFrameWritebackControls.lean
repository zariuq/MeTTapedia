import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback

/-!
# Kernel-checked controls of the CeTTa frame writeback
-/


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.GSLT.LanguageDef.NativeOps
namespace NativeFrames
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Token)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
namespace ExpressionControls

private def root : Address := ⟨71, 0, []⟩
private def items : Address := ⟨72, 4, []⟩
private def left : Address := ⟨73, 0, []⟩
private def right : Address := ⟨74, 0, []⟩
private def parent : BindingValueView := ⟨some root, 19, 1⟩

private def memory (kind count : BitVec 64) (elements : Option Address)
    (entries : List (Option Address)) : TargetMemory :=
  ⟨fun storage index =>
    if storage = root.storage ∧ index = 0 then
      some (.record "Atom" [.word kind, .word 0, .word 0, .word 0, .word 0,
        .reference none, .word 0, .word 0,
        .record "expr" [.reference elements, .word count]])
    else if storage = items.storage ∧ items.element ≤ index then
      (entries[index - items.element]?).map TargetValue.reference
    else none,
    fun _ => none⟩

theorem order_repeats_and_context_are_retained :
    readExpressionChildren? (memory 3 3 (some items) [some left, some right, some left]) parent =
      some [parent.child (some left), parent.child (some right), parent.child (some left)] := by
  decide

theorem zero_length_has_no_pointer_read :
    readExpressionChildren? (memory 3 0 none []) parent = some [] := by decide

theorem null_child_is_present_before_graph_admission :
    readExpressionChildren? (memory 3 1 (some items) [none]) parent =
      some [parent.child none] ∧
    readExpressionChildren? (memory 3 1 (some items) []) parent = none := by decide

theorem missing_array_or_wrong_parent_is_refused :
    readExpressionChildren? (memory 3 1 none []) parent = none ∧
    readExpressionChildren? (memory 2 1 (some items) [some left]) parent = none := by decide

end ExpressionControls
end NativeFrames
end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.GSLT.LanguageDef.NativeOps
namespace NativeFrames
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Token)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
namespace OrdinaryBindings
namespace Controls

private def bindings : Address := ⟨81, 0, []⟩
private def shared : Address := ⟨82, 4, []⟩
private def owned : Address := ⟨83, 7, []⟩
private def payload : Address := ⟨84, 0, []⟩
private def old : Row := ⟨5, ⟨some payload, 13, 1⟩⟩
private def other : Row := ⟨6, ⟨some payload, 17, 2⟩⟩
private def cleared : Row := ⟨5, ⟨none, 19, 1⟩⟩

private def rowRecord (row : Row) : TargetValue :=
  .record "Binding" [.word row.identifier, .word 0, .reference none,
    .record "BindingValue" [.reference row.value.skeleton,
      .word row.value.epoch, .word row.value.kind]]

private def memory (count sharedCount : BitVec 64) (entries sharedEntries : Option Address)
    (sharedRows ownedRows : List Row) : TargetMemory :=
  ⟨fun storage index =>
    if storage = bindings.storage ∧ index = bindings.element then
      some (.record "Bindings" [.reference none, .reference entries, .word count, .word count,
        .reference none, .word 0, .word 0, .byte 0,
        .record "rhs_variable_bloom" [.byte 0, .byte 0, .byte 0], .word 0, .word 0,
        .reference none, .reference none, .reference sharedEntries, .word sharedCount,
        .word sharedCount, .reference none])
    else if storage = shared.storage ∧ shared.element ≤ index then
      (sharedRows[index - shared.element]?).map rowRecord
    else if storage = owned.storage ∧ owned.element ≤ index then
      (ownedRows[index - owned.element]?).map rowRecord
    else none,
    fun _ => none⟩

theorem shared_prefix_and_owned_suffix_keep_order_and_duplicates :
    readback? (memory 4 2 (some owned) (some shared) [old, other] [old, cleared]) bindings =
      some [old, other, old, cleared] := by decide

theorem last_null_row_shadows_shared_value :
    lookup? [old, other, cleared] 5 = some cleared.value ∧
      (lookup? [old, other, cleared] 5).bind BindingValueView.payload = none ∧
      lookup? [old, other] 5 = some old.value ∧ lookup? [old, other] 9 = none := by decide

theorem empty_segments_need_no_pointer :
    readback? (memory 0 0 none none [] []) bindings = some [] ∧
    readback? (memory 1 1 none (some shared) [old] []) bindings = some [old] ∧
    readback? (memory 1 0 (some owned) none [] [old]) bindings = some [old] := by decide

theorem inconsistent_counts_are_refused :
    readback? (memory 1 2 (some owned) (some shared) [old, other] []) bindings = none ∧
    readHeader? (memory (2 ^ 32) 0 none none [] []) bindings = none := by decide

theorem missing_or_inadmissible_row_is_not_silently_dropped :
    readback? (memory 2 1 (some owned) (some shared) [old] []) bindings = none ∧
    readback? (memory 1 0 none none [] [old]) bindings = none ∧
    readback? (memory 1 1 none none [old] []) bindings = none ∧
    readback? (memory 1 0 (some owned) none [] [⟨5, ⟨some payload, 0, 3⟩⟩]) bindings =
      none := by decide

end Controls
end OrdinaryBindings
end NativeFrames
end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.GSLT.LanguageDef.NativeOps
namespace NativeFrames
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Token)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
namespace ReadbackControls

private def address : Address := ⟨19, 0, []⟩

theorem directory_clock_survives_empty_inventory :
    readFrameDirectory? (.record "BindingsFrameDirectoryStateView"
      [.reference (some ⟨1, 0, []⟩), .reference (some ⟨2, 0, []⟩),
       .word 0, .word 12, .word 31]) = some ⟨⟨1, 0, []⟩, some ⟨2, 0, []⟩, 0, 12, 31⟩ ∧
    (readFrameDirectory? (.record "BindingsFrameDirectoryStateView"
      [.reference (some ⟨1, 0, []⟩), .reference none, .word 0, .word 0, .word 31])).isSome =
        false := by decide

private def header (token : Token) (slots schemaSlots clock boundary : Nat)
    (hasBoundary : Bool := true) : TargetValue :=
  .record "BindingsFrameStateView"
    [.reference (some ⟨1, 0, []⟩), .reference (some ⟨2, 0, []⟩),
     .record "BindingsFrameRef" [.word (encode token)],
     .word (BitVec.ofNat 64 slots), .word (BitVec.ofNat 64 schemaSlots),
     .word 7, .word (BitVec.ofNat 64 clock), .word (BitVec.ofNat 64 boundary),
     .bool hasBoundary, .bool true, .bool false]

private def value (skeleton : Option Address) (epoch kind : Nat) : TargetValue :=
  .record "BindingValue" [.reference skeleton, .word (BitVec.ofNat 64 epoch),
    .word (BitVec.ofNat 64 kind)]

private def slot (token : Token) (source spelling : Nat) (declared : Bool)
    (payload : TargetValue) (version : Nat) (qualified : Option Nat := none) : TargetValue :=
  .record "BindingsFrameSlotStateView"
    [.word (BitVec.ofNat 64 source),
     .word (BitVec.ofNat 64 (qualified.getD ((encode token).toNat * 2 ^ 32 + source))),
     .word (BitVec.ofNat 64 spelling), .reference none, .bool declared,
     payload, .word (BitVec.ofNat 64 version)]

private def sparseRows : List TargetValue :=
  [slot ⟨5, 2⟩ 9 3 true (value none 3145740 2) 13,
   slot ⟨5, 2⟩ 27 3 true (value (some address) 0 0) 16]

private def directory (count revision clock : Nat) : TargetValue :=
  .record "BindingsFrameDirectoryStateView"
    [.reference (some ⟨1, 0, []⟩), .reference (some ⟨2, 0, []⟩),
     .word (BitVec.ofNat 64 count), .word (BitVec.ofNat 64 revision),
     .word (BitVec.ofNat 64 clock)]

/-- Only the observed Atom-header prefix is supplied here. A missing VarId
field remains a missing reading, and no ownership is inferred from storage. -/
private def variableMemory (kind : BitVec 64) (identifier : Option (BitVec 64)) : TargetMemory :=
  ⟨fun storage position => if storage = address.storage ∧ position = 0 then
      some (.record "Atom" ([.word kind, .word 0] ++
        identifier.toList.map TargetValue.word)) else none,
    fun _ => none⟩

theorem contextual_variable_replaces_the_previous_epoch :
    readVariableId? (variableMemory 1 (some (BitVec.ofNat 64 (99 * 2 ^ 32 + 9))))
      ⟨some address, encode ⟨5, 2⟩, 1⟩ =
        some (BitVec.ofNat 64 ((encode ⟨5, 2⟩).toNat * 2 ^ 32 + 9)) ∧
    readVariableId? (variableMemory 1 (some (BitVec.ofNat 64 (99 * 2 ^ 32 + 9))))
      ⟨some address, encode ⟨6, 3⟩, 2⟩ =
        some (BitVec.ofNat 64 ((encode ⟨6, 3⟩).toNat * 2 ^ 32 + 9)) := by decide

theorem materialized_variable_keeps_its_full_identifier :
    readVariableId? (variableMemory 1 (some (BitVec.ofNat 64 (99 * 2 ^ 32 + 9))))
      ⟨some address, encode ⟨5, 2⟩, 0⟩ =
        some (BitVec.ofNat 64 (99 * 2 ^ 32 + 9)) := by decide

theorem sparse_variable_edges_keep_exact_slot_history :
    ((readDirectory? (directory 1 7 17) 6 [(header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).bind
      (fun image => image.readVariableSlot? (variableMemory 1 (some 9))
        ⟨some address, encode ⟨5, 2⟩, 1⟩)) =
        some ⟨none, 13, 17, some 11⟩ ∧
    ((readDirectory? (directory 1 7 17) 6 [(header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).bind
      (fun image => image.readVariableSlot? (variableMemory 1 (some 27))
        ⟨some address, encode ⟨5, 2⟩, 2⟩)) =
        some ⟨some ⟨some address, 0, 0⟩, 16, 17, some 11⟩ := by decide

theorem identical_variable_pointer_keeps_context_and_selected_world :
    ((readDirectory? (directory 2 7 17) 7
      [(header ⟨5, 2⟩ 2 2 17 11, sparseRows),
       (header ⟨6, 3⟩ 1 1 17 12,
        [slot ⟨6, 3⟩ 9 3 true (value (some address) 0 0) 15])]).bind
      (fun image => image.readVariableSlot? (variableMemory 1 (some 9))
        ⟨some address, encode ⟨6, 3⟩, 1⟩)) =
        some ⟨some ⟨some address, 0, 0⟩, 15, 17, some 12⟩ ∧
    ((readDirectory? (directory 1 7 19) 6
      [(header ⟨5, 2⟩ 1 1 19 11,
        [slot ⟨5, 2⟩ 9 3 true (value (some address) 0 0) 19])]).bind
      (fun image => image.readVariableSlot? (variableMemory 1 (some 9))
        ⟨some address, encode ⟨5, 2⟩, 1⟩)) =
        some ⟨some ⟨some address, 0, 0⟩, 19, 19, some 11⟩ := by decide

theorem stale_missing_or_ambient_variable_edges_are_refused :
    ((readDirectory? (directory 1 7 17) 6 [(header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).bind
      (fun image => image.readVariableSlot? (variableMemory 1 (some 9))
        ⟨some address, encode ⟨5, 1⟩, 1⟩)) = none ∧
    ((readDirectory? (directory 1 7 17) 6 [(header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).bind
      (fun image => image.readVariableSlot? (variableMemory 1 (some 10))
        ⟨some address, encode ⟨5, 2⟩, 1⟩)) = none ∧
    ((readDirectory? (directory 1 7 17) 6 [(header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).bind
      (fun image => image.readVariableSlot? (variableMemory 1 (some 9))
        ⟨some address, 0, 0⟩)) = none := by decide

theorem malformed_or_allocating_variable_edges_are_refused :
    readVariableId? (variableMemory 1 none) ⟨some address, 0, 0⟩ = none ∧
    readVariableId? (variableMemory 1 (some 9)) ⟨none, 0, 0⟩ = none ∧
    readVariableId? (variableMemory 1 (some 9)) ⟨some address, 0, 3⟩ = none ∧
    readVariableId? (variableMemory 1 (some 0)) ⟨some address, encode ⟨5, 2⟩, 1⟩ = none ∧
    readVariableId? (variableMemory 0 none) ⟨some address, 0, 0⟩ = none := by decide

theorem directory_assembly_keeps_native_handle_and_clock :
    ((readDirectory? (directory 1 7 17) 6 [(header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).map
      (fun readback => readback.toImage.readSlot? (Token.ref ⟨5, 2⟩ 0))) =
      some (some ⟨none, 13, 17, some 11⟩) ∧
    ((readDirectory? (directory 0 12 31) 0 []).map
      (fun readback => readback.toImage.writeClock)) = some 31 := by decide

theorem partial_duplicate_or_mismatched_directory_is_refused :
    (readDirectory? (directory 1 7 17) 6 []).isSome = false ∧
    (readDirectory? (directory 2 7 17) 6
      [(header ⟨5, 2⟩ 2 2 17 11, sparseRows),
       (header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).isSome = false ∧
    (readDirectory? (directory 1 7 19) 6
      [(header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).isSome = false ∧
    (readDirectory? (directory 1 7 17) 5
      [(header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).isSome = false := by decide

namespace AliasControls

open RootResolution
open Mettapedia.Machines.ReadOnlyQuery (run checkReads)

private def term : BindingValueView := ⟨some ⟨20, 0, []⟩, 0, 0⟩
private def first : BindingValueView := ⟨some address, 0, 0⟩
private def duplicate : BindingValueView := ⟨some ⟨21, 0, []⟩, 0, 0⟩
private def second : BindingValueView := ⟨some ⟨22, 0, []⟩, 0, 0⟩
private def framed : BindingValueView := ⟨some address, encode ⟨5, 2⟩, 1⟩
private def stale : BindingValueView := ⟨some address, encode ⟨5, 1⟩, 1⟩

private def inventory : DirectoryReadback :=
  ((readDirectory? (directory 1 7 17) 6
    [(header ⟨5, 2⟩ 2 2 17 11, sparseRows)]).get (by decide +kernel))

/-- A real ordinary-row memory view is present beside three variable headers
and a terminal expression header. The terminal's children need no readback. -/
private def memory (rows : List OrdinaryBindings.Row) : TargetMemory :=
  ⟨fun storage index =>
    if storage = 1 ∧ index = 0 then
      some (.record "Bindings" [.reference none, .reference (some ⟨23, 0, []⟩),
        .word (BitVec.ofNat 64 rows.length), .word 0,
        .reference none, .word 0, .word 0, .byte 0,
        .record "rhs_variable_bloom" [.byte 0, .byte 0, .byte 0], .word 0, .word 0,
        .reference none, .reference none, .reference none, .word 0, .word 0, .reference none])
    else if storage = 23 then
      (rows[index]?).map fun row => .record "Binding" [.word row.identifier, .word 0,
        .reference none, .record "BindingValue" [.reference row.value.skeleton,
          .word row.value.epoch, .word row.value.kind]]
    else if index ≠ 0 then none
    else if storage = 19 ∨ storage = 21 then some (.record "Atom" [.word 1, .word 0, .word 27])
    else if storage = 22 then some (.record "Atom" [.word 1, .word 0, .word 28])
    else if storage = 20 then some (.record "Atom" [.word 3])
    else none,
    fun _ => none⟩

private def current (rows : List OrdinaryBindings.Row) : Query.Key → Query.Reply :=
  Query.store (memory rows) (lookup inventory rows)

theorem actual_rows_feed_the_alias_query :
    OrdinaryBindings.readback? (memory [⟨27, term⟩]) inventory.directory.bindings =
      some [⟨27, term⟩] ∧
    ((Query.readStore? (memory [⟨27, term⟩]) inventory).map fun provider =>
      (run provider (Query.walk 2 framed)).answer) = some (.resolved term) := by decide +kernel

theorem frame_to_ordinary_to_terminal_preserves_context :
    Query.resolve (memory [⟨27, term⟩]) (lookup inventory [⟨27, term⟩]) 2 framed =
      .resolved term ∧
    Query.resolve (memory [⟨27, term⟩]) (lookup inventory [⟨27, term⟩]) 1 framed =
      .refused := by decide +kernel

theorem terminal_children_are_not_traversed :
    (run (current []) (Query.walk 0 term)).answer = .resolved term ∧
    (run (current []) (Query.walk 0 term)).reads =
      [(.field ⟨20, 0, [0]⟩, .field (some 3))] := by decide +kernel

theorem zero_allowance_still_distinguishes_open_self_and_proper_alias :
    (run (current []) (Query.walk 0 first)).answer = .resolved first ∧
    (run (current [⟨27, duplicate⟩]) (Query.walk 0 first)).answer = .resolved first ∧
    (run (current [⟨27, term⟩]) (Query.walk 0 first)).answer = .refused ∧
    first ≠ duplicate := by decide +kernel

theorem longer_cycle_refuses_without_reclassifying_self_links :
    (run (current [⟨27, second⟩, ⟨28, first⟩]) (Query.walk 7 first)).answer = .refused ∧
    (run (current [⟨27, duplicate⟩]) (Query.walk 7 first)).answer = .resolved first := by decide +kernel

theorem stale_frame_cannot_use_an_ordinary_impostor :
    (run (current [⟨BitVec.ofNat 64 ((encode ⟨5, 1⟩).toNat * 2 ^ 32 + 27), term⟩])
      (Query.walk 0 stale)).answer = .resolved stale := by decide +kernel

theorem private_variant_ids_are_ordinary :
    hasFrame (BitVec.ofNat 64 (0xFFFFA11A * 2 ^ 32 + 27)) = false ∧
    lookup inventory [⟨BitVec.ofNat 64 (0xFFFFA11A * 2 ^ 32 + 27), term⟩]
      (BitVec.ofNat 64 (0xFFFFA11A * 2 ^ 32 + 27)) = some term := by decide +kernel

theorem empty_newest_row_does_not_reveal_the_old_alias :
    (run (current [⟨27, term⟩, ⟨27, ⟨none, 19, 1⟩⟩]) (Query.walk 1 first)).answer =
      .resolved first := by decide +kernel

theorem missing_header_is_not_an_open_variable :
    (run (current []) (Query.walk 1 ⟨some ⟨99, 0, []⟩, 0, 0⟩)).answer = .unreadable ∧
    (run (current []) (Query.walk 1 first)).answer = .resolved first := by decide +kernel

private def saved := Mettapedia.Machines.ReadCertifiedQueryReuse.populate
  Query.family (9 : Nat) (1, first) (current [⟨27, duplicate⟩])

theorem validated_cache_keeps_pointer_identity_and_ignores_unread_rows :
    Mettapedia.Machines.ReadCertifiedQueryReuse.reuse Query.family 9 (1, first)
      (current [⟨27, duplicate⟩, ⟨28, term⟩]) saved = (.resolved first, 0) ∧
    Mettapedia.Machines.ReadCertifiedQueryReuse.reuse Query.family 9 (1, duplicate)
      (current [⟨27, duplicate⟩]) saved = (.resolved duplicate, 1) := by decide +kernel

theorem changed_binding_or_owner_recomputes :
    Mettapedia.Machines.ReadCertifiedQueryReuse.reuse Query.family 9 (1, first)
      (current [⟨27, term⟩]) saved = (.resolved term, 1) ∧
    Mettapedia.Machines.ReadCertifiedQueryReuse.reuse Query.family 10 (1, first)
      (current [⟨27, duplicate⟩]) saved = (.resolved first, 1) := by decide +kernel

theorem cursor_completion_agrees_with_the_mixed_alias_walk :
    ((Mettapedia.Machines.Cursor.ReadOnlyQuery.completed? (current [⟨27, term⟩])
      (Query.advance (memory [⟨27, term⟩]) inventory [⟨27, term⟩] 2 20 framed).2).map
        Mettapedia.Machines.ReadOnlyQuery.Observation.answer) = some (.resolved term) ∧
    ((Mettapedia.Machines.Cursor.ReadOnlyQuery.completed? (current [⟨27, term⟩])
      (Query.advance (memory [⟨27, term⟩]) inventory [⟨27, term⟩] 2 2 framed).2).map
        Mettapedia.Machines.ReadOnlyQuery.Observation.answer) = none := by decide +kernel

/-- The absence read was already performed, even though the cursor has not
yet returned. A later binding invalidates this retained continuation. -/
theorem performed_absence_rejects_a_revised_binding :
    checkReads (current [⟨27, term⟩])
      (Mettapedia.Machines.Cursor.ReadOnlyQuery.recorded (current [])
        (Query.advance (memory []) inventory [] 1 3 first).2) = false := by decide +kernel

theorem refused_revision_keeps_the_complete_saved_cursor :
    Mettapedia.Machines.Cursor.ReadOnlyQuery.resumeValidated (current [])
      (current [⟨27, term⟩]) 20 (Query.advance (memory []) inventory [] 1 3 first) =
        .error (Query.advance (memory []) inventory [] 1 3 first) :=
  Mettapedia.Machines.Cursor.ReadOnlyQuery.resumeValidated_refused _ _ _ _
    performed_absence_rejects_a_revised_binding

end AliasControls

/-- Sparse authored IDs and identical spelling remain distinct coordinates. -/
theorem sparse_inventory_keeps_unbound_history :
    ((readFrame? (header ⟨5, 2⟩ 2 2 17 11) sparseRows).map
      (fun readback => readback.toEntry.readSlot? readback.view.writeClock 0)) =
        some (some ⟨none, 13, 17, some 11⟩) ∧
    ((readFrame? (header ⟨5, 2⟩ 2 2 17 11) sparseRows).map
      (fun readback => readback.toEntry.readSlot? readback.view.writeClock 1)) =
        some (some ⟨some ⟨some address, 0, 0⟩, 16, 17, some 11⟩) := by decide

theorem unbound_sidecar_keeps_epoch_and_kind :
    ((readFrame? (header ⟨5, 2⟩ 2 2 17 11) sparseRows).bind
      (fun readback => readback.slots[0]?)).map FrameSlotView.value =
        some ⟨none, BitVec.ofNat 64 3145740, 2⟩ := by decide

/-- Neither a materialized epoch nor a boundary beyond the current clock is
silently normalized. Any protocol restriction on them is a further law. -/
theorem independent_raw_metadata_survives :
    ((readFrame? (header ⟨5, 2⟩ 1 1 3 23)
      [slot ⟨5, 2⟩ 9 0 true (value (some address) 41 0) 0]).map
        (fun readback => readback.toEntry.readSlot? readback.view.writeClock 0)) =
      some (some ⟨some ⟨some address, 41, 0⟩, 0, 3, some 23⟩) := by decide

theorem identical_skeletons_keep_distinct_contexts :
    readBindingValue? (value (some address) 1048581 1) ≠
      readBindingValue? (value (some address) 2097157 1) ∧
    readBindingValue? (value (some address) 0 1) =
      some ⟨some address, 0, 1⟩ := by decide

private def grownRows : List TargetValue :=
  [slot ⟨8, 1⟩ 1 3 true (value none 0 0) 2,
   slot ⟨8, 1⟩ 2 0 false (value none 0 0) 4,
   slot ⟨8, 1⟩ 3 0 false (value (some address) 0 0) 5]

theorem grown_slots_need_no_synthetic_presentation :
    (readFrame? (header ⟨8, 1⟩ 3 1 7 2) grownRows).isSome = true ∧
    ((readFrame? (header ⟨8, 1⟩ 3 1 7 2) grownRows).map
      (fun readback => readback.toEntry.readSlot? readback.view.writeClock 1)) =
        some (some ⟨none, 4, 7, some 2⟩) := by decide

theorem partial_or_inconsistent_inventory_is_refused :
    (readFrame? (header ⟨5, 2⟩ 2 2 17 11) (sparseRows.take 1)).isSome = false ∧
    (readFrame? (header ⟨5, 2⟩ 1 1 17 11)
      [slot ⟨5, 2⟩ 9 0 true (value none 0 0) 13 (some 9)]).isSome = false ∧
    (readFrame? (header ⟨5, 2⟩ 2 2 17 11)
      [slot ⟨5, 2⟩ 9 0 true (value none 0 0) 13,
       slot ⟨5, 2⟩ 9 0 true (value none 0 0) 16]).isSome = false ∧
    (readFrame? (header ⟨8, 1⟩ 3 1 7 2)
      [slot ⟨8, 1⟩ 9 3 true (value none 0 0) 2,
       slot ⟨8, 1⟩ 2 0 false (value none 0 0) 4,
       slot ⟨8, 1⟩ 3 0 false (value none 0 0) 5]).isSome = false ∧
    (readFrame? (header ⟨8, 1⟩ 0 0 0 0) []).isSome = false := by decide

private def activationRecord (boundary : Nat)
    (epoch : BitVec 64 := encode ⟨5, 2⟩) : TargetValue :=
  .record "BindingsActivationView"
    [.reference (some ⟨60, 0, []⟩), .reference (some ⟨61, 0, []⟩),
     .record "BindingsFrameRef" [.word (encode ⟨5, 2⟩)], .word 2, .word 9, .bool false,
     .word epoch, .word 1, .word 0, .word (BitVec.ofNat 64 boundary)]

private def activationMemory (boundary : Nat) (flags : BitVec 64)
    (missing : Bool := false) (epoch : BitVec 64 := encode ⟨5, 2⟩) : TargetMemory :=
  ⟨fun storage position =>
    if storage = 60 then
      if position = 0 then some (.word 9)
      else if position = 1 ∧ !missing then some (.word 27) else none
    else if position = 0 then
      if storage = 1 then
        some (.record "Bindings" [.reference none, .reference none, .word 0])
      else if storage = 40 then
        some (.record "BindingsTermCursorContextV1"
          [.reference (some ⟨1, 0, []⟩), .reference (some ⟨50, 0, []⟩)])
      else if storage = 41 then
        some (.record "BindingsTermCursorContextV1"
          [.reference (some ⟨1, 0, []⟩), .reference (some ⟨51, 0, []⟩)])
      else if storage = 50 ∨ storage = 51 then some (activationRecord boundary epoch)
      else if storage = 100 then some (.record "Atom" [.word 1, .word 1, .word 9])
      else if storage = 101 then some (.record "Atom" [.word 1, .word 1, .word 27])
      else if storage = 102 then some (.record "Atom" [.word 1, .word 1, .word 32])
      else if storage = address.storage then some (.record "Atom" [.word 3, .word flags])
      else none
    else none,
    fun _ => none⟩

private def activationRows (payloadKind : Nat) : List TargetValue :=
  [slot ⟨5, 2⟩ 9 3 true (value none 0 0) 13,
   slot ⟨5, 2⟩ 27 3 true (value (some address) 0 payloadKind) 16]

private def activationProbe (boundary root scope context payloadKind : Nat)
    (flags : BitVec 64) (missing : Bool := false) : Option Activation.Action :=
  (readDirectory? (directory 1 7 17) 6
    [(header ⟨5, 2⟩ 2 2 17 11, activationRows payloadKind)]).bind fun image =>
    Activation.readContextRoot? (activationMemory boundary flags missing) image
      ⟨context, 0, []⟩ ⟨some ⟨root, 0, []⟩, some ⟨scope, 0, []⟩⟩

private def activationHeader : FrameStateView :=
  ⟨⟨1, 0, []⟩, ⟨2, 0, []⟩, ⟨5, 2⟩, 2, 2, 7, 17, 11, true, true, false⟩

private def activationSlots (kind : Fin 3) : List FrameSlotView :=
  [⟨9, BitVec.ofNat 64 ((encode ⟨5, 2⟩).toNat * 2 ^ 32 + 9), 3, none, true,
      ⟨none, 0, 0⟩, 13⟩,
   ⟨27, BitVec.ofNat 64 ((encode ⟨5, 2⟩).toNat * 2 ^ 32 + 27), 3, none, true,
      ⟨some address, 0, BitVec.ofNat 64 kind.val⟩, 16⟩]

private def activationFrame (kind : Fin 3) : FrameReadback where
  view := activationHeader
  slots := activationSlots kind
  admitted := by
    obtain ⟨kind, bound⟩ := kind
    have cases : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · exact (by decide : InventoryAgrees activationHeader (activationSlots (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3)))
    · exact (by decide : InventoryAgrees activationHeader (activationSlots (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ : Fin 3)))
    · exact (by decide : InventoryAgrees activationHeader (activationSlots (⟨2, Nat.lt_succ_self 2⟩ : Fin 3)))

private def activationDirectory (kind : Fin 3) : DirectoryReadback where
  directory := ⟨⟨1, 0, []⟩, some ⟨2, 0, []⟩, 1, 7, 17⟩
  capacity := 6
  frames := [activationFrame kind]
  admitted := by
    simp [DirectoryAgrees, FrameDirectoryView.Admissible, FrameStateView.Compatible,
      activationFrame, activationHeader]

private theorem activationHeader_read :
    readFrameState? (header ⟨5, 2⟩ 2 2 17 11) = some activationHeader := by
  change (decode? (encode ⟨5, 2⟩)).bind (fun token =>
    if ({ activationHeader with token := token } : FrameStateView).Admissible
      then some { activationHeader with token := token } else none) = _
  rw [decode_encode (by decide : Representable ⟨5, 2⟩)]
  change (if activationHeader.Admissible then some activationHeader else none) = _
  rw [if_pos (by decide : activationHeader.Admissible)]

private theorem activationSlots_read (kind : Fin 3) :
    readFrameSlots? (activationRows kind.val) = some (activationSlots kind) := by
  obtain ⟨kind, bound⟩ := kind
  have cases : kind = 0 ∨ kind = 1 ∨ kind = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact (by decide : readFrameSlots? (activationRows 0) = some (activationSlots (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3)))
  · exact (by decide : readFrameSlots? (activationRows 1) = some (activationSlots (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ : Fin 3)))
  · exact (by decide : readFrameSlots? (activationRows 2) = some (activationSlots (⟨2, Nat.lt_succ_self 2⟩ : Fin 3)))

private theorem activationFrame_read (kind : Fin 3) :
    readFrame? (header ⟨5, 2⟩ 2 2 17 11) (activationRows kind.val) =
      some (activationFrame kind) := by
  unfold readFrame?
  rw [activationHeader_read, activationSlots_read]
  dsimp only [Bind.bind, Option.bind]
  split
  · rfl
  · next refused => exact False.elim (refused (activationFrame kind).admitted)

private theorem activationDirectory_read (kind : Fin 3) :
    readDirectory? (directory 1 7 17) 6
      [(header ⟨5, 2⟩ 2 2 17 11, activationRows kind.val)] =
        some (activationDirectory kind) := by
  have directoryRead : readFrameDirectory? (directory 1 7 17) =
      some (activationDirectory kind).directory := by
    change readFrameDirectory? (directory 1 7 17) =
      some ⟨⟨1, 0, []⟩, some ⟨2, 0, []⟩, 1, 7, 17⟩
    decide
  unfold readDirectory?
  rw [directoryRead]
  simp only [readFrames?, activationFrame_read]
  dsimp only [Bind.bind, Option.bind, Pure.pure]
  split
  · rfl
  · next refused => exact False.elim (refused (activationDirectory kind).admitted)

private def activationView (boundary : Nat)
    (epoch : BitVec 64 := encode ⟨5, 2⟩) : Activation.View :=
  ⟨some ⟨60, 0, []⟩, some ⟨61, 0, []⟩, encode ⟨5, 2⟩, 2, 9, false,
    epoch, 1, 0, boundary⟩

private def activationInventory (boundary : Nat) (bounded : boundary < 2 ^ 64) :
    Activation.Inventory where
  view := activationView boundary
  sources := [9, 27]
  admitted := by
    simp [Activation.InventoryAgrees, activationView, Activation.View.Admissible,
      encode, encoding, classOneFirst]
    exact bounded

private theorem activationView_read (boundary : Nat) (bounded : boundary < 2 ^ 64) :
    Activation.readView? (activationRecord boundary) = some (activationView boundary) := by
  have boundaryWord : (BitVec.ofNat 64 boundary).toNat = boundary := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
  have valid : (activationView boundary).Admissible :=
    (activationInventory boundary bounded).admitted.1
  unfold activationRecord Activation.readView?
  simp only [boundaryWord]
  change (if (activationView boundary).Admissible then some (activationView boundary) else none) = _
  rw [if_pos valid]

private theorem activationInventory_read (boundary : Nat) (bounded : boundary < 2 ^ 64)
    (flags : BitVec 64) :
    Activation.readInventory? (activationMemory boundary flags) (activationView boundary) =
      some (activationInventory boundary bounded) := by
  have ids : Activation.readSourceIds? (activationMemory boundary flags)
      (activationView boundary) = some [9, 27] := by rfl
  unfold Activation.readInventory?
  rw [ids]
  dsimp only [Bind.bind, Option.bind]
  split
  · rfl
  · next refused => exact False.elim (refused (activationInventory boundary bounded).admitted)

private theorem activation_available (kind : Fin 3) (boundary : Nat) :
    (activationView boundary).available (activationDirectory kind) 0 = true := by
  have authority := Activation.View.authorityPresent_current (activationView boundary)
    (activationDirectory kind) (activationFrame kind) (by simp [activationDirectory]) rfl
  unfold Activation.View.available
  apply decide_eq_true
  exact ⟨(by change encode ⟨5, 2⟩ ≠ 0; decide), Or.inl rfl, Nat.zero_le _,
    Or.inr ⟨rfl, rfl, authority⟩⟩

private theorem activationScope_inventory (kind : Fin 3) (boundary : Nat)
    (bounded : boundary < 2 ^ 64) (flags : BitVec 64) (root scope : Nat)
    (selected : scope = 50 ∨ scope = 51) (missing : Bool := false) :
    Activation.readScope? (activationMemory boundary flags missing) (activationDirectory kind)
      ⟨some ⟨1, 0, []⟩, some ⟨scope, 0, []⟩⟩
      ⟨some ⟨root, 0, []⟩, some ⟨scope, 0, []⟩⟩ =
        Activation.readInventory? (activationMemory boundary flags missing) (activationView boundary) := by
  rcases selected with rfl | rfl
  all_goals
    change (Activation.readView? (activationRecord boundary)).bind (fun view =>
      if view.available (activationDirectory kind) 0
        then Activation.readInventory? (activationMemory boundary flags missing) view
        else none) = _
    rw [activationView_read boundary bounded]
    dsimp only [Bind.bind, Option.bind]
    rw [activation_available]
    rfl

private theorem activationContextRoot_eq (kind : Fin 3) (boundary : Nat)
    (bounded : boundary < 2 ^ 64) (flags : BitVec 64) (root scope context : Nat)
    (selected : (scope = 50 ∧ context = 40) ∨ (scope = 51 ∧ context = 41))
    (missing : Bool := false) :
    Activation.readContextRoot? (activationMemory boundary flags missing)
      (activationDirectory kind) ⟨context, 0, []⟩
      ⟨some ⟨root, 0, []⟩, some ⟨scope, 0, []⟩⟩ =
        (Activation.readInventory? (activationMemory boundary flags missing)
          (activationView boundary)).bind fun inventory =>
            (Activation.readValue? (activationDirectory kind)
              (activationMemory boundary flags missing) inventory ⟨root, 0, []⟩).bind
                (Activation.nextAction? (activationMemory boundary flags missing)
                  ⟨some ⟨root, 0, []⟩, some ⟨scope, 0, []⟩⟩) := by
  have sameScope : scope = 50 ∨ scope = 51 := selected.imp And.left And.left
  have contextRead : Activation.readContextRoot? (activationMemory boundary flags missing)
      (activationDirectory kind) ⟨context, 0, []⟩
      ⟨some ⟨root, 0, []⟩, some ⟨scope, 0, []⟩⟩ =
        Activation.readAuthoredRoot? (activationMemory boundary flags missing)
          (activationDirectory kind) ⟨some ⟨1, 0, []⟩, some ⟨scope, 0, []⟩⟩
          ⟨some ⟨root, 0, []⟩, some ⟨scope, 0, []⟩⟩ := by
    rcases selected with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rw [contextRead]
  unfold Activation.readAuthoredRoot?
  rw [activationScope_inventory kind boundary bounded flags root scope sameScope missing]
  rfl

private theorem activationProbe_read (kind : Fin 3) (boundary root scope context : Nat)
    (flags : BitVec 64) (missing : Bool := false) :
    activationProbe boundary root scope context kind.val flags missing =
      Activation.readContextRoot? (activationMemory boundary flags missing)
        (activationDirectory kind) ⟨context, 0, []⟩
        ⟨some ⟨root, 0, []⟩, some ⟨scope, 0, []⟩⟩ := by
  unfold activationProbe
  rw [activationDirectory_read]
  rfl

private theorem activation_bound_lookup (kind : Fin 3) (boundary : Nat)
    (bounded : boundary < 2 ^ 64) (flags : BitVec 64) :
    Activation.readValue? (activationDirectory kind) (activationMemory boundary flags)
      (activationInventory boundary bounded) ⟨101, 0, []⟩ =
        some (.known (if boundary < 16 then
          some ⟨some address, 0, BitVec.ofNat 64 kind.val⟩ else none)) := by
  have read := Activation.readValue?_source_slot (activationDirectory kind)
    (activationMemory boundary flags) (activationInventory boundary bounded) ⟨101, 0, []⟩
    (activationFrame kind) (by simp [activationDirectory]) (⟨1, Nat.lt_succ_self 1⟩ : Fin 2) rfl
    (by change (27 : BitVec 64) ∈ [9, 27]; simp) (by rfl) (by rfl)
  exact read

private theorem activation_open_lookup (kind : Fin 3) (boundary : Nat)
    (bounded : boundary < 2 ^ 64) (flags : BitVec 64) :
    Activation.readValue? (activationDirectory kind) (activationMemory boundary flags)
      (activationInventory boundary bounded) ⟨100, 0, []⟩ = some (.known none) := by
  have read := Activation.readValue?_source_slot (activationDirectory kind)
    (activationMemory boundary flags) (activationInventory boundary bounded) ⟨100, 0, []⟩
    (activationFrame kind) (by simp [activationDirectory]) (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2) rfl
    (by change (9 : BitVec 64) ∈ [9, 27]; simp) (by rfl) (by rfl)
  change Activation.readValue? (activationDirectory kind) (activationMemory boundary flags)
    (activationInventory boundary bounded) ⟨100, 0, []⟩ =
      some (.known (if boundary < 13 then none else none)) at read
  simpa only [ite_self] using read

private theorem activation_unknown_lookup (kind : Fin 3) (boundary : Nat)
    (bounded : boundary < 2 ^ 64) (flags : BitVec 64) :
    Activation.readValue? (activationDirectory kind) (activationMemory boundary flags)
      (activationInventory boundary bounded) ⟨102, 0, []⟩ = some .unknown := by
  apply Activation.readValue?_unknown _ _ _ _ 32 (by rfl)
  change (32 : BitVec 64) ∉ [9, 27]
  decide

/-- A complete context-record, view-record, inventory and Atom-field read
reaches the source-slot theorem before choosing the next native action. -/
private theorem activation_bound_pipeline (kind : Fin 3) (boundary : Nat)
    (bounded : boundary < 2 ^ 64) (flags : BitVec 64) (scope context : Nat)
    (selected : (scope = 50 ∧ context = 40) ∨ (scope = 51 ∧ context = 41)) :
    activationProbe boundary 101 scope context kind.val flags =
      Activation.nextAction? (activationMemory boundary flags)
        ⟨some ⟨101, 0, []⟩, some ⟨scope, 0, []⟩⟩
          (.known (if boundary < 16 then
            some ⟨some address, 0, BitVec.ofNat 64 kind.val⟩ else none)) := by
  rw [activationProbe_read kind, activationContextRoot_eq kind boundary bounded flags
    101 scope context selected, activationInventory_read boundary bounded flags]
  dsimp only [Option.bind]
  rw [activation_bound_lookup kind boundary bounded flags]

/-- Equal view contents do not replace the native pointer-equality check. -/
theorem activation_same_metadata_requires_selected_scope :
    activationProbe 11 101 50 40 0 0 = some (.outer address) ∧
    activationProbe 11 101 51 40 0 0 = none ∧
    activationProbe 11 101 51 41 0 0 = some (.outer address) := by
  constructor
  · rw [activation_bound_pipeline (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 11 (by decide) 0 50 40 (Or.inl ⟨rfl, rfl⟩)]
    rfl
  constructor
  · rw [activationProbe_read (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3)]
    change Activation.readAuthoredRoot? (activationMemory 11 0) (activationDirectory 0)
      ⟨some ⟨1, 0, []⟩, some ⟨50, 0, []⟩⟩
      ⟨some ⟨101, 0, []⟩, some ⟨51, 0, []⟩⟩ = none
    unfold Activation.readAuthoredRoot?
    rw [Activation.readScope?_different_scope _ _ _ _ (by
      change (some ⟨50, 0, []⟩ : Option Address) ≠ some ⟨51, 0, []⟩
      decide)]
    rfl
  · rw [activation_bound_pipeline (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 11 (by decide) 0 51 41 (Or.inr ⟨rfl, rfl⟩)]
    rfl

/-- Known unbound and pre-boundary values stay scoped; only unknown sources
request the separate fallback. The frame's stored boundary is 11 throughout. -/
theorem activation_known_open_is_not_unknown :
    activationProbe 11 100 50 40 0 0 =
        some (.stay ⟨some ⟨100, 0, []⟩, some ⟨50, 0, []⟩⟩) ∧
    activationProbe 16 101 50 40 0 0 =
        some (.stay ⟨some ⟨101, 0, []⟩, some ⟨50, 0, []⟩⟩) ∧
    activationProbe 15 101 50 40 0 0 = some (.outer address) ∧
    activationProbe 11 102 50 40 0 0 = some .fallback := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [activationProbe_read (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3),
      activationContextRoot_eq (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 11 (by decide) 0 100 50 40 (Or.inl ⟨rfl, rfl⟩),
      activationInventory_read 11 (by decide) 0]
    dsimp only [Option.bind]
    rw [activation_open_lookup (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 11 (by decide) 0]
    rfl
  · rw [activation_bound_pipeline (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 16 (by decide) 0 50 40 (Or.inl ⟨rfl, rfl⟩)]
    rfl
  · rw [activation_bound_pipeline (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 15 (by decide) 0 50 40 (Or.inl ⟨rfl, rfl⟩)]
    rfl
  · rw [activationProbe_read (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3),
      activationContextRoot_eq (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 11 (by decide) 0 102 50 40 (Or.inl ⟨rfl, rfl⟩),
      activationInventory_read 11 (by decide) 0]
    dsimp only [Option.bind]
    rw [activation_unknown_lookup (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 11 (by decide) 0]
    rfl

theorem activation_contextual_flags_decide_the_next_action :
    activationProbe 11 101 50 40 1 1 = some .defer ∧
    activationProbe 11 101 50 40 2 1 = some .defer ∧
    activationProbe 11 101 50 40 1 0 = some (.outer address) ∧
    activationProbe 11 101 50 40 0 1 = some (.outer address) ∧
    activationProbe 11 101 50 40 1 (BitVec.ofNat 64 (2 ^ 32)) = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [activation_bound_pipeline (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ : Fin 3) 11 (by decide) 1 50 40 (Or.inl ⟨rfl, rfl⟩)]
    rfl
  · rw [activation_bound_pipeline (⟨2, Nat.lt_succ_self 2⟩ : Fin 3) 11 (by decide) 1 50 40 (Or.inl ⟨rfl, rfl⟩)]
    rfl
  · rw [activation_bound_pipeline (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ : Fin 3) 11 (by decide) 0 50 40 (Or.inl ⟨rfl, rfl⟩)]
    rfl
  · rw [activation_bound_pipeline (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 11 (by decide) 1 50 40 (Or.inl ⟨rfl, rfl⟩)]
    rfl
  · rw [activation_bound_pipeline (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ : Fin 3) 11 (by decide)
      (BitVec.ofNat 64 (2 ^ 32)) 50 40 (Or.inl ⟨rfl, rfl⟩)]
    rfl

theorem activation_missing_inventory_is_not_an_open_slot :
    activationProbe 11 100 50 40 0 0 true = none ∧
    Activation.readCursor? (.record "CettaGsltTermCursorV1"
      [.reference (some address), .reference (some ⟨50, 0, []⟩)]) =
        some ⟨some address, some ⟨50, 0, []⟩⟩ := by
  constructor
  · rw [activationProbe_read (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 11 100 50 40 0 true,
      activationContextRoot_eq (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3) 11 (by decide) 0 100 50 40 (Or.inl ⟨rfl, rfl⟩) true]
    have missing : Activation.readSourceIds? (activationMemory 11 0 true)
        (activationView 11) = none := by rfl
    unfold Activation.readInventory?
    rw [missing]
    rfl
  · rfl

private theorem activationView_fields (ids pointers : Option Address)
    (authority count first epoch kind firstEntry firstWrite : BitVec 64) (contiguous : Bool)
    (admitted : (⟨ids, pointers, authority, count.toNat, first, contiguous,
      epoch, kind, firstEntry.toNat, firstWrite.toNat⟩ : Activation.View).Admissible) :
    Activation.readView? (.record "BindingsActivationView"
      [.reference ids, .reference pointers, .record "BindingsFrameRef" [.word authority],
       .word count, .word first, .bool contiguous, .word epoch, .word kind,
       .word firstEntry, .word firstWrite]) =
        some ⟨ids, pointers, authority, count.toNat, first, contiguous,
          epoch, kind, firstEntry.toNat, firstWrite.toNat⟩ := by
  simp only [Activation.readView?, if_pos admitted]

private theorem activationInventory_fields (memory : TargetMemory) (inventory : Activation.Inventory)
    (observed : Activation.readSourceIds? memory inventory.view = some inventory.sources) :
    Activation.readInventory? memory inventory.view = some inventory := by
  unfold Activation.readInventory?
  rw [observed]
  dsimp only [Bind.bind, Option.bind]
  split
  · cases inventory; rfl
  · next refused => exact False.elim (refused inventory.admitted)

private theorem activationAuthority_zero (view : Activation.View) (image : DirectoryReadback)
    (zero : view.authority = 0) : view.authorityPresent image = false := by
  have decodeZero : decode? 0 = none := by decide
  unfold Activation.View.authorityPresent
  rw [zero, decodeZero]
  rfl

private def activationEmptyView : Activation.View :=
  ⟨none, none, 0, 0, 0, false, encode ⟨5, 2⟩, 1, 0, 0⟩

private def activationEmptyInventory : Activation.Inventory :=
  ⟨activationEmptyView, [], by
    have epochFits := encode_fits_uint32 (by decide : Representable ⟨5, 2⟩)
    simp [Activation.InventoryAgrees, activationEmptyView, Activation.View.Admissible]
    exact epochFits⟩

/-- A zero-count view needs neither arrays nor an available authority. Its
variable observation requests fallback rather than inventing an open slot. -/
theorem activation_zero_count_needs_no_authority :
    Activation.readView? (.record "BindingsActivationView"
      [.reference none, .reference none, .record "BindingsFrameRef" [.word 0],
       .word 0, .word 0, .bool false, .word (encode ⟨5, 2⟩), .word 1, .word 0, .word 0]) =
        some activationEmptyView ∧
    activationEmptyView.authorityPresent (activationDirectory ⟨0, Nat.zero_lt_succ 2⟩) = false ∧
    activationEmptyView.available (activationDirectory ⟨0, Nat.zero_lt_succ 2⟩) 0 = true ∧
    ((Activation.readInventory? (activationMemory 11 0 true) activationEmptyView).bind
      fun inventory => Activation.readValue? (activationDirectory ⟨0, Nat.zero_lt_succ 2⟩)
        (activationMemory 11 0 true) inventory ⟨101, 0, []⟩) = some .unknown := by
  refine ⟨?_, activationAuthority_zero _ _ rfl, ?_, ?_⟩
  · exact activationView_fields none none 0 0 0 (encode ⟨5, 2⟩) 1 0 0 false
      activationEmptyInventory.admitted.1
  · unfold Activation.View.available
    apply decide_eq_true
    exact ⟨(by change encode ⟨5, 2⟩ ≠ 0; decide), Or.inl rfl, Nat.zero_le _, Or.inl rfl⟩
  have inventoryRead : Activation.readInventory? (activationMemory 11 0 true)
      activationEmptyView = some activationEmptyInventory :=
    activationInventory_fields (activationMemory 11 0 true) activationEmptyInventory (by rfl)
  rw [inventoryRead]
  dsimp only [Option.bind]
  apply Activation.readValue?_unknown _ _ _ _ 27 (by rfl)
  exact List.not_mem_nil

private def activationOtherInventory : Activation.Inventory :=
  ⟨activationView 11 (encode ⟨6, 3⟩), [9, 27], by
    have authorityFits := encode_fits_uint32 (by decide : Representable ⟨5, 2⟩)
    have epochFits := encode_fits_uint32 (by decide : Representable ⟨6, 3⟩)
    simp [Activation.InventoryAgrees, activationView, Activation.View.Admissible]
    exact ⟨authorityFits, epochFits⟩⟩

/-- The actual view record may carry another epoch. Known-slot selection
still reads through its separate authority in the admitted current image. -/
theorem activation_authority_is_not_the_view_epoch :
    Activation.readView? (activationRecord 11 (encode ⟨6, 3⟩)) =
      some (activationView 11 (encode ⟨6, 3⟩)) ∧
    (activationView 11 (encode ⟨6, 3⟩)).authority ≠
      (activationView 11 (encode ⟨6, 3⟩)).epoch ∧
    Activation.readValue? (activationDirectory ⟨0, Nat.zero_lt_succ 2⟩)
      (activationMemory 11 0 false (encode ⟨6, 3⟩)) activationOtherInventory ⟨101, 0, []⟩ =
        some (.known (some ⟨some address, 0, 0⟩)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact activationView_fields (some ⟨60, 0, []⟩) (some ⟨61, 0, []⟩)
      (encode ⟨5, 2⟩) 2 9 (encode ⟨6, 3⟩) 1 0 11 false
      activationOtherInventory.admitted.1
  · intro same
    have tokens := encode_injective (by decide : Representable ⟨5, 2⟩)
      (by decide : Representable ⟨6, 3⟩) same
    exact (by decide : (⟨5, 2⟩ : Token) ≠ ⟨6, 3⟩) tokens
  · have lookup := Activation.readValue?_source_slot
      (activationDirectory ⟨0, Nat.zero_lt_succ 2⟩)
      (activationMemory 11 0 false (encode ⟨6, 3⟩)) activationOtherInventory ⟨101, 0, []⟩
      (activationFrame ⟨0, Nat.zero_lt_succ 2⟩) (by simp [activationDirectory])
      (⟨1, Nat.lt_succ_self 1⟩ : Fin 2) rfl
      (by change (27 : BitVec 64) ∈ [9, 27]; simp) (by rfl) (by rfl)
    exact lookup

end ReadbackControls
end NativeFrames
end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.GSLT.LanguageDef.NativeOps
open NativeFrames
open Mettapedia.TypeTheory (IndexedPolynomial)
open Mettapedia.Machines.Cursor
namespace Controls

open _root_.CategoryTheory

private def header : FrameStateView :=
  ⟨⟨1, 0, []⟩, ⟨2, 0, []⟩, ⟨5, 2⟩, 2, 2, 7, 17, 11, true, true, true⟩

private def first : FrameSlotView :=
  ⟨5, BitVec.ofNat 64 ((encode header.token).toNat * 2 ^ 32 + 5),
    99, none, true, ⟨none, 777, 2⟩, 13⟩

private def second : FrameSlotView :=
  ⟨9, BitVec.ofNat 64 ((encode header.token).toNat * 2 ^ 32 + 9),
    99, none, true, ⟨some ⟨41, 0, []⟩, 20, 1⟩, 16⟩

private def caller : FrameReadback := ⟨header, [first, second], by decide⟩

private def directory : DirectoryReadback :=
  ⟨⟨⟨1, 0, []⟩, some ⟨2, 0, []⟩, 1, 7, 17⟩, 6, [caller], by decide⟩

private def reply : BindingValueView := ⟨some ⟨42, 0, []⟩, 100, 2⟩

private def wanted : Destination := destination caller ⟨0, by decide⟩

theorem receipt_keeps_context_and_other_slot :
    (receive? caller wanted reply).map (fun after =>
      (after.toEntry.readSlot? after.view.writeClock 0,
       after.toEntry.readSlot? after.view.writeClock 1)) =
      some (some ⟨some reply, 18, 18, some 11⟩,
        some ⟨second.value.payload, 16, 18, some 11⟩) := by decide

theorem directory_receipt_uses_handle_not_enumeration_position :
    (receive? caller wanted reply).map (fun after =>
      ((commitImage directory.toImage after).readSlot? (header.token.ref 0),
       (commitImage directory.toImage after).lookup ⟨0, 2, 0⟩)) =
      some (some ⟨some reply, 18, 18, some 11⟩, none) := by decide

theorem dropping_context_changes_the_received_value :
    (receive? caller wanted reply).map (fun after => after.toEntry.values[0]?) ≠
      (receive? caller wanted { reply with epoch := 0, kind := 0 }).map
        (fun after => after.toEntry.values[0]?) := by decide

theorem equal_spelling_is_not_equal_destination :
    first.spelling = second.spelling ∧
    destination caller ⟨0, by decide⟩ ≠ destination caller ⟨1, by decide⟩ ∧
    (receive? caller { wanted with slot := 1 } reply).isSome = false := by decide

theorem receipt_rejects_other_world_generation_and_null :
    (receive? caller { wanted with bindings := ⟨3, 0, []⟩ } reply).isSome = false ∧
    (receive? caller { wanted with token := ⟨5, 1⟩ } reply).isSome = false ∧
    (receive? caller wanted ⟨none, 100, 2⟩).isSome = false ∧
    (receive? caller wanted ⟨some ⟨42, 0, []⟩, 100, 3⟩).isSome = false := by decide

theorem reacquired_directory_accepts_same_destination :
    (relocateDirectory caller ⟨3, 0, []⟩).view.directory ≠ caller.view.directory ∧
    (receive? (relocateDirectory caller ⟨3, 0, []⟩) wanted reply).isSome = true := by decide

private def full : FrameReadback :=
  ⟨{ header with writeClock := 2 ^ 64 - 1 }, [first, second], by decide⟩

theorem native_clock_does_not_wrap :
    (receive? full wanted reply).isSome = false := by decide

private def script : Client (P := protocol) (Return := fun _ _ => List Bool) where
  V _ _ := List (Destination × BindingValueView) × List Bool
  str := fun _ _ => ↾fun (remaining, accepted) =>
    match remaining with
    | [] => ⟨.inl accepted.reverse, fun impossible => nomatch impossible⟩
    | request :: rest => ⟨.inr request, fun reply => (rest, reply :: accepted)⟩

private def start (requests : List (Destination × BindingValueView)) :
    Packet provider script () := ⟨(), (requests, []), caller⟩

private def observed (result : Nat × Outcome provider script ()) :
    Nat × Bool × Nat × List Bool × Nat :=
  match result.2 with
  | .paused ⟨_, (remaining, replies), frame⟩ =>
    (result.1, false, remaining.length, replies.reverse, frame.view.writeClock)
  | .done ⟨_, replies, frame⟩ => (result.1, true, 0, replies, frame.view.writeClock)

/-- Two equal payloads at equal destinations still denote two receipts.
The suspended client retains the second request and its already paid prefix. -/
theorem pause_and_resume_keep_receipt_occurrences :
    observed (advance provider script (fun _ _ => 1) 1
      (start [(wanted, reply), (wanted, reply)])) = (1, false, 1, [true], 18) ∧
    observed (resume provider script (fun _ _ => 1) 2
      (advance provider script (fun _ _ => 1) 1
        (start [(wanted, reply), (wanted, reply)]))) = (2, true, 0, [true, true], 19) := by
  decide

/-- A failed return does not consume a write version; its continuation can
submit a valid destination against the retained image. -/
theorem refusal_retains_image_for_following_receipt :
    observed (advance provider script (fun _ _ => 1) 3
      (start [({ wanted with token := ⟨5, 1⟩ }, reply), (wanted, reply)])) =
      (2, true, 0, [false, true], 18) := by decide

private def siblingHeader : FrameStateView :=
  { header with token := ⟨8, 2⟩, activationWriteBoundary := 12 }

private def siblingFirst : FrameSlotView :=
  { first with varId := BitVec.ofNat 64 ((encode siblingHeader.token).toNat * 2 ^ 32 + 5) }

private def siblingSecond : FrameSlotView :=
  { second with varId := BitVec.ofNat 64 ((encode siblingHeader.token).toNat * 2 ^ 32 + 9) }

private def sibling : FrameReadback :=
  ⟨siblingHeader, [siblingFirst, siblingSecond], by decide⟩

private def siblings : DirectoryReadback :=
  ⟨{ directory.directory with frameCount := 2 }, 9, [caller, sibling], by decide⟩

private def siblingDestination : Destination := destination sibling ⟨0, by decide⟩

private def siblingReply : BindingValueView := ⟨some ⟨43, 0, []⟩, 101, 1⟩

private def interleaved : Option DirectoryReadback := do
  let first ← receiveDirectory? siblings wanted reply
  receiveDirectory? first siblingDestination siblingReply

/-- Interleaved receipts use one shared clock, and preserve both contextual
payloads and the untouched slots of both frames. -/
theorem sibling_receipts_stamp_consecutively :
    interleaved.map (fun after =>
      (after.toImage.readSlot? (header.token.ref 0),
       after.toImage.readSlot? (siblingHeader.token.ref 0),
       after.toImage.readSlot? (header.token.ref 1),
       after.toImage.readSlot? (siblingHeader.token.ref 1))) =
      some (some ⟨some reply, 18, 19, some 11⟩,
        some ⟨some siblingReply, 19, 19, some 12⟩,
        some ⟨second.value.payload, 16, 19, some 11⟩,
        some ⟨siblingSecond.value.payload, 16, 19, some 12⟩) := by decide

/-- Independent old frame snapshots duplicate the write stamp: they cannot
replace the directory provider when sibling writes are interleaved. -/
theorem stale_frame_snapshots_duplicate_stamp :
    (receive? caller wanted reply).map (fun after => after.view.writeClock) = some 18 ∧
    (receive? sibling siblingDestination siblingReply).map
      (fun after => after.view.writeClock) = some 18 ∧
    interleaved.map (fun after => after.directory.writeClock) = some 19 := by decide

theorem receipt_refreshes_sibling_header_only :
    (receiveDirectory? siblings wanted reply).map (fun after =>
      (after.frames[1]?.map (fun frame => frame.view.writeClock),
       after.frames[1]?.map FrameReadback.toEntry)) =
      some (some 18, some sibling.toEntry) := by rfl

private def directoryStart (requests : List (Destination × BindingValueView)) :
    Packet directoryProvider script () := ⟨(), (requests, []), siblings⟩

private def directoryObserved (result : Nat × Outcome directoryProvider script ()) :
    Nat × Bool × Nat × List Bool × Nat × Option Nat × Option Nat :=
  let observe := fun world : DirectoryReadback =>
    ((world.toImage.readSlot? (header.token.ref 0)).map SlotReadbackOf.writeVersion,
     (world.toImage.readSlot? (siblingHeader.token.ref 0)).map SlotReadbackOf.writeVersion)
  match result.2 with
  | .paused ⟨_, (remaining, replies), world⟩ =>
    (result.1, false, remaining.length, replies.reverse, world.directory.writeClock,
      (observe world).1, (observe world).2)
  | .done ⟨_, replies, world⟩ =>
    (result.1, true, 0, replies, world.directory.writeClock, (observe world).1, (observe world).2)

/-- A pause keeps the complete world, while an equal repeated receipt remains
a distinct occurrence and receives its own write version. -/
theorem directory_pause_keeps_siblings_and_duplicate_receipts :
    directoryObserved (advance directoryProvider script (fun _ _ => 1) 1
      (directoryStart [(wanted, reply), (siblingDestination, siblingReply), (wanted, reply)])) =
        (1, false, 2, [true], 18, some 18, some 13) ∧
    directoryObserved (resume directoryProvider script (fun _ _ => 1) 3
      (advance directoryProvider script (fun _ _ => 1) 1
        (directoryStart [(wanted, reply), (siblingDestination, siblingReply), (wanted, reply)]))) =
        (3, true, 0, [true, true, true], 20, some 20, some 19) := by
  constructor <;> rfl

theorem directory_refusal_consumes_no_write_version :
    directoryObserved (advance directoryProvider script (fun _ _ => 1) 4
      (directoryStart [({ wanted with token := ⟨5, 1⟩ }, reply),
        (siblingDestination, siblingReply), (wanted, reply)])) =
      (3, true, 0, [false, true, true], 19, some 19, some 18) := by rfl

theorem directory_refuses_wrong_world_source_and_missing_frame :
    (receiveDirectory? siblings { wanted with bindings := ⟨3, 0, []⟩ } reply).isSome = false ∧
    (receiveDirectory? siblings { wanted with sourceId := 9 } reply).isSome = false ∧
    (receiveDirectory? siblings { wanted with token := ⟨7, 2⟩ } reply).isSome = false := by decide

theorem directory_reheader_preserves_receipt_destinations :
    (reheaderDirectory? siblings { siblings.directory with directory := some ⟨3, 0, []⟩ }).isSome =
      true ∧
    (receiveDirectory? (relocateDirectoryView siblings ⟨3, 0, []⟩) wanted reply).isSome = true ∧
    (relocateDirectoryView siblings ⟨3, 0, []⟩).toImage.readSlot? (siblingHeader.token.ref 1) =
      siblings.toImage.readSlot? (siblingHeader.token.ref 1) := by decide

theorem directory_reheader_rejects_changed_world_or_clock :
    (reheaderDirectory? siblings { siblings.directory with bindings := ⟨3, 0, []⟩ }).isSome = false ∧
    (reheaderDirectory? siblings { siblings.directory with writeClock := 18 }).isSome = false ∧
    (reheaderDirectory? siblings { siblings.directory with schemaRevision := 8 }).isSome = false ∧
    (reheaderDirectory? siblings { siblings.directory with directory := none }).isSome = false := by
  decide

private def variableAddress : Address := ⟨50, 0, []⟩

/-- A borrowed Atom header whose old packed epoch differs from the contextual
binding epoch. The readback does not synthesize ownership from these cells. -/
private def variableMemory : Mettapedia.GSLT.LanguageDef.NativeOps.TargetMemory :=
  ⟨fun storage position =>
    if storage = variableAddress.storage ∧ position = 0 then
      some (.record "Atom" [.word 1, .word 0, .word (BitVec.ofNat 64 (99 * 2 ^ 32 + 5))])
    else none,
    fun _ => none⟩

private def variableOperand : BindingValueView :=
  ⟨some variableAddress, encode header.token, 1⟩

theorem contextual_variable_reads_received_child :
    (receiveDirectory? siblings wanted reply).map
      (fun after => after.readVariableSlot? variableMemory variableOperand) =
      some (some ⟨some reply, 18, 18, some 11⟩) ∧
    interleaved.map (fun after => after.readVariableSlot? variableMemory variableOperand) =
      some (some ⟨some reply, 18, 19, some 11⟩) := by decide

theorem receipt_preserves_both_variable_coordinates :
    interleaved.map (fun after =>
      (after.variableCoordinate? first.varId, after.variableCoordinate? siblingFirst.varId)) =
      some (some (header.token.ref 0), some (siblingHeader.token.ref 0)) := by decide

theorem receipt_does_not_repair_lost_context_or_stale_generation :
    interleaved.map (fun after => after.readVariableSlot? variableMemory
      { variableOperand with kind := 0 }) = some none ∧
    interleaved.map (fun after => after.readVariableSlot? variableMemory
      { variableOperand with epoch := encode ⟨5, 1⟩ }) = some none := by decide

/-! The source holds one count for each actual frame; whole capture constructs
the second counts before either source owner is released. Atom storage is still
borrowed and is not licensed by this separate frame-identity allocator. -/

private def sourceFree : Shared.Allocator :=
  ⟨Array.replicate 9 ⟨2, 0⟩, 4095⟩

private def sourceFirst : Shared.Allocator × Shared.Token :=
  (Shared.allocate? sourceFree header.token.handle).get (by decide)

private def sourceSecond : Shared.Allocator × Shared.Token :=
  (Shared.allocate? sourceFirst.1 siblingHeader.token.handle).get (by decide)

private def writtenDirectory : DirectoryReadback := interleaved.get (by decide)

private def wholeCapture : Shared.Allocator × Shared.ImageOf BindingValueView :=
  (writtenDirectory.toImage.captureAll? sourceSecond.1).get (by decide)

private def rawCapture : Shared.Allocator × Shared.ImageOf BindingValueView :=
  (siblings.toImage.captureAll? sourceSecond.1).get (by decide)

private def sourceReleasedFirst : Shared.Allocator :=
  (Shared.release? wholeCapture.1 header.token).get (by decide)

private def sourceReleasedSecond : Shared.Allocator :=
  (Shared.release? sourceReleasedFirst siblingHeader.token).get (by decide)

/-- Both source releases are held histories for both escaped frame tokens. -/
theorem whole_capture_source_releases_keep_every_count :
    ∀ token ∈ writtenDirectory.toImage.inventory,
      Shared.HeldTrace token wholeCapture.1 sourceReleasedSecond := by
  intro token member
  have inventory : writtenDirectory.toImage.inventory = [header.token, siblingHeader.token] :=
    by decide
  rw [inventory] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have first : Shared.HeldStep header.token wholeCapture.1 sourceReleasedFirst :=
      .releaseShared (cell := ⟨2, 2⟩) (by decide) (by decide) (by decide)
    have second : Shared.HeldStep header.token sourceReleasedFirst sourceReleasedSecond :=
      .releaseOther (other := siblingHeader.token) (by decide) (by decide)
    exact .next (.next (.refl _) first) second
  · have first : Shared.HeldStep siblingHeader.token wholeCapture.1 sourceReleasedFirst :=
      .releaseOther (other := header.token) (by decide) (by decide)
    have second : Shared.HeldStep siblingHeader.token sourceReleasedFirst sourceReleasedSecond :=
      .releaseShared (cell := ⟨2, 2⟩) (by decide) (by decide) (by decide)
    exact .next (.next (.refl _) first) second

/-- Concrete native contextual operands select both captured frames after the
two source releases. Their interleaved write stamps share the captured clock. -/
theorem whole_capture_contextual_readback_after_source_releases :
    readCapturedVariableSlot? writtenDirectory wholeCapture.2 sourceReleasedSecond
      variableMemory variableOperand = some ⟨some reply, 18, 19, some 11⟩ ∧
    readCapturedVariableSlot? writtenDirectory wholeCapture.2 sourceReleasedSecond
      variableMemory { variableOperand with epoch := encode siblingHeader.token } =
        some ⟨some siblingReply, 19, 19, some 12⟩ := by
  have success : writtenDirectory.toImage.captureAll? sourceSecond.1 = some wholeCapture :=
    (Option.some_get (by decide)).symm
  constructor
  · exact (captureAll_readVariableSlot writtenDirectory success
      whole_capture_source_releases_keep_every_count variableMemory variableOperand).trans
        (by decide)
  · exact (captureAll_readVariableSlot writtenDirectory success
      whole_capture_source_releases_keep_every_count variableMemory
      { variableOperand with epoch := encode siblingHeader.token }).trans (by decide)

/-- Capture retains a valid unbound slot's stamp and boundary too, rather than
collapsing it into a missing frame. Frame counts do not create Atom owners. -/
theorem whole_capture_unbound_metadata_and_independent_storage :
    readCapturedVariableSlot? siblings rawCapture.2 sourceReleasedSecond
      variableMemory variableOperand = some ⟨none, 13, 17, some 11⟩ ∧
    sourceReleasedSecond.cells[5]? = some ⟨2, 1⟩ ∧
    sourceReleasedSecond.cells[8]? = some ⟨2, 1⟩ ∧
    variableMemory.owned variableAddress.storage = none := by decide

private def finalFirstRelease : Shared.Allocator :=
  (Shared.release? sourceReleasedSecond header.token).get (by decide)

private def reusedFirst : Shared.Allocator × Shared.Token :=
  (Shared.allocate? finalFirstRelease header.token.handle).get (by decide)

/-- Final release revokes the captured first frame while the sibling remains
held. Reallocation at that handle cannot revive the old contextual operand. -/
theorem whole_capture_final_release_and_reuse_revoke_old_variable :
    readCapturedVariableSlot? writtenDirectory wholeCapture.2 finalFirstRelease
      variableMemory variableOperand = none ∧
    readCapturedVariableSlot? writtenDirectory wholeCapture.2 finalFirstRelease
      variableMemory { variableOperand with epoch := encode siblingHeader.token } =
        some ⟨some siblingReply, 19, 19, some 12⟩ ∧
    reusedFirst.2 = ⟨5, 3⟩ ∧
    readCapturedVariableSlot? writtenDirectory wholeCapture.2 reusedFirst.1
      variableMemory variableOperand = none ∧
    writtenDirectory.toImage.captureAll? reusedFirst.1 = none := by decide

/-- Lost context or a stale packed generation cannot select an owned captured
slot; retaining both current tokens does not repair either operand. -/
theorem whole_capture_refuses_lost_context_and_stale_operand :
    readCapturedVariableSlot? writtenDirectory wholeCapture.2 sourceReleasedSecond
      variableMemory { variableOperand with kind := 0 } = none ∧
    readCapturedVariableSlot? writtenDirectory wholeCapture.2 sourceReleasedSecond
      variableMemory { variableOperand with epoch := encode ⟨5, 1⟩ } = none := by decide

end Controls
end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.CurrentValueRead
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.LanguageDef.NativeOps (Address TargetValue)
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
namespace Controls
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage
open ProductiveBlocks

def frameAddress : Ptr := ⟨1, 0⟩
def sourceAddress : Ptr := ⟨2, 0⟩
def destinationAddress : Ptr := ⟨3, 0⟩
def skeletonAddress : Ptr := ⟨4, 0⟩
def payload : List CVal := valueCells (some skeletonAddress) 17 1

def initialStorage : Storage CVal :=
  [(1, ⟨true, [none, none, none, none, some (.ptr (some sourceAddress))]⟩),
   (2, ⟨true, payload.map some⟩), (3, ⟨true, [none, none, none]⟩)]

def initial : State CVal (ReadBlock.Result StatementBlock.ObjectBindings.Context) :=
  ⟨program frameAddress destinationAddress 0, initialStorage, []⟩

def outputCells (storage : Storage CVal) : List (Option CVal) :=
  [load storage destinationAddress, load storage (destinationAddress + 1),
    load storage (destinationAddress + 2)]

def complete (outcome : Outcome (State CVal (ReadBlock.Result StatementBlock.ObjectBindings.Context))
    (Verdict CVal (ReadBlock.Result StatementBlock.ObjectBindings.Context))
    (AllocationRequest CVal)) : Bool :=
  match outcome with
  | .finished (.returned _) => true
  | _ => false

def storageOf (outcome : Outcome (State CVal (ReadBlock.Result StatementBlock.ObjectBindings.Context))
    (Verdict CVal (ReadBlock.Result StatementBlock.ObjectBindings.Context))
    (AllocationRequest CVal)) : Storage CVal :=
  match outcome with
  | .finished (.returned final) => final.storage
  | .finished (.fault saved) | .stuck saved | .exhausted saved | .suspended _ saved => saved.storage
  | .faulted => []

theorem copied_context_is_complete :
    complete ((machine.run 8 initial).2) = true ∧
    outputCells (storageOf ((machine.run 8 initial).2)) = payload.map some := by
  rw [show initial = ⟨operations frameAddress destinationAddress 0, initialStorage, []⟩ by
    simp only [initial, copy_uses_current_memory]]
  decide +kernel

theorem partial_copy_is_pending :
    complete ((machine.run 5 initial).2) = false ∧
    outputCells (storageOf ((machine.run 5 initial).2)) =
      [some (.ptr (some skeletonAddress)), none, none] := by
  rw [show initial = ⟨operations frameAddress destinationAddress 0, initialStorage, []⟩ by
    simp only [initial, copy_uses_current_memory]]
  decide +kernel

def saved : State CVal (ReadBlock.Result StatementBlock.ObjectBindings.Context) :=
  match (machine.run 5 initial).2 with
  | .exhausted state => state
  | _ => initial

theorem resume_only_finishes_remaining_fields :
    (machine.run 3 saved).1.map (fun receipt => receipt.operation) =
      [.store (destinationAddress + 1) (.u32 17), .store (destinationAddress + 2) (.u32 1)] := by
  simp only [saved, initial, copy_uses_current_memory]
  rfl

theorem resumed_copy_matches_complete_copy :
    complete ((machine.run 3 saved).2) = true ∧
    outputCells (storageOf ((machine.run 3 saved).2)) =
      outputCells (storageOf ((machine.run 8 initial).2)) := by
  simp only [saved, initial, copy_uses_current_memory]
  decide +kernel

def shortSource : Storage CVal :=
  put initialStorage 2 ⟨true, [some (.ptr (some skeletonAddress)), some (.u32 17)]⟩

theorem incomplete_value_never_publishes_partial_record :
    complete ((machine.run 8 ⟨operations frameAddress destinationAddress 0, shortSource, []⟩).2) = false ∧
    outputCells (storageOf ((machine.run 8 ⟨operations frameAddress destinationAddress 0, shortSource, []⟩).2)) =
      [none, none, none] := by decide +kernel

theorem whole_value_reader_keeps_context_and_null_metadata :
    readCells? payload = some (cellView (some skeletonAddress) 17 1) ∧
    readCells? (valueCells none 19 2) = some (cellView none 19 2) ∧
    (cellView (some skeletonAddress) 17 1) ≠ cellView (some skeletonAddress) 0 0 := by decide

theorem missing_field_or_unknown_tag_is_not_a_value :
    readCells? [.ptr (some skeletonAddress), .u32 17] = none ∧
    readCells? (valueCells (some skeletonAddress) 17 3) = none := by decide

end Controls
end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.CurrentValueRead
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open StatementBlock
universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]
namespace Controls
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage ProductiveBlocks

def frame : Ptr := ⟨11, 0⟩
def schema : Ptr := ⟨12, 0⟩
def output : Ptr := ⟨13, 0⟩

def storage : Storage CVal :=
  [(11, ⟨true, [none, none, some (.ptr (some schema)), none, none, none, none, none,
    some (.u32 3)]⟩),
   (12, ⟨true, [none, none, none, some (.u64 10)]⟩),
   (13, ⟨true, [some (.u32 99)]⟩)]

def initial (source : UInt64) : State CVal (ReadBlock.Result ObjectBindings.Context) :=
  ⟨program frame output source, storage, []⟩

/-- Status zero is retained work, one is a returned source Boolean, and two
is a physical fault. The output cell is read from the actual resulting store. -/
def observe (result : Outcome (State CVal (ReadBlock.Result ObjectBindings.Context))
    (Verdict CVal (ReadBlock.Result ObjectBindings.Context)) (AllocationRequest CVal)) :
    Nat × Option Bool × Option CVal :=
  match result with
  | .finished (.returned final) =>
      (1, match final.answer with
          | .finished (.returned _ (some (.bool value))) => some value
          | _ => none, load final.storage output)
  | .finished (.fault saved) => (2, none, load saved.storage output)
  | .exhausted saved => (0, none, load saved.storage output)
  | .suspended _ saved | .stuck saved => (3, none, load saved.storage output)
  | .faulted => (4, none, none)

theorem final_source_slot_is_selected :
    observe ((machine.run 7 (initial 12)).2) = (1, some true, some (.u32 2)) := by
  simp only [initial, program_uses_current_memory]
  decide +kernel

theorem below_range_returns_false_without_output_write :
    observe ((machine.run 3 (initial 9)).2) = (1, some false, some (.u32 99)) ∧
    (machine.run 3 (initial 9)).1.map (fun receipt => receipt.operation) =
      [.load (frame + 2), .load (schema + 3)] := by
  simp only [initial, program_uses_current_memory]
  constructor
  · decide +kernel
  · rfl

theorem upper_bound_and_wide_source_do_not_wrap_into_slots :
    observe ((machine.run 6 (initial 13)).2) = (1, some false, some (.u32 99)) ∧
    observe ((machine.run 6 (initial 4294967306)).2) = (1, some false, some (.u32 99)) := by
  simp only [initial, program_uses_current_memory]
  decide +kernel

theorem output_is_not_published_before_its_store :
    observe ((machine.run 5 (initial 12)).2) = (0, none, some (.u32 99)) := by
  simp only [initial, program_uses_current_memory]
  decide +kernel

def saved : State CVal (ReadBlock.Result ObjectBindings.Context) :=
  match (machine.run 5 (initial 12)).2 with
  | .exhausted state => state
  | _ => initial 12

theorem resumed_selector_does_not_repeat_previous_reads :
    (machine.run 2 saved).1.map (fun receipt => receipt.operation) = [.store output (.u32 2)] ∧
    observe ((machine.run 2 saved).2) = (1, some true, some (.u32 2)) := by
  simp only [saved, initial, program_uses_current_memory]
  constructor
  · rfl
  · decide +kernel

def staleSchema : Storage CVal :=
  put storage 12 ⟨false, [none, none, none, some (.u64 10)]⟩

def wrongSchemaType : Storage CVal :=
  put storage 12 ⟨true, [none, none, none, some (.u32 10)]⟩

theorem stale_or_mistyped_schema_is_not_range_refusal :
    observe ((machine.run 7 ⟨operations frame output 12, staleSchema, []⟩).2) =
      (2, none, some (.u32 99)) ∧
    observe ((machine.run 7 ⟨operations frame output 12, wrongSchemaType, []⟩).2) =
      (2, none, some (.u32 99)) := by decide +kernel

end Controls
end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section PettaSortedControls
set_option autoImplicit false
set_option maxRecDepth 12000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedPhysical.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def frame : Ptr := ⟨51, 0⟩
def schema : Ptr := ⟨52, 0⟩

def storage : Storage CVal :=
  [(51, ⟨true, [none, none, some (.ptr (some schema))]⟩),
   (52, ⟨true, [none, some (.u32 3), none, none, none, none, none,
     some (.u64 3), some (.u64 7), some (.u64 12)]⟩)]

def initial (key : UInt64) : State CVal (ReadBlock.Result Window) :=
  ⟨search frame key 3 (0, 3), storage, []⟩

def observation (result : Outcome (State CVal (ReadBlock.Result Window))
    (Verdict CVal (ReadBlock.Result Window)) (AllocationRequest CVal)) :
    Nat × Option (Nat × Nat) :=
  match result with
  | .finished (.returned final) =>
      match final.answer with
      | .finished (.next window) => (1, some (window.1.toNat, window.2.toNat))
      | .exhausted => (2, none)
      | _ => (3, none)
  | .exhausted _ => (0, none)
  | .finished (.fault _) => (4, none)
  | _ => (5, none)

theorem selected_position_keeps_actual_probe_reads :
    observation ((machine.run 5 (initial 7)).2) = (1, some (1, 1)) ∧
    (machine.run 5 (initial 7)).1.map (fun receipt => receipt.operation) =
      [.load (frame + 2), .load (schema + 8),
       .load (frame + 2), .load (schema + 7)] := by
  constructor
  · decide +kernel
  · rfl

def saved : State CVal (ReadBlock.Result Window) :=
  match (machine.run 1 (initial 7)).2 with
  | .exhausted state => state
  | _ => initial 7

theorem paused_probe_keeps_its_read_schema :
    observation ((machine.run 1 (initial 7)).2) = (0, none) ∧
    observation ((machine.run 4 saved).2) = (1, some (1, 1)) ∧
    (machine.run 4 saved).1.map (fun receipt => receipt.operation) =
      [.load (schema + 8), .load (frame + 2), .load (schema + 7)] := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · rfl

theorem absent_source_closes_at_insertion_position :
    observation ((machine.run 5 (initial 8)).2) = (1, some (2, 2)) := by
  decide +kernel

theorem above_inventory_never_probes_past_end :
    observation ((machine.run 5 (initial 20)).2) = (1, some (3, 3)) ∧
    (machine.run 5 (initial 20)).1.map (fun receipt => receipt.operation) =
      [.load (frame + 2), .load (schema + 8),
       .load (frame + 2), .load (schema + 9)] := by
  constructor
  · decide +kernel
  · rfl

theorem false_guard_needs_no_iteration_allowance :
    observation ((machine.run 1 ⟨search frame 7 0 (2, 2), storage, []⟩).2) =
      (1, some (2, 2)) := by decide +kernel

theorem true_guard_without_allowance_is_not_not_found :
    observation ((machine.run 1 ⟨search frame 7 0 (0, 3), storage, []⟩).2) =
      (2, none) := by decide +kernel

theorem missing_array_cell_is_not_normal_rejection :
    observation ((machine.run 5
      ⟨search frame 7 3 (0, 3),
       [(51, ⟨true, [none, none, some (.ptr (some schema))]⟩),
        (52, ⟨true, [none, some (.u32 3)]⟩)], []⟩).2) = (4, none) := by
  decide +kernel

/-- Without an ordered inventory, the same C search can miss a present
identifier. The source admission must earn ordering independently. -/
theorem unordered_inventory_cannot_claim_complete_lookup :
    observation ((machine.run 3
      ⟨search frame 9 2 (0, 2),
       [(51, ⟨true, [none, none, some (.ptr (some schema))]⟩),
        (52, ⟨true, [none, some (.u32 2), none, none, none, none, none,
          some (.u64 9), some (.u64 1)]⟩)], []⟩).2) = (1, some (2, 2)) := by
  decide +kernel

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedPhysical.Controls
end PettaSortedControls
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section PettaSortedWholeControls
set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage ProductiveBlocks


def frame : Ptr := ⟨61, 0⟩
def schema : Ptr := ⟨62, 0⟩
def output : Ptr := ⟨63, 0⟩
def frameType : GSLT.LanguageDef.NativeOps.NativeC.CType := ⟨"BindingsFrameIndex".toList, 1⟩
def context (key : UInt64) : Context := fun name =>
  if name = "frame".toList then scalar frameType (.ptr (some frame))
  else if name = "slot_out".toList then scalar ⟨"uint32_t".toList, 1⟩ (.ptr (some output))
  else if name = "source_id".toList then scalar SortedSource.uint64 (.u64 key)
  else if name = "low".toList then scalar ⟨"bool".toList, 0⟩ (.bool true)
  else if name = "high".toList then scalar ⟨"uint64_t".toList, 0⟩ (.u64 87)
  else if name = "middle".toList then scalar ⟨"uint32_t".toList, 0⟩ (.u32 42)
  else none

def storage : Storage CVal :=
  [(61, ⟨true, [none, none, some (.ptr (some schema))]⟩),
   (62, ⟨true, [none, some (.u32 3), none, none, none, none, none,
     some (.u64 3), some (.u64 7), some (.u64 11)]⟩),
   (63, ⟨true, [some (.u32 99)]⟩)]

def initial (allowance : Nat) (key : UInt64) : State CVal (ReadBlock.Result Context) :=
  ⟨program allowance (context key), storage, []⟩

def observation (result : Outcome (State CVal (ReadBlock.Result Context))
    (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal)) :
    Nat × Option CVal × List (Option CVal) :=
  match result with
  | .finished (.returned final) =>
      match final.answer with
      | .finished (.returned reached (some (.bool answer))) =>
          (if answer then 1 else 2, load final.storage output,
            [ObjectBindings.values reached "low".toList, ObjectBindings.values reached "high".toList,
             ObjectBindings.values reached "middle".toList])
      | .exhausted => (3, load final.storage output, [])
      | _ => (5, load final.storage output, [])
  | .exhausted saved => (0, load saved.storage output, [])
  | .finished (.fault saved) => (4, load saved.storage output, [])
  | _ => (6, none, [])

theorem source_operations (allowance : Nat) (key : UInt64) :
    program allowance (context key) = operations allowance (context key) frame output key :=
  program_uses_memory_operations (context key) frame output key frameType allowance rfl rfl rfl

theorem parsed_success_restores_all_three_shadowed_locals :
    observation ((machine.run 12 (initial 3 7)).2) =
      (1, some (.u32 1), [some (.bool true), some (.u64 87), some (.u32 42)]) := by
  simp only [initial, source_operations]
  decide +kernel

theorem parsed_refusal_keeps_output_and_older_locals :
    observation ((machine.run 11 (initial 3 8)).2) =
      (2, some (.u32 99), [some (.bool true), some (.u64 87), some (.u32 42)]) := by
  simp only [initial, source_operations]
  decide +kernel

theorem upper_refusal_short_circuits_past_end_probe :
    observation ((machine.run 9 (initial 3 20)).2) =
      (2, some (.u32 99), [some (.bool true), some (.u64 87), some (.u32 42)]) ∧
    (machine.run 9 (initial 3 20)).1.map (fun receipt => receipt.operation) =
      [.load (frame + 2), .load (schema + 1),
       .load (frame + 2), .load ((schema + 7) + 1),
       .load (frame + 2), .load ((schema + 7) + 2),
       .load (frame + 2), .load (schema + 1)] := by
  simp only [initial, source_operations]
  constructor
  · decide +kernel
  · rfl

theorem final_store_can_precede_scheduler_pause :
    observation ((machine.run 11 (initial 3 7)).2) = (0, some (.u32 1), []) := by
  simp only [initial, source_operations]
  decide +kernel

def saved : State CVal (ReadBlock.Result Context) :=
  match (machine.run 11 (initial 3 7)).2 with
  | .exhausted reached => reached
  | _ => initial 3 7

theorem resumed_publication_does_not_replay_the_store :
    observation ((machine.run 1 saved).2) =
      (1, some (.u32 1), [some (.bool true), some (.u64 87), some (.u32 42)]) ∧
    (machine.run 1 saved).1 = [] := by
  simp only [saved, initial, source_operations]
  constructor
  · decide +kernel
  · rfl

theorem uncovered_loop_is_not_completed_refusal :
    observation ((machine.run 3 (initial 0 7)).2) = (3, some (.u32 99), []) := by
  simp only [initial, source_operations]
  decide +kernel

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SlotSelector.SortedStatements.Controls
end PettaSortedWholeControls
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section NativeSymbolForward
set_option maxHeartbeats 600000
set_option maxRecDepth 12000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolForward.Controls

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage ProductiveBlocks

def first : Ptr := ⟨41, 0⟩
def second : Ptr := ⟨42, 0⟩
def terminal : Ptr := ⟨43, 0⟩

def storage : Storage CVal :=
  [(41, ⟨true, [none, none, none, none, some (.u32 4294967295), some (.ptr (some second))]⟩),
   (42, ⟨true, [none, none, none, none, some (.u32 4294967295), some (.ptr (some terminal))]⟩),
   (43, ⟨true, [none, none, none, none, some (.u32 17), some (.ptr none)]⟩),
   (44, ⟨true, [some (.u32 913)]⟩)]

def initial : State CVal (ReadBlock.Result (Option Ptr)) :=
  ⟨traversal 2 (some first), storage, []⟩

def observe (result : Outcome (State CVal (ReadBlock.Result (Option Ptr)))
    (Verdict CVal (ReadBlock.Result (Option Ptr))) (AllocationRequest CVal)) :
    Nat × Option Ptr :=
  match result with
  | .exhausted _ => (0, none)
  | .finished (.fault _) => (3, none)
  | .finished (.returned final) =>
      match final.answer with
      | .exhausted => (2, none)
      | .finished (.next pointer) => (1, pointer)
      | _ => (4, none)
  | _ => (4, none)

theorem complete_two_hops :
    observe ((machine.run 20 initial).2) = (1, some terminal) := by decide +kernel

theorem pointer_reads_follow_each_active_forward_arm :
    (machine.run 20 initial).1.map (fun receipt => receipt.operation) =
      [.ptrEq (some first) none, .load (first + 4), .load (first + 5),
       .ptrEq (some second) none, .load (second + 4), .load (second + 5),
       .ptrEq (some terminal) none, .load (terminal + 4)] := by rfl

def saved : State CVal (ReadBlock.Result (Option Ptr)) :=
  match (machine.run 2 initial).2 with
  | .exhausted current => current
  | _ => initial

theorem pause_is_distinct_from_completion :
    observe ((machine.run 2 initial).2) = (0, none) := by decide +kernel

theorem resumed_suffix_does_not_repeat_guard_reads :
    observe ((machine.run 20 saved).2) = (1, some terminal) ∧
    (machine.run 20 saved).1.map (fun receipt => receipt.operation) =
      [.load (first + 5), .ptrEq (some second) none, .load (second + 4),
       .load (second + 5), .ptrEq (some terminal) none, .load (terminal + 4)] := by
  constructor
  · decide +kernel
  · rfl

theorem zero_allowance_still_observes_the_actual_guard :
    observe ((machine.run 20 ⟨traversal 0 (some first), storage, []⟩).2) = (2, none) ∧
    (machine.run 20 ⟨traversal 0 (some first), storage, []⟩).1.map
      (fun receipt => receipt.operation) = [.ptrEq (some first) none, .load (first + 4)] := by
  constructor
  · decide +kernel
  · rfl

theorem ordinary_terminal_needs_no_iteration_allowance :
    observe ((machine.run 20 ⟨traversal 0 (some terminal), storage, []⟩).2) =
      (1, some terminal) := by decide +kernel

theorem null_does_not_read_a_union_arm :
    observe ((machine.run 20 ⟨traversal 0 none, storage, []⟩).2) = (1, none) ∧
    (machine.run 20 ⟨traversal 0 none, storage, []⟩).1.map
      (fun receipt => receipt.operation) = [.ptrEq none none] := by
  constructor
  · decide +kernel
  · rfl

theorem dead_pointer_faults_before_any_arena_read :
    observe ((machine.run 20 ⟨traversal 2 (some ⟨99, 0⟩), storage, []⟩).2) =
      (3, none) := by decide +kernel

theorem wrong_tag_cell_is_not_an_ordinary_terminal :
    observe ((machine.run 20 ⟨traversal 0 (some terminal),
      [(43, ⟨true, [none, none, none, none, some (.bool false)]⟩)], []⟩).2) =
      (3, none) := by decide +kernel

theorem completed_reads_preserve_the_whole_storage :
    (match (machine.run 20 initial).2 with
      | .finished (.returned final) => final.storage
      | _ => []) = storage := by rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolForward.Controls
end NativeSymbolForward
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section ManagedNativeSymbolExecutionControls
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolSpelling.Controls

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage ProductiveBlocks

abbrev hop : Ptr := ⟨71, 0⟩
abbrev atom : Ptr := ⟨72, 0⟩
abbrev spelling : Ptr := ⟨73, 0⟩
abbrev Result := ReadBlock.Result (Option Ptr × Option (Option Ptr × UInt32))

def storage : Storage CVal :=
  [(71, ⟨true, [none, none, none, none, some (.u32 4294967295), some (.ptr (some atom))]⟩),
   (72, ⟨true, [some (.u32 0), none, none, some (.u32 0), some (.u32 17), some (.ptr (some spelling))]⟩),
   (73, ⟨true, [some (.u64 719), some (.u32 3), some (.u8 0x41), some (.u8 0), some (.u8 0xff)]⟩)]

def initial (allowance : Nat) : State CVal Result :=
  ⟨managedAfterForward allowance (some hop), storage, []⟩

def observation (result : Outcome (State CVal Result) (Verdict CVal Result) (AllocationRequest CVal)) :
    Nat × Option Ptr × Option Ptr × UInt32 := match result with
  | .exhausted _ => (0, none, none, 0)
  | .finished (.fault _) => (3, none, none, 0)
  | .finished (.returned final) => match final.answer with
    | .exhausted => (2, none, none, 0)
    | .finished (.next (atom, some (buffer, length))) => (1, atom, buffer, length)
    | .finished (.next (_, none)) => (4, none, none, 0)
    | _ => (5, none, none, 0)
  | _ => (6, none, none, 0)

theorem actual_managed_header_reaches_the_stored_buffer :
    observation ((machine.run 40 (initial 1)).2) = (1, some atom, some (spelling + 2), 3) := by
  decide +kernel

theorem second_forwarding_guard_is_not_erased :
    (machine.run 40 (initial 1)).1.map (fun receipt => receipt.operation) =
      [.ptrEq (some hop) none, .load (hop + 4), .load (hop + 5),
       .ptrEq (some atom) none, .load (atom + 4),
       .ptrEq (some atom) none, .load (atom + 4),
       .ptrEq (some atom) none, .load atom, .load (atom + 3), .load (atom + 5),
       .ptrEq (some spelling) none, .load (atom + 5), .load (atom + 5), .load (spelling + 1)] := by
  rfl

theorem internal_forwarding_exhaustion_is_not_scheduler_pause :
    observation ((machine.run 40 (initial 0)).2) = (2, none, none, 0) ∧
    observation ((machine.run 1 (initial 1)).2) = (0, none, none, 0) := by decide +kernel

theorem resumed_header_does_not_repeat_earlier_guards :
    let saved := machine.run 4 (initial 1)
    let resumed := machine.continueRun 40 saved
    observation resumed.2 = (1, some atom, some (spelling + 2), 3) ∧
      resumed.1.map (fun receipt => receipt.operation) =
        (machine.run 44 (initial 1)).1.map (fun receipt => receipt.operation) := by
  constructor
  · decide +kernel
  · rfl

theorem malformed_length_is_a_fault_not_an_empty_name :
    observation ((machine.run 40
      ⟨managedAfterForward 1 (some hop),
        put storage 73 ⟨true, [some (.u64 719), some (.ptr none), some (.u8 65)]⟩, []⟩).2) =
      (3, none, none, 0) := by decide +kernel

theorem managed_observation_preserves_the_complete_borrowed_storage :
    match (machine.run 40 (initial 1)).2 with
    | .finished (.returned final) => final.storage = storage
    | _ => False := by rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.SymbolSpelling.Controls
end ManagedNativeSymbolExecutionControls
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section NativeDirectoryLookupPackage
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Physical.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def directory : Ptr := ⟨41, 0⟩
def table : Ptr := ⟨40, 0⟩
def first : Ptr := ⟨42, 0⟩
def second : Ptr := ⟨43, 0⟩

def storage : Storage CVal :=
  [(41, ⟨true, [none, none, none, none, none, none, none, none, none,
     some (.ptr (some table))]⟩),
   (40, ⟨true, [some (.ptr (some second)), some (.ptr none), some (.ptr none),
     some (.ptr (some first))]⟩),
   (42, ⟨true, [some (.u32 1048578)]⟩),
   (43, ⟨true, [some (.u32 1048583)]⟩)]

def initial (key : Nat) : State CVal (ReadBlock.Result UInt32) :=
  ⟨search directory key 3 4 3, storage, []⟩

def observation (result : Outcome (State CVal (ReadBlock.Result UInt32))
    (Verdict CVal (ReadBlock.Result UInt32)) (AllocationRequest CVal)) :
    Nat × Option Ptr :=
  match result with
  | .finished (.returned final) => match final.answer with
      | .finished (.returned _ (some (.ptr selected))) => (1, selected)
      | .exhausted => (2, none)
      | _ => (3, none)
  | .exhausted _ => (0, none)
  | .finished (.fault _) => (4, none)
  | _ => (5, none)

theorem collision_wrap_keeps_exact_reads :
    observation ((machine.run 9 (initial 7)).2) = (1, some second) ∧
    (machine.run 9 (initial 7)).1.map (fun receipt => receipt.operation) =
      [.load (directory + 9), .load (table + 3), .ptrEq (some first) none, .load first,
       .load (directory + 9), .load table, .ptrEq (some second) none, .load second] := by
  constructor
  · decide +kernel
  · rfl

def saved : State CVal (ReadBlock.Result UInt32) :=
  match (machine.run 2 (initial 7)).2 with
  | .exhausted state => state
  | _ => initial 7

theorem pause_keeps_selected_pointer_and_resume_does_not_repeat_load :
    observation ((machine.run 2 (initial 7)).2) = (0, none) ∧
    observation ((machine.run 7 saved).2) = (1, some second) ∧
    (machine.run 7 saved).1.map (fun receipt => receipt.operation) =
      [.ptrEq (some first) none, .load first, .load (directory + 9), .load table,
       .ptrEq (some second) none, .load second] := by
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  · rfl

theorem vacancy_is_completed_absence :
    observation ((machine.run 12 (initial 9)).2) = (1, none) := by decide +kernel

theorem iteration_exhaustion_is_not_absence :
    observation ((machine.run 1 ⟨search directory 7 3 0 3, storage, []⟩).2) =
      (2, none) := by decide +kernel

theorem wrong_pointer_cell_is_not_absence :
    observation ((machine.run 3
      ⟨search directory 7 3 4 3,
       [(41, ⟨true, [none, none, none, none, none, none, none, none, none,
          some (.ptr (some table))]⟩),
        (40, ⟨true, [none, none, none, some (.u32 7)]⟩)], []⟩).2) =
      (4, none) := by decide +kernel

theorem dead_selected_entry_is_not_a_vacancy :
    observation ((machine.run 4
      ⟨search directory 7 3 4 3,
       [(41, ⟨true, [none, none, none, none, none, none, none, none, none,
          some (.ptr (some table))]⟩),
        (40, ⟨true, [none, none, none, some (.ptr (some first))]⟩),
        (42, ⟨false, [some (.u32 1048578)]⟩)], []⟩).2) =
      (4, none) := by decide +kernel

/-- A vacancy before a stored key violates the independent no-hole inventory.
The actual probe stops at that vacancy; table membership alone is insufficient. -/
theorem missing_path_admission_can_hide_present_entry :
    observation ((machine.run 4
      ⟨search directory 7 3 4 3,
       [(41, ⟨true, [none, none, none, none, none, none, none, none, none,
          some (.ptr (some table))]⟩),
        (40, ⟨true, [some (.ptr (some second)), none, none, some (.ptr none)]⟩),
        (43, ⟨true, [some (.u32 1048583)]⟩)], []⟩).2) =
      (1, none) := by decide +kernel

theorem full_corrupt_table_does_not_publish_absence :
    observation ((machine.run 9
      ⟨search directory 7 0 2 0,
       [(41, ⟨true, [none, none, none, none, none, none, none, none, none,
          some (.ptr (some table))]⟩),
        (40, ⟨true, [some (.ptr (some first))]⟩),
        (42, ⟨true, [some (.u32 1048578)]⟩)], []⟩).2) =
      (2, none) := by decide +kernel

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Physical.Controls
end NativeDirectoryLookupPackage
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section NativeDirectoryLookupPackage
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.SourceRead.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

abbrev directory := Physical.Controls.directory
abbrev table := Physical.Controls.table
abbrev first := Physical.Controls.first
abbrev second := Physical.Controls.second

def directoryType : CType := ⟨"BindingsFrameIndex".toList, 1⟩
def context : Context := fun name =>
  if name = "index".toList then scalar directoryType (.ptr (some directory))
  else if name = "handle".toList then scalar Source.uint32 (.u32 3)
  else if name = "slot".toList then scalar ⟨"bool".toList, 0⟩ (.bool true)
  else if name = "mask".toList then scalar Source.uint32 (.u32 900)
  else if name = "older".toList then scalar Source.uint32 (.u32 61)
  else none

def storage (shift : UInt32 := 30) : Storage CVal :=
  [(41, ⟨true, [none, none, none, none, none, none, none, none, none,
     some (.ptr (some table)), some (.u32 3), some (.u32 shift)]⟩),
   (40, ⟨true, [some (.ptr (some second)), some (.ptr none), some (.ptr none),
     some (.ptr (some first))]⟩),
   (42, ⟨true, [some (.u32 1048584)]⟩),
   (43, ⟨true, [some (.u32 1048579)]⟩)]

def sourceProgram : CProg CVal (ReadBlock.Result Context) :=
  StatementBlock.executeScopedWith (services decodedHandle) layout 4 12 context Source.lookupBody

theorem source_program : sourceProgram =
    (lookupProgram decodedHandle directory 3 4 >>= fun result => pure (result.mapContext (fun _ => context))) :=
  actual_lookup_body decodedHandle context directory directoryType 3 4 (by rfl) (by rfl)

def initial (memory : Storage CVal := storage) : State CVal (ReadBlock.Result Context) :=
  ⟨sourceProgram, memory, []⟩

def observation (result : Outcome (State CVal (ReadBlock.Result Context))
    (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal)) :
    Nat × Option Ptr :=
  match result with
  | .finished (.returned final) => match final.answer with
      | .finished (.returned _ (some (.ptr selected))) => (1, selected)
      | .exhausted => (2, none)
      | _ => (3, none)
  | .exhausted _ => (0, none)
  | .finished (.fault _) => (4, none)
  | _ => (5, none)

def locals (result : Outcome (State CVal (ReadBlock.Result Context))
    (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal)) :
    Option CVal × Option CVal × Option CVal :=
  match result with
  | .finished (.returned final) => match final.answer with
      | .finished (.returned retained _) =>
          (StatementBlock.ObjectBindings.values retained "slot".toList,
           StatementBlock.ObjectBindings.values retained "mask".toList,
           StatementBlock.ObjectBindings.values retained "older".toList)
      | _ => (none, none, none)
  | _ => (none, none, none)

theorem parsed_lookup_wraps_and_restores_shadowed_locals :
    observation ((machine.run 13 initial).2) = (1, some second) ∧
    locals ((machine.run 13 initial).2) = (some (.bool true), some (.u32 900), some (.u32 61)) := by
  unfold initial
  rw [source_program]
  constructor <;> decide +kernel

theorem parsed_lookup_keeps_initial_and_loop_reads :
    (machine.run 13 initial).1.map (fun receipt => receipt.operation) =
      [.load (directory + 9), .ptrEq (some table) none, .load (directory + 10),
       .load (directory + 11), .load (directory + 9), .load (table + 3),
       .ptrEq (some first) none, .load first, .load (directory + 9), .load table,
       .ptrEq (some second) none, .load second] := by
  unfold initial
  rw [source_program]
  rfl

def saved : State CVal (ReadBlock.Result Context) :=
  match (machine.run 6 initial).2 with
  | .exhausted reached => reached
  | _ => initial

theorem parsed_pause_retains_selected_pointer_and_older_locals :
    observation ((machine.run 6 initial).2) = (0, none) ∧
    observation ((machine.run 7 saved).2) = (1, some second) ∧
    locals ((machine.run 7 saved).2) = (some (.bool true), some (.u32 900), some (.u32 61)) := by
  unfold saved initial
  rw [source_program]
  constructor
  · decide +kernel
  constructor <;> decide +kernel

theorem parsed_resume_does_not_repeat_hash_or_selected_cell_reads :
    (machine.run 7 saved).1.map (fun receipt => receipt.operation) =
      [.ptrEq (some first) none, .load first, .load (directory + 9), .load table,
       .ptrEq (some second) none, .load second] := by
  unfold saved initial
  rw [source_program]
  rfl

theorem invalid_shift_does_not_publish_absence :
    observation ((machine.run 6 (initial (storage 32))).2) = (4, none) := by
  unfold initial
  rw [source_program]
  decide +kernel

def nullTable : Storage CVal :=
  [(41, ⟨true, [none, none, none, none, none, none, none, none, none, some (.ptr none)]⟩)]

theorem null_table_returns_before_missing_mask_and_shift :
    observation ((machine.run 3 (initial nullTable)).2) = (1, none) ∧
    (machine.run 3 (initial nullTable)).1.map (fun receipt => receipt.operation) =
      [.load (directory + 9), .ptrEq none none] := by
  unfold initial
  rw [source_program]
  constructor
  · decide +kernel
  · rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.SourceRead.Controls
end NativeDirectoryLookupPackage
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section NativeIdentityHelperPackage
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option autoImplicit false
set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def output : Ptr := ⟨93, 0⟩
private def storage : Storage CVal := [(93, ⟨true, [none, none, none]⟩)]
private def initial : State CVal Bool := ⟨partsProgram 1048577 output, storage, []⟩
private def saved : State CVal Bool :=
  match (machine.run 2 initial).2 with
  | .exhausted state => state
  | _ => initial
private def tag {A : Type} : Outcome (State CVal A) (Verdict CVal A) (AllocationRequest CVal) → Nat
  | .exhausted _ => 0
  | .finished (.returned _) => 1
  | .finished (.fault _) => 2
  | _ => 3
private def returned {A : Type} : Outcome (State CVal A) (Verdict CVal A) (AllocationRequest CVal) → Option A
  | .finished (.returned final) => some final.answer
  | _ => none
private def stores (events : List (Receipt CVal)) : Nat :=
  (events.filter (fun event => match event.operation with | .store _ _ => true | _ => false)).length

theorem two_stores_are_not_completed : tag (machine.run 2 initial).2 = 0 := rfl

theorem partial_cells_are_retained :
    (saved.storage.lookup 93).map Block.cells = some [some (.u32 1), some (.u32 1), none] := by
  decide +kernel

theorem resume_retains_exact_validation_occurrences :
    (machine.run 7 saved).1.map (fun event => event.operation) =
      [.store (output + 2) (.u32 2046), .load output, .load output,
       .load (output + 1), .load (output + 1), .load (output + 2)] ∧
    returned (machine.run 7 saved).2 = some true := by
  constructor
  · rfl
  · decide +kernel

theorem restart_would_replay_prior_writes :
    stores (machine.run 7 saved).1 = 1 ∧
      stores (machine.run 9 { saved with control := partsProgram 1048577 output }).1 = 3 := by
  constructor <;> decide +kernel

theorem malformed_prefix_writes_before_false :
    returned (machine.run 4 ⟨partsProgram 4026531841 output, storage, []⟩).2 = some false ∧
    stores (machine.run 4 ⟨partsProgram 4026531841 output, storage, []⟩).1 = 3 := by
  constructor <;> decide +kernel

theorem malformed_prefix_handle_wrapper_still_returns_written_handle :
    returned (machine.run 5 ⟨handleProgram 4026531841 output, storage, []⟩).2 = some 152043521 := by
  decide +kernel

theorem reserved_generation_is_not_issuable_but_is_readable :
    returned (machine.run 9 ⟨partsProgram 2146435073 output, storage, []⟩).2 = some false ∧
    returned (machine.run 10 ⟨generationProgram 2146435073 output, storage, []⟩).2 = some 2047 := by
  constructor <;> decide +kernel

theorem dead_local_storage_is_a_fault :
    tag (machine.run 4 ⟨partsProgram 1048577 output, [(93, ⟨false, [none, none, none]⟩)], []⟩).2 = 2 ∧
    (machine.run 4 ⟨partsProgram 1048577 output, [(93, ⟨false, [none, none, none]⟩)], []⟩).1 = [] := by
  constructor <;> rfl

theorem undersized_local_keeps_first_two_stores_then_faults :
    tag (machine.run 4 ⟨partsProgram 1048577 output, [(93, ⟨true, [none, none]⟩)], []⟩).2 = 2 ∧
    stores (machine.run 4 ⟨partsProgram 1048577 output, [(93, ⟨true, [none, none]⟩)], []⟩).1 = 2 := by
  constructor <;> decide +kernel

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityRead.Controls
end NativeIdentityHelperPackage
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section NativeIdentityHelperPackage
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option autoImplicit false
set_option autoImplicit false
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityWrapper.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open ObjectBindings

private def output : Ptr := ⟨94, 0⟩
private def oldParts : Binding := .scalar ⟨"uint32_t".toList, 0⟩ (some (.u32 99))
private def context (identity : UInt32) : Context := fun name =>
  if name = "identity".toList then some (.scalar ⟨"CettaFrameIdentity".toList, 0⟩ (some (.u32 identity)))
  else if name = "parts".toList then some oldParts else none
private def enter : Name → Nat → CProg CVal Ptr := fun _ _ => pure output
private def leave : Name → Ptr → Nat → CProg CVal Unit := fun _ address _ => CProg.free (some address)
private def program (identity : UInt32) : CProg CVal (ReadBlock.Result Context) :=
  executeScopedWith (service 0 (AutomaticRegion.bracket enter leave)) IdentityRead.layout 0 3
    (context identity) IdentitySource.handleBody

theorem actual_wrapper_operations (identity : UInt32) : program identity =
    (IdentityRead.handleProgram identity output >>= fun word =>
      CProg.free (some output) >>= fun _ =>
        pure (.finished (.returned (context identity) (some (.u32 word))))) := by
  unfold program
  rw [actual_handle_body 0 0 enter leave (context identity) identity (by simp only [context, ↓reduceIte])]
  simp only [enter, leave, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind]

private def initial (identity : UInt32) : State CVal (ReadBlock.Result Context) :=
  ⟨program identity, [(94, ⟨true, [none, none, none]⟩)], []⟩
private def observation : Outcome (State CVal (ReadBlock.Result Context))
    (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal) →
      Nat × Option CVal × Bool × Option Bool
  | .finished (.returned final) =>
      match final.answer with
      | .finished (.returned ctx value) =>
          (1, value, decide (ctx "parts".toList = some oldParts), (final.storage.lookup 94).map Block.live)
      | _ => (2, none, false, none)
  | .exhausted saved => (0, none, false, (saved.storage.lookup 94).map Block.live)
  | .finished (.fault saved) => (3, none, false, (saved.storage.lookup 94).map Block.live)
  | _ => (4, none, false, none)

private def saved : State CVal (ReadBlock.Result Context) :=
  match (machine.run 2 (initial 1048577)).2 with
  | .exhausted state => state
  | _ => initial 1048577

theorem actual_wrapper_returns_field_and_restores_shadowed_binding :
    observation (machine.run 11 (initial 1048577)).2 = (1, some (.u32 1), true, some false) := by
  unfold initial
  rw [actual_wrapper_operations]
  decide +kernel

theorem paused_wrapper_keeps_automatic_storage_live :
    observation (machine.run 2 (initial 1048577)).2 = (0, none, false, some true) := by
  unfold initial
  rw [actual_wrapper_operations]
  decide +kernel

theorem resumed_wrapper_runs_remaining_store_reads_and_exit_once :
    (machine.run 9 saved).1.map (fun event => event.operation) =
      [.store (output + 2) (.u32 2046), .load output, .load output,
       .load (output + 1), .load (output + 1), .load (output + 2), .load output,
       .free (some output)] ∧
    observation (machine.run 9 saved).2 = (1, some (.u32 1), true, some false) := by
  unfold saved initial
  rw [actual_wrapper_operations]
  constructor
  · rfl
  · decide +kernel

theorem actual_wrapper_returns_malformed_handle_after_false :
    observation (machine.run 6 (initial 4026531841)).2 =
      (1, some (.u32 152043521), true, some false) := by
  unfold initial
  rw [actual_wrapper_operations]
  decide +kernel

theorem wrong_parts_pointer_shape_is_not_a_codec_result :
    partsCall 0 "cetta_frame_identity_parts".toList [.u32 1048577, .ptr none] = CProg.undefined := rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.IdentityWrapper.Controls
end NativeIdentityHelperPackage
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
section NumberedSymbolReadout
set_option maxHeartbeats 1200000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage ProductiveBlocks

abbrev table : Ptr := ⟨111, 0⟩
abbrev chunks : Ptr := ⟨112, 0⟩
abbrev chunk : Ptr := ⟨113, 0⟩
abbrev firstBytes : Ptr := ⟨114, 0⟩
abbrev secondBytes : Ptr := ⟨115, 0⟩
abbrev atom : Ptr := ⟨116, 0⟩
abbrev untouched : Ptr := ⟨117, 0⟩
abbrev emptyLiteral : Ptr := ⟨118, 0⟩

def storage : Storage CVal :=
  [(111, ⟨true, [some (.ptr none), some (.u32 0), some (.u32 0), some (.u64 19),
    some (.ptr (some chunks)), some (.u32 3)]⟩),
   (112, ⟨true, [some (.ptr (some chunk))]⟩),
   (113, ⟨true, [none, none, none, none, none,
    some (.ptr (some firstBytes)), some (.u32 3), some (.u64 17), some (.u32 0), some (.u32 0),
    some (.ptr (some secondBytes)), some (.u32 1), some (.u64 23), some (.u32 0), some (.u32 0)]⟩),
   (114, ⟨true, [some (.u8 65), some (.u8 0), some (.u8 66)]⟩),
   (115, ⟨true, [some (.u8 90)]⟩),
   (116, ⟨true, [some (.u32 0), none, none, some (.u32 1), some (.u32 7), some (.ptr none)]⟩),
   (117, ⟨true, [some (.u32 937)]⟩),
   (118, ⟨true, [some (.u8 0)]⟩)]

def inventory : PhysicalAtoms.Inventory := fun pointer =>
  if pointer.block = 114 ∧ pointer.offset < 3 then some .byteCell
  else if pointer.block = 115 ∧ pointer.offset < 1 then some .byteCell
  else if pointer = atom then some .atom
  else none

def readBytes (data : Storage CVal) (identifier : UInt32) : Option ByteArray :=
  physicalBytes? inventory (heap data) table identifier

def pointerObservation (result : Outcome (State CVal (Option Ptr))
    (Verdict CVal (Option Ptr)) (AllocationRequest CVal)) : Nat × Option Ptr :=
  match result with
  | .exhausted _ => (0, none)
  | .finished (.returned final) => (1, final.answer)
  | .finished (.fault _) => (2, none)
  | _ => (3, none)

def numberObservation (result : Outcome (State CVal UInt32)
    (Verdict CVal UInt32) (AllocationRequest CVal)) : Nat × UInt32 :=
  match result with
  | .exhausted _ => (0, 0)
  | .finished (.returned final) => (1, final.answer)
  | .finished (.fault _) => (2, 0)
  | _ => (3, 0)

def initialBytes : State CVal (Option Ptr) :=
  ⟨bytesOperation emptyLiteral (some table) 1, storage, []⟩

def forbiddenLookup (_ : Option Ptr) : CProg CVal UInt32 := do
  CProg.store untouched (.u32 0)
  pure 999

theorem numbered_current_id_does_not_call_lookup_or_touch_the_frame :
    numberObservation ((machine.run 20
      ⟨Current.operations forbiddenLookup (some atom), storage, []⟩).2) = (1, 1) ∧
    (match (machine.run 20 ⟨Current.operations forbiddenLookup (some atom), storage, []⟩).2 with
     | .finished (.returned final) => final.storage = storage
     | _ => False) := by exact ⟨rfl, rfl⟩

theorem null_current_id_does_not_read_an_atom :
    numberObservation ((machine.run 4
      ⟨Current.operations forbiddenLookup none, storage, []⟩).2) = (1, 0) ∧
    (machine.run 4 ⟨Current.operations forbiddenLookup none, storage, []⟩).1.map
      (fun receipt => receipt.operation) = [.ptrEq none none] := by
  exact ⟨rfl, rfl⟩

/-- The managed branch dispatches the original Atom to its explicit lookup
component once. This checks dispatch only, not the lookup algorithm. -/
theorem managed_current_id_keeps_its_lookup_component :
    let changed := put storage 116 ⟨true,
      [some (.u32 0), none, none, some (.u32 0), some (.u32 7), some (.ptr (some firstBytes))]⟩
    numberObservation ((machine.run 20
      ⟨Current.operations forbiddenLookup (some atom), changed, []⟩).2) = (1, 999) ∧
    (machine.run 20 ⟨Current.operations forbiddenLookup (some atom), changed, []⟩).1.map
      (fun receipt => receipt.operation) =
      [.ptrEq (some atom) none, .load atom, .load (atom + 3), .load (atom + 5),
       .ptrEq (some firstBytes) none, .store untouched (.u32 0)] := by
  exact ⟨rfl, rfl⟩

theorem numbered_current_id_keeps_both_number_reads :
    (machine.run 20 ⟨Current.operations forbiddenLookup (some atom), storage, []⟩).1.map
      (fun receipt => receipt.operation) =
      [.ptrEq (some atom) none, .load atom, .load (atom + 3), .load (atom + 3)] := by rfl

theorem actual_chunk_and_return_reads_are_retained :
    (machine.run 30 initialBytes).1.map (fun receipt => receipt.operation) =
      [.ptrEq (some table) none, .load (table + 5), .ptrEq (some table) none,
       .load (table + 4), .ptrEq (some chunks) none, .load (table + 4),
       .load chunks, .ptrEq (some chunk) none,
       .ptrEq (some (chunk + 5)) none, .load (chunk + 5),
       .ptrEq (some firstBytes) none, .load (chunk + 5)] := by rfl

theorem actual_table_result_and_resumption :
    pointerObservation ((machine.run 30 initialBytes).2) = (1, some firstBytes) ∧
    pointerObservation ((machine.run 5 initialBytes).2) = (0, none) ∧
    pointerObservation ((machine.continueRun 30 (machine.run 5 initialBytes)).2) = (1, some firstBytes) ∧
    (machine.continueRun 30 (machine.run 5 initialBytes)).1.map (fun receipt => receipt.operation) =
      (machine.run 35 initialBytes).1.map (fun receipt => receipt.operation) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem actual_bytes_helper_preserves_all_storage :
    match (machine.run 30 initialBytes).2 with
    | .finished (.returned final) => final.storage = storage
    | _ => False := by rfl

theorem exact_length_preserves_embedded_nul :
    readBytes storage 1 = some ⟨#[65, 0, 66]⟩ ∧
    String.fromUTF8? ⟨#[65, 0, 66]⟩ = some (String.ofList ['A', '\x00', 'B']) := by
  decide +kernel

theorem different_published_rows_keep_different_bytes :
    readBytes storage 2 = some ⟨#[90]⟩ ∧ readBytes storage 1 ≠ readBytes storage 2 := by decide +kernel

theorem zero_and_unpublished_ids_are_refused_by_the_decoder :
    readBytes storage 0 = none ∧ readBytes storage 3 = none := by decide +kernel

theorem source_zero_fallback_is_distinct_from_decoder_admission :
    pointerObservation ((machine.run 10
      ⟨bytesOperation emptyLiteral (some table) 0, storage, []⟩).2) = (1, some emptyLiteral) ∧
    readBytes storage 0 = none := by decide +kernel

theorem invalid_utf8_is_preserved_as_bytes :
    let changed := put storage 114 ⟨true, [some (.u8 65), some (.u8 255), some (.u8 0)]⟩
    readBytes changed 1 = some ⟨#[65, 255, 0]⟩ ∧
    String.fromUTF8? ⟨#[65, 255, 0]⟩ = none := by decide +kernel

theorem malformed_chunk_pointer_is_not_an_empty_name :
    pointerObservation ((machine.run 30
      ⟨bytesOperation emptyLiteral (some table) 1,
        put storage 112 ⟨true, [some (.u32 113)]⟩, []⟩).2) = (2, none) := by decide +kernel

theorem missing_payload_byte_is_not_filled_in :
    readBytes (put storage 114 ⟨true, [some (.u8 65)]⟩) 1 = none := by decide +kernel

theorem dead_payload_is_refused :
    readBytes (put storage 114 ⟨false, [some (.u8 65), some (.u8 0), some (.u8 66)]⟩) 1 = none := by
  decide +kernel

theorem row_address_crosses_the_actual_chunk_boundary :
    chunkIndex 16383 = 0 ∧ rowIndex 16383 = 16383 ∧
    chunkIndex 16384 = 1 ∧ rowIndex 16384 = 0 := by decide +kernel

/-- This deliberately incoherent forwarding record is a counterexample to
an unrestricted helper-invariance claim, not a claim that native copying
constructs such a record. The real update requires same-symbol evidence. -/
theorem current_id_is_not_unconditionally_forwarding_invariant :
    let target : Ptr := ⟨119, 0⟩
    let changed := put (put storage 119 ⟨true,
      [some (.u32 0), none, none, some (.u32 1), some (.u32 7), some (.ptr none)]⟩)
      116 ⟨true, [some (.u32 0), none, none, some (.u32 2),
        some (.u32 4294967295), some (.ptr (some target))]⟩
    numberObservation ((machine.run 20
      ⟨Current.operations forbiddenLookup (some atom), changed, []⟩).2) = (1, 2) ∧
    numberObservation ((machine.run 20
      ⟨Current.operations forbiddenLookup (some target), changed, []⟩).2) = (1, 1) := by
  exact ⟨rfl, rfl⟩


end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Controls
end NumberedSymbolReadout
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.RefArgument
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.CMemory
open ReadExpressions StatementBlock
open StatementBlock.ObjectBindings
namespace Controls
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def sourceAddress : Ptr := ⟨81, 0⟩
def parameterAddress : Ptr := ⟨82, 0⟩
def scopeMarker : Ptr := ⟨83, 0⟩

def region : AutomaticRegion Context := AutomaticRegion.bracket
  (fun _ _ => CProg.store scopeMarker (.bool true) >>= fun _ => pure parameterAddress)
  (fun _ _ _ => CProg.store scopeMarker (.bool false))

def storage (value : Option CVal) : Storage CVal :=
  [(81, ⟨true, [value]⟩), (82, ⟨true, [none]⟩),
   (83, ⟨true, [some (.bool false)]⟩)]

def initial (value : Option CVal) : State CVal CVal :=
  ⟨call region sourceAddress, storage value, []⟩

def outcome (result : Outcome (State CVal CVal) (Verdict CVal CVal)
    (AllocationRequest CVal)) : Nat × Option CVal :=
  match result with
  | .finished (.returned final) => (1, some final.answer)
  | .finished (.fault _) => (2, none)
  | .exhausted _ => (3, none)
  | _ => (4, none)

def after (result : Outcome (State CVal CVal) (Verdict CVal CVal)
    (AllocationRequest CVal)) : Storage CVal :=
  match result with
  | .finished (.returned final) => final.storage
  | .finished (.fault state) | .exhausted state => state.storage
  | _ => []

theorem zero_identity_is_false :
    outcome ((machine.run 6 (initial (some (.u32 0)))).2) = (1, some (.bool false)) := by
  rw [initial, region, call_retains_operations]
  decide +kernel

theorem nonzero_identity_is_true :
    outcome ((machine.run 6 (initial (some (.u32 1048583)))).2) = (1, some (.bool true)) := by
  rw [initial, region, call_retains_operations]
  decide +kernel

theorem exact_call_receipts :
    (machine.run 6 (initial (some (.u32 7)))).1.map (fun receipt => receipt.operation) =
      [.load sourceAddress, .store scopeMarker (.bool true),
       .store parameterAddress (.u32 7), .load parameterAddress,
       .store scopeMarker (.bool false)] := by
  rw [initial, region, call_retains_operations]
  rfl

theorem source_retained_parameter_copied_scope_closed :
    after ((machine.run 6 (initial (some (.u32 7)))).2) =
      [(83, ⟨true, [some (.bool false)]⟩), (82, ⟨true, [some (.u32 7)]⟩),
       (83, ⟨true, [some (.bool true)]⟩)] ++ storage (some (.u32 7)) := by
  rw [initial, region, call_retains_operations]
  rfl

theorem uninitialized_argument_refuses_before_parameter_entry :
    outcome ((machine.run 6 (initial none)).2) = (2, none) ∧
    (machine.run 6 (initial none)).1 = [] := by
  rw [initial, region, call_retains_operations]
  constructor
  · decide +kernel
  · rfl

theorem wrong_field_type_is_not_false :
    outcome ((machine.run 6 (initial (some (.ptr none)))).2) = (2, none) := by
  rw [initial, region, call_retains_operations]
  decide +kernel

def paused : State CVal CVal :=
  match (machine.run 3 (initial (some (.u32 7)))).2 with
  | .exhausted saved => saved
  | _ => initial (some (.u32 7))

theorem pause_keeps_snapshot_and_resume_does_not_recopy :
    outcome ((machine.run 3 (initial (some (.u32 7)))).2) = (3, none) ∧
    outcome ((machine.run 3 paused).2) = (1, some (.bool true)) ∧
    (machine.run 3 paused).1.map (fun receipt => receipt.operation) =
      [.load parameterAddress, .store scopeMarker (.bool false)] := by
  constructor
  · rw [initial, region, call_retains_operations]
    decide +kernel
  constructor
  · simp only [paused, initial, region, call_retains_operations]
    decide +kernel
  · simp only [paused, initial, region, call_retains_operations]
    rfl

end Controls
end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.RefArgument
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful.Controls
open DirectoryProbe.SourceRead (lookupProgram actual_lookup_body)
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open ObjectBindings
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

abbrev directory := Physical.Controls.directory
abbrev table := Physical.Controls.table
abbrev first := Physical.Controls.first
abbrev second := Physical.Controls.second

def output : Ptr := ⟨94, 0⟩
def marker : Ptr := ⟨95, 0⟩
def callee : Context := fun name =>
  if name = "identity".toList then SourceRead.scalar Source.uint32 (.u32 71)
  else if name = "parts".toList then SourceRead.scalar Source.uint32 (.u32 72)
  else none

def enter : Name → Nat → CProg CVal Ptr := fun _ _ =>
  CProg.store marker (.bool true) >>= fun _ => pure output
def leave : Name → Ptr → Nat → CProg CVal Unit := fun _ _ _ =>
  CProg.store marker (.bool false)
def decoder : UInt32 → CProg CVal UInt32 := IdentityWrapper.handleCall 0 enter leave callee

def sourceProgram : CProg CVal (ReadBlock.Result Context) :=
  executeScopedWith (SourceRead.services decoder) SourceRead.layout 4 12
    SourceRead.Controls.context Source.lookupBody

theorem source_program : sourceProgram =
    (lookupProgram (fun identity => CProg.store marker (.bool true) >>= fun _ =>
      IdentityRead.handleProgram identity output >>= fun word =>
        CProg.store marker (.bool false) >>= fun _ => pure word)
      directory 3 4 >>= fun result =>
        pure (result.mapContext (fun _ => SourceRead.Controls.context))) := by
  rw [sourceProgram, actual_lookup_body decoder SourceRead.Controls.context directory
    SourceRead.Controls.directoryType 3 4 (by rfl) (by rfl)]
  have decoderBody : decoder = fun identity => CProg.store marker (.bool true) >>= fun _ =>
      IdentityRead.handleProgram identity output >>= fun word =>
        CProg.store marker (.bool false) >>= fun _ => pure word := by
    funext identity
    rw [decoder, IdentityWrapper.handle_call_keeps_source_operations]
    simp only [enter, leave, Prog.bind_eq, Prog.bind_assoc, Prog.pure_eq, Prog.ret_bind]
  rw [decoderBody]

def storage : Storage CVal :=
  [(94, ⟨true, [none, none, none]⟩), (95, ⟨true, [some (.bool false)]⟩)] ++
    SourceRead.Controls.storage

def initial (memory : Storage CVal := storage) : State CVal (ReadBlock.Result Context) :=
  ⟨sourceProgram, memory, []⟩

abbrev observation := SourceRead.Controls.observation
abbrev locals := SourceRead.Controls.locals

def saved : State CVal (ReadBlock.Result Context) :=
  match (machine.run 11 initial).2 with
  | .exhausted state => state
  | _ => initial

def after (result : Outcome (State CVal (ReadBlock.Result Context))
    (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal)) : Storage CVal :=
  match result with
  | .finished (.returned final) => final.storage
  | .finished (.fault state) | .exhausted state => state.storage
  | _ => []

/-- A borrowed scratch activation has observable entry/exit markers; the
underlying native automatic allocator and ABI remain separate obligations. -/
theorem parsed_lookup_with_effectful_helpers :
    observation (machine.run 35 initial).2 = (1, some second) ∧
    locals (machine.run 35 initial).2 = (some (.bool true), some (.u32 900), some (.u32 61)) ∧
    ((after (machine.run 35 initial).2).lookup 95).map Block.cells =
      some [some (.bool false)] := by
  unfold initial
  rw [source_program]
  constructor
  · decide +kernel
  constructor <;> decide +kernel

theorem both_helper_invocations_keep_all_stores :
    ((machine.run 35 initial).1.filter fun event => match event.operation with
      | .store _ _ => true | _ => false).length = 10 := by
  unfold initial
  rw [source_program]
  decide +kernel

theorem paused_after_partial_helper_writes :
    observation (machine.run 11 initial).2 = (0, none) ∧
    (saved.storage.lookup 94).map Block.cells =
      some [some (.u32 8), some (.u32 1), none] ∧
    (saved.storage.lookup 95).map Block.cells = some [some (.bool true)] := by
  unfold saved initial
  rw [source_program]
  constructor
  · decide +kernel
  constructor <;> decide +kernel

theorem resume_begins_at_remaining_field_and_preserves_parent_loop :
    (machine.run 24 saved).1.head?.map (fun event => event.operation) =
      some (.store (output + 2) (.u32 2046)) ∧
    observation (machine.run 24 saved).2 = (1, some second) := by
  unfold saved initial
  rw [source_program]
  constructor
  · rfl
  · decide +kernel

/-- A pure decoder has the same successful pointer, but loses helper entry,
partial stores, validation-read occurrences and exit. It cannot be the trace
observer for the actual called helper. -/
theorem pure_decoder_loses_effects :
    observation (machine.run 35 initial).2 =
      observation (machine.run 13 SourceRead.Controls.initial).2 ∧
    (machine.run 35 initial).1.length ≠
      (machine.run 13 SourceRead.Controls.initial).1.length := by
  unfold initial
  rw [source_program]
  unfold SourceRead.Controls.initial
  rw [SourceRead.Controls.source_program]
  constructor <;> decide +kernel

def undersized : Storage CVal :=
  [(94, ⟨true, [none, none]⟩), (95, ⟨true, [some (.bool false)]⟩)] ++
    SourceRead.Controls.storage

theorem partial_helper_fault_is_not_lookup_absence :
    observation (machine.run 35 (initial undersized)).2 = (4, none) ∧
    ((after (machine.run 35 (initial undersized)).2).lookup 94).map Block.cells =
      some [some (.u32 8), some (.u32 1)] ∧
    ((after (machine.run 35 (initial undersized)).2).lookup 95).map Block.cells =
      some [some (.bool true)] := by
  unfold initial
  rw [source_program]
  constructor
  · decide +kernel
  constructor <;> decide +kernel

theorem exhausted_loop_does_not_publish_absence :
    observation (machine.run 5
      ⟨lookupProgram decoder directory 3 0 >>= fun result =>
        pure (result.mapContext (fun _ => SourceRead.Controls.context)), storage, []⟩).2 =
      (2, none) := by decide +kernel


def staleLocal : Storage CVal :=
  [(94, ⟨false, [none, none, none]⟩), (95, ⟨true, [some (.bool false)]⟩)] ++
    SourceRead.Controls.storage

theorem stale_local_cannot_be_replaced_by_pure_decode :
    observation (machine.run 35 (initial staleLocal)).2 = (4, none) ∧
    ((after (machine.run 35 (initial staleLocal)).2).lookup 95).map Block.cells =
      some [some (.bool true)] := by
  unfold initial
  rw [source_program]
  constructor <;> decide +kernel

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.DirectoryProbe.Effectful.Controls
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.ReadExpressions
open Mettapedia.Machines.CMemory.StatementBlock
open ObjectBindings
open Mettapedia.Machines.CMemory.ProductiveBlocks
open Mettapedia.Machines.CMemory.ExecutableStorage
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open DirectoryProbe

abbrev directory := Physical.Controls.directory
abbrev second := Physical.Controls.second
abbrev parts := Effectful.Controls.output
abbrev partsMarker := Effectful.Controls.marker
def temporaryRef : Ptr := ⟨96, 0⟩
def refMarker : Ptr := ⟨97, 0⟩
def outerRef : Ptr := ⟨98, 0⟩
def outerMarker : Ptr := ⟨99, 0⟩

def outer : Context := fun name =>
  if name = "index".toList then SourceRead.scalar Source.uint32 (.u32 81)
  else if name = "ref".toList then SourceRead.scalar Source.uint32 (.u32 82)
  else if name = "entry".toList then SourceRead.scalar Source.uint32 (.u32 83)
  else if name = "older".toList then SourceRead.scalar Source.uint32 (.u32 84)
  else none

def enter : Name → Nat → CProg CVal Ptr := fun name _ =>
  if name = "parts".toList then
    CProg.store partsMarker (.bool true) >>= fun _ => pure parts
  else if name = RefArgument.refName then
    CProg.store refMarker (.bool true) >>= fun _ => pure temporaryRef
  else CProg.undefined

def leave : Name → Ptr → Nat → CProg CVal Unit := fun name _ _ =>
  if name = "parts".toList then CProg.store partsMarker (.bool false)
  else if name = RefArgument.refName then CProg.store refMarker (.bool false)
  else CProg.undefined

def parameterEnter : Name → Nat → CProg CVal Ptr := fun _ _ =>
  CProg.store outerMarker (.bool true) >>= fun _ => pure outerRef

def parameterLeave : Name → Ptr → Nat → CProg CVal Unit := fun _ _ _ =>
  CProg.store outerMarker (.bool false)

def region : AutomaticRegion Context := AutomaticRegion.bracket enter leave

def sourceProgram (identity : UInt32) (index : Option Ptr := some directory) :
    CProg CVal (ReadBlock.Result Context) :=
  invoke (AutomaticRegion.bracket parameterEnter parameterLeave) region
    (actualCalls 0 4 enter leave Effectful.Controls.callee region)
    SourceRead.layout 3 outer [.scalar (.ptr index), .record RefArgument.refType [.u32 identity]]

def decoder (identity : UInt32) : CProg CVal UInt32 := do
  CProg.store partsMarker (.bool true)
  let value ← IdentityRead.handleProgram identity parts
  CProg.store partsMarker (.bool false)
  pure value

def continuation : CProg CVal CVal := do
  let identity ← CProg.loadU32 outerRef
  let key ← decoder identity
  let result ← SourceRead.lookupProgram decoder directory key 4
  let value ← RefArgument.returnedScalar (result.mapContext (fun _ => Effectful.Controls.callee))
  let entry ← pointer value
  finalRead entry outerRef

/-- Normalize only through proved source squares before executing controls.
The resulting operation tree still contains every physical load and store. -/
theorem source_program (identity : UInt32) : sourceProgram identity =
    (CProg.store outerMarker (.bool true) >>= fun _ =>
      CProg.store outerRef (.u32 identity) >>= fun _ =>
      CProg.ptrEq (some directory) none >>= fun isNull =>
      (if isNull then pure (.ptr none) else
        CProg.load outerRef >>= fun captured =>
        CProg.store refMarker (.bool true) >>= fun _ =>
        CProg.store temporaryRef captured >>= fun _ =>
        CProg.loadU32 temporaryRef >>= fun observed =>
        CProg.store refMarker (.bool false) >>= fun _ =>
        if observed == 0 then pure (.ptr none) else continuation) >>= fun value =>
      CProg.store outerMarker (.bool false) >>= fun _ =>
      pure (.finished (.returned outer (some value)))) := by
  unfold sourceProgram
  change invoke (AutomaticRegion.bracket parameterEnter parameterLeave)
    (AutomaticRegion.bracket enter leave)
    (actualCalls 0 4 enter leave Effectful.Controls.callee region) SourceRead.layout (0 + 3)
    outer [.scalar (.ptr (some directory)), .record RefArgument.refType [.u32 identity]] = _
  rw [invoke_keeps_actual_body (actualCalls 0 4 enter leave Effectful.Controls.callee region)
    outer (some directory) identity parameterEnter enter parameterLeave leave 0]
  have decode : IdentityWrapper.handleCall 0 enter leave Effectful.Controls.callee = decoder := by
    funext value
    rw [IdentityWrapper.handle_call_keeps_source_operations]
    simp only [decoder, enter, leave, ↓reduceIte, Prog.bind_eq, Prog.bind_assoc,
      Prog.pure_eq, Prog.ret_bind]
  have after : afterGuard (actualCalls 0 4 enter leave Effectful.Controls.callee region)
      (some directory) outerRef = continuation := by
    rw [after_guard_actual_helpers, decode]
    rfl
  simp only [parameterEnter, parameterLeave, bodyOperations, Prog.bind_eq, Prog.bind_assoc,
    Prog.pure_eq, Prog.ret_bind, enter, leave,
    if_neg (by decide : RefArgument.refName ≠ "parts".toList), ↓reduceIte, after]

def storage : Storage CVal :=
  [(96, ⟨true, [none]⟩), (97, ⟨true, [some (.bool false)]⟩),
   (98, ⟨true, [none]⟩), (99, ⟨true, [some (.bool false)]⟩)] ++ Effectful.Controls.storage

def initial (identity : UInt32 := 1048579) (memory : Storage CVal := storage) :
    State CVal (ReadBlock.Result Context) := ⟨sourceProgram identity, memory, []⟩

abbrev observation := SourceRead.Controls.observation
abbrev after := Effectful.Controls.after

def lexical (result : Outcome (State CVal (ReadBlock.Result Context))
    (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal)) : List (Option CVal) :=
  match result with
  | .finished (.returned completed) => match completed.answer with
      | .finished (.returned context _) =>
          [ObjectBindings.values context "index".toList,
           ObjectBindings.values context "ref".toList,
           ObjectBindings.values context "entry".toList,
           ObjectBindings.values context "older".toList]
      | _ => []
  | _ => []

theorem actual_nested_helpers_and_shadowed_locals :
    observation (machine.run 80 initial).2 = (1, some second) ∧
    lexical (machine.run 80 initial).2 =
      [some (.u32 81), some (.u32 82), some (.u32 83), some (.u32 84)] ∧
    ((after (machine.run 80 initial).2).lookup 99).map Block.cells = some [some (.bool false)] := by
  unfold initial
  rw [source_program]
  constructor
  · decide +kernel
  constructor <;> decide +kernel

theorem stale_generation_is_completed_absence :
    observation (machine.run 80 (initial 2097155)).2 = (1, none) := by
  unfold initial
  rw [source_program]
  decide +kernel

theorem zero_reference_stops_before_handle_and_lookup :
    observation (machine.run 15 (initial 0)).2 = (1, none) ∧
    ((machine.run 15 (initial 0)).1.filter fun receipt => match receipt.operation with
      | .load address => address == directory + 9 | _ => false).isEmpty = true := by
  unfold initial
  rw [source_program]
  constructor <;> decide +kernel


/-- The outer copied Ref and two first helper stores survive a scheduler pause.
The third store has not occurred and neither helper exit has been invented. -/
def saved : State CVal (ReadBlock.Result Context) :=
  match (machine.run 12 initial).2 with
  | .exhausted state => state
  | _ => initial

theorem pause_retains_partial_helper_and_outer_parameter :
    observation (machine.run 12 initial).2 = (0, none) ∧
    (saved.storage.lookup 94).map Block.cells = some [some (.u32 3), some (.u32 1), none] ∧
    (saved.storage.lookup 95).map Block.cells = some [some (.bool true)] ∧
    (saved.storage.lookup 98).map Block.cells = some [some (.u32 1048579)] ∧
    (saved.storage.lookup 99).map Block.cells = some [some (.bool true)] := by
  unfold saved initial
  rw [source_program]
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor
  · decide +kernel
  constructor <;> decide +kernel

theorem resumed_source_starts_with_pending_store :
    (machine.run 68 saved).1.head?.map (fun receipt => receipt.operation) =
      some (.store (parts + 2) (.u32 2046)) ∧
    observation (machine.run 68 saved).2 = (1, some second) ∧
    lexical (machine.run 68 saved).2 =
      [some (.u32 81), some (.u32 82), some (.u32 83), some (.u32 84)] := by
  unfold saved initial
  rw [source_program]
  constructor
  · rfl
  constructor <;> decide +kernel

theorem resumed_source_keeps_exact_receipt_prefix :
    machine.run 80 initial =
      ((machine.run 12 initial).1 ++ (machine.run 68 saved).1, (machine.run 68 saved).2) := by
  apply resume_after_prefix 12 68 initial saved
  unfold saved initial
  rw [source_program]
  rfl

theorem restarting_source_repeats_recorded_effects :
    ((machine.run 12 initial).1 ++ (machine.run 80 initial).1).length ≠
      (machine.run 80 initial).1.length := by
  unfold initial
  rw [source_program]
  decide +kernel

def undersized : Storage CVal :=
  (94, ⟨true, [none, none]⟩) :: storage

theorem partial_write_fault_retains_outer_activation :
    observation (machine.run 80 (initial 1048579 undersized)).2 = (4, none) ∧
    ((after (machine.run 80 (initial 1048579 undersized)).2).lookup 94).map Block.cells =
      some [some (.u32 3), some (.u32 1)] ∧
    ((after (machine.run 80 (initial 1048579 undersized)).2).lookup 99).map Block.cells =
      some [some (.bool true)] := by
  unfold initial
  rw [source_program]
  constructor
  · decide +kernel
  constructor <;> decide +kernel

def deadParameter : Storage CVal :=
  (98, ⟨false, [none]⟩) :: storage

theorem invalid_parameter_storage_is_fault_not_absence :
    observation (machine.run 80 (initial 1048579 deadParameter)).2 = (4, none) ∧
    ((after (machine.run 80 (initial 1048579 deadParameter)).2).lookup 99).map Block.cells =
      some [some (.bool true)] := by
  unfold initial
  rw [source_program]
  constructor <;> decide +kernel


theorem null_index_copies_outer_parameter_but_skips_nested_calls :
    observation (machine.run 8 ⟨sourceProgram 1048579 none, storage, []⟩).2 = (1, none) ∧
    (machine.run 8 ⟨sourceProgram 1048579 none, storage, []⟩).1.map
      (fun receipt => receipt.operation) =
      [.store outerMarker (.bool true), .store outerRef (.u32 1048579),
       .ptrEq none none, .store outerMarker (.bool false)] := by
  have source : sourceProgram 1048579 none =
      (parameterEnter RefArgument.refName 1 >>= fun address =>
        CProg.store address (.u32 1048579) >>= fun _ =>
        bodyOperations enter leave
          (actualCalls 0 4 enter leave Effectful.Controls.callee region) none address >>= fun value =>
        parameterLeave RefArgument.refName address 1 >>= fun _ =>
        pure (.finished (.returned outer (some value)))) :=
    invoke_keeps_actual_body (actualCalls 0 4 enter leave Effectful.Controls.callee region)
      outer none 1048579 parameterEnter enter parameterLeave leave 0
  rw [source]
  constructor
  · decide +kernel
  · rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.FindRefArgument.Controls
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.EntryMatch.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage ProductiveBlocks

abbrev entry : Ptr := ⟨221, 0⟩
abbrev stored : Ptr := ⟨222, 0⟩
abbrev query : Ptr := ⟨223, 0⟩
abbrev count : Ptr := ⟨224, 0⟩

def storage : Storage CVal :=
  [(221, ⟨true, [some (.ptr (some stored)), some (.u32 3), some (.u64 17)]⟩),
   (222, ⟨true, [some (.u8 65), some (.u8 0), some (.u8 255)]⟩),
   (223, ⟨true, [some (.u8 65), some (.u8 0), some (.u8 255)]⟩),
   (224, ⟨true, [some (.u32 0)]⟩)]

/-- A component control reads the actual two spans and marks one invocation.
It tests the adapter's selected address/length and resumption, not libc internals. -/
def observedCompare (left right : Option Ptr) (length : UInt32) : CProg CVal Int32 := do
  match left, right with
  | some left, some right =>
    let leftBytes ← CProg.loadCells left length.toNat
    let rightBytes ← CProg.loadCells right length.toNat
    let calls ← CProg.loadU32 count
    CProg.store count (.u32 (calls + 1))
    pure (if leftBytes = rightBytes then 0 else 1)
  | _, _ => CProg.undefined

def forbiddenCompare (_ _ : Option Ptr) (_ : UInt32) : CProg CVal Int32 := CProg.undefined

def observation (result : Outcome (State CVal Bool) (Verdict CVal Bool) (AllocationRequest CVal)) :
    Nat × Bool :=
  match result with
  | .exhausted _ => (0, false)
  | .finished (.returned final) => (1, final.answer)
  | .finished (.fault _) => (2, false)
  | _ => (3, false)

def initial : State CVal Bool :=
  ⟨operations observedCompare (some entry) (some query) 3 17, storage, []⟩

theorem exact_byte_spans_are_selected :
    observation ((machine.run 30 initial).2) = (1, true) ∧
    (match (machine.run 30 initial).2 with
      | .finished (.returned final) => final.storage = put storage count.block ⟨true, [some (.u32 1)]⟩
      | _ => False) := by exact ⟨rfl, rfl⟩

theorem equal_hash_and_length_do_not_admit_different_bytes :
    let changed := put storage query.block ⟨true, [some (.u8 65), some (.u8 0), some (.u8 254)]⟩
    observation ((machine.run 30
      ⟨operations observedCompare (some entry) (some query) 3 17, changed, []⟩).2) = (1, false) := by rfl

theorem nul_and_non_utf8_are_not_truncated :
    (machine.run 30 initial).1.map (fun receipt => receipt.operation) =
      [.ptrEq (some entry) none, .load entry, .ptrEq (some stored) none,
       .load (entry + 1), .load (entry + 2), .load entry,
       .load stored, .load (stored + 1), .load (stored + 2),
       .load query, .load (query + 1), .load (query + 2),
       .load count, .store count (.u32 1)] := by rfl

theorem null_entry_skips_all_later_operands :
    observation ((machine.run 5
      ⟨operations forbiddenCompare none (some query) 3 17, [], []⟩).2) = (1, false) ∧
    (machine.run 5 ⟨operations forbiddenCompare none (some query) 3 17, [], []⟩).1.map
      (fun receipt => receipt.operation) = [.ptrEq none none] := by exact ⟨rfl, rfl⟩

theorem null_bytes_do_not_read_length_or_hash :
    let missing := [(221, ⟨true, [some (.ptr none)]⟩)]
    observation ((machine.run 10
      ⟨operations forbiddenCompare (some entry) (some query) 3 17, missing, []⟩).2) = (1, false) := by rfl

theorem mismatched_length_does_not_read_hash :
    let missing := [(221, ⟨true, [some (.ptr (some stored)), some (.u32 2)]⟩),
      (222, ⟨true, []⟩)]
    observation ((machine.run 10
      ⟨operations forbiddenCompare (some entry) (some query) 3 17, missing, []⟩).2) = (1, false) := by rfl

theorem mismatched_hash_does_not_invoke_comparison :
    observation ((machine.run 10
      ⟨operations forbiddenCompare (some entry) (some query) 3 18, storage, []⟩).2) = (1, false) := by rfl

theorem matched_headers_do_not_hide_a_refused_comparison :
    observation ((machine.run 10
      ⟨operations forbiddenCompare (some entry) (some query) 3 17, storage, []⟩).2) = (2, false) := by rfl

theorem malformed_length_is_refused :
    let changed := put storage entry.block
      ⟨true, [some (.ptr (some stored)), some (.u64 3), some (.u64 17)]⟩
    observation ((machine.run 10
      ⟨operations observedCompare (some entry) (some query) 3 17, changed, []⟩).2) = (2, false) := by rfl

theorem dead_entry_is_refused :
    let changed := put storage entry.block
      ⟨false, [some (.ptr (some stored)), some (.u32 3), some (.u64 17)]⟩
    observation ((machine.run 10
      ⟨operations observedCompare (some entry) (some query) 3 17, changed, []⟩).2) = (2, false) := by rfl

theorem resumed_comparison_is_not_repeated :
    observation ((machine.run 13 initial).2) = (0, false) ∧
    observation ((machine.continueRun 10 (machine.run 13 initial)).2) = (1, true) ∧
    (match (machine.continueRun 10 (machine.run 13 initial)).2 with
      | .finished (.returned final) => final.storage = put storage count.block ⟨true, [some (.u32 1)]⟩
      | _ => False) ∧
    (machine.continueRun 10 (machine.run 13 initial)).1.map (fun receipt => receipt.operation) =
      (machine.run 23 initial).1.map (fun receipt => receipt.operation) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem exhausted_scheduler_is_not_false_completion :
    observation ((machine.run 0 initial).2) = (0, false) ∧
    observation ((machine.run 30 initial).2) = (1, true) := by exact ⟨rfl, rfl⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.EntryMatch.Controls
end
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.Physical.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage ProductiveBlocks

abbrev table : Ptr := ⟨231, 0⟩
abbrev slots : Ptr := ⟨232, 0⟩
abbrev chunks : Ptr := ⟨233, 0⟩
abbrev entries : Ptr := ⟨234, 0⟩
abbrev firstBytes : Ptr := ⟨235, 0⟩
abbrev secondBytes : Ptr := ⟨236, 0⟩
abbrev query : Ptr := ⟨237, 0⟩
abbrev count : Ptr := EntryMatch.Controls.count

def storage : Storage CVal :=
  [(231, ⟨true, [some (.ptr (some slots)), some (.u32 4), some (.u32 2),
    some (.u64 9), some (.ptr (some chunks)), some (.u32 3)]⟩),
   (232, ⟨true, [some (.u64 0), some (.u32 0), some (.u32 0),
    some (.u64 17), some (.u32 3), some (.u32 1),
    some (.u64 17), some (.u32 3), some (.u32 2),
    some (.u64 0), some (.u32 0), some (.u32 0)]⟩),
   (233, ⟨true, [some (.ptr (some entries))]⟩),
   (234, ⟨true, [none, none, none, none, none,
    some (.ptr (some firstBytes)), some (.u32 3), some (.u64 17), none, none,
    some (.ptr (some secondBytes)), some (.u32 3), some (.u64 17), none, none]⟩),
   (235, ⟨true, [some (.u8 65), some (.u8 0), some (.u8 254)]⟩),
   (236, ⟨true, [some (.u8 65), some (.u8 0), some (.u8 255)]⟩),
   (237, ⟨true, [some (.u8 65), some (.u8 0), some (.u8 255)]⟩),
   (224, ⟨true, [some (.u32 0)]⟩)]

def initial (allowance : Nat) : State CVal (ReadBlock.Result Context) :=
  ⟨search EntryMatch.Controls.observedCompare table query 3 17 allowance (home 17 4, 0), storage, []⟩

def observation
    (result : Outcome (State CVal (ReadBlock.Result Context))
      (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal)) : Nat × UInt32 :=
  match result with
  | .exhausted _ => (0, 0)
  | .finished (.returned final) => match final.answer with
      | .exhausted => (3, 0)
      | .finished (.next (_, selected)) => (1, selected)
      | _ => (4, 0)
  | .finished (.fault _) => (2, 0)
  | _ => (4, 0)

def reachedStorage
    (result : Outcome (State CVal (ReadBlock.Result Context))
      (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal)) : Option (Storage CVal) :=
  match result with
  | .finished (.returned final) => some final.storage
  | _ => none

theorem hash_collision_requires_actual_byte_equality :
    observation ((machine.run 100 (initial 4)).2) = (1, 2) ∧
    reachedStorage ((machine.run 100 (initial 4)).2) =
      some (put (put storage count.block ⟨true, [some (.u32 1)]⟩) count.block ⟨true, [some (.u32 2)]⟩) := by exact ⟨rfl, rfl⟩

theorem missing_bytes_stop_at_the_actual_empty_slot :
    let changed := put storage query.block ⟨true, [some (.u8 65), some (.u8 0), some (.u8 253)]⟩
    observation ((machine.run 100
      ⟨search EntryMatch.Controls.observedCompare table query 3 17 4 (1, 0), changed, []⟩).2) =
      (1, 0) := by rfl

theorem successful_probe_reloads_selected_id :
    ((machine.run 100 (initial 4)).1.map (fun receipt => receipt.operation)).getLast? =
      some (.load (slots + 8)) := by rfl

theorem stopped_loop_has_no_iteration_allowance_requirement :
    observation ((machine.run 10
      ⟨search EntryMatch.Controls.forbiddenCompare table query 3 17 0 (3, 0), storage, []⟩).2) =
      (1, 0) := by rfl

theorem iteration_exhaustion_is_not_failed_lookup_or_scheduler_pause :
    observation ((machine.run 10 (initial 0)).2) = (3, 0) ∧
    observation ((machine.run 0 (initial 4)).2) = (0, 0) ∧
    observation ((machine.run 100 (initial 4)).2) = (1, 2) := by exact ⟨rfl, rfl, rfl⟩

theorem hash_mismatch_skips_chunk_and_comparison :
    let changed := put storage slots.block ⟨true,
      [some (.u64 0), some (.u32 0), some (.u32 0),
       some (.u64 16), some (.u32 3), some (.u32 1),
       some (.u64 0), some (.u32 0), some (.u32 0)]⟩
    observation ((machine.run 20
      ⟨search EntryMatch.Controls.forbiddenCompare table query 3 17 4 (1, 0), changed, []⟩).2) =
      (1, 0) := by rfl

theorem resumed_probe_does_not_repeat_the_first_comparison_effect :
    observation ((machine.run 25 (initial 4)).2) = (0, 0) ∧
    observation ((machine.continueRun 100 (machine.run 25 (initial 4))).2) = (1, 2) ∧
    reachedStorage ((machine.continueRun 100 (machine.run 25 (initial 4))).2) =
      some (put (put storage count.block ⟨true, [some (.u32 1)]⟩) count.block ⟨true, [some (.u32 2)]⟩) ∧
    (machine.continueRun 100 (machine.run 25 (initial 4))).1.map (fun receipt => receipt.operation) =
      (machine.run 125 (initial 4)).1.map (fun receipt => receipt.operation) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem dead_chunk_is_not_an_absent_symbol :
    let changed := put storage entries.block ⟨false, []⟩
    observation ((machine.run 30
      ⟨search EntryMatch.Controls.observedCompare table query 3 17 4 (1, 0), changed, []⟩).2) =
      (2, 0) := by rfl

theorem out_of_range_row_is_not_an_absent_symbol :
    let changed := put storage slots.block ⟨true,
      [some (.u64 0), some (.u32 0), some (.u32 0),
       some (.u64 17), some (.u32 3), some (.u32 9)]⟩
    observation ((machine.run 30
      ⟨search EntryMatch.Controls.observedCompare table query 3 17 4 (1, 0), changed, []⟩).2) =
      (2, 0) := by rfl

theorem zero_modulus_is_a_refused_continuation :
    let changed := put storage table.block ⟨true, [some (.ptr (some slots)), some (.u32 0)]⟩
    observation ((machine.run 10
      ⟨next table (1, 0), changed, []⟩).2) = (2, 0) := by rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.Physical.Controls
end
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.Machines.CMemory.StatementBlock
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ExecutableStorage ProductiveBlocks

abbrev table : Ptr := Physical.Controls.table
abbrev bytes : Ptr := Physical.Controls.query
abbrev calls : Ptr := ⟨238, 0⟩

/-- These counters instrument the two admitted synchronization calls. They
check source selection and retained effects, not a mutex implementation. -/
def observedMutex (acquiring : Bool) (address : Ptr) : CProg CVal CVal := do
  if address ≠ table + 6 then CProg.undefined else do
    let cell := calls + if acquiring then 0 else 1
    let count ← CProg.loadU32 cell
    CProg.store cell (.u32 (count + 1))
    pure (.i32 0)

def forbiddenMutex (_ : Bool) (_ : Ptr) : CProg CVal CVal := CProg.undefined

def storage : Storage CVal :=
  (238, ⟨true, [some (.u32 0), some (.u32 0)]⟩) :: Physical.Controls.storage

def outer (length : UInt32) : Context := fun name =>
  if name = "st".toList then scalar tablePointerType (.ptr (some table))
  else if name = "bytes".toList then scalar bytePointerType (.ptr (some bytes))
  else if name = "len".toList then scalar uint32 (.u32 length)
  else if name = "hash".toList then scalar uint64 (.u64 17)
  else if name = "SYMBOL_ID_NONE".toList then scalar identityType (.u32 0)
  else scalar uint32 (.u32 99)

theorem parameters (length : UInt32) : Parameters (outer length) table bytes length 17 := by
  constructor <;> rfl

def sourceProgram (mutex : MutexCall) (length : UInt32) (allowance : Nat) :
    CProg CVal (ReadBlock.Result Context) :=
  StatementBlock.executeScopedWith (services EntryMatch.Controls.observedCompare mutex)
    layout allowance 14 (outer length) Source.body

theorem sourceProgram_eq (mutex : MutexCall) (length : UInt32) (allowance : Nat) :
    sourceProgram mutex length allowance =
      (lookupProgram EntryMatch.Controls.observedCompare mutex table bytes length 17 allowance >>=
        fun result => pure (result.mapContext (fun _ => outer length))) :=
  actual_lookup_body _ _ _ _ _ _ _ _ (parameters length)

def initial (length : UInt32) (allowance : Nat) (cells : Storage CVal := storage) :
    State CVal (ReadBlock.Result Context) :=
  ⟨sourceProgram observedMutex length allowance, cells, []⟩

def observation
    (result : Outcome (State CVal (ReadBlock.Result Context))
      (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal)) : Nat × UInt32 :=
  match result with
  | .exhausted _ => (0, 0)
  | .finished (.returned final) => match final.answer with
      | .exhausted => (3, 0)
      | .finished (.returned _ (some (.u32 selected))) => (1, selected)
      | _ => (4, 0)
  | .finished (.fault _) => (2, 0)
  | _ => (4, 0)

def cellAt
    (result : Outcome (State CVal (ReadBlock.Result Context))
      (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal))
    (address : Ptr) : Option CVal :=
  match result with
  | .exhausted state => load state.storage address
  | .finished (.returned final) => load final.storage address
  | _ => none

def localAt
    (result : Outcome (State CVal (ReadBlock.Result Context))
      (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal))
    (name : Name) : Option ObjectBindings.Binding :=
  match result with
  | .finished (.returned final) => match final.answer with
      | .finished (.returned context _) => context name
      | _ => none
  | _ => none

theorem complete_source_collision_lookup_retains_each_effect :
    observation ((machine.run 120 (initial 3 4)).2) = (1, 2) ∧
    cellAt ((machine.run 120 (initial 3 4)).2) calls = some (.u32 1) ∧
    cellAt ((machine.run 120 (initial 3 4)).2) (calls + 1) = some (.u32 1) ∧
    cellAt ((machine.run 120 (initial 3 4)).2) EntryMatch.Controls.count = some (.u32 2) := by
  simp only [initial, sourceProgram_eq]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem complete_source_restores_shadowed_locals :
    localAt ((machine.run 120 (initial 3 4)).2) "found".toList = scalar uint32 (.u32 99) ∧
    localAt ((machine.run 120 (initial 3 4)).2) "slot".toList = scalar uint32 (.u32 99) ∧
    localAt ((machine.run 120 (initial 3 4)).2) "entry".toList = scalar uint32 (.u32 99) := by
  simp only [initial, sourceProgram_eq]
  exact ⟨rfl, rfl, rfl⟩

theorem complete_source_resume_does_not_reacquire_or_repeat_comparisons :
    observation ((machine.run 30 (initial 3 4)).2) = (0, 0) ∧
    observation ((machine.continueRun 120 (machine.run 30 (initial 3 4))).2) = (1, 2) ∧
    cellAt ((machine.continueRun 120 (machine.run 30 (initial 3 4))).2) calls = some (.u32 1) ∧
    cellAt ((machine.continueRun 120 (machine.run 30 (initial 3 4))).2) EntryMatch.Controls.count = some (.u32 2) ∧
    (machine.continueRun 120 (machine.run 30 (initial 3 4))).1.map (fun r => r.operation) =
      (machine.run 150 (initial 3 4)).1.map (fun r => r.operation) := by
  simp only [initial, sourceProgram_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem empty_input_returns_before_acquire :
    observation ((machine.run 10 ⟨sourceProgram forbiddenMutex 0 4, storage, []⟩).2) = (1, 0) ∧
    (machine.run 10 ⟨sourceProgram forbiddenMutex 0 4, storage, []⟩).1.map (fun r => r.operation) =
      [.ptrEq (some table) none, .ptrEq (some bytes) none] := by
  simp only [sourceProgram_eq]
  exact ⟨rfl, rfl⟩

theorem empty_table_unlocks_without_modulo_or_entry_reads :
    let changed := put storage table.block ⟨true, [some (.ptr none), some (.u32 0)]⟩
    observation ((machine.run 30 (initial 3 0 changed)).2) = (1, 0) ∧
    cellAt ((machine.run 30 (initial 3 0 changed)).2) calls = some (.u32 1) ∧
    cellAt ((machine.run 30 (initial 3 0 changed)).2) (calls + 1) = some (.u32 1) ∧
    cellAt ((machine.run 30 (initial 3 0 changed)).2) EntryMatch.Controls.count = some (.u32 0) := by
  simp only [initial, sourceProgram_eq]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem exhausted_loop_does_not_fabricate_unlock_or_public_failure :
    observation ((machine.run 30 (initial 3 0)).2) = (3, 0) ∧
    cellAt ((machine.run 30 (initial 3 0)).2) calls = some (.u32 1) ∧
    cellAt ((machine.run 30 (initial 3 0)).2) (calls + 1) = some (.u32 0) ∧
    observation ((machine.run 0 (initial 3 4)).2) = (0, 0) := by
  simp only [initial, sourceProgram_eq]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem refused_acquire_is_not_a_missing_symbol :
    observation ((machine.run 10 ⟨sourceProgram forbiddenMutex 3 4, storage, []⟩).2) = (2, 0) := by
  simp only [sourceProgram_eq]
  rfl

theorem dead_input_pointer_is_not_a_missing_symbol :
    let changed := put storage bytes.block ⟨false, []⟩
    observation ((machine.run 10 (initial 3 4 changed)).2) = (2, 0) := by
  simp only [initial, sourceProgram_eq]
  rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.Lookup.SourceRead.Controls
end
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section ManagedSpellingLookupSource
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open ExecutableStorage ProductiveBlocks

abbrev table : Ptr := Lookup.Physical.Controls.table
abbrev spelling : Ptr := ⟨239, 0⟩
abbrev atom : Ptr := ⟨240, 0⟩
abbrev first : Ptr := ⟨241, 0⟩
abbrev second : Ptr := ⟨242, 0⟩
abbrev comparisonCount : Ptr := EntryMatch.Controls.count
abbrev mutexCount : Ptr := Lookup.SourceRead.Controls.calls

def storage : Storage CVal :=
  [(239, ⟨true, [some (.u64 17), some (.u32 3),
    some (.u8 65), some (.u8 0), some (.u8 255)]⟩),
   (240, ⟨true, [some (.u32 0), none, none, some (.u32 0), some (.u32 7),
    some (.ptr (some spelling))]⟩),
   (241, ⟨true, [some (.u32 0), none, none, some (.u32 0), some (.u32 4294967295),
    some (.ptr (some second))]⟩),
   (242, ⟨true, [some (.u32 0), none, none, some (.u32 0), some (.u32 4294967295),
    some (.ptr (some atom))]⟩)] ++ Lookup.SourceRead.Controls.storage

def initial (forwardAllowance lookupAllowance : Nat)
    (cells : Storage CVal := storage) : State CVal (ReadBlock.Result (Option Ptr)) :=
  ⟨checkedOperations EntryMatch.Controls.observedCompare Lookup.SourceRead.Controls.observedMutex
    forwardAllowance 0 lookupAllowance (some table) (some first), cells, []⟩

def observation {Context : Type}
    (result : Outcome (State CVal (ReadBlock.Result Context))
      (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal)) : Nat × UInt32 :=
  match result with
  | .exhausted _ => (0, 0)
  | .finished (.returned final) => match final.answer with
      | .exhausted => (3, 0)
      | .finished (.returned _ (some (.u32 selected))) => (1, selected)
      | _ => (4, 0)
  | .finished (.fault _) => (2, 0)
  | _ => (4, 0)

def cellAt {Context : Type}
    (result : Outcome (State CVal (ReadBlock.Result Context))
      (Verdict CVal (ReadBlock.Result Context)) (AllocationRequest CVal))
    (address : Ptr) : Option CVal :=
  match result with
  | .exhausted state => load state.storage address
  | .finished (.returned final) => load final.storage address
  | _ => none

def environment : ReadExpressions.Environment := fun name =>
  if name = "atom".toList then some (.ptr (some first))
  else if name = "g_symbols".toList then some (.ptr (some table))
  else some (.u32 73)

def sourceInitial : State CVal ReadBlock.Result :=
  ⟨program (completedForward 2) (completedSpelled 0)
    (completedSpan EntryMatch.Controls.observedCompare Lookup.SourceRead.Controls.observedMutex 4)
    environment, storage, []⟩

theorem physical_lookup_earns_nonzero_id_from_collision_bytes :
    observation ((machine.run 160 (initial 2 4)).2) = (1, 2) ∧
    cellAt ((machine.run 160 (initial 2 4)).2) comparisonCount = some (.u32 2) ∧
    cellAt ((machine.run 160 (initial 2 4)).2) mutexCount = some (.u32 1) ∧
    cellAt ((machine.run 160 (initial 2 4)).2) (mutexCount + 1) = some (.u32 1) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem exact_source_body_uses_the_same_physical_lookup :
    observation ((machine.run 160 sourceInitial).2) = (1, 2) ∧
    cellAt ((machine.run 160 sourceInitial).2) comparisonCount = some (.u32 2) := by
  simp only [sourceInitial, actual_body_uses_operations _ _ _ environment (some table) (some first) rfl rfl]
  exact ⟨rfl, rfl⟩

theorem source_keeps_reached_pointer_and_other_locals :
    (match (machine.run 160 sourceInitial).2 with
      | .finished (.returned final) => match final.answer with
          | .finished (.returned reached _) =>
              (reached "atom".toList, reached "saved".toList, reached "g_symbols".toList)
          | _ => (none, none, none)
      | _ => (none, none, none)) =
      (some (.ptr (some atom)), some (.u32 73), some (.ptr (some table))) := by
  simp only [sourceInitial, actual_body_uses_operations _ _ _ environment (some table) (some first) rfl rfl]
  rfl

theorem two_forwarding_calls_and_three_header_occurrences_are_retained :
    ((machine.run 160 (initial 2 4)).1.map (fun receipt => receipt.operation)).take 20 =
      [.ptrEq (some first) none, .load (first + 4), .load (first + 5),
       .ptrEq (some second) none, .load (second + 4), .load (second + 5),
       .ptrEq (some atom) none, .load (atom + 4),
       .ptrEq (some atom) none, .load (atom + 4),
       .ptrEq (some atom) none, .load atom, .load (atom + 3), .load (atom + 5),
       .ptrEq (some spelling) none, .load (atom + 5), .load (atom + 5),
       .load (spelling + 1), .load (atom + 5), .load spelling] := by rfl

theorem helper_exhaustion_is_not_absence_or_scheduler_pause :
    observation ((machine.run 160 (initial 0 4)).2) = (3, 0) ∧
    observation ((machine.run 0 (initial 2 4)).2) = (0, 0) ∧
    observation ((machine.run 160 (initial 2 0)).2) = (3, 0) := by
  exact ⟨rfl, rfl, rfl⟩

theorem missing_spelling_is_a_completed_absence_after_real_comparisons :
    let changed := put storage spelling.block
      ⟨true, [some (.u64 17), some (.u32 3), some (.u8 65), some (.u8 0), some (.u8 253)]⟩
    observation ((machine.run 160 (initial 2 4 changed)).2) = (1, 0) ∧
    cellAt ((machine.run 160 (initial 2 4 changed)).2) comparisonCount = some (.u32 2) := by
  exact ⟨rfl, rfl⟩

theorem nul_and_non_utf8_storage_is_not_rewritten :
    cellAt ((machine.run 160 (initial 2 4)).2) (spelling + 2) = some (.u8 65) ∧
    cellAt ((machine.run 160 (initial 2 4)).2) (spelling + 3) = some (.u8 0) ∧
    cellAt ((machine.run 160 (initial 2 4)).2) (spelling + 4) = some (.u8 255) ∧
    cellAt ((machine.run 160 (initial 2 4)).2) (atom + 3) = some (.u32 0) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem saved_execution_does_not_repeat_completed_effects :
    observation ((machine.run 50 (initial 2 4)).2) = (0, 0) ∧
    observation ((machine.continueRun 160 (machine.run 50 (initial 2 4))).2) = (1, 2) ∧
    cellAt ((machine.continueRun 160 (machine.run 50 (initial 2 4))).2) comparisonCount =
      some (.u32 2) ∧
    (machine.continueRun 160 (machine.run 50 (initial 2 4))).1.map (fun receipt => receipt.operation) =
      (machine.run 210 (initial 2 4)).1.map (fun receipt => receipt.operation) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem dead_spelling_is_not_a_missing_symbol :
    let changed := put storage spelling.block ⟨false, []⟩
    observation ((machine.run 40 (initial 2 4 changed)).2) = (2, 0) := by rfl

theorem malformed_length_is_not_a_missing_symbol :
    let changed := put storage spelling.block ⟨true, [some (.u64 17), some (.u64 3)]⟩
    observation ((machine.run 40 (initial 2 4 changed)).2) = (2, 0) := by rfl

theorem null_uses_only_the_real_pointer_guards :
    let state : State CVal (ReadBlock.Result (Option Ptr)) :=
      ⟨checkedOperations EntryMatch.Controls.forbiddenCompare Lookup.SourceRead.Controls.forbiddenMutex
        0 0 0 (some table) none, [], []⟩
    observation ((machine.run 10 state).2) = (1, 0) ∧
    (machine.run 10 state).1.map (fun receipt => receipt.operation) =
      [.ptrEq none none, .ptrEq none none, .ptrEq none none, .ptrEq none none] := by
  exact ⟨rfl, rfl⟩

theorem numbered_fallback_does_not_invent_a_managed_lookup :
    let numbered := [(240, ⟨true,
      [some (.u32 0), none, none, some (.u32 11), some (.u32 7), none]⟩)]
    let state : State CVal (ReadBlock.Result (Option Ptr)) :=
      ⟨checkedOperations EntryMatch.Controls.forbiddenCompare Lookup.SourceRead.Controls.forbiddenMutex
        0 0 0 (some table) (some atom), numbered, []⟩
    observation ((machine.run 20 state).2) = (1, 11) := by rfl

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup.Controls
end ManagedSpellingLookupSource
end


section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section ManagedSpellingLookupSource
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000
namespace Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup.Controls
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open ExecutableStorage ProductiveBlocks

/-- The actual header-inline current-ID helper now calls the parsed managed
lookup body, rather than a fixture supplying the expected ID. -/
def currentInitial (cells : Storage CVal := storage) : State CVal ReadBlock.Result :=
  ⟨Current.program
    (lookupFromBody EntryMatch.Controls.observedCompare Lookup.SourceRead.Controls.observedMutex
      2 0 4 (some table)) environment, cells, []⟩

theorem actual_current_id_calls_the_constructed_lookup :
    observation ((machine.run 170 (currentInitial)).2) = (1, 2) ∧
    cellAt ((machine.run 170 (currentInitial)).2) comparisonCount = some (.u32 2) ∧
    cellAt ((machine.run 170 (currentInitial)).2) mutexCount = some (.u32 1) ∧
    cellAt ((machine.run 170 (currentInitial)).2) (mutexCount + 1) = some (.u32 1) := by
  simp only [currentInitial, Current.actual_body_uses_operations _ environment (some first) rfl]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem nested_helper_does_not_overwrite_the_current_id_callers_parameter :
    (match (machine.run 170 (currentInitial)).2 with
      | .finished (.returned final) => match final.answer with
          | .finished (.returned reached _) =>
              (reached "atom".toList, reached "saved".toList)
          | _ => (none, none)
      | _ => (none, none)) = (some (.ptr (some first)), some (.u32 73)) := by
  simp only [currentInitial, Current.actual_body_uses_operations _ environment (some first) rfl]
  rfl

theorem current_id_resume_preserves_one_lookup_effect_sequence :
    observation ((machine.run 55 (currentInitial)).2) = (0, 0) ∧
    observation ((machine.continueRun 170 (machine.run 55 (currentInitial))).2) = (1, 2) ∧
    cellAt ((machine.continueRun 170 (machine.run 55 (currentInitial))).2) comparisonCount =
      some (.u32 2) ∧
    (machine.continueRun 170 (machine.run 55 (currentInitial))).1.map (fun receipt => receipt.operation) =
      (machine.run 225 (currentInitial)).1.map (fun receipt => receipt.operation) := by
  simp only [currentInitial, Current.actual_body_uses_operations _ environment (some first) rfl]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Deliberately incoherent same-symbol forwarding storage is not silently
admitted as an invariant. The actual raw current-ID guard preserves a nonzero
incoming number, while the separate lookup helper follows the forwarding path. -/
theorem current_id_is_not_unconditional_forwarded_identity :
    let changed := put storage first.block
      ⟨true, [some (.u32 0), none, none, some (.u32 11), some (.u32 4294967295),
        some (.ptr (some second))]⟩
    observation ((machine.run 170 (currentInitial changed)).2) = (1, 11) ∧
    cellAt ((machine.run 170 (currentInitial changed)).2) comparisonCount = some (.u32 0) ∧
    observation ((machine.run 160 (initial 2 4 changed)).2) = (1, 2) := by
  simp only [currentInitial, Current.actual_body_uses_operations _ environment (some first) rfl]
  exact ⟨rfl, rfl, rfl⟩

end Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaFrameWriteback.NativeFrames.NumberedSymbol.ManagedLookup.Controls
end ManagedSpellingLookupSource
end
