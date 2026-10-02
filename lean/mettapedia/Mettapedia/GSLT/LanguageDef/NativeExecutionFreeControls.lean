import Mettapedia.GSLT.LanguageDef.NativeExecutionFreeInvariant

/-! Defined releases, untouched foreign state, and invalid aliasing controls. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionFreeControls

open NativeOps (Address SourceMemory SourceState SourceValue)
open NativeExecutionNodeRelease (World Node)

private def pointer (storage : Nat) : Address := ⟨storage, 0, []⟩
private def receipt : NativeExecutionScope.Observation := ⟨⟨⟨[7], [7], [7]⟩, 1⟩, [7]⟩
private def nodes : List Node :=
  [⟨pointer 20, ⟨pointer 10, receipt⟩⟩, ⟨pointer 21, ⟨pointer 11, receipt⟩⟩]
private def world : World := ⟨[⟨pointer 1, nodes⟩, ⟨pointer 2, []⟩]⟩
private def payload : SourceValue := .record "Observation"
  [.reference (some (pointer 100)), .reference (some (pointer 101)),
    .reference (some (pointer 102)), .reference (some (pointer 103)),
    .word 1, .word 1, .word 1, .word 1]
private def memory : SourceMemory :=
  ⟨fun storage element => if element = 0 then
      if storage = 10 then some payload else if storage = 999 then some (.word 42)
      else if storage ∈ [100, 101, 102, 103] then some (.byte 7) else none
    else none,
    fun storage => if storage ∈ [10, 20, 100, 101, 102, 103, 999] then some 64 else none⟩
private def state : SourceState World :=
  ⟨memory, some .invalidRequest, false, false, world, NativeOps.AllocatorStats.sourceEmpty⟩
private def afterFields : SourceMemory :=
  [100, 101, 102, 103].foldl NativeOps.sourceRelease memory
private def afterObservation : SourceMemory := NativeOps.sourceRelease afterFields 10
private def afterNode : SourceMemory := NativeOps.sourceRelease afterObservation 20
private def post : SourceState World :=
  NativeExecutionFreeCall.sourceUpdated state afterNode (pointer 1) nodes.tail

theorem owned_release_has_defined_full_post_state :
    NativeExecutionFreeCall.SourceCall state (some (pointer 1)) (some (pointer 10)) post := by
  apply NativeExecutionFreeCall.SourceCall.owned (nodes := nodes)
    (selected := ⟨pointer 20, ⟨pointer 10, receipt⟩⟩) (intermediate := afterObservation)
  · rfl
  · rfl
  · rfl
  · rfl

theorem owned_release_clears_all_six_allocations :
    afterNode.owned 100 = none ∧ afterNode.owned 101 = none ∧
      afterNode.owned 102 = none ∧ afterNode.owned 103 = none ∧
      afterNode.owned 10 = none ∧ afterNode.owned 20 = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem owned_release_preserves_other_storage :
    afterNode.cells 999 0 = some (.word 42) ∧ afterNode.owned 999 = some 64 := by
  exact ⟨rfl, rfl⟩

theorem owned_release_keeps_other_nodes_in_order :
    post.external.scopes = [⟨pointer 1, [⟨pointer 21, ⟨pointer 11, receipt⟩⟩]⟩,
      ⟨pointer 2, []⟩] := rfl

theorem owned_release_retains_existing_context_fault : post.fault = some .invalidRequest := rfl

theorem false_compact_release_callback_does_not_block_system_free :
    post.releaseAvailable = false ∧ post.allocatorStats = state.allocatorStats := ⟨rfl, rfl⟩

theorem null_scope_returns_before_lookup (pre : SourceState World) (handle : Option Address) :
    NativeExecutionFreeCall.SourceCall pre none handle pre := .nullScope pre handle

theorem null_observation_returns_before_scope_lookup (pre : SourceState World) (scope : Address) :
    NativeExecutionFreeCall.SourceCall pre (some scope) none pre := .nullObservation pre scope

theorem foreign_handle_returns_before_payload_read :
    NativeExecutionFreeCall.SourceCall state (some (pointer 1)) (some (pointer 777)) state := by
  exact .foreign (nodes := nodes) rfl rfl

theorem other_scope_cannot_free_this_scope_observation :
    NativeExecutionFreeCall.SourceCall state (some (pointer 2)) (some (pointer 10)) state := by
  exact .foreign (nodes := []) rfl rfl

theorem second_observation_free_is_undefined :
    NativeExecutionFreeObservation.sourceFree afterObservation (some (pointer 10)) = none := rfl

theorem second_scoped_release_is_noop :
    NativeExecutionFreeCall.SourceCall post (some (pointer 1)) (some (pointer 10)) post := by
  exact .foreign (nodes := nodes.tail) rfl rfl

private def selfAliasedMemory : SourceMemory := NativeOps.sourceStoreCell memory 10 0
  (.record "Observation" [.reference (some (pointer 10)), .reference (some (pointer 101)),
    .reference (some (pointer 102)), .reference (some (pointer 103)),
    .word 1, .word 1, .word 1, .word 1])

theorem freeing_observation_as_first_buffer_invalidates_later_field_read :
    NativeExecutionFreeObservation.sourceFree selfAliasedMemory (some (pointer 10)) = none := rfl

private def duplicateBufferMemory : SourceMemory := NativeOps.sourceStoreCell memory 10 0
  (.record "Observation" [.reference (some (pointer 100)), .reference (some (pointer 100)),
    .reference (some (pointer 102)), .reference (some (pointer 103)),
    .word 1, .word 1, .word 1, .word 1])

theorem duplicate_buffer_has_no_defined_double_free :
    NativeExecutionFreeObservation.sourceFree duplicateBufferMemory (some (pointer 10)) = none := rfl

theorem foreign_scope_with_null_handle_needs_no_payload_storage :
    NativeExecutionFreeCall.SourceCall state (some (pointer 777)) none state :=
  .nullObservation state (pointer 777)

end Mettapedia.GSLT.LanguageDef.NativeExecutionFreeControls
