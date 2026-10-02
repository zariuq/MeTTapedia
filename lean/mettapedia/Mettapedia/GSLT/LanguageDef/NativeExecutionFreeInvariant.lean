import Mettapedia.GSLT.LanguageDef.NativeExecutionFreeExternal

/-!
Node-aware destruction projects to logical observation release. The unique
handle condition is obtained from reached execution scopes, not imposed as a
new C guard. The resulting world contains only reached scopes. The interface
therefore revokes observations without introducing an authority premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionFreeInvariant

open NativeOps (Address SourceState TargetState StateRelated)
open NativeExecutionNodeRelease (World Node entries projectCell projectWorld)
open NativeExecutionScope (Contract Reached)

theorem source_store_projection (world : World) (address : Address) (nodes : List Node) :
    projectWorld ⟨NativeExecutionNodeRelease.sourceCells world.scopes address nodes⟩ =
      NativeExecutionScopeStorage.sourceStore (projectWorld world) address (entries nodes) := by
  change NativeExecutionMatchesExternal.World.mk
      ((NativeExecutionNodeRelease.sourceCells world.scopes address nodes).map projectCell) =
    NativeExecutionMatchesExternal.World.mk
      (NativeExecutionScopeStorage.sourceCells (world.scopes.map projectCell) address (entries nodes))
  rw [← NativeExecutionNodeRelease.store_correspondence,
    NativeExecutionNodeRelease.store_projection, NativeExecutionScopeStorage.cells_correspondence]

theorem found_scope_reached (contract : Contract) (world : World)
    (reached : NativeExecutionScopeStorage.ScopesReached contract (projectWorld world))
    (address : Address) (nodes : List Node)
    (found : NativeExecutionNodeRelease.sourceFind world.scopes address = some nodes) :
    Reached contract (entries nodes) := by
  have lookup : ∀ cells : List NativeExecutionNodeRelease.ScopeCell,
      (∀ cell ∈ cells, Reached contract (entries cell.nodes)) →
      NativeExecutionNodeRelease.targetFind cells address = some nodes →
      Reached contract (entries nodes) := by
    intro cells
    induction cells with
    | nil => intro _ impossible; cases impossible
    | cons cell rest ih =>
      intro prior selected
      by_cases same : cell.address = address
      · rw [NativeExecutionNodeRelease.targetFind, if_pos same] at selected
        have equal : cell.nodes = nodes := Option.some.inj selected
        rw [← equal]
        exact prior cell List.mem_cons_self
      · rw [NativeExecutionNodeRelease.targetFind, if_neg same] at selected
        exact ih (fun current member => prior current (List.mem_cons.mpr (Or.inr member))) selected
  apply lookup world.scopes
  · intro cell member
    exact reached (projectCell cell) (List.mem_map.mpr ⟨cell, member, rfl⟩)
  · rw [NativeExecutionNodeRelease.find_correspondence]
    exact found

theorem selected_remainder_is_logical_release (contract : Contract) (nodes : List Node)
    (reached : Reached contract (entries nodes)) (handle : Address) (selected : Node)
    (rest : List Node)
    (extracted : NativeExecutionNodeRelease.sourceExtract nodes handle = some (selected, rest)) :
    entries rest = NativeExecutionScope.sourceRelease (entries nodes) (some handle) := by
  have projected := NativeExecutionNodeRelease.extraction_projects_to_removal nodes handle
  rw [NativeExecutionNodeRelease.extraction_correspondence, extracted,
    NativeExecutionNodeRelease.remainder] at projected
  exact projected.trans (NativeExecutionScope.release_correspondence (entries nodes)
    (some handle) (NativeExecutionScope.reached_valid reached).1)

theorem source_call_preserves_reached (contract : Contract) (pre post : SourceState World)
    (reached : NativeExecutionScopeStorage.ScopesReached contract (projectWorld pre.external))
    (scope handle : Option Address) (called : NativeExecutionFreeCall.SourceCall pre scope handle post) :
    NativeExecutionScopeStorage.ScopesReached contract (projectWorld post.external) := by
  cases called with
  | nullScope => exact reached
  | nullObservation => exact reached
  | foreign => exact reached
  | @owned scopeAddress requested nodes rest selected _ _ found extracted _ _ =>
    have prior := found_scope_reached contract pre.external reached scopeAddress nodes found
    have remaining := selected_remainder_is_logical_release contract nodes prior requested
      selected rest extracted
    change NativeExecutionScopeStorage.ScopesReached contract
      (projectWorld ⟨NativeExecutionNodeRelease.sourceCells pre.external.scopes scopeAddress rest⟩)
    rw [source_store_projection, remaining]
    exact NativeExecutionScopeStorage.source_store_preserves_reached contract
      (projectWorld pre.external) reached scopeAddress
      (NativeExecutionScope.sourceRelease (entries nodes) (some requested)) (.released _ prior)

theorem target_call_preserves_reached (contract : Contract) (source : SourceState World)
    (target post : TargetState World) (related : StateRelated Eq source target)
    (reached : NativeExecutionScopeStorage.ScopesReached contract (projectWorld source.external))
    (scope handle : Option Address) (called : NativeExecutionFreeCall.TargetCall target scope handle post) :
    NativeExecutionScopeStorage.ScopesReached contract (projectWorld post.external) := by
  obtain ⟨sourcePost, sourceCalled, postRelated⟩ :=
    NativeExecutionFreeCall.call_backward source target related scope handle post called
  rw [← postRelated.external]
  exact source_call_preserves_reached contract source sourcePost reached scope handle sourceCalled

theorem source_call_revokes_handle (contract : Contract) (pre post : SourceState World)
    (reached : NativeExecutionScopeStorage.ScopesReached contract (projectWorld pre.external))
    (scope handle : Address)
    (called : NativeExecutionFreeCall.SourceCall pre (some scope) (some handle) post) :
    ∃ remaining,
      NativeExecutionMatchesExternal.targetFind (projectWorld post.external).scopes scope =
        some remaining ∧ NativeExecutionScope.targetRead remaining (some handle) = none := by
  cases called with
  | @foreign _ _ nodes found absent =>
    refine ⟨entries nodes, ?_, ?_⟩
    · change NativeExecutionMatchesExternal.targetFind
        (pre.external.scopes.map projectCell) scope = some (entries nodes)
      rw [NativeExecutionNodeRelease.find_projection,
        NativeExecutionNodeRelease.find_correspondence, found]
      rfl
    · have selected := NativeExecutionNodeRelease.extraction_observation nodes handle
      rw [NativeExecutionNodeRelease.extraction_correspondence, absent, Option.map_none] at selected
      exact selected.symm
  | @owned _ _ nodes rest selected _ _ found extracted _ _ =>
    have prior := found_scope_reached contract pre.external reached scope nodes found
    have removed := selected_remainder_is_logical_release contract nodes prior handle selected rest extracted
    refine ⟨entries rest, ?_, ?_⟩
    · have original : NativeExecutionMatchesExternal.targetFind
          (projectWorld pre.external).scopes scope = some (entries nodes) := by
        rw [show (projectWorld pre.external).scopes = pre.external.scopes.map projectCell from rfl,
          NativeExecutionNodeRelease.find_projection, NativeExecutionNodeRelease.find_correspondence,
          found]
        rfl
      change NativeExecutionMatchesExternal.targetFind
        (projectWorld ⟨NativeExecutionNodeRelease.sourceCells pre.external.scopes scope rest⟩).scopes
        scope = some (entries rest)
      rw [source_store_projection, ← NativeExecutionScopeStorage.store_correspondence]
      exact NativeExecutionScopeStorage.target_read_after_store _ scope (entries nodes)
        (entries rest) original
    · rw [removed, ← NativeExecutionScope.release_correspondence (entries nodes)
        (some handle) (NativeExecutionScope.reached_valid prior).1]
      exact NativeExecutionScope.released_handle_unreadable (entries nodes) handle
        (NativeExecutionScope.reached_valid prior).1

end Mettapedia.GSLT.LanguageDef.NativeExecutionFreeInvariant
