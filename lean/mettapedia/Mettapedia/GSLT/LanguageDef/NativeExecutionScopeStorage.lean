import Mettapedia.GSLT.LanguageDef.NativeExecutionMatchesExternal

/-!
Storage effects of updating a live execution-scope object. The source selects
its finite-store index and changes that cell. The target traverses the cells
and changes the first matching address. Missing addresses do not allocate new
objects. The update preserves every scope-object address and all lookups at
other addresses; concrete pointer realization remains an ABI obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionScopeStorage

open NativeOps (Address)
open NativeExecutionScope (Scope Contract Reached)
open NativeExecutionMatchesExternal (ScopeCell World)

def sourceCells (cells : List ScopeCell) (address : Address) (scope : Scope) : List ScopeCell :=
  cells.modify (cells.findIdx (fun cell => cell.address == address))
    (fun cell => { cell with scope := scope })

def targetCells : List ScopeCell → Address → Scope → List ScopeCell
  | [], _, _ => []
  | cell :: rest, address, scope =>
    if cell.address = address then { cell with scope := scope } :: rest
    else cell :: targetCells rest address scope

theorem cells_correspondence (cells : List ScopeCell) (address : Address) (scope : Scope) :
    targetCells cells address scope = sourceCells cells address scope := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    by_cases same : cell.address = address
    · have equal : (cell.address == address) = true := beq_iff_eq.mpr same
      simp only [targetCells, if_pos same, sourceCells, List.findIdx_cons, equal,
        Bool.cond_true, List.modify_cons, if_true]
    · have different : (cell.address == address) = false := beq_eq_false_iff_ne.mpr same
      simp only [targetCells, if_neg same, sourceCells, List.findIdx_cons, different,
        Bool.cond_false, List.modify_cons]
      exact congrArg (List.cons cell) ih

def sourceStore (world : World) (address : Address) (scope : Scope) : World :=
  ⟨sourceCells world.scopes address scope⟩

def targetStore (world : World) (address : Address) (scope : Scope) : World :=
  ⟨targetCells world.scopes address scope⟩

theorem store_correspondence (world : World) (address : Address) (scope : Scope) :
    targetStore world address scope = sourceStore world address scope := by
  exact congrArg World.mk (cells_correspondence world.scopes address scope)

theorem target_read_after_store (cells : List ScopeCell) (address : Address)
    (previous scope : Scope) (found : NativeExecutionMatchesExternal.targetFind cells address =
      some previous) :
    NativeExecutionMatchesExternal.targetFind (targetCells cells address scope) address =
      some scope := by
  induction cells with
  | nil => cases found
  | cons cell rest ih =>
    by_cases same : cell.address = address
    · simp only [targetCells, NativeExecutionMatchesExternal.targetFind, same, if_true]
    · rw [NativeExecutionMatchesExternal.targetFind, if_neg same] at found
      simp only [targetCells, if_neg same, NativeExecutionMatchesExternal.targetFind]
      exact ih found

theorem target_missing_store_is_unchanged (cells : List ScopeCell) (address : Address)
    (scope : Scope) (missing : NativeExecutionMatchesExternal.targetFind cells address = none) :
    targetCells cells address scope = cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    by_cases same : cell.address = address
    · rw [NativeExecutionMatchesExternal.targetFind, if_pos same] at missing
      cases missing
    · rw [NativeExecutionMatchesExternal.targetFind, if_neg same] at missing
      rw [targetCells, if_neg same, ih missing]

theorem target_other_scope_unchanged (cells : List ScopeCell) (address other : Address)
    (different : other ≠ address) (scope : Scope) :
    NativeExecutionMatchesExternal.targetFind (targetCells cells address scope) other =
      NativeExecutionMatchesExternal.targetFind cells other := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    by_cases same : cell.address = address
    · have separate : cell.address ≠ other := by
        intro equal
        exact different (equal.symm.trans same)
      simp only [targetCells, if_pos same, NativeExecutionMatchesExternal.targetFind,
        if_neg separate]
    · simp only [targetCells, if_neg same, NativeExecutionMatchesExternal.targetFind]
      by_cases here : cell.address = other
      · simp only [if_pos here]
      · simp only [if_neg here, ih]

theorem target_addresses_preserved (cells : List ScopeCell) (address : Address) (scope : Scope) :
    (targetCells cells address scope).map ScopeCell.address = cells.map ScopeCell.address := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    by_cases same : cell.address = address
    · simp only [targetCells, if_pos same, List.map_cons]
    · simp only [targetCells, if_neg same, List.map_cons, ih]

def ScopesReached (contract : Contract) (world : World) : Prop :=
  ∀ cell ∈ world.scopes, Reached contract cell.scope

theorem target_store_preserves_reached (contract : Contract) (world : World)
    (before : ScopesReached contract world) (address : Address) (scope : Scope)
    (after : Reached contract scope) : ScopesReached contract (targetStore world address scope) := by
  have helper : ∀ cells : List ScopeCell,
      (∀ cell ∈ cells, Reached contract cell.scope) →
        ∀ cell ∈ targetCells cells address scope, Reached contract cell.scope := by
    intro cells
    induction cells with
    | nil => intro _ _ impossible; cases impossible
    | cons first rest ih =>
      intro beforeCells
      by_cases same : first.address = address
      · rw [targetCells, if_pos same]
        intro cell member
        rcases List.mem_cons.mp member with current | prior
        · subst cell; exact after
        · exact beforeCells cell (List.mem_cons.mpr (Or.inr prior))
      · rw [targetCells, if_neg same]
        intro cell member
        rcases List.mem_cons.mp member with current | updated
        · subst cell; exact beforeCells first List.mem_cons_self
        · exact ih (fun cell member => beforeCells cell (List.mem_cons.mpr (Or.inr member)))
            cell updated
  exact helper world.scopes before

theorem source_store_preserves_reached (contract : Contract) (world : World)
    (before : ScopesReached contract world) (address : Address) (scope : Scope)
    (after : Reached contract scope) : ScopesReached contract (sourceStore world address scope) := by
  rw [← store_correspondence world address scope]
  exact target_store_preserves_reached contract world before address scope after

private def first : Address := ⟨1, 0, []⟩
private def second : Address := ⟨2, 0, []⟩
private def handle : Address := ⟨3, 0, []⟩
private def observation : NativeExecutionScope.Observation := ⟨⟨⟨[], [], []⟩, 0⟩, []⟩
private def scope : Scope := [⟨handle, observation⟩]
private def cells : List ScopeCell := [⟨first, []⟩, ⟨second, []⟩]

theorem storing_second_scope_preserves_first_scope :
    sourceCells cells second scope = [⟨first, []⟩, ⟨second, scope⟩] := rfl

theorem missing_scope_store_does_not_create_an_object :
    targetCells cells ⟨9, 0, []⟩ scope = cells := rfl

theorem stored_scope_retains_completed_observation :
    NativeExecutionMatchesExternal.targetFind (targetCells cells second scope) second =
      some scope := rfl

end Mettapedia.GSLT.LanguageDef.NativeExecutionScopeStorage
