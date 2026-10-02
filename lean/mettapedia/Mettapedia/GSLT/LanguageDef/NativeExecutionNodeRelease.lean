import Mettapedia.GSLT.LanguageDef.NativeExecutionScopeStorage

/-!
Execution-scope nodes retain their own allocation addresses in addition to
the observation handles. Source removal selects a finite-store index; target
removal traverses and unlinks the first matching node. Both retain order and
remove exactly one occurrence. Projection recovers the existing observation
scope; its uniqueness invariant is derived from reached scopes separately.
The node sequence represents a live linked list, with concrete links and
pointer realization remaining an ABI obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionNodeRelease

open NativeOps (Address)
open NativeExecutionScope (Entry Scope)

structure Node where
  address : Address
  entry : Entry
  deriving DecidableEq, Repr

def entries (nodes : List Node) : Scope := nodes.map Node.entry

def sourceExtract (nodes : List Node) (handle : Address) : Option (Node × List Node) := do
  let index := nodes.findIdx (fun node => node.entry.handle == handle)
  let selected ← nodes[index]?
  some (selected, nodes.eraseIdx index)

def targetExtract : List Node → Address → Option (Node × List Node)
  | [], _ => none
  | node :: rest, handle =>
    if node.entry.handle = handle then some (node, rest)
    else (targetExtract rest handle).map (fun pair => (pair.1, node :: pair.2))

theorem extraction_correspondence (nodes : List Node) (handle : Address) :
    targetExtract nodes handle = sourceExtract nodes handle := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    by_cases same : node.entry.handle = handle
    · have equal : (node.entry.handle == handle) = true := beq_iff_eq.mpr same
      simp only [targetExtract, if_pos same, sourceExtract, List.findIdx_cons, equal,
        Bool.cond_true, List.getElem?_cons_zero, bind, Option.bind_some, List.eraseIdx_cons_zero]
    · have different : (node.entry.handle == handle) = false := beq_eq_false_iff_ne.mpr same
      simp only [targetExtract, if_neg same, ih, sourceExtract, List.findIdx_cons, different,
        Bool.cond_false, List.getElem?_cons_succ, List.eraseIdx_cons_succ]
      cases rest[rest.findIdx (fun current => current.entry.handle == handle)]? <;> rfl

def remainder (nodes : List Node) (extracted : Option (Node × List Node)) : List Node :=
  match extracted with
  | none => nodes
  | some pair => pair.2

theorem extraction_observation (nodes : List Node) (handle : Address) :
    (targetExtract nodes handle).map (fun pair => pair.1.entry.observation) =
      NativeExecutionScope.targetFind (entries nodes) handle := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    by_cases same : node.entry.handle = handle
    · simp only [targetExtract, entries, List.map_cons, NativeExecutionScope.targetFind,
        if_pos same, Option.map_some]
    · simp only [entries] at ih
      simp only [targetExtract, entries, List.map_cons, NativeExecutionScope.targetFind,
        if_neg same, ← ih]
      cases targetExtract rest handle <;> rfl

theorem extraction_projects_to_removal (nodes : List Node) (handle : Address) :
    entries (remainder nodes (targetExtract nodes handle)) =
      NativeExecutionScope.targetRemove (entries nodes) handle := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    by_cases same : node.entry.handle = handle
    · simp only [targetExtract, remainder, entries, List.map_cons,
        NativeExecutionScope.targetRemove, if_pos same]
    · simp only [targetExtract, entries, List.map_cons,
        NativeExecutionScope.targetRemove, if_neg same] at ih ⊢
      cases extracted : targetExtract rest handle with
      | none =>
        simp only [extracted, Option.map_none, remainder] at ih ⊢
        exact congrArg (List.cons node.entry) ih
      | some pair =>
        simp only [extracted, Option.map_some, remainder] at ih ⊢
        exact congrArg (List.cons node.entry) ih

theorem extracted_handle_and_membership (nodes : List Node) (handle : Address)
    (selected : Node) (rest : List Node)
    (extracted : targetExtract nodes handle = some (selected, rest)) :
    selected.entry.handle = handle ∧ selected ∈ nodes ∧ rest.Sublist nodes := by
  induction nodes generalizing selected rest with
  | nil => cases extracted
  | cons node tail ih =>
    by_cases same : node.entry.handle = handle
    · rw [targetExtract, if_pos same] at extracted
      have pair := Option.some.inj extracted
      have selectedEqual : node = selected := congrArg Prod.fst pair
      have restEqual : tail = rest := congrArg Prod.snd pair
      subst selected
      subst rest
      exact ⟨same, List.mem_cons_self, List.Sublist.cons node (List.Sublist.refl tail)⟩
    · rw [targetExtract, if_neg same] at extracted
      cases recursive : targetExtract tail handle with
      | none => simp only [recursive, Option.map_none] at extracted; cases extracted
      | some pair =>
        have equal : (pair.1, node :: pair.2) = (selected, rest) := by
          apply Option.some.inj
          simpa only [recursive, Option.map_some] using extracted
        have selectedEqual : pair.1 = selected := congrArg Prod.fst equal
        have restEqual : node :: pair.2 = rest := congrArg Prod.snd equal
        obtain ⟨found, member, remaining⟩ := ih pair.1 pair.2 recursive
        rw [← selectedEqual, ← restEqual]
        exact ⟨found, List.mem_cons.mpr (Or.inr member), remaining.cons_cons node⟩

structure ScopeCell where
  address : Address
  nodes : List Node
  deriving DecidableEq, Repr

structure World where
  scopes : List ScopeCell
  deriving DecidableEq, Repr

def projectCell (cell : ScopeCell) : NativeExecutionMatchesExternal.ScopeCell :=
  ⟨cell.address, entries cell.nodes⟩

def projectWorld (world : World) : NativeExecutionMatchesExternal.World :=
  ⟨world.scopes.map projectCell⟩

def sourceFind (cells : List ScopeCell) (address : Address) : Option (List Node) :=
  (cells.find? (fun cell => cell.address == address)).map ScopeCell.nodes

def targetFind : List ScopeCell → Address → Option (List Node)
  | [], _ => none
  | cell :: rest, address =>
    if cell.address = address then some cell.nodes else targetFind rest address

theorem find_correspondence (cells : List ScopeCell) (address : Address) :
    targetFind cells address = sourceFind cells address := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    by_cases same : cell.address = address
    · simp only [targetFind, if_pos same, sourceFind, List.find?_cons, beq_iff_eq.mpr same,
        Option.map_some]
    · have different : (cell.address == address) = false := beq_eq_false_iff_ne.mpr same
      simp only [targetFind, if_neg same, sourceFind, List.find?_cons, different,
        ih]

theorem find_projection (cells : List ScopeCell) (address : Address) :
    NativeExecutionMatchesExternal.targetFind (cells.map projectCell) address =
      (targetFind cells address).map entries := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    by_cases same : cell.address = address
    · simp only [List.map_cons, NativeExecutionMatchesExternal.targetFind, projectCell,
        if_pos same, targetFind, Option.map_some]
    · simp only [List.map_cons, NativeExecutionMatchesExternal.targetFind, projectCell,
        if_neg same, targetFind, ih]

def sourceCells (cells : List ScopeCell) (address : Address) (nodes : List Node) : List ScopeCell :=
  cells.modify (cells.findIdx (fun cell => cell.address == address))
    (fun cell => { cell with nodes := nodes })

def targetCells : List ScopeCell → Address → List Node → List ScopeCell
  | [], _, _ => []
  | cell :: rest, address, nodes =>
    if cell.address = address then { cell with nodes := nodes } :: rest
    else cell :: targetCells rest address nodes

theorem store_correspondence (cells : List ScopeCell) (address : Address) (nodes : List Node) :
    targetCells cells address nodes = sourceCells cells address nodes := by
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

theorem store_projection (cells : List ScopeCell) (address : Address) (nodes : List Node) :
    (targetCells cells address nodes).map projectCell =
      NativeExecutionScopeStorage.targetCells (cells.map projectCell) address (entries nodes) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    by_cases same : cell.address = address
    · simp only [targetCells, List.map_cons, projectCell,
        NativeExecutionScopeStorage.targetCells, if_pos same]
    · simp only [targetCells, List.map_cons, projectCell,
        NativeExecutionScopeStorage.targetCells, if_neg same, ih]

end Mettapedia.GSLT.LanguageDef.NativeExecutionNodeRelease
