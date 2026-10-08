import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.OfFn

/-!
# Named spaces and state cells

Allocation and frame laws are independent of the space and value carrier.
The executable evaluator instantiates this store with ordered Atom rows.
The Pattern command specialization belongs to `PatternRewrite.Commands`, which
depends on this store; the generic storage layer does not depend on an evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces

inductive Handle where
  | self
  | privateSpace (index : Nat)
  deriving DecidableEq, Repr

universe uSpace uValue

/-- Allocation and cells are independent of the stored payload representation. -/
structure Store (Space : Type uSpace) (Value : Type uValue) where
  core : Space
  next : Nat := 0
  spaces : Nat → Space := fun _ => core
  cells : String → Option Value := fun _ => none

namespace Store

variable {Space : Type uSpace} {Value : Type uValue}

def new (core empty : Space) : Store Space Value :=
  { core, spaces := fun _ => empty }

def read (state : Store Space Value) : Handle → Option Space
  | .self => some state.core
  | .privateSpace index => if index < state.next then some (state.spaces index) else none

def write (state : Store Space Value) : Handle → Space → Option (Store Space Value)
  | .self, space => some { state with core := space }
  | .privateSpace index, space =>
    if index < state.next then
      some { state with spaces := Function.update state.spaces index space }
    else none

def allocate (state : Store Space Value) (empty : Space) : Handle × Store Space Value :=
  (.privateSpace state.next,
    { state with
      next := state.next + 1
      spaces := Function.update state.spaces state.next empty })

def putCell (state : Store Space Value) (name : String) (value : Value) : Store Space Value :=
  { state with cells := Function.update state.cells name (some value) }

@[simp] theorem read_self (state : Store Space Value) : state.read .self = some state.core := rfl

@[simp] theorem read_unallocated (state : Store Space Value) (index : Nat)
    (unallocated : state.next ≤ index) : state.read (.privateSpace index) = none := by
  simp [read, Nat.not_lt.mpr unallocated]

@[simp] theorem allocation_reads_empty (state : Store Space Value) (empty : Space) :
    (state.allocate empty).2.read (state.allocate empty).1 = some empty := by
  simp [allocate, read]

@[simp] theorem allocation_core (state : Store Space Value) (empty : Space) : (state.allocate empty).2.core = state.core := rfl

@[simp] theorem allocation_cells (state : Store Space Value) (empty : Space) : (state.allocate empty).2.cells = state.cells := rfl

theorem allocation_read_existing (state : Store Space Value) (empty : Space) (handle : Handle)
    (different : handle ≠ (state.allocate empty).1) :
    (state.allocate empty).2.read handle = state.read handle := by
  cases handle with
  | self => rfl
  | privateSpace index =>
    have unequal : index ≠ state.next := by
      intro same
      apply different
      simp [allocate, same]
    have before : (index < state.next + 1) = (index < state.next) := by
      apply propext
      omega
    simp [allocate, read, before, unequal]

theorem successive_allocations_distinct (state : Store Space Value) (empty : Space) :
    (state.allocate empty).1 ≠ ((state.allocate empty).2.allocate empty).1 := by
  simp [allocate]

theorem write_reads_back (state : Store Space Value) (handle : Handle) (space : Space)
    (after : Store Space Value) (written : state.write handle space = some after) :
    after.read handle = some space := by
  cases handle with
  | self =>
    simp only [write, Option.some.injEq] at written
    subst after
    rfl
  | privateSpace index =>
    simp only [write] at written
    split at written
    next allocated =>
      cases written
      simp [read, allocated]
    next => contradiction

theorem write_exists_of_read_some (state : Store Space Value) (handle : Handle)
    (before space : Space) (allocated : state.read handle = some before) :
    ∃ after, state.write handle space = some after := by
  cases handle with
  | self => exact ⟨_, rfl⟩
  | privateSpace index =>
      have bounded : index < state.next := by
        by_contra absent
        simp [read, absent] at allocated
      simp [write, bounded]

theorem write_read_other (state : Store Space Value) (handle other : Handle) (space : Space)
    (after : Store Space Value) (written : state.write handle space = some after)
    (different : other ≠ handle) : after.read other = state.read other := by
  cases handle with
  | self =>
    simp only [write, Option.some.injEq] at written
    subst after
    cases other with
    | self => exact False.elim (different rfl)
    | privateSpace index => rfl
  | privateSpace index =>
    simp only [write] at written
    split at written
    next =>
      cases written
      cases other with
      | self => rfl
      | privateSpace otherIndex =>
        have unequal : otherIndex ≠ index := by
          intro same
          exact different (congrArg Handle.privateSpace same)
        simp [read, unequal]
    next => contradiction

theorem write_preserves_cells (state : Store Space Value) (handle : Handle) (space : Space)
    (after : Store Space Value) (written : state.write handle space = some after) :
    after.cells = state.cells := by
  cases handle with
  | self =>
    simp only [write, Option.some.injEq] at written
    subst after
    rfl
  | privateSpace index =>
    simp only [write] at written
    split at written
    next => cases written; rfl
    next => contradiction

@[simp] theorem cell_reads_back (state : Store Space Value) (name : String) (value : Value) :
    (state.putCell name value).cells name = some value := by
  simp [putCell]

theorem cell_read_other (state : Store Space Value) (name other : String) (value : Value)
    (different : other ≠ name) :
    (state.putCell name value).cells other = state.cells other := by
  simp [putCell, different]

@[simp] theorem cell_preserves_spaces (state : Store Space Value) (name : String) (value : Value)
    (handle : Handle) :
    (state.putCell name value).read handle = state.read handle := by
  cases handle <;> rfl

/-! ## Finitely supported cells in reachable stores -/

/-- Every present state cell has a name in a finite support list. -/
def FiniteCells (state : Store Space Value) : Prop :=
  ∃ names : List String, ∀ name, name ∉ names → state.cells name = none

theorem new_finiteCells (core empty : Space) : FiniteCells (new core empty : Store Space Value) :=
  ⟨[], fun _ _ => rfl⟩

theorem finiteCells_of_same_cells {state after : Store Space Value}
    (finite : FiniteCells state) (same : after.cells = state.cells) : FiniteCells after := by
  obtain ⟨names, covers⟩ := finite
  exact ⟨names, fun name missing => by rw [same]; exact covers name missing⟩

theorem write_finiteCells {state after : Store Space Value} {handle : Handle} {space : Space}
    (finite : FiniteCells state) (written : state.write handle space = some after) :
    FiniteCells after :=
  finiteCells_of_same_cells finite (write_preserves_cells state handle space after written)

theorem allocate_finiteCells {state : Store Space Value}
    (finite : FiniteCells state) (empty : Space) : FiniteCells (state.allocate empty).2 :=
  finiteCells_of_same_cells finite rfl

theorem putCell_finiteCells {state : Store Space Value}
    (finite : FiniteCells state) (name : String) (value : Value) :
    FiniteCells (state.putCell name value) := by
  obtain ⟨names, covers⟩ := finite
  refine ⟨name :: names, ?_⟩
  intro other missing
  have absent : other ≠ name ∧ other ∉ names := by simpa using missing
  have different : other ≠ name := absent.1
  rw [cell_read_other state name other value different]
  exact covers other absent.2

/-- A present cell cannot be encoded with an empty support list. -/
theorem putCell_support_not_empty (state : Store Space Value)
    (name : String) (value : Value) :
    ¬ (∀ other, other ∉ ([] : List String) →
      (state.putCell name value).cells other = none) := by
  intro covers
  have impossible := covers name (by simp)
  simp at impossible

/-! ## Finite representation of private spaces -/

/-- Ordered private spaces allocated so far, indexed by their actual handles. -/
def spacesPrefix (state : Store Space Value) : List Space :=
  List.ofFn (fun index : Fin state.next => state.spaces index)

@[simp] theorem spacesPrefix_length (state : Store Space Value) :
    state.spacesPrefix.length = state.next := by simp [spacesPrefix]

/-- Every private read is determined by a finite prefix, even when the
underlying function has arbitrary values outside the allocated handles. -/
theorem read_private_from_prefix (state : Store Space Value) (index : Nat) :
    state.read (.privateSpace index) = state.spacesPrefix[index]? := by
  simp [read, spacesPrefix, List.getElem?_ofFn]

/-- All unallocated slots contain the designated empty payload. -/
def EmptyTail (state : Store Space Value) (empty : Space) : Prop :=
  ∀ index, state.next ≤ index → state.spaces index = empty

theorem new_emptyTail (core empty : Space) :
    EmptyTail (new core empty : Store Space Value) empty := fun _ _ => rfl

theorem write_emptyTail {state after : Store Space Value} {handle : Handle}
    {space empty : Space} (vacant : EmptyTail state empty)
    (written : state.write handle space = some after) : EmptyTail after empty := by
  cases handle with
  | self =>
      simp only [write, Option.some.injEq] at written
      cases written
      exact vacant
  | privateSpace writtenIndex =>
      simp only [write] at written
      split at written
      next allocated =>
        cases written
        intro index outside
        change state.next ≤ index at outside
        have different : index ≠ writtenIndex := by omega
        simpa only [Function.update_of_ne different] using vacant index outside
      next => contradiction

theorem allocate_emptyTail {state : Store Space Value} {empty : Space}
    (vacant : EmptyTail state empty) : EmptyTail (state.allocate empty).2 empty := by
  intro index outside
  have different : index ≠ state.next := by
    change state.next + 1 ≤ index at outside
    omega
  simpa only [allocate, Function.update_of_ne different] using
    vacant index (by change state.next + 1 ≤ index at outside; omega)

theorem putCell_emptyTail {state : Store Space Value} {empty : Space}
    (vacant : EmptyTail state empty) (name : String) (value : Value) :
    EmptyTail (state.putCell name value) empty := vacant

/-- An empty tail gives exact reconstruction of the entire space function,
not only equality of its reads. -/
theorem spaces_eq_prefix_of_emptyTail {state : Store Space Value} {empty : Space}
    (vacant : EmptyTail state empty) (index : Nat) :
    state.spaces index = (state.spacesPrefix[index]?).getD empty := by
  rw [← read_private_from_prefix]
  by_cases allocated : index < state.next
  · simp [read, allocated]
  · simpa [read, allocated] using vacant index (Nat.le_of_not_gt allocated)

/-- A private handle at the next allocation index cannot read a payload. -/
theorem prefix_does_not_invent_unallocated_space (state : Store Space Value) :
    state.spacesPrefix[state.next]? = none := by
  rw [← read_private_from_prefix]
  exact read_unallocated state state.next le_rfl

/-- The named cell values at a supplied finite support, including absent cells. -/
def cellRows (state : Store Space Value) (names : List String) : List (String × Option Value) :=
  names.map (fun name => (name, state.cells name))

theorem cellRows_lookup (state : Store Space Value) (names : List String) (name : String) :
    (state.cellRows names).lookup name =
      if name ∈ names then some (state.cells name) else none := by
  induction names with
  | nil => simp [cellRows]
  | cons first rest ih =>
      by_cases same : name = first
      · subst first
        simp [cellRows]
      · have unequal : (name == first) = false := by simp [same]
        simpa [cellRows, List.lookup_cons, unequal, same] using ih

/-- A support witness gives exact reconstruction of every cell read. -/
theorem cells_eq_rows_lookup (state : Store Space Value) (names : List String)
    (covers : ∀ name, name ∉ names → state.cells name = none) (name : String) :
    state.cells name = ((state.cellRows names).lookup name).join := by
  rw [cellRows_lookup]
  by_cases present : name ∈ names
  · simp [present]
  · simp [present, covers name present]

/-- Reconstruct the existing store carrier from finite space and cell payloads. -/
def reconstruct (core empty : Space) (spaces : List Space)
    (cells : List (String × Option Value)) : Store Space Value :=
  { core, next := spaces.length,
    spaces := fun index => (spaces[index]?).getD empty,
    cells := fun name => (cells.lookup name).join }

/-- Exact finite reconstruction is available when the cell support is supplied
and the unallocated space tail is empty. Neither a cell nor a private space is
silently discarded. -/
theorem reconstruct_exact (state : Store Space Value) (empty : Space) (names : List String)
    (vacant : EmptyTail state empty)
    (covers : ∀ name, name ∉ names → state.cells name = none) :
    reconstruct state.core empty state.spacesPrefix (state.cellRows names) = state := by
  have spaces : (fun index => (state.spacesPrefix[index]?).getD empty) = state.spaces := by
    funext index
    exact (spaces_eq_prefix_of_emptyTail vacant index).symm
  have cells : (fun name => ((state.cellRows names).lookup name).join) = state.cells := by
    funext name
    exact (cells_eq_rows_lookup state names covers name).symm
  simp only [reconstruct, spacesPrefix_length, spaces, cells]

theorem finite_reconstruction_exists (state : Store Space Value) (empty : Space)
    (finite : FiniteCells state) (vacant : EmptyTail state empty) :
    ∃ names, reconstruct state.core empty state.spacesPrefix (state.cellRows names) = state := by
  obtain ⟨names, covers⟩ := finite
  exact ⟨names, reconstruct_exact state empty names vacant covers⟩

end Store

end Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces
