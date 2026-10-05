import Mettapedia.Languages.MeTTa.PeTTa.Effects

/-!
# Named spaces and state cells extending the PeTTa command core

The existing `PeTTaSpace` remains the authority for stored atoms, matching and
mutation. This extension adds fresh private handles and named cells, as used by
programs that keep several independent tables. The same allocation and frame laws apply to any space and value carrier.
The Pattern specialization retains the existing `EvalState` default space.

These are executable storage operations and their frame laws. They do not yet
establish evaluation of an arbitrary source program or physical C conformance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces

open Mettapedia.OSLF.MeTTaIL.Syntax

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

end Store

/-- The existing Pattern-space command core specializes the same store. -/
abbrev State := Store PeTTaSpace Pattern

namespace State

def ofCore (core : EvalState) : State := Store.new core.space PeTTaSpace.empty

def read (state : State) (handle : Handle) : Option PeTTaSpace := Store.read state handle

def write (state : State) (handle : Handle) (space : PeTTaSpace) : Option State :=
  Store.write state handle space

def allocate (state : State) : Handle × State := Store.allocate state PeTTaSpace.empty

def putCell (state : State) (name : String) (value : Pattern) : State :=
  Store.putCell state name value

def query (state : State) (handle : Handle) (pattern template : Pattern) :
    Option Answers :=
  (state.read handle).map fun space => space.spaceMatch pattern template

def contents (state : State) (handle : Handle) : Option Answers :=
  (state.read handle).map PeTTaSpace.storedAtoms

def insert (state : State) (handle : Handle) (atom : Pattern) : Option State := do
  let space ← state.read handle
  state.write handle (space.addAtom atom)

def erase (state : State) (handle : Handle) (atom : Pattern) : Option State := do
  let space ← state.read handle
  state.write handle (space.removeAtom atom)

theorem insert_self (core : EvalState) (atom : Pattern) :
    (ofCore core).insert .self atom = some (ofCore (core.addAtom atom)) := rfl

theorem erase_self (core : EvalState) (atom : Pattern) :
    (ofCore core).erase .self atom = some (ofCore (core.removeAtom atom)) := rfl

theorem query_self (core : EvalState) (pattern template : Pattern) :
    (ofCore core).query .self pattern template = some (core.space.spaceMatch pattern template) := rfl

theorem query_exact (state : State) (handle : Handle) (pattern template : Pattern)
    (space : PeTTaSpace) (selected : state.read handle = some space) :
    state.query handle pattern template = some (space.spaceMatch pattern template) := by
  simp [query, selected]

theorem query_answer_sound (state : State) (handle : Handle) (pattern template : Pattern)
    (answers : Answers) (returned : state.query handle pattern template = some answers)
    (answer : Pattern) (member : answer ∈ answers) :
    ∃ space, state.read handle = some space ∧
      ∃ atom ∈ space.storedAtoms, ∃ bindings ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern pattern atom,
        answer = Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings template := by
  unfold query at returned
  cases selected : state.read handle with
  | none => simp [selected] at returned
  | some space =>
    simp only [selected, Option.map_some, Option.some.injEq] at returned
    subst answers
    exact ⟨space, rfl, PeTTaSpace.spaceMatch_sound space pattern template answer member⟩

theorem query_answer_complete (state : State) (handle : Handle) (pattern template : Pattern)
    (space : PeTTaSpace) (selected : state.read handle = some space)
    (atom : Pattern) (stored : atom ∈ space.storedAtoms)
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings)
    (matched : bindings ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern pattern atom) :
    ∃ answers, state.query handle pattern template = some answers ∧
      Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings template ∈ answers :=
  ⟨space.spaceMatch pattern template, query_exact state handle pattern template space selected,
    PeTTaSpace.spaceMatch_complete space pattern template atom bindings stored matched⟩

end State

/-! ## Positive and negative allocation controls -/

private def initial : State := State.ofCore EvalState.empty
private def payload : Pattern := .apply "payload" []

theorem two_private_spaces_are_isolated :
    let first := initial.allocate
    let second := first.2.allocate
    ∃ populated, second.2.insert first.1 payload = some populated ∧
      populated.contents first.1 = some [payload] ∧
      populated.contents second.1 = some [] := by
  simp [initial, State.ofCore, EvalState.empty, State.allocate, State.insert, State.read,
    State.write, State.contents, Store.new, Store.allocate, Store.read, Store.write,
    PeTTaSpace.storedAtoms, PeTTaSpace.storedRuleAtoms, PeTTaSpace.addAtom, PeTTaSpace.empty]

theorem unallocated_space_cannot_be_written :
    initial.write (.privateSpace 0) PeTTaSpace.empty = none := rfl

theorem changing_a_cell_does_not_add_a_fact :
    (initial.putCell "memo" payload).contents .self = some [] := rfl

end Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces
