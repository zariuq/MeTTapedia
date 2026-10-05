import Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces
import Mettapedia.Languages.MeTTa.PeTTa.SourceProgram
import Mathlib.Data.String.Lemmas

/-!
# Ground source primitives and private storage

The source carrier is the existing four-constructor Atom, so a Boolean value,
a bare symbol and a nullary expression retain their distinct meanings. Private
spaces specialize the shared allocation and frame laws to ordered atom lists.

Handles are opaque grounded values. Their internal token is an abstract fresh
identifier, not a physical pointer or an observable integer. The text reader
does not construct this grounded type. Native conformance must preserve handle
identity, allocation, ordered queries and effects; physical representation is
outside this semantics.

Primitive faults remain separate from an empty answer bag and from the Boolean
False. Arithmetic below specifies mathematical integers; the MM0 input profile
restricts number arguments to naturals and nonzero division denominators.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SourcePrimitives

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst)
open NamedSpaces (Handle Store)

abbrev State := Store (List Atom) Atom

def empty : State := Store.new [] []

def handleValue : Handle → Atom
  | .self => .symbol "&self"
  | .privateSpace index =>
      .grounded (.custom "PeTTa.Space" (String.replicate index '#'))

def readHandle : Atom → Option Handle
  | .symbol "&self" => some .self
  | .grounded (.custom "PeTTa.Space" token) =>
      if token = String.replicate token.length '#' then
        some (.privateSpace token.length)
      else none
  | _ => none

@[simp] theorem readHandle_handleValue (handle : Handle) :
    readHandle (handleValue handle) = some handle := by
  cases handle <;> simp [handleValue, readHandle]

theorem handleValue_injective : Function.Injective handleValue := by
  intro first second same
  have := congrArg readHandle same
  simpa using this

def query (rows : List Atom) (pattern template : Atom) : List Atom :=
  rows.filterMap fun row =>
    (SourceProgram.matchValue [] pattern row).map fun bindings => applySubst bindings template

def insert (state : State) (handle : Handle) (atom : Atom) : Option State := do
  let rows ← state.read handle
  state.write handle (rows ++ [atom])

def erase (state : State) (handle : Handle) (atom : Atom) : Option State := do
  let rows ← state.read handle
  state.write handle (rows.filter (· != atom))

@[simp] theorem query_append (first second : List Atom) (pattern template : Atom) :
    query (first ++ second) pattern template =
      query first pattern template ++ query second pattern template := by
  simp [query]

theorem query_sound {rows : List Atom} {pattern template answer : Atom}
    (found : answer ∈ query rows pattern template) :
    ∃ row ∈ rows, ∃ bindings,
      SourceProgram.matchValue [] pattern row = some bindings ∧
        applySubst bindings template = answer := by
  rw [query, List.mem_filterMap] at found
  obtain ⟨row, member, matched⟩ := found
  cases bound : SourceProgram.matchValue [] pattern row with
  | none => simp [bound] at matched
  | some bindings =>
      exact ⟨row, member, bindings, bound, by simpa [bound] using matched⟩

theorem query_complete {rows : List Atom} {pattern template row : Atom}
    {bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst}
    (member : row ∈ rows)
    (matched : SourceProgram.matchValue [] pattern row = some bindings) :
    applySubst bindings template ∈ query rows pattern template := by
  rw [query, List.mem_filterMap]
  exact ⟨row, member, by simp [matched]⟩

theorem insert_reads_back {state after : State} {handle : Handle} {atom : Atom}
    (inserted : insert state handle atom = some after) :
    ∃ before, state.read handle = some before ∧
      after.read handle = some (before ++ [atom]) := by
  unfold insert at inserted
  cases read : state.read handle with
  | none => simp [read] at inserted
  | some rows =>
      simp only [read] at inserted
      exact ⟨rows, rfl, Store.write_reads_back state handle _ after inserted⟩

theorem insert_read_other {state after : State} {handle other : Handle} {atom : Atom}
    (inserted : insert state handle atom = some after) (different : other ≠ handle) :
    after.read other = state.read other := by
  unfold insert at inserted
  cases read : state.read handle with
  | none => simp [read] at inserted
  | some rows =>
      simp only [read] at inserted
      exact Store.write_read_other state handle other _ after inserted different

theorem insert_preserves_cells {state after : State} {handle : Handle} {atom : Atom}
    (inserted : insert state handle atom = some after) : after.cells = state.cells := by
  unfold insert at inserted
  cases read : state.read handle with
  | none => simp [read] at inserted
  | some rows =>
      simp only [read] at inserted
      exact Store.write_preserves_cells state handle _ after inserted

theorem insert_exists_of_read_some {state : State} {handle : Handle} {rows : List Atom}
    (allocated : state.read handle = some rows) (atom : Atom) :
    ∃ after, insert state handle atom = some after := by
  obtain ⟨after, written⟩ := Store.write_exists_of_read_some state handle rows
    (rows ++ [atom]) allocated
  exact ⟨after, by simp [insert, allocated, written]⟩

theorem erase_exists_of_read_some {state : State} {handle : Handle} {rows : List Atom}
    (allocated : state.read handle = some rows) (atom : Atom) :
    ∃ after, erase state handle atom = some after := by
  obtain ⟨after, written⟩ := Store.write_exists_of_read_some state handle rows
    (rows.filter (· != atom)) allocated
  exact ⟨after, by simp [erase, allocated, written]⟩

theorem erase_reads_back {state after : State} {handle : Handle} {atom : Atom}
    (erased : erase state handle atom = some after) :
    ∃ before, state.read handle = some before ∧
      after.read handle = some (before.filter (· != atom)) := by
  unfold erase at erased
  cases read : state.read handle with
  | none => simp [read] at erased
  | some rows =>
      simp only [read] at erased
      exact ⟨rows, rfl, Store.write_reads_back state handle _ after erased⟩

theorem erase_read_other {state after : State} {handle other : Handle} {atom : Atom}
    (erased : erase state handle atom = some after) (different : other ≠ handle) :
    after.read other = state.read other := by
  unfold erase at erased
  cases read : state.read handle with
  | none => simp [read] at erased
  | some rows =>
      simp only [read] at erased
      exact Store.write_read_other state handle other _ after erased different

theorem erase_preserves_cells {state after : State} {handle : Handle} {atom : Atom}
    (erased : erase state handle atom = some after) : after.cells = state.cells := by
  unfold erase at erased
  cases read : state.read handle with
  | none => simp [read] at erased
  | some rows =>
      simp only [read] at erased
      exact Store.write_preserves_cells state handle _ after erased

inductive Fault where
  | invalidSpace
  | missingCell (name : String)
  | invalidArguments (head : String)
  | zeroDivisor
  deriving DecidableEq, Repr

abbrev Result := Except Fault (State × List Atom)

def boolean (value : Bool) : Atom := .grounded (.bool value)

def known (head : String) : Bool :=
  head ∈ ["+", "-", "*", "//", "%", "<", "<=", "==", "cons", "size-atom",
    "index-atom", "new-space", "add-atom", "remove-atom", "get-atoms", "match",
    "get-state", "change-state!"]

/-- Native argument demand: patterns, templates and stored data are values;
numeric operands and locations are evaluated. -/
def rawArgument (head : String) (index : Nat) : Bool :=
  (head = "match" && index > 0) ||
  ((head = "add-atom" || head = "remove-atom" || head = "change-state!") && index = 1)

def apply (state : State) (head : String) (arguments : List Atom) : Result :=
  let answer := fun value => Except.ok (state, [value])
  let bad := Except.error (Fault.invalidArguments head)
  match head, arguments with
  | "+", [.grounded (.int left), .grounded (.int right)] =>
      answer (.grounded (.int (left + right)))
  | "-", [.grounded (.int left), .grounded (.int right)] =>
      answer (.grounded (.int (left - right)))
  | "*", [.grounded (.int left), .grounded (.int right)] =>
      answer (.grounded (.int (left * right)))
  | "//", [.grounded (.int left), .grounded (.int right)] =>
      if right = 0 then .error .zeroDivisor else answer (.grounded (.int (left / right)))
  | "%", [.grounded (.int left), .grounded (.int right)] =>
      if right = 0 then .error .zeroDivisor else answer (.grounded (.int (left % right)))
  | "<", [.grounded (.int left), .grounded (.int right)] => answer (boolean (left < right))
  | "<=", [.grounded (.int left), .grounded (.int right)] => answer (boolean (left ≤ right))
  | "==", [left, right] => answer (boolean (left == right))
  | "cons", [first, .expression rest] => answer (.expression (first :: rest))
  | "size-atom", [.expression items] => answer (.grounded (.int items.length))
  | "size-atom", [_] => answer (.expression [])
  | "index-atom", [.expression items, .grounded (.int index)] =>
      if index < 0 then .ok (state, [])
      else .ok (state, (items[index.toNat]?).toList)
  | "new-space", [] =>
      let (handle, after) := state.allocate []
      .ok (after, [handleValue handle])
  | "add-atom", [location, atom] =>
      match readHandle location >>= fun handle => insert state handle atom with
      | some after => .ok (after, [boolean true])
      | none => .error .invalidSpace
  | "remove-atom", [location, atom] =>
      match readHandle location >>= fun handle => erase state handle atom with
      | some after => .ok (after, [boolean true])
      | none => .error .invalidSpace
  | "get-atoms", [location] =>
      match readHandle location >>= state.read with
      | some rows => .ok (state, rows)
      | none => .error .invalidSpace
  | "match", [location, pattern, template] =>
      match readHandle location >>= state.read with
      | some rows => .ok (state, query rows pattern template)
      | none => .error .invalidSpace
  | "change-state!", [.symbol name, value] =>
      .ok (state.putCell name value, [boolean true])
  | "get-state", [.symbol name] =>
      match state.cells name with
      | some value => answer value
      | none => .error (.missingCell name)
  | _, _ => bad

/-! ## Positive and negative primitive controls -/

theorem fresh_handle_reads_empty (state : State) :
    ((state.allocate []).2).read (state.allocate []).1 = some [] :=
  Store.allocation_reads_empty state []

theorem repeated_rows_retain_occurrences (row pattern template : Atom) :
    query [row, row] pattern template =
      query [row] pattern template ++ query [row] pattern template :=
  query_append [row] [row] pattern template

theorem missing_cell_is_fault (state : State) (name : String)
    (missing : state.cells name = none) :
    apply state "get-state" [.symbol name] = .error (.missingCell name) := by
  simp [apply, missing]

theorem zero_division_is_fault (state : State) (left : Int) :
    apply state "//" [.grounded (.int left), .grounded (.int 0)] = .error .zeroDivisor := by
  simp [apply]

theorem stored_false_is_an_answer (state : State) (name : String) :
    apply (state.putCell name (boolean false)) "get-state" [.symbol name] =
      .ok (state.putCell name (boolean false), [boolean false]) := by
  simp [apply]

end Mettapedia.Languages.MeTTa.PeTTa.SourcePrimitives
