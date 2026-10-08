import Mettapedia.Languages.MeTTa.PeTTa.Answers
import Mettapedia.Languages.MeTTa.PeTTa.NamedSpaces
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mathlib.Data.String.Lemmas

/-!
# PeTTa state: named spaces, rows and primitive outcomes

`State` keeps ordered rows of atoms in the `&self` space and in private
spaces, together with named state cells, using the shared store of
`NamedSpaces`. A space handle is an opaque grounded value, not an observable
integer. Insertion appends a row; removal deletes the rows that match an
expression pattern. A primitive fault is distinct from an empty answer list
and from the Boolean `False`. The MeTTaIL view of the `&self` command
judgment over `Pattern` is in `PatternRewrite.Commands`.
-/

set_option autoImplicit false


namespace Mettapedia.Languages.MeTTa.PeTTa.Effects

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (applySubst matchAtom)
open NamedSpaces (Handle Store)
open SpaceSemantics (query query_append)

abbrev State := Store (List Atom) Atom

def empty : State := Store.new [] []

/-- The store after loading a program: `&self` holds the loaded atoms in source
order, and there are no private spaces or cells yet. -/
def loaded (program : SpaceSemantics.Program) : State :=
  Store.new (SpaceSemantics.loadedAtoms program) []

/-- Loading a program derives finite cell support from the store constructor. -/
theorem loaded_finite_cells (program : SpaceSemantics.Program) :
    Store.FiniteCells (loaded program) := Store.new_finiteCells _ _

theorem empty_finite_cells : Store.FiniteCells empty := Store.new_finiteCells _ _

theorem loaded_empty_tail (program : SpaceSemantics.Program) :
    Store.EmptyTail (loaded program) [] := Store.new_emptyTail _ _

theorem empty_empty_tail : Store.EmptyTail empty [] := Store.new_emptyTail _ _

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

def insert (state : State) (handle : Handle) (atom : Atom) : Option State := do
  let rows ← state.read handle
  state.write handle (rows ++ [atom])

/-- PeTTa removal uses an ordinary expression pattern, without the `cons`
list-view interpretation used by case selection. This ground-store fragment
uses the existing matcher; open stored equations require the dialect's scoped
unifier. A bare variable is not a universal removal request. -/
def removalMatches (pattern row : Atom) : Bool :=
  match pattern with
  | .expression (_ :: _) => (matchAtom [] pattern row).isSome
  | _ => false

theorem removalMatches_self (first : Atom) (rest : List Atom) :
    removalMatches (.expression (first :: rest)) (.expression (first :: rest)) = true :=
  SpaceSemantics.matchAtom_self _

def erase (state : State) (handle : Handle) (pattern : Atom) : Option State := do
  let rows ← state.read handle
  state.write handle (rows.filter fun row => !removalMatches pattern row)

/-- Physical row shape, independent of the validity or currency of its fields. -/
def RowsHaveArity (arity : Nat) (rows : List Atom) : Prop :=
  ∀ row ∈ rows, ∃ fields, row = .expression fields ∧ fields.length = arity

@[simp] theorem rowsHaveArity_nil (arity : Nat) : RowsHaveArity arity [] := by
  simp [RowsHaveArity]

theorem rowsHaveArity_append {arity : Nat} {first second : List Atom}
    (left : RowsHaveArity arity first) (right : RowsHaveArity arity second) :
    RowsHaveArity arity (first ++ second) := by
  intro row member
  rcases List.mem_append.mp member with member | member
  · exact left row member
  · exact right row member

theorem removalMatches_literal (fields : List Atom) (nonempty : fields ≠ [])
    (literal : SpaceSemantics.Literal (.expression fields)) (row : Atom) :
    removalMatches (.expression fields) row = decide (.expression fields = row) := by
  cases fields with
  | nil => contradiction
  | cons first rest =>
      simp only [removalMatches, SpaceSemantics.matchAtom_literal literal]
      split <;> simp_all


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

theorem insert_preserves_empty_tail {state after : State} {handle : Handle} {atom : Atom}
    (vacant : Store.EmptyTail state []) (inserted : insert state handle atom = some after) :
    Store.EmptyTail after [] := by
  unfold insert at inserted
  cases read : state.read handle with
  | none => simp [read] at inserted
  | some rows =>
      simp only [read] at inserted
      exact Store.write_emptyTail vacant inserted

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
    (rows.filter fun row => !removalMatches atom row) allocated
  exact ⟨after, by simp [erase, allocated, written]⟩

theorem erase_reads_back {state after : State} {handle : Handle} {atom : Atom}
    (erased : erase state handle atom = some after) :
    ∃ before, state.read handle = some before ∧
      after.read handle = some (before.filter fun row => !removalMatches atom row) := by
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

theorem erase_preserves_empty_tail {state after : State} {handle : Handle} {atom : Atom}
    (vacant : Store.EmptyTail state []) (erased : erase state handle atom = some after) :
    Store.EmptyTail after [] := by
  unfold erase at erased
  cases read : state.read handle with
  | none => simp [read] at erased
  | some rows =>
      simp only [read] at erased
      exact Store.write_emptyTail vacant erased

/-- One pattern pass clears exactly those rows it selects. No field-validity
assumption is hidden in the frame properties. -/
theorem erase_all_selected {state : State} {handle : Handle} {rows : List Atom} {pattern : Atom}
    (allocated : state.read handle = some rows)
    (selected : ∀ row ∈ rows, removalMatches pattern row = true) :
    ∃ after, erase state handle pattern = some after ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = state.read other) ∧
      after.cells = state.cells := by
  obtain ⟨after, erased⟩ := erase_exists_of_read_some allocated pattern
  obtain ⟨before, readBefore, readAfter⟩ := erase_reads_back erased
  have same : before = rows := Option.some.inj (readBefore.symm.trans allocated)
  subst before
  have filtered : rows.filter (fun row => !removalMatches pattern row) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row member
    simp [selected row member]
  exact ⟨after, erased, by simpa [filtered] using readAfter,
    fun other different => erase_read_other erased different, erase_preserves_cells erased⟩

theorem erase_literal_reads_back {state after : State} {handle : Handle}
    {fields : List Atom} (nonempty : fields ≠ [])
    (literal : SpaceSemantics.Literal (.expression fields))
    (erased : erase state handle (.expression fields) = some after) :
    ∃ before, state.read handle = some before ∧
      after.read handle = some (before.filter (· != .expression fields)) := by
  obtain ⟨before, allocated, result⟩ := erase_reads_back erased
  refine ⟨before, allocated, ?_⟩
  have predicates : (fun row => !removalMatches (.expression fields) row) =
      (fun row => row != .expression fields) := by
    funext row
    rw [removalMatches_literal fields nonempty literal]
    change (!decide (.expression fields = row)) = (!(row == .expression fields))
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
    exact eq_comm
  simpa only [predicates] using result

inductive Fault where
  | invalidSpace
  | missingCell (name : String)
  | invalidArguments (head : String)
  | zeroDivisor
  deriving DecidableEq, Repr

abbrev Result := Except Fault (State × Answers)

def boolean (value : Bool) : Atom := .grounded (.bool value)

theorem fresh_handle_reads_empty (state : State) :
    ((state.allocate []).2).read (state.allocate []).1 = some [] :=
  Store.allocation_reads_empty state []

theorem repeated_rows_retain_occurrences (row pattern template : Atom) :
    query [row, row] pattern template =
      query [row] pattern template ++ query [row] pattern template :=
  query_append [row] [row] pattern template

end Mettapedia.Languages.MeTTa.PeTTa.Effects

/-! ## Shared execution configurations

These are the existing control and continuation carriers, shared by the
independent operational rules and the executable machine. They carry the same
store and observations; no second term, state or answer representation is used.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Cases)
open Effects (State Fault)

inductive Target where
  | function (head : String)
  | data
  deriving Repr

inductive Control where
  | evaluate (bindings : Subst) (expression : Atom)
  | arguments (bindings : Subst) (target : Target)
      (remaining values : List Atom) (index : Nat)
  | sequence (remaining : List Control) (answers : Answers)
  | returned (answers : Answers)
  | fault (reason : Fault)
  deriving Repr

inductive Frame where
  | bind (bindings : Subst) (pattern body : Atom)
  | select (bindings : Subst) (cases : Cases)
  | branch (bindings : Subst) (yes no : Atom)
  | collect
  | argument (bindings : Subst) (target : Target)
      (remaining values : List Atom) (index : Nat)
  | sequence (remaining : List Control) (answers : Answers)
  deriving Repr

structure Configuration where
  state : State
  control : Control
  frames : List Frame := []
  input : List Atom := []
  output : List Atom := []

inductive Outcome where
  | complete (state : State) (answers : Answers) (input output : List Atom)
  | exhausted (configuration : Configuration)
  | fault (reason : Fault)

end Mettapedia.Languages.MeTTa.PeTTa.Eval
