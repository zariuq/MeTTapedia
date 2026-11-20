import Mettapedia.Languages.MeTTa.PeTTa.StdLib

/-!
# The native call table, one equation per call

`StdLib.apply` is one case analysis on the name and the arguments of a
native call. Unfolding it to evaluate a single call costs more as the table
grows, and a proof that evaluates one call by unfolding the whole table
stops working when the table gains cases.

Each equation here is the evaluation of one call shape, proved by reduction
of the table. They are simplification lemmas of high priority: a
simplification that also unfolds the table uses the equation for the call
at hand first, and never reaches the rest of the table.

The equations already stated beside the table are given the same role.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StdLib

open Mettapedia.Languages.MeTTa.OSLFCore
open NamedSpaces (Handle Store)
open Effects
open SpaceSemantics (query)

attribute [simp high] structural_equality native_cons integer_addition greater_comparison
  greater_equal_comparison reverse_returns_expression

@[simp high]
theorem integer_subtraction (state : State) (left right : Int) :
    apply state "-" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [.grounded (.int (left - right))]) := rfl

@[simp high]
theorem integer_multiplication (state : State) (left right : Int) :
    apply state "*" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [.grounded (.int (left * right))]) := rfl

@[simp high]
theorem less_comparison (state : State) (left right : Int) :
    apply state "<" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [boolean (left < right)]) := rfl

@[simp high]
theorem less_equal_comparison (state : State) (left right : Int) :
    apply state "<=" [.grounded (.int left), .grounded (.int right)] =
      .ok (state, [boolean (left ≤ right)]) := rfl

@[simp high]
theorem cons_call (state : State) (first : Atom) (rest : List Atom) :
    apply state "cons" [first, .expression rest] = .ok (state, [.expression (first :: rest)]) := rfl

/-- The native name denotes ordered concatenation, retaining duplicate
occurrences. This equation concerns expression-valued arguments. -/
@[simp high]
theorem union_atom_call (state : State) (left right : List Atom) :
    apply state "union-atom" [.expression left, .expression right] =
      .ok (state, [.expression (left ++ right)]) := rfl

@[simp high]
theorem size_of_expression (state : State) (items : List Atom) :
    apply state "size-atom" [.expression items] =
      .ok (state, [.grounded (.int items.length)]) := rfl

@[simp high]
theorem index_of_expression (state : State) (items : List Atom) (index : Int) :
    apply state "index-atom" [.expression items, .grounded (.int index)] =
      (if index < 0 then .ok (state, []) else .ok (state, (items[index.toNat]?).toList)) := rfl

@[simp high]
theorem membership_call (state : State) (value : Atom) (items : List Atom) :
    apply state "is-member" [value, .expression items] =
      .ok (state, membershipAnswers value items) := rfl

@[simp high]
theorem new_space_call (state : State) :
    apply state "new-space" [] =
      .ok ((state.allocate []).2, [handleValue (state.allocate []).1]) := rfl

@[simp high]
theorem add_atom_call (state : State) (location atom : Atom) :
    apply state "add-atom" [location, atom] =
      (if atom.isVariable then .error .instantiation else
       match readHandle location >>= fun handle => insert state handle atom with
       | some after => .ok (after, [boolean true])
       | none => .error .invalidSpace) := rfl

@[simp high]
theorem remove_atom_call (state : State) (location atom : Atom) :
    apply state "remove-atom" [location, atom] =
      (if removalNeedsValue atom then .error .instantiation else
       match readHandle location with
       | none => .error .invalidSpace
       | some handle =>
           match state.read handle with
           | none => .error .invalidSpace
           | some rows =>
               match erase state handle atom with
               | some after => .ok (after,
                   [boolean (((after.read handle).getD []).length < rows.length)])
               | none => .error .invalidSpace) := rfl

/-- A successful add identifies the actual space and the value it inserted. -/
theorem add_atom_success {state after : State} {location atom : Atom} {answers : List Atom}
    (returned : apply state "add-atom" [location, atom] = .ok (after, answers)) :
    ∃ handle, readHandle location = some handle ∧ atom.isVariable = false ∧
      insert state handle atom = some after := by
  have specified := successful_add_value returned
  simp only [add_atom_call, specified, Bool.false_eq_true, ↓reduceIte] at returned
  cases inserted : (readHandle location >>= fun handle => insert state handle atom) with
  | none => simp [inserted] at returned
  | some next =>
      rw [inserted] at returned
      obtain ⟨handle, resolved, written⟩ := Option.bind_eq_some_iff.mp inserted
      cases returned
      exact ⟨handle, resolved, specified, written⟩

/-- A successful remove is the erasure at its selected address. Its reply
can be false; that is distinct from rejecting a malformed request. -/
theorem remove_atom_success {state after : State} {location atom : Atom} {answers : List Atom}
    (returned : apply state "remove-atom" [location, atom] = .ok (after, answers)) :
    ∃ handle, readHandle location = some handle ∧ erase state handle atom = some after := by
  rw [remove_atom_call] at returned
  cases needsValue : removalNeedsValue atom with
  | true => simp [needsValue] at returned
  | false =>
      simp only [needsValue, Bool.false_eq_true, ↓reduceIte] at returned
      cases resolved : readHandle location with
      | none => simp [resolved] at returned
      | some handle =>
          cases opened : state.read handle with
          | none => simp [resolved, opened] at returned
          | some rows =>
              simp only [resolved, opened] at returned
              cases erased : erase state handle atom with
              | none => simp [erased] at returned
              | some next =>
                  rw [erased] at returned
                  cases returned
                  exact ⟨handle, rfl, erased⟩

@[simp high]
theorem get_atoms_call (state : State) (location : Atom) :
    apply state "get-atoms" [location] =
      (match readHandle location >>= state.read with
       | some rows => .ok (state, rows)
       | none => .error .invalidSpace) := rfl

@[simp high]
theorem match_call (state : State) (location pattern template : Atom) :
    apply state "match" [location, pattern, template] =
      (match readHandle location >>= state.read with
       | some rows => .ok (state, query rows pattern template)
       | none => .error .invalidSpace) := rfl

@[simp high]
theorem change_state_call (state : State) (name : String) (value : Atom) :
    apply state "change-state!" [.symbol name, value] =
      .ok (state.putCell name value, [boolean true]) := rfl

@[simp high]
theorem get_state_call (state : State) (name : String) :
    apply state "get-state" [.symbol name] =
      (match state.cells name with
       | some value => .ok (state, [value])
       | none => .error (.missingCell name)) := rfl

/-- A call of another name is not one of the calls above. -/
example (state : State) :
    apply state "unregistered" [] = .error (.invalidArguments "unregistered") := rfl

end Mettapedia.Languages.MeTTa.PeTTa.StdLib
