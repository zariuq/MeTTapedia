import Mathlib.Data.List.Basic

/-!
# Constructor and arity tests before an ordered match

A wildcard admits every shape. A constructor test can be used to narrow
a candidate sequence when every successful match passes it. The matcher
still decides constraints such as repeated bindings. The proof retains
each occurrence and its position relative to every other success.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.PatternPlans

universe u v w x
variable {Symbol : Type u} [DecidableEq Symbol]

abbrev Shape (Symbol : Type u) := Symbol × Nat
abbrev Test (Symbol : Type u) := Option (Shape Symbol)

def accepts (test : Test Symbol) (shape : Shape Symbol) : Bool :=
  match test with
  | none => true
  | some expected => decide (shape = expected)

def disjoint (one other : Test Symbol) : Bool :=
  match one, other with
  | some a, some b => decide (a ≠ b)
  | _, _ => false

theorem disjoint_excludes_joint_match {one other : Test Symbol} (separated : disjoint one other = true)
    (shape : Shape Symbol) (oneMatches : accepts one shape = true) :
    accepts other shape = false := by
  cases one <;> cases other <;> simp_all [disjoint, accepts]

variable {Row : Type v} {Input : Type w} {Value : Type x}

theorem filter_preserves_matches (test : Row → Test Symbol) (shape : Input → Shape Symbol)
    (matchRow : Row → Input → Option Value)
    (covers : ∀ row input value, matchRow row input = some value → accepts (test row) (shape input) = true)
    (rows : List Row) (input : Input) :
    (rows.filter (fun row => accepts (test row) (shape input))).filterMap (matchRow · input) =
      rows.filterMap (matchRow · input) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases outcome : matchRow row input with
    | none => by_cases allowed : accepts (test row) (shape input) = true <;>
        simp [allowed, outcome, ih]
    | some value => simp [covers row input value outcome, outcome, ih]

namespace Controls

theorem constructor_arity_separates :
    disjoint (some ("pair", 2)) (some ("pair", 1)) = true := by decide +kernel

theorem a_wildcard_overlaps_any_constructor :
    disjoint none (some ("pair", 2)) = false ∧ accepts none ("pair", 2) = true := by decide +kernel

private def headTest (row : String × Nat) : Test String := some (row.1, 0)
private def matchHead (row : String × Nat) (head : String) : Option Nat :=
  if head = row.1 then some row.2 else none

theorem duplicates_survive_a_shape_index :
    (([("same", 7), ("other", 2), ("same", 7)].filter
      (fun row => accepts (headTest row) ("same", 0))).filterMap (matchHead · "same")) = [7, 7] := by decide +kernel

end Controls

end Mettapedia.Machines.Specialization.PatternPlans
