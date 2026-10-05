import Mettapedia.Languages.Chaitin.Syntax

/-!
# Dynamic binding laws for Chaitin's historical Lisp

The first occurrence of a parameter wins, matching the reference interpreter.
Bindings of distinct names preserve lookup; unsigned integers evaluate to
themselves even when present among the parameter names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.EnvironmentLaws

@[simp] theorem lookup_cons_same (name : String) (value : SExpr)
    (environment : Environment) :
    lookup ((.symbol name, value) :: environment) (.symbol name) = value := by
  simp [lookup]

theorem lookup_cons_ne (name key : SExpr) (value : SExpr)
    (environment : Environment) (different : name ≠ key) :
    lookup ((name, value) :: environment) key = lookup environment key := by
  cases key <;> simp [lookup, different]

theorem lookup_filter_ne (name key : SExpr) (environment : Environment)
    (different : name ≠ key) :
    lookup (environment.filter (fun entry => entry.1 != name)) key =
      lookup environment key := by
  have finds :
      (environment.filter (fun entry => entry.1 != name)).find?
          (fun entry => entry.1 == key) =
        environment.find? (fun entry => entry.1 == key) := by
    rw [List.find?_filter]
    congr 1
    funext entry
    by_cases same : entry.1 = key
    · simp [same, Ne.symm different]
    · simp [same]
  cases key <;> simp only [lookup, finds]

/-- A binding does not change the value of a name absent from its parameters. -/
theorem lookup_bindNames_of_not_mem (names arguments : List SExpr)
    (environment : Environment) (key : SExpr) (absent : key ∉ names) :
    lookup (bindNames names arguments environment) key = lookup environment key := by
  induction names generalizing arguments with
  | nil => rfl
  | cons name names recurse =>
      have different : name ≠ key := by
        intro same
        exact absent (by simp [same])
      have remaining : key ∉ names := fun member => absent (List.mem_cons_of_mem _ member)
      rw [bindNames, lookup_cons_ne _ _ _ _ different,
        lookup_filter_ne _ _ _ different, recurse arguments.tail remaining]

@[simp] theorem lookup_bindNames_head (name : String) (names arguments : List SExpr)
    (environment : Environment) :
    lookup (bindNames (.symbol name :: names) arguments environment) (.symbol name) =
      arguments.headD SExpr.nil := by
  simp only [bindNames, lookup_cons_same]

/-- Repeated parameter names retain the first supplied value. -/
@[simp] theorem duplicate_parameter_first_wins (name : String)
    (first second : SExpr) (environment : Environment) :
    lookup (bindNames [.symbol name, .symbol name] [first, second] environment)
      (.symbol name) = first := by
  simp

/-- Missing actual arguments bind their names to the empty list. -/
@[simp] theorem missing_argument_binds_nil (name : String)
    (environment : Environment) :
    lookup (bindNames [.symbol name] [] environment) (.symbol name) = SExpr.nil := by
  simp

/-- A later distinct parameter retains its own supplied argument. -/
theorem lookup_bindNames_tail (name : SExpr) (names arguments : List SExpr)
    (environment : Environment) (key : SExpr) (different : name ≠ key) :
    lookup (bindNames (name :: names) arguments environment) key =
      lookup (bindNames names arguments.tail environment) key := by
  rw [bindNames, lookup_cons_ne _ _ _ _ different, lookup_filter_ne _ _ _ different]

theorem lookup_bind_of_not_mem (parameters arguments : SExpr)
    (environment : Environment) (key : SExpr) (absent : key ∉ parameters.elements) :
    lookup (bind parameters arguments environment) key = lookup environment key :=
  lookup_bindNames_of_not_mem parameters.elements arguments.elements environment key absent

theorem lookup_bind_single (name : String) (value : SExpr) (environment : Environment) :
    lookup (bind (.list [.symbol name]) (.list [value]) environment) (.symbol name) =
      value := by
  simp [bind, SExpr.elements]

theorem number_parameter_does_not_override_literal (number : Nat) (value : SExpr)
    (environment : Environment) :
    lookup (bindNames [.number number] [value] environment) (.number number) =
      .number number := rfl

/-- The first occurrence of a word parameter receives the argument at the
same position, or `nil` if the argument list is shorter. -/
theorem lookup_bindNames_index (index : Nat) (names arguments : List SExpr)
    (environment : Environment) (name : String)
    (position : names[index]? = some (.symbol name))
    (first : .symbol name ∉ names.take index) :
    lookup (bindNames names arguments environment) (.symbol name) =
      (arguments[index]?).getD SExpr.nil := by
  induction index generalizing names arguments with
  | zero =>
      cases names with
      | nil => simp at position
      | cons head rest =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at position
          subst head
          rw [lookup_bindNames_head]
          cases arguments <;> rfl
  | succ index recurse =>
      cases names with
      | nil => simp at position
      | cons head rest =>
          have different : head ≠ .symbol name := by
            intro same
            apply first
            simp [List.take, same]
          have remaining : .symbol name ∉ rest.take index := by
            intro member
            apply first
            simp [List.take, member]
          rw [lookup_bindNames_tail _ _ _ _ _ different]
          have atRest : rest[index]? = some (.symbol name) := by simpa using position
          simpa using recurse rest arguments.tail atRest remaining

end Mettapedia.Languages.Chaitin.EnvironmentLaws
