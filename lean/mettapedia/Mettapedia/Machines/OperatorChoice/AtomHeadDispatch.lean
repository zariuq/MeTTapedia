import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mathlib.Data.List.Basic

/-!
# General head equations as function definitions or rewrite rules

Both readings use the existing Atom carrier, executable one-way matcher and
substitution. They differ before a successful firing: a function definition
establishes callability by head and arity, while a failed rewrite leaves its
input unchanged. The relation `Fires` specifies successful row steps
independently of candidate enumeration.

This is a finite one-step comparison. It does not specify PeTTa's bidirectional
list-view unifier, fresh extra right-hand-side variables, recursive evaluation,
typed admission, effects or native representation. In particular, equality of
successful firings does not establish equality of the complete observations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.AtomHeadDispatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst matchAtom applySubst MatchAtomRel)

structure Row where
  scope : Nat
  left : Atom
  right : Atom
  deriving DecidableEq, Repr

def matchRow (row : Row) (term : Atom) : Option Atom :=
  (matchAtom [] row.left term).map (fun substitution => applySubst substitution row.right)

def answers (scope : Nat) (rows : List Row) (term : Atom) : List Atom :=
  rows.filterMap fun row => if row.scope = scope then matchRow row term else none

def Fires (scope : Nat) (rows : List Row) (source target : Atom) : Prop :=
  ∃ row ∈ rows, row.scope = scope ∧ ∃ substitution,
    MatchAtomRel [] row.left source substitution ∧ target = applySubst substitution row.right

theorem answer_iff_fires (scope : Nat) (rows : List Row) (source target : Atom) :
    target ∈ answers scope rows source ↔ Fires scope rows source target := by
  constructor
  · intro found
    obtain ⟨row, member, selected⟩ := List.mem_filterMap.mp found
    by_cases visible : row.scope = scope
    · simp only [if_pos visible, matchRow, Option.map_eq_some_iff] at selected
      obtain ⟨substitution, matched, same⟩ := selected
      exact ⟨row, member, visible, substitution,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_sound matched, same.symm⟩
    · simp [visible] at selected
  · rintro ⟨row, member, visible, substitution, matched, rfl⟩
    exact List.mem_filterMap.mpr ⟨row, member, by
      simp [visible, matchRow,
        Mettapedia.Languages.ProcessCalculi.MORK.matchAtom_complete matched]⟩

theorem answers_append (scope : Nat) (first second : List Row) (term : Atom) :
    answers scope (first ++ second) term = answers scope first term ++ answers scope second term := by
  simp [answers]

theorem foreign_rows_do_not_fire (scope : Nat) (rows added : List Row) (term : Atom)
    (foreign : ∀ row ∈ added, row.scope ≠ scope) :
    answers scope (rows ++ added) term = answers scope rows term := by
  rw [answers_append]
  have absent : answers scope added term = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro row member
    simp [foreign row member]
  simp [absent]

def defines (generalHeads : Bool) (name : String) (arity : Nat) (row : Row) : Bool :=
  match row.left with
  | .expression (.symbol head :: arguments) => head == name && arguments.length == arity
  | .expression (.var _ :: arguments) => generalHeads && arguments.length == arity
  | _ => false

def functionRows (generalHeads : Bool) (name : String) (arity : Nat) (rows : List Row) : List Row :=
  rows.filter (defines generalHeads name arity)

inductive Result where
  | returned (term : Atom)
  | called (answers : List Atom)
  deriving DecidableEq, Repr

/-- Establishing a function can change a previously inert nonmatching call
into an empty call, even when it adds no successful firing for that input. -/
def functionResult (generalHeads : Bool) (scope : Nat) (rows : List Row) (term : Atom) : Result :=
  match term with
  | .expression (.symbol name :: arguments) =>
      let visible := (functionRows generalHeads name arguments.length rows).filter
        (fun row => row.scope == scope)
      if visible.isEmpty then .returned term else .called (answers scope visible term)
  | _ => .returned term

/-- A failed rewrite is a normal form of this finite row set, not a proof
that it is an inhabited value of a declared type. -/
def rewriteResult (scope : Nat) (rows : List Row) (term : Atom) : Result :=
  match answers scope rows term with
  | [] => .returned term
  | first :: rest => .called (first :: rest)

/-- Holding is an entry-role decision, independent of head-pattern power. -/
def enter (generalHeads held : Bool) (scope : Nat) (rows : List Row) (term : Atom) : Result :=
  if held then .returned term else functionResult generalHeads scope rows term

theorem held_is_returned (generalHeads : Bool) (scope : Nat) (rows : List Row) (term : Atom) :
    enter generalHeads true scope rows term = .returned term := rfl

theorem rewrite_returns_on_no_firing (scope : Nat) (rows : List Row) (term : Atom)
    (none : ∀ target, ¬ Fires scope rows term target) :
    rewriteResult scope rows term = .returned term := by
  cases found : answers scope rows term with
  | nil => simp [rewriteResult, found]
  | cons first rest =>
    have member : first ∈ answers scope rows term := by simp [found]
    exact False.elim (none first ((answer_iff_fires _ _ _ _).mp member))

namespace Controls

def number (n : Int) : Atom := .grounded (.int n)
def call (head : String) (n : Int) : Atom := .expression [.symbol head, number n]
def row : Row := ⟨0, .expression [.var "head", number 4], number 8⟩

theorem a_general_head_matches_through_the_real_matcher :
    answers 0 [row] (call "double" 4) = [number 8] := by decide

theorem the_same_row_does_not_match_another_argument :
    answers 0 [row] (call "foo" 5) = [] := by decide

theorem function_callability_and_rewriting_disagree_on_failure :
    functionResult true 0 [row] (call "foo" 5) = .called [] ∧
      rewriteResult 0 [row] (call "foo" 5) = .returned (call "foo" 5) := by decide

theorem named_function_policy_keeps_the_expression_inert :
    functionResult false 0 [row] (call "double" 4) = .returned (call "double" 4) ∧
      functionResult true 0 [row] (call "double" 4) = .called [number 8] := by decide

theorem a_public_general_rule_can_capture_an_unprotected_internal_term :
    functionResult true 0 [row] (call "pm:state" 4) = .called [number 8] ∧
      enter true true 0 [row] (call "pm:state" 4) = .returned (call "pm:state" 4) := by decide

def tagged : Row := ⟨0, .expression [.var "head", .var "arg"],
  .expression [.symbol "selected", .var "head", .var "arg"]⟩

theorem the_head_binding_and_argument_are_preserved :
    answers 0 [tagged] (call "double" 4) =
      [.expression [.symbol "selected", .symbol "double", number 4]] := by decide

theorem a_rule_of_another_scope_does_not_change_the_call :
    functionResult true 1 [row] (call "double" 4) = .returned (call "double" 4) ∧
      rewriteResult 1 [row] (call "double" 4) = .returned (call "double" 4) := by decide

theorem equal_payload_occurrences_are_not_deduplicated :
    answers 0 [row, row] (call "double" 4) = [number 8, number 8] := by decide

end Controls

end Mettapedia.Machines.OperatorChoice.AtomHeadDispatch
