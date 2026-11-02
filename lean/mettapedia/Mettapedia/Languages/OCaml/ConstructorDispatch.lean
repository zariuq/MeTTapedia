import Mettapedia.Languages.OCaml.PatternProperties

/-!
# Compiled outer-constructor screens for ordered clauses

Each row keeps its authored pattern and body, and precomputes a necessary
outer shape test. The compiled selector still commits to the first full
match. Bind/wildcard patterns remain candidates for every value. Tuple arity,
variant identity and literal kind/value are preserved in the screen.

This is a compiled decision list, not a hash index or a cost theorem. It
avoids interpreting rejected patterns while retaining exact ordered choice.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.ConstructorDispatch

inductive Shape
  | literal (value : Literal)
  | tuple (arity : Nat)
  | cons
  | variant (typeId constructor arity : Nat)
  | closure
  deriving DecidableEq, Repr

def valueShape : Value → Shape
  | .literal value => .literal value
  | .tuple fields => .tuple fields.length
  | .cons _ _ => .cons
  | .variant typeId constructor fields => .variant typeId constructor fields.length
  | .closure _ _ => .closure

def patternShape : MatchPattern → Option Shape
  | .bind | .wildcard => none
  | .literal value => some (.literal value)
  | .tuple fields => some (.tuple fields.length)
  | .cons _ _ => some .cons
  | .variant typeId constructor fields => some (.variant typeId constructor fields.length)

def passes (expected : Option Shape) (value : Value) : Bool :=
  match expected with
  | none => true
  | some shape => decide (shape = valueShape value)

theorem matched_fields_length {patterns : List MatchPattern} {values bindings : List Value}
    (matched : matchFields patterns values = some bindings) : patterns.length = values.length := by
  induction patterns generalizing values bindings with
  | nil => cases values <;> simp [matchFields] at matched ⊢
  | cons pattern rest ih =>
      cases values with
      | nil => cases matched
      | cons value tail =>
          cases first : matchPattern pattern value with
          | none => simp [matchFields, first] at matched
          | some captured =>
              cases later : matchFields rest tail with
              | none => simp [matchFields, first, later] at matched
              | some remaining => simpa using congrArg Nat.succ (ih later)

theorem match_passes (pattern : MatchPattern) (value : Value) (bindings : List Value)
    (matched : matchPattern pattern value = some bindings) : passes (patternShape pattern) value = true := by
  cases pattern with
  | bind | wildcard => rfl
  | literal expected =>
      cases value <;> simp only [matchPattern] at matched
      all_goals first | contradiction | skip
      split at matched
      next same => simp [passes, patternShape, valueShape, same]
      next => cases matched
  | tuple fields =>
      cases value <;> simp only [matchPattern] at matched
      all_goals first | contradiction | skip
      simp [passes, patternShape, valueShape, matched_fields_length matched]
  | cons head tail =>
      cases value <;> simp only [matchPattern] at matched
      all_goals first | contradiction | rfl
  | variant typeId constructor fields =>
      cases value <;> simp only [matchPattern] at matched
      all_goals first | contradiction | skip
      split at matched
      next same =>
        obtain ⟨rfl, rfl⟩ := same
        simp [passes, patternShape, valueShape, matched_fields_length matched]
      next => cases matched

theorem rejected_cannot_match (pattern : MatchPattern) (value : Value)
    (rejected : passes (patternShape pattern) value = false) : matchPattern pattern value = none := by
  cases matched : matchPattern pattern value with
  | none => rfl
  | some bindings =>
      have accepted := match_passes pattern value bindings matched
      rw [rejected] at accepted
      cases accepted

structure Row where
  source : Clause
  shape : Option Shape
  consistent : shape = patternShape source.pattern

def compile (clauses : List Clause) : List Row :=
  clauses.map fun clause => ⟨clause, patternShape clause.pattern, rfl⟩

def select : List Row → Value → Option (Code × List Value)
  | [], _ => none
  | row :: rest, value =>
      if passes row.shape value then
        match matchPattern row.source.pattern value with
        | some bindings => some (row.source.body, bindings)
        | none => select rest value
      else select rest value

theorem select_exact (rows : List Row) (value : Value) :
    select rows value = selectClause (rows.map Row.source) value := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [select, List.map_cons, selectClause]
      cases tested : passes row.shape value with
      | false =>
          have rejected := rejected_cannot_match row.source.pattern value (by simpa [row.consistent] using tested)
          simp [rejected, ih]
      | true => cases matchPattern row.source.pattern value <;> simp [ih]

theorem compiled_select_exact (clauses : List Clause) (value : Value) :
    select (compile clauses) value = selectClause clauses value := by
  rw [select_exact]
  simp [compile, List.map_map, Function.comp_def]

theorem compiled_occurrences_retained (clauses : List Clause) :
    (compile clauses).map Row.source = clauses := by simp [compile, List.map_map, Function.comp_def]

theorem compiled_length (clauses : List Clause) : (compile clauses).length = clauses.length := by simp [compile]

theorem selected_binding_count (clauses : List Clause) (value : Value) (body : Code) (bindings : List Value)
    (selected : select (compile clauses) value = some (body, bindings)) :
    ∃ clause ∈ clauses, clause.body = body ∧ bindings.length = clause.pattern.binders := by
  rw [compiled_select_exact] at selected
  obtain ⟨before, clause, after, shape, same, matched, _⟩ := selectClause_authorized clauses value body bindings selected
  exact ⟨clause, by simp [shape], same, matchPattern_binding_count clause.pattern value bindings matched⟩

namespace Controls

def wildcardFirst : List Clause := [⟨.wildcard, 7⟩, ⟨.literal (.integer 1), 9⟩]

theorem wildcard_keeps_priority :
    select (compile wildcardFirst) (.literal (.integer 1)) = some (7, []) := by rfl

theorem reversing_clauses_changes_the_result :
    select (compile wildcardFirst.reverse) (.literal (.integer 1)) = some (9, []) := by rfl

theorem boolean_is_not_integer_one :
    select (compile [⟨.literal (.integer 1), 7⟩]) (.literal (.boolean true)) = none := by decide +kernel

theorem tuple_field_order_keeps_binding_order :
    select (compile [⟨.tuple [.bind, .bind], 3⟩]) (.tuple [.literal (.integer 4), .literal (.integer 5)]) =
      some (3, [.literal (.integer 4), .literal (.integer 5)]) := by rfl

theorem same_constructor_number_wrong_type_is_not_a_match :
    select (compile [⟨.variant 1 0 [.bind], 3⟩]) (.variant 2 0 [.literal (.integer 4)]) = none := by decide +kernel

end Controls

end Mettapedia.Languages.OCaml.ConstructorDispatch
