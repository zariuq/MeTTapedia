import Mettapedia.Languages.OCaml.Syntax

/-! Linear OCaml patterns bind fresh slots in source order. Clause selection
stops at the first successful pattern; it never unions later clause bindings.
The shared GSLT matcher is a separate realization of this source operation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

mutual
  def matchPattern : MatchPattern → Value → Option (List Value)
    | .bind, value => some [value]
    | .wildcard, _ => some []
    | .literal expected, .literal actual => if expected = actual then some [] else none
    | .tuple patterns, .tuple values => matchFields patterns values
    | .cons head tail, .cons first rest => do
        pure ((← matchPattern head first) ++ (← matchPattern tail rest))
    | .variant typeId constructor patterns, .variant actualType actualConstructor values =>
        if typeId = actualType ∧ constructor = actualConstructor then matchFields patterns values else none
    | _, _ => none

  def matchFields : List MatchPattern → List Value → Option (List Value)
    | [], [] => some []
    | pattern :: rest, value :: tail => do
        pure ((← matchPattern pattern value) ++ (← matchFields rest tail))
    | _, _ => none
end

def selectClause (clauses : List Clause) (value : Value) : Option (Code × List Value) :=
  match clauses with
  | [] => none
  | clause :: rest => match matchPattern clause.pattern value with
      | some bindings => some (clause.body, bindings)
      | none => selectClause rest value

theorem selectClause_first (clause : Clause) (rest : List Clause) (value : Value)
    (bindings : List Value) (matched : matchPattern clause.pattern value = some bindings) :
    selectClause (clause :: rest) value = some (clause.body, bindings) := by
  simp [selectClause, matched]

theorem selectClause_skip (clause : Clause) (rest : List Clause) (value : Value)
    (failed : matchPattern clause.pattern value = none) :
    selectClause (clause :: rest) value = selectClause rest value := by
  simp [selectClause, failed]

theorem selectClause_authorized (clauses : List Clause) (value : Value)
    (body : Code) (bindings : List Value)
    (selected : selectClause clauses value = some (body, bindings)) :
    ∃ before clause after, clauses = before ++ clause :: after ∧ clause.body = body ∧
      matchPattern clause.pattern value = some bindings ∧
      ∀ earlier ∈ before, matchPattern earlier.pattern value = none := by
  induction clauses with
  | nil => simp [selectClause] at selected
  | cons clause rest ih =>
      cases matching : matchPattern clause.pattern value with
      | some found =>
          have same : (clause.body, found) = (body, bindings) :=
            Option.some.inj (by simpa [selectClause, matching] using selected)
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
          exact ⟨[], clause, rest, rfl, rfl, matching, by simp⟩
      | none =>
          obtain ⟨before, winner, after, shape, same, succeeds, failures⟩ :=
            ih (by simpa [selectClause, matching] using selected)
          refine ⟨clause :: before, winner, after, by simp [shape], same, succeeds, ?_⟩
          intro earlier present
          rcases List.mem_cons.mp present with rfl | present
          · exact matching
          · exact failures earlier present

end Mettapedia.Languages.OCaml
