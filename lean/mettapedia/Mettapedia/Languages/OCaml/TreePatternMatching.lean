import Mettapedia.Languages.OCaml.TreeValue

/-! Pattern matching on tree values, before code allocation. Bindings retain
source field order and clause selection stops at the first successful row. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

mutual
  def matchTreePattern : MatchPattern → TreeValue → Option (List TreeValue)
    | .bind, value => some [value]
    | .wildcard, _ => some []
    | .literal expected, .literal actual => if expected = actual then some [] else none
    | .tuple patterns, .tuple values => matchTreeFields patterns values
    | .cons head tail, .cons first rest => do
        pure ((← matchTreePattern head first) ++ (← matchTreePattern tail rest))
    | .variant typeId constructor patterns, .variant actualType actualConstructor values =>
        if typeId = actualType ∧ constructor = actualConstructor then matchTreeFields patterns values else none
    | _, _ => none

  def matchTreeFields : List MatchPattern → List TreeValue → Option (List TreeValue)
    | [], [] => some []
    | pattern :: rest, value :: tail => do
        pure ((← matchTreePattern pattern value) ++ (← matchTreeFields rest tail))
    | _, _ => none
end

def selectTreeClause (clauses : List (MatchPattern × ExpressionTree)) (value : TreeValue) :
    Option (ExpressionTree × List TreeValue) :=
  match clauses with
  | [] => none
  | (pattern, body) :: rest => match matchTreePattern pattern value with
      | some bindings => some (body, bindings)
      | none => selectTreeClause rest value

theorem selectTreeClause_first (pattern : MatchPattern) (body : ExpressionTree)
    (rest : List (MatchPattern × ExpressionTree)) (value : TreeValue) (bindings : List TreeValue)
    (matched : matchTreePattern pattern value = some bindings) :
    selectTreeClause ((pattern, body) :: rest) value = some (body, bindings) := by
  simp [selectTreeClause, matched]

theorem selectTreeClause_skip (pattern : MatchPattern) (body : ExpressionTree)
    (rest : List (MatchPattern × ExpressionTree)) (value : TreeValue)
    (failed : matchTreePattern pattern value = none) :
    selectTreeClause ((pattern, body) :: rest) value = selectTreeClause rest value := by
  simp [selectTreeClause, failed]

#print axioms selectTreeClause_first
#print axioms selectTreeClause_skip

end Mettapedia.Languages.OCaml
