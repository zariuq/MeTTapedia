import Mettapedia.Languages.Erlang.Syntax

/-! Core patterns bind a vector in source order. Pinned slots refer to the
outer environment and are not rebound. Guards are evaluated separately by
the sequential machine; a successful pattern does not choose a clause until
its guard returns the atom true. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

mutual
  def matchPattern (environment : Environment) : MatchPattern → Value → Option (List Value)
    | .bind, value => some [value]
    | .wildcard, _ => some []
    | .literal expected, .literal actual => if expected = actual then some [] else none
    | .pinned index, value => do
        let existing ← environment[index]?
        if existing == value then some [] else none
    | .alias pattern, value => (matchPattern environment pattern value).map (value :: ·)
    | .tuple patterns, .tuple values => matchFields environment patterns values
    | .cons head tail, .cons first rest => do
        pure ((← matchPattern environment head first) ++ (← matchPattern environment tail rest))
    | _, _ => none

  def matchFields (environment : Environment) : List MatchPattern → List Value → Option (List Value)
    | [], [] => some []
    | pattern :: rest, value :: tail => do
        pure ((← matchPattern environment pattern value) ++ (← matchFields environment rest tail))
    | _, _ => none
end

theorem match_pinned_success {environment : Environment} {index : Nat} {existing value : Value}
    (found : environment[index]? = some existing) (same : (existing == value) = true) :
    matchPattern environment (.pinned index) value = some [] := by
  simp [matchPattern, found, same]

theorem match_pinned_failure {environment : Environment} {index : Nat} {existing value : Value}
    (found : environment[index]? = some existing) (different : (existing == value) = false) :
    matchPattern environment (.pinned index) value = none := by
  simp [matchPattern, found, different]

theorem match_alias {environment : Environment} {pattern : MatchPattern} {value : Value} {bindings : List Value}
    (matched : matchPattern environment pattern value = some bindings) :
    matchPattern environment (.alias pattern) value = some (value :: bindings) := by
  simp [matchPattern, matched]

end Mettapedia.Languages.Erlang
