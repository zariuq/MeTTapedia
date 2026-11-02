import Mettapedia.Languages.OCaml.NamedPattern

/-! Anonymous matcher answers reconstruct named source bindings. Together
with soundness this preserves both failure and every successful binding
sequence, including nested tuples, lists and constructor patterns. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.NamedPattern

theorem erased_match_complete (pattern : NamedPattern) :
    ∀ (value : Value) (values : List Value), matchPattern pattern.erase value = some values →
      ∃ bindings, Matches pattern value bindings ∧ bindings.map Prod.snd = values := by
  refine NamedPattern.rec
    (motive_1 := fun pattern => ∀ value values, matchPattern pattern.erase value = some values →
      ∃ bindings, Matches pattern value bindings ∧ bindings.map Prod.snd = values)
    (motive_2 := fun patterns => ∀ actual values, matchFields (patterns.map erase) actual = some values →
      ∃ bindings, FieldsMatch patterns actual bindings ∧ bindings.map Prod.snd = values)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
  · intro name value values matched
    have same : [value] = values := by simpa [erase, matchPattern] using matched
    exact ⟨[(name, value)], .variable name value, same⟩
  · intro value values matched
    have same : [] = values := by simpa [erase, matchPattern] using matched
    exact ⟨[], .wildcard value, same⟩
  · intro expected value values matched
    cases value
    case literal actual =>
      by_cases same : expected = actual
      · subst actual
        have empty : [] = values := by simpa [erase, matchPattern] using matched
        exact ⟨[], .literal expected, empty⟩
      · simp [erase, matchPattern, same] at matched
    all_goals simp [erase, matchPattern] at matched
  · intro patterns ih value values matched
    cases value
    case tuple actual =>
      obtain ⟨bindings, named, same⟩ := ih actual values (by simpa [erase, matchPattern] using matched)
      exact ⟨bindings, .tuple named, same⟩
    all_goals simp [erase, matchPattern] at matched
  · intro head tail firstIH restIH value values matched
    cases value
    case cons first rest =>
      cases firstMatch : matchPattern head.erase first with
      | none => simp [erase, matchPattern, firstMatch] at matched
      | some firstValues =>
        cases restMatch : matchPattern tail.erase rest with
        | none => simp [erase, matchPattern, firstMatch, restMatch] at matched
        | some restValues =>
          have combined : firstValues ++ restValues = values := by
            simpa [erase, matchPattern, firstMatch, restMatch] using matched
          obtain ⟨firstBindings, firstNamed, firstSame⟩ := firstIH first firstValues firstMatch
          obtain ⟨restBindings, restNamed, restSame⟩ := restIH rest restValues restMatch
          exact ⟨firstBindings ++ restBindings, .cons firstNamed restNamed, by
            rw [List.map_append, firstSame, restSame, combined]⟩
    all_goals simp [erase, matchPattern] at matched
  · intro typeId constructor patterns ih value values matched
    cases value
    case variant actualType actualConstructor actual =>
      by_cases same : typeId = actualType ∧ constructor = actualConstructor
      · obtain ⟨rfl, rfl⟩ := same
        obtain ⟨bindings, named, same⟩ := ih actual values (by simpa [erase, matchPattern] using matched)
        exact ⟨bindings, .variant named, same⟩
      · simp [erase, matchPattern, same] at matched
    all_goals simp [erase, matchPattern] at matched
  · intro actual values matched
    cases actual <;> simp [matchFields] at matched
    subst values
    exact ⟨[], .nil, rfl⟩
  · intro pattern patterns firstIH restIH actual values matched
    cases actual with
    | nil => simp [matchFields] at matched
    | cons first rest =>
      cases firstMatch : matchPattern pattern.erase first with
      | none => simp [matchFields, firstMatch] at matched
      | some firstValues =>
        cases restMatch : matchFields (patterns.map erase) rest with
        | none => simp [matchFields, firstMatch, restMatch] at matched
        | some restValues =>
          have combined : firstValues ++ restValues = values := by
            simpa [matchFields, firstMatch, restMatch] using matched
          obtain ⟨firstBindings, firstNamed, firstSame⟩ := firstIH first firstValues firstMatch
          obtain ⟨restBindings, restNamed, restSame⟩ := restIH rest restValues restMatch
          exact ⟨firstBindings ++ restBindings, .cons firstNamed restNamed, by
            rw [List.map_append, firstSame, restSame, combined]⟩

theorem erased_match_iff (pattern : NamedPattern) (value : Value) (values : List Value) :
    matchPattern pattern.erase value = some values ↔
      ∃ bindings, Matches pattern value bindings ∧ bindings.map Prod.snd = values :=
  ⟨erased_match_complete pattern value values,
    fun ⟨_bindings, matched, same⟩ => same ▸ matches_erased matched⟩

theorem erased_match_failure_iff (pattern : NamedPattern) (value : Value) :
    matchPattern pattern.erase value = none ↔ ¬ ∃ bindings, Matches pattern value bindings := by
  constructor
  · intro failed ⟨bindings, matched⟩
    rw [matches_erased matched] at failed
    cases failed
  · intro failed
    cases matched : matchPattern pattern.erase value with
    | none => rfl
    | some values =>
      obtain ⟨bindings, named, _⟩ := erased_match_complete pattern value values matched
      exact (failed ⟨bindings, named⟩).elim

#print axioms erased_match_complete
#print axioms erased_match_iff
#print axioms erased_match_failure_iff

end Mettapedia.Languages.OCaml.NamedPattern
