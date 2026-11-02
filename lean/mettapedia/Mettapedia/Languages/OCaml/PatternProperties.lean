import Mettapedia.Languages.OCaml.PatternMatching

/-! Successful pattern matching supplies exactly the declared binder count.
This is a property of the source operation, independent of GSLT matching and
of the environment machine. Clause priority includes the separating case
where several clauses match but return different values. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

theorem matchPattern_binding_count (pattern : MatchPattern) :
    ∀ (value : Value) (bindings : List Value),
      matchPattern pattern value = some bindings → bindings.length = pattern.binders := by
  refine MatchPattern.rec
    (motive_1 := fun pattern => ∀ (value : Value) (bindings : List Value),
      matchPattern pattern value = some bindings → bindings.length = pattern.binders)
    (motive_2 := fun patterns => ∀ (values : List Value) (bindings : List Value),
      matchFields patterns values = some bindings →
        bindings.length = (patterns.map MatchPattern.binders).sum)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
  · intro value bindings matched
    have same : [value] = bindings := Option.some.inj matched
    rw [← same]
    simp [MatchPattern.binders]
  · intro value bindings matched
    have same : [] = bindings := Option.some.inj matched
    rw [← same]
    simp [MatchPattern.binders]
  · intro expected value bindings matched
    cases value
    case literal actual =>
      by_cases same : expected = actual
      · simp [matchPattern, same] at matched
        cases matched
        simp [MatchPattern.binders]
      · simp [matchPattern, same] at matched
    all_goals simp [matchPattern] at matched
  · intro fields ih value bindings matched
    cases value
    case tuple actual =>
      simpa only [MatchPattern.binders] using ih actual bindings matched
    all_goals simp [matchPattern] at matched
  · intro head tail firstIH restIH value bindings matched
    cases value
    case cons first rest =>
      simp only [matchPattern] at matched
      cases firstMatch : matchPattern head first with
      | none => simp [firstMatch] at matched
      | some firstBindings =>
          cases restMatch : matchPattern tail rest with
          | none => simp [firstMatch, restMatch] at matched
          | some restBindings =>
              have same : firstBindings ++ restBindings = bindings := by
                simpa [firstMatch, restMatch] using matched
              rw [← same, List.length_append, firstIH first _ firstMatch, restIH rest _ restMatch]
              simp [MatchPattern.binders]
    all_goals simp [matchPattern] at matched
  · intro typeId constructor fields ih value bindings matched
    cases value
    case variant actualType actualConstructor actual =>
      by_cases same : typeId = actualType ∧ constructor = actualConstructor
      · simpa only [MatchPattern.binders] using ih actual bindings
          (by simpa [matchPattern, same] using matched)
      · simp [matchPattern, same] at matched
    all_goals simp [matchPattern] at matched
  · intro values bindings matched
    cases values <;> simp [matchFields] at matched
    cases matched
    rfl
  · intro pattern rest firstIH restIH values bindings matched
    cases values with
    | nil => simp [matchFields] at matched
    | cons first tail =>
        simp only [matchFields] at matched
        cases firstMatch : matchPattern pattern first with
        | none => simp [firstMatch] at matched
        | some firstBindings =>
            cases restMatch : matchFields rest tail with
            | none => simp [firstMatch, restMatch] at matched
            | some restBindings =>
                have same : firstBindings ++ restBindings = bindings := by
                  simpa [firstMatch, restMatch] using matched
                rw [← same, List.length_append, firstIH first _ firstMatch, restIH tail _ restMatch]
                rfl

theorem matchFields_binding_count (patterns : List MatchPattern) (values : List Value)
    (bindings : List Value) (matched : matchFields patterns values = some bindings) :
    bindings.length = (patterns.map MatchPattern.binders).sum := by
  simpa only [MatchPattern.binders] using
    matchPattern_binding_count (.tuple patterns) (.tuple values) bindings matched

theorem selectClause_of_first (before : List Clause) (clause : Clause) (after : List Clause)
    (value : Value) (bindings : List Value)
    (failed : ∀ earlier ∈ before, matchPattern earlier.pattern value = none)
    (matched : matchPattern clause.pattern value = some bindings) :
    selectClause (before ++ clause :: after) value = some (clause.body, bindings) := by
  induction before with
  | nil => simpa using selectClause_first clause after value bindings matched
  | cons head tail ih =>
      simp only [List.cons_append, selectClause, failed head (by simp)]
      apply ih
      intro earlier member
      exact failed earlier (by simp [member])

end Mettapedia.Languages.OCaml
