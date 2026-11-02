import Mettapedia.Languages.Erlang.PatternMatching

/-! Successful Core patterns supply exactly their declared number of fresh
slots. Pinned outer slots supply none; aliases supply the whole value before
the inner pattern's bindings. This source property does not assume the
shared GSLT matcher or frontend lowering. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

theorem matchPattern_binding_count (environment : Environment) (pattern : MatchPattern) :
    ∀ (value : Value) (bindings : List Value),
      matchPattern environment pattern value = some bindings → bindings.length = pattern.binders := by
  refine MatchPattern.rec
    (motive_1 := fun pattern => ∀ (value : Value) (bindings : List Value),
      matchPattern environment pattern value = some bindings → bindings.length = pattern.binders)
    (motive_2 := fun patterns => ∀ (values : List Value) (bindings : List Value),
      matchFields environment patterns values = some bindings →
        bindings.length = (patterns.map MatchPattern.binders).sum)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
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
  · intro index value bindings matched
    cases found : environment[index]? with
    | none => simp [matchPattern, found] at matched
    | some existing =>
        by_cases same : (existing == value) = true
        · simp [matchPattern, found, same] at matched
          cases matched
          simp [MatchPattern.binders]
        · simp [matchPattern, found, same] at matched
  · intro pattern ih value bindings matched
    cases found : matchPattern environment pattern value with
    | none => simp [matchPattern, found] at matched
    | some inner =>
        have same : value :: inner = bindings := by simpa [matchPattern, found] using matched
        rw [← same]
        simpa [MatchPattern.binders, Nat.add_comm] using congrArg Nat.succ (ih value inner found)
  · intro fields ih value bindings matched
    cases value
    case tuple actual => simpa only [MatchPattern.binders] using ih actual bindings matched
    all_goals simp [matchPattern] at matched
  · intro head tail firstIH restIH value bindings matched
    cases value
    case cons first rest =>
      simp only [matchPattern] at matched
      cases firstMatch : matchPattern environment head first with
      | none => simp [firstMatch] at matched
      | some firstBindings =>
          cases restMatch : matchPattern environment tail rest with
          | none => simp [firstMatch, restMatch] at matched
          | some restBindings =>
              have same : firstBindings ++ restBindings = bindings := by
                simpa [firstMatch, restMatch] using matched
              rw [← same, List.length_append, firstIH first _ firstMatch, restIH rest _ restMatch]
              simp [MatchPattern.binders]
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
        cases firstMatch : matchPattern environment pattern first with
        | none => simp [firstMatch] at matched
        | some firstBindings =>
            cases restMatch : matchFields environment rest tail with
            | none => simp [firstMatch, restMatch] at matched
            | some restBindings =>
                have same : firstBindings ++ restBindings = bindings := by
                  simpa [firstMatch, restMatch] using matched
                rw [← same, List.length_append, firstIH first _ firstMatch, restIH tail _ restMatch]
                rfl

theorem matchFields_binding_count (environment : Environment) (patterns : List MatchPattern)
    (values bindings : List Value) (matched : matchFields environment patterns values = some bindings) :
    bindings.length = (patterns.map MatchPattern.binders).sum := by
  simpa only [MatchPattern.binders] using
    matchPattern_binding_count environment (.tuple patterns) (.tuple values) bindings matched

theorem match_pinned_iff (environment : Environment) (index : Nat) (value : Value) :
    matchPattern environment (.pinned index) value = some [] ↔ environment[index]? = some value := by
  cases found : environment[index]? with
  | none => simp [matchPattern, found]
  | some existing =>
      have exact : (existing == value) = true ↔ existing = value := Value.sameTerm_eq_true_iff existing value
      simp [matchPattern, found, exact]

end Mettapedia.Languages.Erlang
