import Mettapedia.Computability.RegularLanguages.Repetition
import Mettapedia.Computability.RegularLanguages.Literals
import Mettapedia.Computability.RegularLanguages.Normalization
import Mettapedia.Computability.RegularLanguages.LexerSemantics
import Mettapedia.Computability.RegularLanguages.Replacement

/-!
# Executable consumers of the proved regex language

Matching, search, replacement of the first match or of all matches, and
tokenization share one set-of-words semantics. Search chooses leftmost-longest
matches; tokenization additionally requires positive lengths and uses the
declared order of rules for ties. Positions count alphabet elements, hence
Unicode scalars for `Char`, not bytes.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u} [DecidableEq α]

/-- A regex rule uses the simplifying derivative matcher, justified by the
independent language interpretation. -/
def regexLexerRule (p : Regex α) : LexerRule α where
  language := language p
  accepts := matchNormalized p
  accepts_correct := matchNormalized_correct p

/-- Choose the simplifying matcher as the membership procedure, without
changing the independently specified language. -/
@[instance_reducible]
def normalizedLanguageDecider (p : Regex α) : DecidablePred (· ∈ language p) :=
  fun input => decidable_of_iff (matchNormalized p input = true) (matchNormalized_correct p input)

/-- Search is an application of the common language algorithm, not a second
regex-specific implementation. -/
def regexSearch (p : Regex α) (input : List α) : Option MatchSpan :=
  letI := normalizedLanguageDecider p
  search (language p) input

theorem regexSearch_some_iff (p : Regex α) (input : List α) (span : MatchSpan) :
    regexSearch p input = some span ↔ LeftmostLongest (language p) input span :=
  letI := normalizedLanguageDecider p
  search_some_iff (language p) input span

theorem regexSearch_none_iff (p : Regex α) (input : List α) :
    regexSearch p input = none ↔ ∀ span, ¬ SpanMatch (language p) input span :=
  letI := normalizedLanguageDecider p
  search_none_iff (language p) input

/-- Expressions with the same language find the same span. -/
theorem regexSearch_congr {p q : Regex α} (same : language p = language q) (input : List α) :
    regexSearch p input = regexSearch q input := by
  cases result : regexSearch q input with
  | none =>
      apply (regexSearch_none_iff p input).mpr
      rw [same]
      exact (regexSearch_none_iff q input).mp result
  | some span =>
      apply (regexSearch_some_iff p input span).mpr
      rw [same]
      exact (regexSearch_some_iff q input span).mp result

/-- Replace the leftmost-longest match once; a miss returns the input. -/
def regexReplaceFirst (p : Regex α) (template : ReplacementTemplate α) (input : List α) :
    ReplacementResult α :=
  letI := normalizedLanguageDecider p
  replaceFirst (language p) template input

theorem regexReplaceFirst_eq (p : Regex α) (template : ReplacementTemplate α) (input : List α) :
    regexReplaceFirst p template input =
      match regexSearch p input with
      | none => ⟨input, []⟩
      | some span => ⟨input.take span.start ++ template.render (span.text input) ++
          input.drop (span.start + span.length), [span]⟩ :=
  rfl

/-- The first replacement in terms of the language alone: the input unchanged
when no span matches, and otherwise the leftmost-longest span replaced. -/
theorem regexReplaceFirst_spec (p : Regex α) (template : ReplacementTemplate α)
    (input : List α) :
    ((∀ span, ¬ SpanMatch (language p) input span) ∧
        regexReplaceFirst p template input = ⟨input, []⟩) ∨
      ∃ span, LeftmostLongest (language p) input span ∧
        regexReplaceFirst p template input = ⟨input.take span.start ++
          template.render (span.text input) ++ input.drop (span.start + span.length), [span]⟩ :=
  letI := normalizedLanguageDecider p
  replaceFirst_spec (language p) template input

theorem regexReplaceFirst_congr {p q : Regex α} (same : language p = language q)
    (template : ReplacementTemplate α) (input : List α) :
    regexReplaceFirst p template input = regexReplaceFirst q template input := by
  rw [regexReplaceFirst_eq, regexReplaceFirst_eq, regexSearch_congr same]

def regexReplaceAll (p : Regex α) (template : ReplacementTemplate α) (input : List α) :
    ReplacementResult α :=
  letI := normalizedLanguageDecider p
  replaceAll (language p) template input

/-- Replacement of all matches when nothing matches. -/
theorem regexReplaceAll_of_search_none {p : Regex α} (template : ReplacementTemplate α)
    {input : List α} (absent : regexSearch p input = none) :
    regexReplaceAll p template input = ⟨input, []⟩ :=
  letI := normalizedLanguageDecider p
  replaceAll_of_search_none (language p) template input absent

/-- Replacement of all matches at an empty match at the end of the input. -/
theorem regexReplaceAll_of_finalEmpty {p : Regex α} (template : ReplacementTemplate α)
    {input : List α} {span : MatchSpan} (found : regexSearch p input = some span)
    (final : span.FinalEmpty input) :
    regexReplaceAll p template input =
      ⟨input.take span.start ++ template.render (span.text input), [span]⟩ :=
  letI := normalizedLanguageDecider p
  replaceAll_of_finalEmpty (language p) template input span found final

/-- Replacement of all matches at any other match: replace it and continue
after it in the original input. -/
theorem regexReplaceAll_step {p : Regex α} (template : ReplacementTemplate α)
    {input : List α} {span : MatchSpan} (found : regexSearch p input = some span)
    (nonfinal : ¬ span.FinalEmpty input) :
    regexReplaceAll p template input =
      ⟨input.take span.start ++ template.render (span.text input) ++ span.emptyGap input ++
        (regexReplaceAll p template (input.drop span.nextCursor)).output,
        span :: (regexReplaceAll p template (input.drop span.nextCursor)).spans.map
          (MatchSpan.shiftBy span.nextCursor)⟩ :=
  letI := normalizedLanguageDecider p
  replaceAll_step (language p) template input span found nonfinal

theorem regexReplaceAll_eq_iff (p : Regex α) (template : ReplacementTemplate α)
    (input output : List α) (spans : List MatchSpan) :
    regexReplaceAll p template input = ⟨output, spans⟩ ↔
      ReplacementDerivation (language p) template input output spans :=
  letI := normalizedLanguageDecider p
  replaceAll_eq_iff (language p) template input output spans

/-- Semantic equality preserves the complete replacement observation,
including all original-input spans, not just the output text. -/
theorem regexReplaceAll_congr {p q : Regex α} (same : language p = language q)
    (template : ReplacementTemplate α) (input : List α) :
    regexReplaceAll p template input = regexReplaceAll q template input := by
  cases result : regexReplaceAll q template input with
  | mk output spans =>
      apply (regexReplaceAll_eq_iff p template input output spans).mpr
      rw [same]
      exact (regexReplaceAll_eq_iff q template input output spans).mp result

def regexTokenize (rules : List (Regex α)) (input : List α) : TokenizationResult α :=
  tokenize (rules.map regexLexerRule) input

/-- Tokenization agrees with the independent whole-input semantics, including
maximal length, authored priority, EOF, and exact refusal location. -/
theorem regexTokenize_eq_iff (rules : List (Regex α)) (input : List α)
    (result : TokenizationResult α) :
    regexTokenize rules input = result ↔
      TokenizationDerivation (rules.map regexLexerRule) 0 input result :=
  tokenize_eq_iff (rules.map regexLexerRule) input result

theorem regexTokenize_reconstruct (rules : List (Regex α)) (input : List α) :
    (regexTokenize rules input).tokens.flatMap LexerToken.text ++
      (regexTokenize rules input).remaining = input :=
  tokenize_reconstruct (rules.map regexLexerRule) input

theorem regexTokenize_tokens_valid (rules : List (Regex α)) (input : List α) :
    ∀ token ∈ (regexTokenize rules input).tokens,
      token.Valid (rules.map regexLexerRule) :=
  tokenize_tokens_valid (rules.map regexLexerRule) input

/-- Every token is a nonempty word of the language of the expression at its
rule position. -/
theorem regexTokenize_token_mem (rules : List (Regex α)) (input : List α) :
    ∀ token ∈ (regexTokenize rules input).tokens,
      token.text ≠ [] ∧ ∃ p, rules[token.ruleIndex]? = some p ∧ token.text ∈ language p := by
  intro token member
  obtain ⟨positive, rule, atIndex, accepted⟩ :=
    regexTokenize_tokens_valid rules input token member
  rw [List.getElem?_map] at atIndex
  obtain ⟨p, found, rfl⟩ := Option.map_eq_some_iff.mp atIndex
  exact ⟨List.ne_nil_of_length_pos positive, p, found, accepted⟩

theorem regexTokenize_refusal (rules : List (Regex α)) (input : List α) (position : Nat)
    (failed : (regexTokenize rules input).refusedAt = some position) :
    position = ((regexTokenize rules input).tokens.flatMap LexerToken.text).length ∧
      (regexTokenize rules input).remaining ≠ [] ∧
      lexOne (rules.map regexLexerRule) (regexTokenize rules input).remaining = none :=
  tokenize_refusal (rules.map regexLexerRule) input position failed

end Mettapedia.Computability.RegularLanguages
