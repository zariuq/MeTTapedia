import Mettapedia.Computability.RegularLanguages.Library

/-!
# Regex controls grounded in Unicode text and JSON numbers

The number expression uses JSON's decimal syntax: no leading zero except the
integer zero itself; a decimal point and exponent each require following
digits. Whitespace and the three JSON keywords provide a small lexer client.
This is a numeric/keyword lexical fragment, not a JSON parser or string decoder.

Its controls deliberately distinguish full-word validity from successful
tokenization of several adjacent words. In particular, splitting `01` into
two number tokens does not certify it as one valid JSON number.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.Examples

def digit : Regex Char := oneOf ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']
def nonzeroDigit : Regex Char := oneOf ['1', '2', '3', '4', '5', '6', '7', '8', '9']
def integerPart : Regex Char := literal '0' + nonzeroDigit * digit.star
def fractionPart : Regex Char := literal '.' * positiveRepeat digit
def exponentPart : Regex Char :=
  oneOf ['e', 'E'] * optional (oneOf ['+', '-']) * positiveRepeat digit

/-- The standard JSON number form, independently elaborated from its decimal
components. Signs on exponents are separate from the leading minus sign. -/
def jsonNumber : Regex Char :=
  optional (literal '-') * integerPart * optional fractionPart * optional exponentPart

def jsonWhitespace : Regex Char := positiveRepeat (oneOf [' ', '\t', '\r', '\n'])

/-- Rule order is retained as a numeric token position. Whitespace is emitted
like any other token, so reconstruction preserves the complete original text. -/
def jsonLexicalRules : List (Regex Char) :=
  [jsonNumber, jsonWhitespace, word "true".toList, word "false".toList, word "null".toList]

theorem number_accepts_exponent : matchNormalized jsonNumber "1e3".toList = true := by decide

theorem number_accepts_decimal_signs :
    matchNormalized jsonNumber "-1.2e+3".toList = true := by decide

theorem number_accepts_negative_zero : matchNormalized jsonNumber "-0".toList = true := by decide

theorem number_rejects_leading_zero : matchNormalized jsonNumber "01".toList = false := by decide

theorem number_rejects_missing_exponent_digits :
    matchNormalized jsonNumber "1e".toList = false := by decide

theorem number_rejects_missing_fraction_digits :
    matchNormalized jsonNumber "1.".toList = false := by decide

theorem number_rejects_leading_plus : matchNormalized jsonNumber "+1".toList = false := by decide

private theorem leading_zero_first_step :
    lexOne ([jsonNumber].map regexLexerRule) "01".toList = some ⟨0, 1⟩ := by decide

private theorem leading_zero_second_step :
    lexOne ([jsonNumber].map regexLexerRule) "1".toList = some ⟨0, 1⟩ := by decide

private theorem leading_zero_second_token :
    tokenizeFrom ([jsonNumber].map regexLexerRule) 1 "1".toList =
      ⟨[⟨0, "1".toList⟩], [], none⟩ := by
  rw [tokenizeFrom_next leading_zero_second_step]
  change (⟨⟨0, "1".toList⟩ :: (tokenizeFrom _ 2 []).tokens,
    (tokenizeFrom _ 2 []).remaining, (tokenizeFrom _ 2 []).refusedAt⟩ : TokenizationResult Char) = _
  rw [tokenizeFrom_nil]

/-- The lexer splits `01` into the two number tokens `0` and `1`. -/
theorem leading_zero_tokens :
    regexTokenize [jsonNumber] "01".toList =
      ⟨[⟨0, "0".toList⟩, ⟨0, "1".toList⟩], [], none⟩ := by
  change tokenizeFrom ([jsonNumber].map regexLexerRule) 0 "01".toList = _
  rw [tokenizeFrom_next leading_zero_first_step]
  change (⟨⟨0, "0".toList⟩ :: (tokenizeFrom _ 1 "1".toList).tokens,
    (tokenizeFrom _ 1 "1".toList).remaining,
    (tokenizeFrom _ 1 "1".toList).refusedAt⟩ : TokenizationResult Char) = _
  rw [leading_zero_second_token]

/-- Lexer completion alone is weaker than full-word number validity. -/
theorem tokenization_is_not_number_validation :
    (regexTokenize [jsonNumber] "01".toList).refusedAt = none ∧
      (regexTokenize [jsonNumber] "01".toList).tokens.length = 2 ∧
      matchNormalized jsonNumber "01".toList = false := by
  rw [leading_zero_tokens]
  exact ⟨rfl, rfl, number_rejects_leading_zero⟩

private theorem fragment_number_step :
    lexOne (jsonLexicalRules.map regexLexerRule) "1e3 true".toList = some ⟨0, 3⟩ := by decide

private theorem fragment_space_step :
    lexOne (jsonLexicalRules.map regexLexerRule) " true".toList = some ⟨1, 1⟩ := by decide

private theorem fragment_keyword_step :
    lexOne (jsonLexicalRules.map regexLexerRule) "true".toList = some ⟨2, 4⟩ := by decide

private theorem fragment_keyword_tokens :
    tokenizeFrom (jsonLexicalRules.map regexLexerRule) 4 "true".toList =
      ⟨[⟨2, "true".toList⟩], [], none⟩ := by
  rw [tokenizeFrom_next fragment_keyword_step]
  change (⟨⟨2, "true".toList⟩ :: (tokenizeFrom _ 8 []).tokens,
    (tokenizeFrom _ 8 []).remaining, (tokenizeFrom _ 8 []).refusedAt⟩ : TokenizationResult Char) = _
  rw [tokenizeFrom_nil]

private theorem fragment_space_tokens :
    tokenizeFrom (jsonLexicalRules.map regexLexerRule) 3 " true".toList =
      ⟨[⟨1, [' ']⟩, ⟨2, "true".toList⟩], [], none⟩ := by
  rw [tokenizeFrom_next fragment_space_step]
  change (⟨⟨1, [' ']⟩ :: (tokenizeFrom _ 4 "true".toList).tokens,
    (tokenizeFrom _ 4 "true".toList).remaining,
    (tokenizeFrom _ 4 "true".toList).refusedAt⟩ : TokenizationResult Char) = _
  rw [fragment_keyword_tokens]

theorem json_fragment_tokens :
    regexTokenize jsonLexicalRules "1e3 true".toList =
      ⟨[⟨0, "1e3".toList⟩, ⟨1, [' ']⟩, ⟨2, "true".toList⟩], [], none⟩ := by
  change tokenizeFrom (jsonLexicalRules.map regexLexerRule) 0 "1e3 true".toList = _
  rw [tokenizeFrom_next fragment_number_step]
  change (⟨⟨0, "1e3".toList⟩ :: (tokenizeFrom _ 3 " true".toList).tokens,
    (tokenizeFrom _ 3 " true".toList).remaining,
    (tokenizeFrom _ 3 " true".toList).refusedAt⟩ : TokenizationResult Char) = _
  rw [fragment_space_tokens]

theorem json_fragment_reconstructs :
    (regexTokenize jsonLexicalRules "1e3 true".toList).tokens.flatMap LexerToken.text =
      "1e3 true".toList := by
  rw [json_fragment_tokens]
  rfl

theorem unknown_character_refuses :
    (regexTokenize jsonLexicalRules "1?".toList).refusedAt = some 1 := by
  have first : lexOne (jsonLexicalRules.map regexLexerRule) "1?".toList = some ⟨0, 1⟩ := by
    decide
  have refused : tokenizeFrom (jsonLexicalRules.map regexLexerRule) 1 "?".toList =
      ⟨[], "?".toList, some 1⟩ := tokenizeFrom_refused (by decide) (by decide)
  change (tokenizeFrom (jsonLexicalRules.map regexLexerRule) 0 "1?".toList).refusedAt = _
  rw [tokenizeFrom_next first]
  change (tokenizeFrom _ 1 "?".toList).refusedAt = _
  rw [refused]

/-- Leftmost-longest chooses both scalars, rather than the first authored
alternative or an encoded-byte count. -/
theorem unicode_search_is_longest :
    regexSearch (word "λ".toList + word "λβ".toList) "xλβ!".toList = some ⟨1, 2⟩ := by decide

theorem wildcard_unicode_is_one_scalar : matchNormalized any "λ".toList = true := by decide

theorem wildcard_two_scalars_rejected : matchNormalized any "λβ".toList = false := by decide

theorem word_rejects_wrong_order : matchNormalized (word "λβ".toList) "βλ".toList = false := by decide

theorem empty_match_replacement :
    regexReplaceAll (1 : Regex Char) (.literal "x".toList) "λβ".toList =
      ⟨"xλxβx".toList, [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩]⟩ := by cbv

theorem replacement_uses_longest_match :
    regexReplaceAll (word "a".toList + word "aa".toList) (.literal "x".toList)
      "aabaa".toList = ⟨"xbx".toList, [⟨0, 2⟩, ⟨3, 2⟩]⟩ := by
  have first : regexSearch (word ['a'] + word ['a', 'a']) ['a', 'a', 'b', 'a', 'a'] =
      some ⟨0, 2⟩ := by decide
  have second : regexSearch (word ['a'] + word ['a', 'a']) ['b', 'a', 'a'] =
      some ⟨1, 2⟩ := by decide
  have last : regexSearch (word ['a'] + word ['a', 'a']) [] = none := by decide
  change regexReplaceAll (word ['a'] + word ['a', 'a']) (.literal ['x'])
    ['a', 'a', 'b', 'a', 'a'] = ⟨['x', 'b', 'x'], [⟨0, 2⟩, ⟨3, 2⟩]⟩
  simp [regexReplaceAll_step _ first (by decide), regexReplaceAll_step _ second (by decide),
    regexReplaceAll_of_search_none _ last, MatchSpan.nextCursor, MatchSpan.emptyGap,
    MatchSpan.shiftBy, ReplacementTemplate.render]

theorem replacement_text_not_rescanned :
    regexReplaceAll (word "a".toList + word "aa".toList) (.literal "aa".toList)
      "a".toList = ⟨"aa".toList, [⟨0, 1⟩]⟩ := by cbv


private def greedySegmentationRules : List (LexerRule Char) :=
  [LexerRule.literal "ab".toList, LexerRule.literal "a".toList,
    LexerRule.literal "bc".toList]

/-- Maximal munch can refuse despite a different complete decomposition into
valid token words. This is a lexical policy, not global segmentation search. -/
theorem maximal_munch_is_not_global_segmentation :
    tokenize greedySegmentationRules "abc".toList =
      ⟨[⟨0, "ab".toList⟩], ['c'], some 2⟩ ∧
    (∀ token ∈ ([⟨1, "a".toList⟩, ⟨2, "bc".toList⟩] : List (LexerToken Char)),
      token.Valid greedySegmentationRules) ∧
    ([⟨1, "a".toList⟩, ⟨2, "bc".toList⟩] : List (LexerToken Char)).flatMap
      LexerToken.text = "abc".toList := by
  refine ⟨by cbv, ?_, by rfl⟩
  intro token member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨by decide, LexerRule.literal "a".toList, rfl, rfl⟩
  · have same : token = ⟨2, "bc".toList⟩ := List.mem_singleton.mp member
    subst token
    exact ⟨by decide, LexerRule.literal "bc".toList, rfl, rfl⟩

end Mettapedia.Computability.RegularLanguages.Examples
