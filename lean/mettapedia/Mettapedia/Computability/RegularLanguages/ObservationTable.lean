import Mettapedia.Computability.RegularLanguages.Library
import Mettapedia.Computability.RegularLanguages.Utf8Spans

/-!
# The observation table of the capture-free profile

Dylon Edwards' regex GSLT contract in F1R3FLY-io/mettail-rust, revision
`99885f467e42d52ef60ca0bb6076eb0fa25bfa0e`, lists the observations every
implementation of the profile must produce. Each row is proved here for the
functions of this library: whole-word matching, nullability, the derivative,
leftmost-longest search with its span reported in bytes, and replacement of
the first match or of all matches.

One row needs care. The derivative of `a+` by `a` is listed as `a*`. The
derivative simplified by the equations of the profile is `a*`; the
unsimplified derivative is the concatenation of the empty word with `a*`,
which has the same language and is a different expression.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.ObservationTable

/-- The pattern `a(b|c)+`. -/
def aThenBsOrCs : Regex Char :=
  literal 'a' * positiveRepeat (group (literal 'b' + literal 'c'))

/-- The pattern `a+`. -/
def someAs : Regex Char := positiveRepeat (literal 'a')

/-- The pattern `λ+`. -/
def someLambdas : Regex Char := positiveRepeat (literal 'λ')

/-- The pattern `a|aa`. -/
def oneOrTwoAs : Regex Char := literal 'a' + literal 'a' * literal 'a'

/-- The template `x`. -/
def letterX : ReplacementTemplate Char := .literal "x".toList

/-- The template that puts the match in brackets. -/
def bracketed : ReplacementTemplate Char :=
  .append (.literal "[".toList) (.append .whole (.literal "]".toList))

/-- Leftmost-longest search with its span reported in bytes. -/
def searchBytes (p : Regex Char) (input : String) : Option ByteMatch :=
  (regexSearch p input.toList).map fun span => span.byteMatch input.toList

/-! ## Whole-word matching and nullability -/

/-- Row M1. -/
theorem accepts_abcb : fullMatch aThenBsOrCs "abcb".toList = true := by decide

/-- Row M2. -/
theorem rejects_ax : fullMatch aThenBsOrCs "ax".toList = false := by decide

/-- Row M3: a whole-word match is not a search. The pattern occurs inside the
word, and the word is rejected. -/
theorem rejects_xab_although_found :
    fullMatch aThenBsOrCs "xab".toList = false ∧
      regexSearch aThenBsOrCs "xab".toList = some ⟨1, 2⟩ := by decide

/-- Row M4: `a?` accepts the empty word, and the wildcard accepts a newline. -/
theorem optional_nullable_and_wildcard_newline :
    (optional (literal 'a')).matchEpsilon = true ∧
      fullMatch (any : Regex Char) "\n".toList = true := by decide

/-- Row M5: `a{2,3}` on one, three and four letters. -/
theorem range_two_to_three :
    fullMatch (boundedRepeat (literal 'a') 2 3) "a".toList = false ∧
      fullMatch (boundedRepeat (literal 'a') 2 3) "aaa".toList = true ∧
      fullMatch (boundedRepeat (literal 'a') 2 3) "aaaa".toList = false := by decide

/-- Row M6: `a{3,2}` is the expression of the empty language. -/
theorem reversed_range_fails : boundedRepeat (literal 'a') 3 2 = 0 := rfl

/-! ## The derivative -/

/-- Row D1: the simplified derivative of `a+` by `a` is `a*`. -/
theorem derivative_of_someAs : normalizedDerivative 'a' someAs = (literal 'a').star := by
  decide

/-- The unsimplified derivative keeps the empty word in front. -/
theorem unsimplified_derivative_of_someAs :
    derivative 'a' someAs = 1 * (literal 'a').star ∧
      derivative 'a' someAs ≠ (literal 'a').star := by decide

/-- The two derivatives have the same language. -/
theorem derivative_of_someAs_language :
    language (derivative 'a' someAs) = language (literal 'a').star := by
  rw [← derivative_of_someAs, normalizedDerivative, normalize_language]

/-! ## Search -/

/-- Row S1: bytes one to four of `xaaab`. -/
theorem search_someAs : searchBytes someAs "xaaab" = some ⟨1, 4, "aaa".toList⟩ := by decide

/-- Row S2: the longer alternative wins although the shorter is written
first. -/
theorem search_longest_alternative :
    searchBytes oneOrTwoAs "aa" = some ⟨0, 2, "aa".toList⟩ := by decide

/-- Row S3. -/
theorem search_no_match : searchBytes someAs "bc" = none := by decide

/-- Row U1: scalars one to three of `éλλx` are bytes two to six. -/
theorem search_nonAscii :
    regexSearch someLambdas "éλλx".toList = some ⟨1, 2⟩ ∧
      searchBytes someLambdas "éλλx" = some ⟨2, 6, "λλ".toList⟩ := by decide

/-- Row U2: the letter U+00E9 does not match U+0065 followed by the combining
accent U+0301. Text is not normalized. -/
theorem no_unicode_normalization :
    fullMatch (literal 'é') ['e', '́'] = false ∧
      fullMatch (literal 'é') ['é'] = true := by decide

/-! ## Replacement -/

/-- Row R1. -/
theorem replaceFirst_someAs :
    (regexReplaceFirst someAs letterX "baac".toList).output = "bxc".toList := by decide

/-- Row R2. -/
theorem replaceAll_someAs :
    (regexReplaceAll someAs letterX "aaba".toList).output = "xbx".toList := by cbv

/-- Row R3: the template may use the whole match. -/
theorem replaceFirst_bracketed :
    (regexReplaceFirst someAs bracketed "baac".toList).output = "b[aa]c".toList := by decide

/-- Row R4: a miss returns the input. -/
theorem replaceFirst_no_match :
    regexReplaceFirst someAs letterX "bc".toList = ⟨"bc".toList, []⟩ := by decide

/-- Row R5: the empty pattern matches at every boundary. -/
theorem replaceAll_empty_pattern :
    (regexReplaceAll (1 : Regex Char) letterX "ab".toList).output = "xaxbx".toList := by cbv

/-- Row R6: after an empty match one scalar is copied, not one byte. -/
theorem replaceAll_empty_pattern_nonAscii :
    (regexReplaceAll (1 : Regex Char) letterX "λ".toList).output = "xλx".toList := by cbv

/-- Row R7: after the match `a` the empty match at the end is replaced once. -/
theorem replaceAll_final_empty_match :
    (regexReplaceAll (literal 'a').star letterX "a".toList).output = "xx".toList := by cbv

end Mettapedia.Computability.RegularLanguages.ObservationTable
