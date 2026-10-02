import Mathlib.Computability.RegularExpressions
import Mettapedia.Computability.RegularLanguages.LanguageDerivatives

/-!
# Regular expressions with literal and wildcard atoms

The expression structure is Mathlib's `RegularExpression`. Only the alphabet
of atoms is extended: a literal denotes one specified letter, and a wildcard
denotes any one letter. This avoids enumerating an alphabet to interpret dot.

`language` is an independent set-of-words interpretation. The executable
derivative matcher is proved correct against it, and the literal-only fragment
agrees with Mathlib's language and matcher. Search and lexing policies are
separate consumers of this semantics.

The capture-free operation profile follows Dylon Edwards' regex GSLT contract
in F1R3FLY-io/mettail-rust, revision
`99885f467e42d52ef60ca0bb6076eb0fa25bfa0e`. The constructions and proofs here
are founded on Mathlib's formal languages, rather than taking a matcher as
the definition of its own correctness.
-/

set_option autoImplicit false

open scoped Computability

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- An atom consumes exactly one alphabet element. -/
inductive Atom (α : Type u) where
  | literal : α → Atom α
  | any : Atom α
  deriving DecidableEq, Repr

abbrev Regex (α : Type u) := RegularExpression (Atom α)

/-- Literal expression, with no interpretation of an alphabet element as
syntax or as several encoded bytes. -/
def literal (a : α) : Regex α := .char (.literal a)

/-- Wildcard expression; it consumes one alphabet element, including newline
when the alphabet is `Char`. -/
def any : Regex α := .char .any

/-- The independent language of a one-letter atom. -/
def atomLanguage : Atom α → Language α
  | .literal a => {[a]}
  | .any => {w | ∃ a, w = [a]}

/-- Interpret the regular-expression operations in Mathlib's Kleene algebra
of languages. This definition does not call the derivative matcher. -/
def language : Regex α → Language α
  | .zero => 0
  | .epsilon => 1
  | .char a => atomLanguage a
  | .plus p q => language p + language q
  | .comp p q => language p * language q
  | .star p => (language p)∗

@[simp] theorem language_zero : language (0 : Regex α) = 0 := rfl
@[simp] theorem language_one : language (1 : Regex α) = 1 := rfl
@[simp] theorem language_literal (a : α) : language (literal a) = {[a]} := rfl
@[simp] theorem language_any : language (any : Regex α) = {w | ∃ a, w = [a]} := rfl
@[simp] theorem language_add (p q : Regex α) : language (p + q) = language p + language q := rfl
@[simp] theorem language_mul (p q : Regex α) : language (p * q) = language p * language q := rfl
@[simp] theorem language_star (p : Regex α) : language p.star = (language p)∗ := rfl

@[simp] theorem language_pow (p : Regex α) (n : Nat) : language (p ^ n) = language p ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change language (p ^ n * p) = _
      rw [language_mul, ih, pow_succ]

private theorem nil_mem_mul (L M : Language α) : [] ∈ L * M ↔ [] ∈ L ∧ [] ∈ M := by
  constructor
  · rintro h
    obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.mp h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv
    exact ⟨hu, hv⟩
  · rintro ⟨hL, hM⟩
    exact Language.mem_mul.mpr ⟨[], hL, [], hM, rfl⟩

/-- Mathlib's structural nullability test is correct for the extended atoms. -/
theorem nullable_correct (p : Regex α) : p.matchEpsilon = true ↔ [] ∈ language p := by
  induction p with
  | zero => simp [RegularExpression.matchEpsilon, language]
  | epsilon => simp [RegularExpression.matchEpsilon, language]
  | char a =>
      cases a with
      | literal a =>
          change false = true ↔ ([] : List α) = [a]
          simp
      | any =>
          change false = true ↔ ∃ a : α, ([] : List α) = [a]
          simp
  | plus p q hp hq =>
      change (p.matchEpsilon || q.matchEpsilon) = true ↔ [] ∈ language p + language q
      rw [Bool.or_eq_true_iff, Language.mem_add, hp, hq]
  | comp p q hp hq =>
      simp [RegularExpression.matchEpsilon, language, nil_mem_mul, hp, hq]
  | star p _ =>
      exact ⟨fun _ => Language.nil_mem_kstar _, fun _ => rfl⟩

section Executable
variable [DecidableEq α]

def Atom.accepts : Atom α → α → Bool
  | .literal expected, actual => decide (expected = actual)
  | .any, _ => true

/-- Removing a first letter from the language of an atom leaves the empty
word when the atom accepts the letter, and nothing otherwise. -/
theorem leftDerivative_atomLanguage (a : α) (atom : Atom α) :
    leftDerivative a (atomLanguage atom) =
      if atom.accepts a then (1 : Language α) else 0 := by
  cases atom with
  | literal expected =>
      rw [atomLanguage, leftDerivative_singleton]
      simp only [Atom.accepts]
      by_cases h : a = expected <;> simp [h, eq_comm]
  | any =>
      simpa [atomLanguage, Atom.accepts] using
        leftDerivative_letters a (fun _ : α => True)

/-- Brzozowski derivative, using a literal or wildcard test only at atoms. -/
def derivative (a : α) : Regex α → Regex α
  | .zero => 0
  | .epsilon => 0
  | .char atom => if atom.accepts a then 1 else 0
  | .plus p q => derivative a p + derivative a q
  | .comp p q =>
      if p.matchEpsilon then derivative a p * q + derivative a q
      else derivative a p * q
  | .star p => derivative a p * p.star

/-- The derivative computes the actual left quotient of the language. -/
theorem derivative_language (a : α) (p : Regex α) :
    language (derivative a p) = leftDerivative a (language p) := by
  classical
  induction p with
  | zero => simp [derivative, language]
  | epsilon => simp [derivative, language]
  | char atom =>
      rw [derivative, language, leftDerivative_atomLanguage]
      split <;> rfl
  | plus p q hp hq =>
      change language (derivative a p + derivative a q) =
        leftDerivative a (language p + language q)
      rw [language_add, leftDerivative_add, hp, hq]
  | comp p q hp hq =>
      change language (derivative a (.comp p q)) = leftDerivative a (language p * language q)
      by_cases h : p.matchEpsilon = true
      · have hn := (nullable_correct p).mp h
        simp only [derivative, if_pos h, language_add, language_mul, hp, hq,
          leftDerivative_mul, if_pos hn]
      · have hn : [] ∉ language p := fun hm => h ((nullable_correct p).mpr hm)
        simp only [derivative, if_neg h, language_mul, hp,
          leftDerivative_mul, if_neg hn, add_zero]
  | star p hp => simp [derivative, language, leftDerivative_kstar, hp]

/-- Match an entire word, consuming one actual alphabet element per step. -/
def fullMatch : Regex α → List α → Bool
  | p, [] => p.matchEpsilon
  | p, a :: rest => fullMatch (derivative a p) rest

theorem fullMatch_correct (p : Regex α) (w : List α) :
    fullMatch p w = true ↔ w ∈ language p := by
  induction w generalizing p with
  | nil => exact nullable_correct p
  | cons a rest ih =>
      rw [fullMatch, ih, derivative_language, mem_leftDerivative]

/-- The derivative by a word, one letter at a time. -/
def derivatives : Regex α → List α → Regex α
  | p, [] => p
  | p, a :: rest => derivatives (derivative a p) rest

/-- The derivative by a word computes Mathlib's left quotient of the language
by that word. -/
theorem derivatives_language (p : Regex α) (word : List α) :
    language (derivatives p word) = (language p).leftQuotient word := by
  induction word generalizing p with
  | nil => rfl
  | cons a rest ih =>
      rw [derivatives, ih, derivative_language, leftQuotient_cons]

/-- Matching a word is nullability of the derivative by that word. -/
theorem fullMatch_eq_nullable_derivatives (p : Regex α) (word : List α) :
    fullMatch p word = (derivatives p word).matchEpsilon := by
  induction word generalizing p with
  | nil => rfl
  | cons a rest ih => exact ih (derivative a p)

/-- A word of the left quotient by `word` is a continuation that completes
`word` to a word of the language. -/
theorem fullMatch_append (p : Regex α) (word continuation : List α) :
    fullMatch p (word ++ continuation) = fullMatch (derivatives p word) continuation := by
  induction word generalizing p with
  | nil => rfl
  | cons a rest ih => exact ih (derivative a p)

/-- Search and lexing can use the proved matcher as the language's computable
membership decision. -/
instance decidableLanguage (p : Regex α) : DecidablePred (· ∈ language p) :=
  fun w => decidable_of_iff (fullMatch p w = true) (fullMatch_correct p w)

end Executable

/-- Embed Mathlib's literal-only expressions without changing their syntax
operations. -/
def ofRegular (p : RegularExpression α) : Regex α := p.map Atom.literal

theorem ofRegular_language (p : RegularExpression α) : language (ofRegular p) = p.matches' := by
  induction p with
  | zero => rfl
  | epsilon => rfl
  | char a => rfl
  | plus p q hp hq => simpa [ofRegular, RegularExpression.map, language] using congrArg₂ (· + ·) hp hq
  | comp p q hp hq => simpa [ofRegular, RegularExpression.map, language] using congrArg₂ (· * ·) hp hq
  | star p hp => simpa [ofRegular, RegularExpression.map, language] using congrArg KStar.kstar hp

theorem ofRegular_fullMatch [DecidableEq α] (p : RegularExpression α) (w : List α) :
    fullMatch (ofRegular p) w = p.rmatch w := by
  apply Bool.eq_iff_iff.mpr
  rw [fullMatch_correct, ofRegular_language, RegularExpression.rmatch_iff_matches']

/-- Semantic equivalence preserves full-match observations. It does not
identify authored syntax or computation histories. -/
theorem fullMatch_congr [DecidableEq α] {p q : Regex α} (h : language p = language q)
    (w : List α) : fullMatch p w = fullMatch q w := by
  apply Bool.eq_iff_iff.mpr
  rw [fullMatch_correct, fullMatch_correct, h]

end Mettapedia.Computability.RegularLanguages
