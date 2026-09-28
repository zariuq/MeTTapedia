import Mettapedia.GSLT.Parsing.TptpLexicalNames

/-!
# Host-safe spelling of ordinary TPTP words

The host reader determines which bare spellings cease to be symbols. The
predicate is a parameter so different MeTTa readers can provide their own
lexical policy; it is not a TPTP production list. The reserved escape is
outside the source word alphabet, so it cannot collide with a source word.
This is a representation component, not a claim that a host reader or the
prepared TPTP executor has already adopted it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TptpHostWordEscape

open TptpLexicalNames (Word word)

def escape : Char := '¤'

theorem escape_not_lower : TptpLexicalNames.lower escape = false := by decide +kernel
theorem escape_not_upper : TptpLexicalNames.upper escape = false := by decide +kernel

theorem escape_not_word (rest : List Char) : word (escape :: rest) = false := by
  change ((TptpLexicalNames.lower escape || TptpLexicalNames.upper escape) &&
    TptpLexicalNames.suffix rest) = false
  simp [escape_not_lower, escape_not_upper]

def encode (mustEscape : String → Bool) (value : Word) : List Char :=
  if mustEscape (String.ofList value.val) then escape :: value.val else value.val

def checked (characters : List Char) : Option Word :=
  if valid : word characters = true then some ⟨characters, valid⟩ else none

def decode (mustEscape : String → Bool) : List Char → Option Word
  | '¤' :: rest =>
      if mustEscape (String.ofList rest) then checked rest else none
  | characters =>
      if mustEscape (String.ofList characters) then none else checked characters

theorem decode_encode (mustEscape : String → Bool) (value : Word) :
    decode mustEscape (encode mustEscape value) = some value := by
  rcases value with ⟨characters, valid⟩
  cases special : mustEscape (String.ofList characters) with
  | true =>
    change decode mustEscape
      (if mustEscape (String.ofList characters) then escape :: characters
       else characters) = some ⟨characters, valid⟩
    rw [special]
    simp [decode, checked, valid, escape, special]
  | false =>
    have noPrefix : ∀ rest, characters ≠ escape :: rest := by
      intro rest equal
      have impossible := escape_not_word rest
      rw [← equal] at impossible
      simp [valid] at impossible
    cases characters with
    | nil => simp [word] at valid
    | cons first rest =>
        have first_ne : first ≠ escape := by
          intro equal
          apply noPrefix rest
          simp [equal]
        change decode mustEscape
          (if mustEscape (String.ofList (first :: rest)) then
            escape :: first :: rest else first :: rest) =
          some ⟨first :: rest, valid⟩
        rw [special]
        split <;> simp_all [decode, checked, escape]

theorem encode_injective (mustEscape : String → Bool) :
    Function.Injective (encode mustEscape) := by
  intro first second same
  have decoded := congrArg (decode mustEscape) same
  simpa only [decode_encode, Option.some.injEq] using decoded

def toAtom (mustEscape : String → Bool) (value : Word) :
    Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  .symbol (String.ofList (encode mustEscape value))

def fromAtom (mustEscape : String → Bool) :
    Mettapedia.Languages.MeTTa.OSLFCore.Atom → Option Word
  | .symbol spelling => decode mustEscape spelling.toList
  | _ => none

theorem fromAtom_toAtom (mustEscape : String → Bool) (value : Word) :
    fromAtom mustEscape (toAtom mustEscape value) = some value := by
  simp [fromAtom, toAtom, String.toList_ofList, decode_encode]

namespace Examples

private def samplePolicy (name : String) : Bool := name == "True"
private def truth : Word := ⟨['T', 'r', 'u', 'e'], by decide +kernel⟩
private def ordinary : Word := ⟨['c', 'a', 't'], by decide +kernel⟩

example : encode samplePolicy truth = ['¤', 'T', 'r', 'u', 'e'] := by decide +kernel
example : encode samplePolicy ordinary = ['c', 'a', 't'] := by decide +kernel
example : decode samplePolicy ['¤', 'T', 'r', 'u', 'e'] = some truth := by
  decide +kernel
example : decode samplePolicy ['T', 'r', 'u', 'e'] = none := by decide +kernel
example : decode samplePolicy ['¤', 'c', 'a', 't'] = none := by decide +kernel
example : decode samplePolicy ['§', 'i'] = none := by decide +kernel

end Examples

#print axioms decode_encode
#print axioms encode_injective
#print axioms fromAtom_toAtom

end Mettapedia.GSLT.Parsing.TptpHostWordEscape
