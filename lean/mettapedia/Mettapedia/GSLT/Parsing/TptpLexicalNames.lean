import Mettapedia.GSLT.Parsing.MeTTaAtomActionCompiler

/-!
# Reversible lexical names in ordinary host atoms

This is the interpretation of already classified lexical values, not another
TPTP lexer or a public formula datatype. The word alphabets are TPTP's
lower-case, upper-case, numeric and underscore character classes. Quoted
payloads are decoded text; their outer delimiters and escape characters are
reconstructed by the printer.

The spelling is a reversible representation in host atoms: single-quoted
atomic words are host strings, back-quoted words use `(⌜ text)`, distinct
objects use `(◊ text)`, and defined/system words use one/two section signs.
The input classification is retained even for `cat` versus `'cat'`; this is a
finer observation than the standard's optional removal of redundant single
quotes.

The codec is about actual atom kinds. It does not claim that the host's plain
text printer preserves every symbol: names such as `True` are symbols here,
whereas a host reader can interpret that printed token as a boolean. Nor does
the spelling isolate data from arbitrary user equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TptpLexicalNames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open MeTTaAtomConstruction

/-- TPTP's `<lower_alpha>`, `<upper_alpha>`, `<numeric>` and underscore. -/
def lower (character : Char) : Bool := 'a' ≤ character && character ≤ 'z'
def upper (character : Char) : Bool := 'A' ≤ character && character ≤ 'Z'
def digit (character : Char) : Bool := '0' ≤ character && character ≤ '9'
def underscore (character : Char) : Bool := character == '_'

def alphaNumeric (character : Char) : Bool :=
  lower character || upper character || digit character || underscore character

def suffix (characters : List Char) : Bool := characters.all alphaNumeric

def word : List Char → Bool
  | [] => false
  | first :: rest => (lower first || upper first) && suffix rest

abbrev Word := { characters : List Char // word characters = true }
abbrev Suffix := { characters : List Char // suffix characters = true }

@[simp] theorem lower_sigil : lower '§' = false := by decide +kernel
@[simp] theorem upper_sigil : upper '§' = false := by decide +kernel
@[simp] theorem alphaNumeric_sigil : alphaNumeric '§' = false := by decide +kernel
@[simp] theorem suffix_sigil (rest : List Char) : suffix ('§' :: rest) = false := by
  simp [suffix]
@[simp] theorem word_sigil (rest : List Char) : word ('§' :: rest) = false := by
  simp [word]

/-- Classified lexical input. Only the resulting `Atom` is the public value.
Quoted payloads may contain arbitrary host text; source lexical admission is
separate and can restrict that larger reversible domain to visible ASCII. -/
inductive Name where
  | word : Word → Name
  | quoted : String → Name
  | defined : Suffix → Name
  | system : Suffix → Name
  | backQuoted : String → Name
  | distinctObject : String → Name

def wrapper (head payload : String) : Atom :=
  .expression [.symbol head, .grounded (.string payload)]

def encode : Name → Atom
  | .word value => .symbol (String.ofList value.val)
  | .quoted value => .grounded (.string value)
  | .defined value => .symbol (String.ofList ('§' :: value.val))
  | .system value => .symbol (String.ofList ('§' :: '§' :: value.val))
  | .backQuoted value => wrapper "⌜" value
  | .distinctObject value => wrapper "◊" value

def checkedWord (characters : List Char) : Option Name :=
  if valid : word characters = true then some (.word ⟨characters, valid⟩) else none

def checkedSuffix (kind : Suffix → Name) (characters : List Char) : Option Name :=
  if valid : suffix characters = true then some (kind ⟨characters, valid⟩) else none

def decodeSymbol : List Char → Option Name
  | '§' :: '§' :: rest => checkedSuffix .system rest
  | '§' :: rest => checkedSuffix .defined rest
  | characters => checkedWord characters

def decode : Atom → Option Name
  | .symbol text => decodeSymbol text.toList
  | .grounded (.string text) => some (.quoted text)
  | .expression [.symbol head, .grounded (.string text)] =>
      if head = "⌜" then some (.backQuoted text)
      else if head = "◊" then some (.distinctObject text)
      else none
  | _ => none

theorem decodeSymbol_word (value : Word) :
    decodeSymbol value.val = some (.word value) := by
  rcases value with ⟨characters, valid⟩
  cases characters with
  | nil => simp [word] at valid
  | cons first rest =>
      by_cases first_sigil : first = '§'
      · subst first
        simp at valid
      · simp [decodeSymbol, first_sigil, checkedWord, valid]

theorem decodeSymbol_defined (value : Suffix) :
    decodeSymbol ('§' :: value.val) = some (.defined value) := by
  rcases value with ⟨characters, valid⟩
  cases characters with
  | nil => simp [decodeSymbol, checkedSuffix, valid]
  | cons first rest =>
      by_cases first_sigil : first = '§'
      · subst first
        simp at valid
      · simp [decodeSymbol, first_sigil, checkedSuffix, valid]

theorem decode_encode (name : Name) : decode (encode name) = some name := by
  cases name with
  | word value => simpa [encode, decode] using decodeSymbol_word value
  | defined value => simpa [encode, decode] using decodeSymbol_defined value
  | system value => simp [encode, decode, decodeSymbol, checkedSuffix, value.property]
  | quoted value => rfl
  | backQuoted value => simp [encode, wrapper, decode]
  | distinctObject value => simp [encode, wrapper, decode]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have result := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using result

/-- Canonical TPTP escaping acts on decoded payloads, not UTF-8 bytes. -/
def escape (delimiter : Char) : List Char → List Char
  | [] => []
  | character :: rest =>
      if character = delimiter || character = '\\' then
        '\\' :: character :: escape delimiter rest
      else character :: escape delimiter rest

/-- This decodes an already delimited payload. It refuses dangling or
unrecognized escapes and an unescaped delimiter. -/
def unescape (delimiter : Char) : List Char → Option (List Char)
  | [] => some []
  | '\\' :: character :: rest =>
      if character = delimiter || character = '\\' then
        (unescape delimiter rest).map (character :: ·)
      else none
  | '\\' :: [] => none
  | character :: rest =>
      if character = delimiter then none
      else (unescape delimiter rest).map (character :: ·)

theorem unescape_escape (delimiter : Char) (characters : List Char) :
    unescape delimiter (escape delimiter characters) = some characters := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
      by_cases slash : character = '\\'
      · subst character
        simp [escape, unescape, ih]
      · by_cases closing : character = delimiter
        · subst character
          simp [escape, unescape, ih]
        · simp [escape, unescape, slash, closing, ih]

theorem escape_injective (delimiter : Char) : Function.Injective (escape delimiter) := by
  intro first second same
  have result := congrArg (unescape delimiter) same
  simpa only [unescape_escape, Option.some.injEq] using result

/-- Canonical spelling after lexical classification has already been read.
This printer does not implement tokenization or substitute for SyntaxBNF. -/
def print : Name → String
  | .word value => String.ofList value.val
  | .quoted text => String.ofList ('\'' :: escape '\'' text.toList ++ ['\''])
  | .defined value => String.ofList ('$' :: value.val)
  | .system value => String.ofList ('$' :: '$' :: value.val)
  | .backQuoted text => "`" ++ text
  | .distinctObject text => String.ofList ('"' :: escape '"' text.toList ++ ['"'])

/-- Recover a canonical TPTP spelling from a compact lexical atom. -/
def printAtom (atom : Atom) : Option String := (decode atom).map print

theorem printAtom_encode (name : Name) : printAtom (encode name) = some (print name) := by
  simp [printAtom, decode_encode]

inductive LexicalKind where
  | word | quoted | defined | system | backQuoted | distinctObject
  deriving DecidableEq, Repr

def Name.kind : Name → LexicalKind
  | .word _ => .word
  | .quoted _ => .quoted
  | .defined _ => .defined
  | .system _ => .system
  | .backQuoted _ => .backQuoted
  | .distinctObject _ => .distinctObject

def Name.payload : Name → String
  | .word value => String.ofList value.val
  | .quoted text => text
  | .defined value => String.ofList value.val
  | .system value => String.ofList value.val
  | .backQuoted text => text
  | .distinctObject text => text

def removeDelimiters (delimiter : Char) : List Char → Option (List Char)
  | [] => none
  | first :: rest =>
      if first = delimiter then
        match rest.reverse with
        | [] => none
        | last :: middle => if last = delimiter then some middle.reverse else none
      else none

theorem removeDelimiters_correct (delimiter : Char) (body : List Char) :
    removeDelimiters delimiter (delimiter :: body ++ [delimiter]) = some body := by
  simp [removeDelimiters, List.reverse_append]

/-- The grammar supplies the token class. This inverse only removes the
class's known delimiters and escapes; it is not an independent token lexer. -/
def readClassified (kind : LexicalKind) (text : String) : Option Name :=
  match kind, text.toList with
  | .word, characters => checkedWord characters
  | .quoted, characters => do
      let body ← removeDelimiters '\'' characters
      let payload ← unescape '\'' body
      return .quoted (String.ofList payload)
  | .defined, '$' :: payload => checkedSuffix .defined payload
  | .system, '$' :: '$' :: payload => checkedSuffix .system payload
  | .backQuoted, '`' :: payload => some (.backQuoted (String.ofList payload))
  | .distinctObject, characters => do
      let body ← removeDelimiters '"' characters
      let payload ← unescape '"' body
      return .distinctObject (String.ofList payload)
  | _, _ => none

theorem readClassified_print (name : Name) :
    readClassified name.kind (print name) = some name := by
  cases name with
  | word value => simp [readClassified, Name.kind, print, checkedWord, value.property]
  | defined value => simp [readClassified, Name.kind, print, checkedSuffix, value.property]
  | system value => simp [readClassified, Name.kind, print, checkedSuffix, value.property]
  | quoted text =>
      have strip := removeDelimiters_correct '\'' (escape '\'' text.toList)
      simp only [List.cons_append] at strip
      simp [readClassified, Name.kind, print, strip, unescape_escape]
  | backQuoted text => simp [readClassified, Name.kind, print]
  | distinctObject text =>
      have strip := removeDelimiters_correct '"' (escape '"' text.toList)
      simp only [List.cons_append] at strip
      simp [readClassified, Name.kind, print, strip, unescape_escape]

/-- These existing typed actions build the exact same values from decoded
text. No lexical decoder or class test is hidden in these operations. -/
def wordAction : Action [.text] .atom := symbolAction
def quotedAction : Action [.text] .atom := stringAction

def sigilAction (sigil : String) : Action [.text] .atom :=
  .apply .symbol (.cons
    (.apply .textAppend (.cons (.source sigil) (.cons (.input .here) .nil))) .nil)

def wrapperAction (head : String) : Action [.text] .atom :=
  .apply .application (.cons (.source (.symbol head)) (.cons
    (.apply .cons (.cons quotedAction (.cons (.apply .empty .nil) .nil))) .nil))

theorem wordAction_correct (value : Word) :
    wordAction.run (.cons (String.ofList value.val) .nil) = encode (.word value) := rfl

theorem quotedAction_correct (value : String) :
    quotedAction.run (.cons value .nil) = encode (.quoted value) := rfl

theorem wrapperAction_correct (head value : String) :
    (wrapperAction head).run (.cons value .nil) = wrapper head value := rfl

theorem sigilAction_correct (sigil value : String) :
    (sigilAction sigil).run (.cons value .nil) = .symbol (sigil ++ value) := rfl

def action : LexicalKind → Action [.text] .atom
  | .word => wordAction
  | .quoted => quotedAction
  | .defined => sigilAction "§"
  | .system => sigilAction "§§"
  | .backQuoted => wrapperAction "⌜"
  | .distinctObject => wrapperAction "◊"

theorem action_correct (name : Name) :
    (action name.kind).run (.cons name.payload .nil) = encode name := by
  cases name with
  | word value => rfl
  | quoted text => rfl
  | defined value =>
      simp [action, Name.kind, Name.payload, sigilAction_correct, encode]
  | system value =>
      simp only [action, Name.kind, Name.payload, sigilAction_correct, encode,
        Atom.symbol.injEq, String.ofList_cons]
      exact @String.append_assoc "§" "§" (String.ofList value.val)
  | backQuoted text => rfl
  | distinctObject text => rfl

/-- All six representation choices lower through the same generic action
compiler. This theorem consumes classified, decoded payloads, not raw bytes. -/
theorem compiled_action_correct (name : Name) :
    MeTTaAtomActionCompiler.executeCodeChecked [.text]
      [.grounded (.string name.payload)]
      (MeTTaAtomActionCompiler.encodeCode
        (MeTTaAtomActionCompiler.compile (action name.kind))) = some (encode name) := by
  have computes := MeTTaAtomActionCompiler.compiled_code_executes_checked
    (action name.kind) (.cons name.payload .nil)
  exact computes.trans (congrArg some (action_correct name))

theorem compiled_wordAction (value : Word) :
    MeTTaAtomActionCompiler.executeCodeChecked [.text]
      [.grounded (.string (String.ofList value.val))]
      (MeTTaAtomActionCompiler.encodeCode (MeTTaAtomActionCompiler.compile wordAction)) =
        some (encode (.word value)) :=
  MeTTaAtomActionCompiler.compiled_code_executes_checked wordAction
    (.cons (String.ofList value.val) .nil)

namespace Examples

def x : Word := ⟨['X'], by decide +kernel⟩
def i : Suffix := ⟨['i'], by decide +kernel⟩
def truth : Word := ⟨['T', 'r', 'u', 'e'], by decide +kernel⟩
def conditional : Word := ⟨['i', 'f'], by decide +kernel⟩
def emptySuffix : Suffix := ⟨[], by decide⟩

example : encode (.word x) = .symbol "X" := rfl
example : encode (.defined i) = .symbol "§i" := rfl
example : encode (.system i) = .symbol "§§i" := rfl
example : encode (.quoted "$i") = .grounded (.string "$i") := rfl
example : encode (.quoted "X") ≠ encode (.word x) := by decide
example : encode (.defined i) ≠ encode (.quoted "$i") := by decide
example : encode (.defined i) ≠ encode (.quoted "§i") := by decide
example : encode (.system i) ≠ encode (.quoted "§§i") := by decide
example : encode (.backQuoted "X") ≠ encode (.quoted "X") := by decide
example : encode (.distinctObject "X") ≠ encode (.quoted "X") := by decide
example : encode (.word truth) ≠ .grounded (.bool true) := by decide
example : encode (.word conditional) = .symbol "if" := rfl
example : encode (.defined emptySuffix) = .symbol "§" := rfl
example : encode (.system emptySuffix) = .symbol "§§" := rfl
example : encode (.defined emptySuffix) ≠ encode (.system emptySuffix) := by decide
example : encode (.quoted "(if $X)") = .grounded (.string "(if $X)") := rfl
example : printAtom (encode (.defined i)) = some "$i" := by decide
example : printAtom (encode (.quoted "a'b\\c")) = some "'a\\'b\\\\c'" := by decide
example : unescape '\'' ['\\'] = none := rfl
example : unescape '\'' ['\\', 'q'] = none := by decide
example : decode (.symbol "§§§i") = none := by decide +kernel

end Examples

#print axioms decode_encode
#print axioms encode_injective
#print axioms unescape_escape
#print axioms readClassified_print
#print axioms compiled_action_correct
#print axioms compiled_wordAction

end Mettapedia.GSLT.Parsing.TptpLexicalNames
