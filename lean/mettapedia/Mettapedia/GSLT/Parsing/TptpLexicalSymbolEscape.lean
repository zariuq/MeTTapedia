import Mettapedia.GSLT.Parsing.TptpLexicalNames

/-!
# Reader-parametric lexical symbol escaping

The input reader must consume exactly one complete host atom and report that
atom, rather than merely its metatype. A spelling is retained verbatim when
that reader returns exactly the requested symbol. Otherwise a reserved prefix
is added. A name already starting with that prefix is escaped once more.
The chosen spelling is admitted only when the actual reader returns that
exact symbol; readers that do not support it cause admission to fail closed.

U+00A4 is the candidate prefix used here. It is disjoint from the pinned
TPTP word alphabet and the existing section-sign defined/system prefixes.
Quoted names remain host strings and are not recoded. The inverse strips
only this lexical escape, then uses the existing classified-name decoder.

These theorems are parametric in an exact reader observation. They do not
formalize any native reader, configure its tokenizer, or guarantee that a
formula cannot be evaluated by user equations. The larger expression/string
printer boundary is also separate from symbol spelling admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TptpLexicalSymbolEscape

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TptpLexicalNames (Name)

/-- Consume exactly one complete atom. Trailing input, errors or unsupported
spellings are represented by `none`, not an approximate classification. -/
abbrev Reader := String → Option Atom

def marker : Char := '¤'

def hasMarker (text : String) : Bool :=
  match text.toList with
  | first :: _ => first == marker
  | [] => false

def escaped (text : String) : String := String.ofList (marker :: text.toList)

def recover (text : String) : String :=
  match text.toList with
  | first :: rest => if first = marker then String.ofList rest else text
  | [] => text

/-- Full value identity matters: a reader may keep the Symbol metatype but
normalize its spelling, for example `True` to the different symbol `true`. -/
def exactSymbol (reader : Reader) (text : String) : Bool :=
  decide (reader text = some (.symbol text))

def spelling (reader : Reader) (text : String) : String :=
  if hasMarker text || !(exactSymbol reader text) then escaped text else text

@[simp] theorem recover_escaped (text : String) : recover (escaped text) = text := by
  simp [recover, escaped]

theorem recover_without_marker {text : String} (plain : hasMarker text = false) :
    recover text = text := by
  unfold hasMarker at plain
  unfold recover
  cases letters : text.toList with
  | nil => rfl
  | cons first rest =>
      have different : first ≠ marker := by simpa [letters] using plain
      simp [different]

theorem recover_spelling (reader : Reader) (text : String) :
    recover (spelling reader text) = text := by
  unfold spelling
  split
  · exact recover_escaped text
  · rename_i condition
    have plain : hasMarker text = false := by
      cases observed : hasMarker text with
      | false => rfl
      | true => simp [observed] at condition
    exact recover_without_marker plain

theorem spelling_injective (reader : Reader) : Function.Injective (spelling reader) := by
  intro first second equal
  have decoded := congrArg recover equal
  simpa only [recover_spelling] using decoded

/-- Even different reader profiles cannot make two different input symbols
share the same admitted escaped spelling. -/
theorem cross_reader_spelling_injective (firstReader secondReader : Reader)
    {first second : String}
    (equal : spelling firstReader first = spelling secondReader second) : first = second := by
  have decoded := congrArg recover equal
  simpa only [recover_spelling] using decoded

theorem ordinary_is_bare (reader : Reader) (text : String)
    (plain : hasMarker text = false)
    (reads : reader text = some (.symbol text)) : spelling reader text = text := by
  simp [spelling, exactSymbol, plain, reads]

theorem exceptional_is_prefixed (reader : Reader) (text : String)
    (different : reader text ≠ some (.symbol text)) : spelling reader text = escaped text := by
  simp [spelling, exactSymbol, different]

theorem reserved_is_prefixed (reader : Reader) (text : String)
    (reserved : hasMarker text = true) : spelling reader text = escaped text := by
  simp [spelling, reserved]

/-- Preparation is conditional on the actual target reader, including its
handling of the escape spelling. No finite reserved-token list is consulted. -/
def prepareSymbol (reader : Reader) (text : String) : Option Atom :=
  let chosen := spelling reader text
  if exactSymbol reader chosen then some (.symbol chosen) else none

theorem prepareSymbol_iff (reader : Reader) (text : String) (atom : Atom) :
    prepareSymbol reader text = some atom ↔
      reader (spelling reader text) = some (.symbol (spelling reader text)) ∧
      atom = .symbol (spelling reader text) := by
  by_cases reads : reader (spelling reader text) = some (.symbol (spelling reader text))
  · simp [prepareSymbol, exactSymbol, reads, eq_comm]
  · simp [prepareSymbol, exactSymbol, reads]

theorem unsupported_spelling_refused (reader : Reader) (text : String)
    (different : reader (spelling reader text) ≠ some (.symbol (spelling reader text))) :
    prepareSymbol reader text = none := by
  simp [prepareSymbol, exactSymbol, different]

def recoverAtom : Atom → Atom
  | .symbol text => .symbol (recover text)
  | atom => atom

theorem prepareSymbol_recovers (reader : Reader) (text : String) (atom : Atom)
    (prepared : prepareSymbol reader text = some atom) :
    recoverAtom atom = .symbol text := by
  obtain ⟨_, exact⟩ := (prepareSymbol_iff reader text atom).mp prepared
  simp [exact, recoverAtom, recover_spelling]

theorem prepareSymbol_read_round_trip (reader : Reader) (text : String) (atom : Atom)
    (prepared : prepareSymbol reader text = some atom) :
    ∃ emitted : String, atom = .symbol emitted ∧ reader emitted = some atom ∧
      recover emitted = text := by
  obtain ⟨reads, exact⟩ := (prepareSymbol_iff reader text atom).mp prepared
  refine ⟨spelling reader text, exact, ?_, recover_spelling reader text⟩
  simpa [exact] using reads

/-- Only symbolic lexical values need symbol spelling preparation. Strings
and the existing back-quote/distinct-object expressions stay unchanged. -/
def prepareAtom (reader : Reader) : Atom → Option Atom
  | .symbol text => prepareSymbol reader text
  | atom => some atom

theorem prepareAtom_recovers (reader : Reader) (input output : Atom)
    (prepared : prepareAtom reader input = some output) : recoverAtom output = input := by
  cases input with
  | symbol text => exact prepareSymbol_recovers reader text output prepared
  | var name =>
      have exact : output = .var name := by simpa [prepareAtom] using prepared.symm
      simp [exact, recoverAtom]
  | grounded value =>
      have exact : output = .grounded value := by simpa [prepareAtom] using prepared.symm
      simp [exact, recoverAtom]
  | expression children =>
      have exact : output = .expression children := by simpa [prepareAtom] using prepared.symm
      simp [exact, recoverAtom]

def prepareName (reader : Reader) (name : Name) : Option Atom :=
  prepareAtom reader (TptpLexicalNames.encode name)

def decodeName (atom : Atom) : Option Name :=
  TptpLexicalNames.decode (recoverAtom atom)

def printName (atom : Atom) : Option String := (decodeName atom).map TptpLexicalNames.print

theorem prepareName_round_trip (reader : Reader) (name : Name) (atom : Atom)
    (prepared : prepareName reader name = some atom) : decodeName atom = some name := by
  unfold decodeName
  rw [prepareAtom_recovers reader (TptpLexicalNames.encode name) atom prepared]
  exact TptpLexicalNames.decode_encode name

theorem prepareName_print (reader : Reader) (name : Name) (atom : Atom)
    (prepared : prepareName reader name = some atom) :
    printName atom = some (TptpLexicalNames.print name) := by
  simp [printName, prepareName_round_trip reader name atom prepared]

theorem prepareName_injective (firstReader secondReader : Reader)
    (first second : Name) (atom : Atom)
    (firstPrepared : prepareName firstReader first = some atom)
    (secondPrepared : prepareName secondReader second = some atom) : first = second := by
  have firstDecoded := prepareName_round_trip firstReader first atom firstPrepared
  have secondDecoded := prepareName_round_trip secondReader second atom secondPrepared
  exact Option.some.inj (firstDecoded.symm.trans secondDecoded)

theorem quoted_unchanged (reader : Reader) (text : String) :
    prepareName reader (.quoted text) = some (.grounded (.string text)) := rfl

theorem back_quoted_unchanged (reader : Reader) (text : String) :
    prepareName reader (.backQuoted text) = some (TptpLexicalNames.wrapper "⌜" text) := rfl

theorem distinct_object_unchanged (reader : Reader) (text : String) :
    prepareName reader (.distinctObject text) = some (TptpLexicalNames.wrapper "◊" text) := rfl

theorem marker_not_source_word (rest : List Char) :
    TptpLexicalNames.word (marker :: rest) = false := by
  have lower : TptpLexicalNames.lower marker = false := by decide +kernel
  have upper : TptpLexicalNames.upper marker = false := by decide +kernel
  simp [TptpLexicalNames.word, lower, upper]

theorem marker_not_defined_prefix : marker ≠ '§' := by decide

namespace Examples

/-- A controlled reader observation for negative examples, not an executable
model or complete description of any real host reader. -/
def changingReader (text : String) : Option Atom :=
  if text = "True" then some (.symbol "true") else some (.symbol text)

example : exactSymbol changingReader "True" = false := by decide
example : spelling changingReader "True" = "¤True" := by decide
example : spelling changingReader "X" = "X" := by decide
example : spelling changingReader "if" = "if" := by decide
example : spelling changingReader "§i" = "§i" := by decide
example : spelling changingReader "§§i" = "§§i" := by decide
example : spelling changingReader "¤True" = "¤¤True" := by decide
example : prepareSymbol changingReader "True" = some (.symbol "¤True") := by decide
example : recover "¤¤True" = "¤True" := by decide
example : spelling changingReader "True" ≠ spelling changingReader "¤True" := by decide
example : prepareName changingReader (.quoted "¤True") =
    some (.grounded (.string "¤True")) := rfl
example : prepareName changingReader (.word TptpLexicalNames.Examples.truth) ≠
    prepareName changingReader (.quoted "¤True") := by decide +kernel
example : prepareSymbol (fun _ => none) "X" = none := by decide
example : recover "§§i" = "§§i" := by decide

end Examples

#print axioms recover_spelling
#print axioms spelling_injective
#print axioms prepareSymbol_iff
#print axioms prepareSymbol_read_round_trip
#print axioms prepareName_round_trip
#print axioms prepareName_injective
#print axioms prepareName_print
#print axioms marker_not_source_word

end Mettapedia.GSLT.Parsing.TptpLexicalSymbolEscape
