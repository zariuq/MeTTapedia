import Mettapedia.GSLT.Parsing.TptpLexicalSymbolEscape

/-!
# One portable compact-name spelling across host readers

The compact text is shared across dialects. A source word is emitted bare
only if every selected exact, whole-atom host reader returns that same symbol.
If any reader changes its atom kind or symbol payload, the source word uses
the reversible escape. Admission of that escape also requires every reader
to return exactly the emitted symbol. The readers here are parameters; their
binding to concrete runtime entry points is an implementation obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TptpPortableSymbolEscape

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TptpLexicalSymbolEscape

/-- The portable policy cannot be justified by an empty endpoint set. -/
structure Endpoints where
  readers : List Reader
  inhabited : readers ≠ []

def commonReader (endpoints : Endpoints) : Reader := fun text =>
  if endpoints.readers.all (fun reader => exactSymbol reader text) then
    some (.symbol text)
  else none

theorem commonReader_exact_iff (endpoints : Endpoints) (text : String) :
    commonReader endpoints text = some (.symbol text) ↔
      ∀ reader ∈ endpoints.readers, reader text = some (.symbol text) := by
  constructor
  · intro agreement reader member
    have all : endpoints.readers.all (fun reader => exactSymbol reader text) = true := by
      by_cases valid : endpoints.readers.all (fun reader => exactSymbol reader text) = true
      · exact valid
      · simp [commonReader, valid] at agreement
    have particular := (List.all_eq_true.mp all) reader member
    simpa [exactSymbol] using particular
  · intro agreement
    have all : endpoints.readers.all (fun reader => exactSymbol reader text) = true :=
      List.all_eq_true.mpr (by
        intro reader member
        simp [exactSymbol, agreement reader member])
    simp [commonReader, all]

/-- A single canonical choice, independent of which dialect first reads it. -/
def portableSpelling (endpoints : Endpoints) (text : String) : String :=
  spelling (commonReader endpoints) text

def preparePortable (endpoints : Endpoints) (text : String) : Option Atom :=
  prepareSymbol (commonReader endpoints) text

theorem portable_recovers (endpoints : Endpoints) (text : String) :
    recover (portableSpelling endpoints text) = text :=
  recover_spelling (commonReader endpoints) text

theorem portable_injective (endpoints : Endpoints) :
    Function.Injective (portableSpelling endpoints) :=
  spelling_injective (commonReader endpoints)

/-- Successful admission means every endpoint can reread the exact same
symbol. Merely sharing the Symbol metatype would not suffice. -/
theorem admitted_by_each (endpoints : Endpoints) (text : String) (atom : Atom)
    (admitted : preparePortable endpoints text = some atom)
    (reader : Reader) (member : reader ∈ endpoints.readers) :
    reader (portableSpelling endpoints text) = some atom := by
  obtain ⟨agreement, exact⟩ :=
    (prepareSymbol_iff (commonReader endpoints) text atom).mp admitted
  have reads := (commonReader_exact_iff endpoints _).mp agreement reader member
  simpa [portableSpelling, exact] using reads

theorem admitted_recovers (endpoints : Endpoints) (text : String) (atom : Atom)
    (admitted : preparePortable endpoints text = some atom) :
    recoverAtom atom = .symbol text :=
  prepareSymbol_recovers (commonReader endpoints) text atom admitted

theorem ordinary_bare_if_all (endpoints : Endpoints) (text : String)
    (notReserved : hasMarker text = false)
    (allRead : ∀ reader ∈ endpoints.readers,
      reader text = some (.symbol text)) :
    portableSpelling endpoints text = text :=
  ordinary_is_bare (commonReader endpoints) text notReserved
    ((commonReader_exact_iff endpoints text).mpr allRead)

theorem one_exception_forces_escape (endpoints : Endpoints) (text : String)
    (reader : Reader) (member : reader ∈ endpoints.readers)
    (different : reader text ≠ some (.symbol text)) :
    portableSpelling endpoints text = escaped text := by
  apply exceptional_is_prefixed
  intro allRead
  exact different ((commonReader_exact_iff endpoints text).mp allRead reader member)

namespace Examples

def exactReader (text : String) : Option Atom := some (.symbol text)
def booleanReader (text : String) : Option Atom :=
  if text = "True" then some (.grounded (.bool true)) else some (.symbol text)
def normalizingReader (text : String) : Option Atom :=
  if text = "True" then some (.symbol "true") else some (.symbol text)

def escapeAfterReading (reader : Reader) (text : String) : Option Atom := do
  let atom ← reader text
  match atom with
  | .symbol normalized => some (.symbol (escaped normalized))
  | _ => none

def twoReaders : Endpoints where
  readers := [exactReader, booleanReader, normalizingReader]
  inhabited := by decide

example : portableSpelling twoReaders "X" = "X" := by decide
example : portableSpelling twoReaders "True" = "¤True" := by decide
example : preparePortable twoReaders "True" = some (.symbol "¤True") := by decide
example : escapeAfterReading normalizingReader "True" =
    some (.symbol "¤true") := by decide
example : escapeAfterReading normalizingReader "True" ≠
    preparePortable twoReaders "True" := by decide
example : portableSpelling twoReaders "¤True" = "¤¤True" := by decide
example : preparePortable twoReaders "True" ≠ some (.symbol "True") := by decide
example : (normalizingReader "True").isSome = true ∧
    portableSpelling twoReaders "True" = "¤True" := by decide

def rejectingReader (_ : String) : Option Atom := none
def unsupported : Endpoints where
  readers := [exactReader, rejectingReader]
  inhabited := by decide

example : preparePortable unsupported "X" = none := by decide

end Examples

#print axioms commonReader_exact_iff
#print axioms admitted_by_each
#print axioms admitted_recovers
#print axioms one_exception_forces_escape

end Mettapedia.GSLT.Parsing.TptpPortableSymbolEscape
