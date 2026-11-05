import Mettapedia.Logic.Prolog.ReaderOperator

/-! Source-reading choices, separate from Prolog control and Datalog admission.
The ISO operator inventory follows 13211-1 with Corrigendum 2; SWI retains
the existing pinned inventory. A profile is not a completeness certificate
for a lexer, parser, or executable implementation. -/

namespace Mettapedia.Logic.Prolog.ReaderProfile

inductive QuotedText where
  | atom | chars | codes | string
  deriving DecidableEq, Repr, BEq

inductive Dialect where
  | iso | swi
  deriving DecidableEq, Repr, BEq

structure Profile where
  dialect : Dialect
  doubleQuotes : QuotedText
  backQuotes : Option QuotedText
  zeroArityCompounds : Bool
  digitSeparators : Bool
  operators : ReaderOperator.Table
  deriving DecidableEq

def isoOperator (row : ReaderOperator.Declaration) : Bool :=
  [":-", "-->", "?-", ";", "->", ",", "\\+", "=", "\\=", "==", "\\==",
   "@<", "@=<", "@>", "@>=", "=..", "is", "=:=", "=\\=", "<", "=<", ">", ">=",
   "+", "-", "/\\", "\\/", "*", "/", "//", "div", "rem", "mod", "<<", ">>",
   "**", "^", "\\"].contains row.name

def isoOperators : ReaderOperator.Table := ReaderOperator.defaults.filter isoOperator

def iso : Profile := ⟨.iso, .codes, none, false, false, isoOperators⟩
def swi : Profile := ⟨.swi, .string, some .codes, true, true, ReaderOperator.defaults⟩

def Profile.lists (profile : Profile) : SourceSignature.ListEncoding :=
  if profile.dialect == .iso then SourceSignature.isoLists else SourceSignature.swiLists

def Profile.nil (profile : Profile) : SourceSignature.Term := profile.lists.nil

def Profile.list (profile : Profile) (values : List SourceSignature.Term)
    (tail : SourceSignature.Term := profile.nil) : SourceSignature.Term := profile.lists.list values tail

def Profile.textTerm (profile : Profile) (mode : QuotedText) (value : String) : SourceSignature.Term :=
  match mode with
  | .atom => SourceSignature.atom value
  | .string => SourceSignature.string value
  | .chars => profile.list (value.toList.map (fun c => SourceSignature.atom (String.singleton c)))
  | .codes => profile.list (value.toList.map (fun c => SourceSignature.integer (Int.ofNat c.toNat)))

/-- SWI permits quoted operator names that require quoting; ordinary quoted
names do not acquire operator meaning. ISO does not make that distinction. -/
def bareAtom (name : String) : Bool :=
  ["!", ";", "[]", "{}"].contains name ||
  (name.toList.head?.any Char.isLower && name.toList.all (fun c => c.isAlphanum || c == '_')) ||
  (!name.isEmpty && name.toList.all ReaderLexer.isGraphic)

theorem bareAtom_graphic_spelling (name : String) : bareAtom name =
    (["!", ";", "[]", "{}"].contains name ||
      (name.toList.head?.any Char.isLower && name.toList.all (fun c => c.isAlphanum || c == '_')) ||
      (!name.isEmpty && name.toList.all (fun c => "#$&*+-./:<=>?@\\^~".toList.contains c))) := by
  have predicate : ReaderLexer.isGraphic =
      (fun c => "#$&*+-./:<=>?@\\^~".toList.contains c) := funext ReaderLexer.isGraphic_spelling
  simp only [bareAtom, predicate]

def Profile.quotedOperator (profile : Profile) (name : String) : Bool :=
  profile.dialect == .iso || !bareAtom name

def Profile.numericAllowed (profile : Profile) (lexeme : String) : Bool :=
  lexeme.startsWith "0'" || profile.digitSeparators || !lexeme.contains '_'

theorem iso_operators_in_swi : iso.operators ⊆ swi.operators := by
  intro row present
  exact (List.mem_filter.mp present).1

theorem text_codes_exact (profile : Profile) (text : String) : profile.textTerm .codes text =
    profile.list (text.toList.map (fun c => SourceSignature.integer (Int.ofNat c.toNat))) := rfl

theorem iso_nil_is_atom : iso.nil = SourceSignature.atom "[]" := rfl

theorem swi_nil_is_not_atom : swi.nil ≠ SourceSignature.atom "[]" := SourceSignature.swi_nil_ne_atom

end Mettapedia.Logic.Prolog.ReaderProfile
