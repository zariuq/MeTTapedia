import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontend

/-! Literal meaning is specified by source constructor spellings and
character/escape derivations. Positional signed and unsigned literals denote
their mathematical values within the declared 64-bit profile. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

inductive Spells : Pattern → String → Prop where
  | declared (label : String) (children : List Pattern) (rule : GrammarRule) (text : String) :
      rule ∈ SourceViews.grammar.terms → rule.label = label →
      CorePrinter.printText? rule.category (.apply label children) = some text →
      Spells (.apply label children) text

private theorem constructor_labels_unique : (SourceViews.grammar.terms.map GrammarRule.label).Nodup := by decide +kernel

theorem spelling_sound (source : Pattern) (text : String) (printed : Frontend.sourceText? source = some text) : Spells source text := by
  cases source with
  | apply label children =>
    change ((SourceViews.grammar.terms.find? (·.label == label)).bind fun rule =>
      CorePrinter.printText? rule.category (.apply label children)) = some text at printed
    obtain ⟨rule,selected,read⟩ := Option.bind_eq_some_iff.mp printed
    exact .declared label children rule text (List.mem_of_find?_eq_some selected)
      (by simpa only [beq_iff_eq] using List.find?_some selected) read
  | _ => cases printed

theorem spelling_complete {source : Pattern} {text : String} (spelling : Spells source text) :
    Frontend.sourceText? source = some text := by
  cases spelling with
  | declared label children rule text member named printed =>
    have selected : SourceViews.grammar.terms.find? (·.label == label) = some rule := by
      cases found : SourceViews.grammar.terms.find? (·.label == label) with
      | none =>
        have rejected := List.find?_eq_none.mp found rule member
        simp [named] at rejected
      | some actual =>
        have actualLabel : actual.label = label := by simpa only [beq_iff_eq] using List.find?_some found
        have same : actual = rule := List.inj_on_of_nodup_map constructor_labels_unique
          (List.mem_of_find?_eq_some found) member (actualLabel.trans named.symm)
        exact congrArg some same
    simpa only [Frontend.sourceText?,selected,Option.bind_eq_bind,Option.bind_some] using printed

inductive Escape : Pattern → Char → Prop where
  | quote : Escape (.apply "dl-src:escape-quote" []) '"'
  | apostrophe : Escape (.apply "dl-src:escape-apostrophe" []) '\''
  | slash : Escape (.apply "dl-src:escape-slash" []) '\\'
  | bell : Escape (.apply "dl-src:escape-bell" []) (Char.ofNat 7)
  | backspace : Escape (.apply "dl-src:escape-backspace" []) (Char.ofNat 8)
  | formfeed : Escape (.apply "dl-src:escape-formfeed" []) (Char.ofNat 12)
  | newline : Escape (.apply "dl-src:escape-newline" []) '\n'
  | returnChar : Escape (.apply "dl-src:escape-return" []) '\r'
  | tab : Escape (.apply "dl-src:escape-tab" []) '\t'
  | verticalTab : Escape (.apply "dl-src:escape-vertical-tab" []) (Char.ofNat 11)

theorem escape_complete {source : Pattern} {character : Char} (meaning : Escape source character) :
    Frontend.escape? source = some character := by cases meaning <;> rfl

theorem escape_sound (source : Pattern) (character : Char) (read : Frontend.escape? source = some character) : Escape source character := by
  fun_cases Frontend.escape? source
  all_goals try (have same := Option.some.inj read; cases same)
  all_goals first
    | exact .quote | exact .apostrophe | exact .slash | exact .bell | exact .backspace
    | exact .formfeed | exact .newline | exact .returnChar | exact .tab | exact .verticalTab
    | simp_all [Frontend.escape?]

inductive SymbolBody : Pattern → List Char → Prop where
  | empty : SymbolBody (.apply "dl-src:symbol-empty" []) []
  | scalar {head tail : Pattern} {character : Char} {rest : List Char} :
      CorePrinter.printText? "DlStringScalar" head = some (String.singleton character) →
      SymbolBody tail rest → SymbolBody (.apply "dl-src:symbol-body" [head,tail]) (character :: rest)
  | escaped {head tail : Pattern} {character : Char} {rest : List Char} :
      Escape head character → SymbolBody tail rest →
      SymbolBody (.apply "dl-src:symbol-escape" [head,tail]) (character :: rest)

inductive Literal : String → Pattern → Mettapedia.Languages.Datalog.Value → Prop where
  | symbol {body : Pattern} {characters : List Char} : SymbolBody body characters →
      Literal "SymbolValue" (.apply "dl-src:symbol" [body]) (.symbol (String.ofList characters))
  | integer (source : Pattern) (value : Int) (text : String) : Spells source text →
      NumericSpelling.Integer text value → Mettapedia.Languages.Datalog.Value.fits64 (.number value) = true →
      Literal "IntegerValue" source (.number value)
  | unsigned (source : Pattern) (value : Nat) (text : String) : Spells source text →
      NumericSpelling.Unsigned text value → Mettapedia.Languages.Datalog.Value.fits64 (.unsigned value) = true →
      Literal "UnsignedValue" source (.unsigned value)

#print axioms spelling_sound
#print axioms spelling_complete
#print axioms escape_sound
#print axioms escape_complete

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning
