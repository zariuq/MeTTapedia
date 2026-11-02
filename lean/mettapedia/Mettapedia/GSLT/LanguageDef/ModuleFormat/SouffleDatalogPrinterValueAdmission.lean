import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmission

/-! Every symbol without NUL and every admitted 64-bit integer constructs formed
source syntax. Escaping and decimal conversion remain the existing printer's
operations, with their domains proved from character and integer properties. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing ParserProfileSemantics
open Mettapedia.Languages.Datalog
open Formation

theorem unescaped_allowed (character : Char) (nonzero : character.toNat ≠ 0) (unescaped : escapeLabel? character = none) :
    Allowed ⟨6, by decide⟩ character := by
  have notQuote : character.toNat ≠ 34 := by
    intro same
    have equal : character = '"' := Char.toNat_inj.mp same
    subst character
    cases unescaped
  have notSlash : character.toNat ≠ 92 := by
    intro same
    have equal : character = '\\' := Char.toNat_inj.mp same
    subst character
    cases unescaped
  have scalar : isUnicodeScalar character.toNat = true := by
    have valid := character.valid
    simp only [isUnicodeScalar, decide_eq_true_eq, Char.toNat]
    omega
  have lookup : SourceViews.profile.class? (ScalarCore.lexicalState ⟨6, by decide⟩).className =
      some ⟨"String", .except [0, 34, 92]⟩ := by decide +kernel
  simp [Allowed, ParserProfileLayer.ClassEvidence, ParserProfileLayer.classAccepts?, lookup,
    LexicalClassKind.accepts, scalar, nonzero, notQuote, notSlash]

theorem escape_formed (character : Char) (label : String) (escaped : escapeLabel? character = some label) :
    Formed "DlEscape" (node label []) := by
  have choices : label = "escape-quote" ∨ label = "escape-slash" ∨ label = "escape-newline" ∨
      label = "escape-return" ∨ label = "escape-tab" ∨ label = "escape-bell" ∨ label = "escape-backspace" ∨
      label = "escape-vertical-tab" ∨ label = "escape-formfeed" := by
    fun_cases escapeLabel? character
    all_goals simp_all [escapeLabel?, ← Char.toNat_inj]
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Formation.escape_quote
  · exact Formation.escape_slash
  · exact Formation.escape_newline
  · exact Formation.escape_return
  · exact Formation.escape_tab
  · exact Formation.escape_bell
  · exact Formation.escape_backspace
  · exact Formation.escape_vertical_tab
  · exact Formation.escape_formfeed

theorem symbol_total (characters : List Char) (nonzero : ∀ character ∈ characters, character.toNat ≠ 0) :
    ∃ pattern, symbolBody? characters = .ok pattern ∧ Formed "DlSymbolBody" pattern := by
  induction characters with
  | nil => exact ⟨_, rfl, Formation.symbol_empty⟩
  | cons first rest ih =>
    obtain ⟨tail, tailRead, tailFormed⟩ := ih (fun character member => nonzero character (List.mem_cons_of_mem _ member))
    cases escaped : escapeLabel? first with
    | some label =>
      exact ⟨_, by simp [symbolBody?, tailRead, escaped, bind, Except.bind, pure, Except.pure],
        Formation.symbol_escape (escape_formed first label escaped) tailFormed⟩
    | none =>
      obtain ⟨head, headRead, headFormed⟩ := scalar_total ⟨6, by decide⟩ first (unescaped_allowed first (nonzero first List.mem_cons_self) escaped)
      change scalar? "DlStringScalar" first = .ok head at headRead
      change Formed "DlStringScalar" head at headFormed
      exact ⟨_, by simp [symbolBody?, tailRead, escaped, headRead, bind, Except.bind, pure, Except.pure],
        Formation.symbol_body headFormed tailFormed⟩

def ValueAdmitted : Mettapedia.Languages.Datalog.Value → Prop
  | .symbol contents => ∀ character ∈ contents.toList, character.toNat ≠ 0
  | .number number => -(2 ^ 63 : Int) ≤ number ∧ number < 2 ^ 63
  | .unsigned number => number < 2 ^ 64
  | .floating _ => False

theorem value_total (value : Mettapedia.Languages.Datalog.Value) (admitted : ValueAdmitted value) :
    ∃ pattern, value? value = .ok pattern ∧ Formed "DlConstant" pattern := by
  cases value with
  | symbol contents =>
    obtain ⟨body, built, formed⟩ := symbol_total contents.toList admitted
    exact ⟨_, by simp [value?, built, bind, Except.bind, pure, Except.pure],
      Formation.constant_symbol (Formation.symbol formed)⟩
  | number number =>
    obtain ⟨digits, built, formed⟩ := decimal_total number.natAbs
    simp only [Nat.toList_repr] at built
    have width : Mettapedia.Languages.Datalog.Value.fits64 (.number number) = true := by
      simpa [Mettapedia.Languages.Datalog.Value.fits64, ValueAdmitted] using admitted
    by_cases negative : number < 0
    · exact ⟨_, by simp [value?, width, built, negative, bind, Except.bind, pure, Except.pure],
        Formation.constant_integer (Formation.integer_negative formed)⟩
    · exact ⟨_, by simp [value?, width, built, negative, bind, Except.bind, pure, Except.pure],
        Formation.constant_integer (Formation.integer_decimal formed)⟩
  | unsigned number =>
    obtain ⟨digits, built, formed⟩ := decimal_total number
    simp only [Nat.toList_repr] at built
    have width : Mettapedia.Languages.Datalog.Value.fits64 (.unsigned number) = true := by
      simpa [Mettapedia.Languages.Datalog.Value.fits64, ValueAdmitted] using admitted
    exact ⟨_, by simp [value?, width, built, bind, Except.bind, pure, Except.pure],
      Formation.constant_unsigned (Formation.unsigned_decimal formed)⟩
  | floating _ => exact False.elim admitted

#print axioms symbol_total
#print axioms value_total

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
