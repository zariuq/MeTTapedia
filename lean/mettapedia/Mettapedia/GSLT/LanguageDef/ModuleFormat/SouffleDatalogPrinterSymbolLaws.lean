import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterLexicalLaws

/-! Printing symbol contents preserves every character and escape through
the existing source interpretation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax

theorem escape_read (character : Char) (label : String) (selected : escapeLabel? character = some label) :
    Frontend.escape? (node label []) = some character := by
  fun_cases escapeLabel? character
  all_goals try (cases Option.some.inj selected)
  all_goals simp_all [escapeLabel?,← Char.toNat_inj]
  all_goals try subst label
  all_goals simp_all [node,Frontend.escape?,← Char.toNat_inj]

theorem symbol_body_read (characters : List Char) (source : Pattern)
    (built : symbolBody? characters = .ok source) : Frontend.symbolBody? source = some characters := by
  induction characters generalizing source with
  | nil =>
    have same : node "symbol-empty" [] = source := Except.ok.inj built
    subst source
    simp [node,Frontend.symbolBody?]
  | cons character rest ih =>
    cases tailResult : symbolBody? rest with
    | error reason =>
      rw [symbolBody?,tailResult] at built
      change (Except.error reason : Except String Pattern) = Except.ok source at built
      cases built
    | ok tail =>
      have tailRead := ih tail tailResult
      cases escaped : escapeLabel? character with
      | some label =>
        have same : node "symbol-escape" [node label [],tail] = source := by
          simpa [symbolBody?,tailResult,escaped,Except.bind,Except.pure] using built
        subst source
        change Frontend.symbolBody? (.apply "dl-src:symbol-escape" [node label [],tail]) = some (character :: rest)
        simp only [Frontend.symbolBody?,escape_read character label escaped,Option.bind_eq_bind,Option.bind_some,tailRead]
        rfl
      | none =>
        cases firstResult : scalar? "DlStringScalar" character with
        | error reason =>
          rw [symbolBody?,tailResult,escaped,firstResult] at built
          change (Except.error reason : Except String Pattern) = Except.ok source at built
          cases built
        | ok first =>
          rw [symbolBody?,tailResult,escaped,firstResult] at built
          have same : node "symbol-body" [first,tail] = source := Except.ok.inj built
          subst source
          have printed := scalar_print "DlStringScalar" character first firstResult
          change Frontend.symbolBody? (.apply "dl-src:symbol-body" [first,tail]) = some (character :: rest)
          simp only [Frontend.symbolBody?,printed,Option.bind_eq_bind,Option.bind_some,String.toList_singleton,tailRead]
          rfl

#print axioms escape_read
#print axioms symbol_body_read

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
