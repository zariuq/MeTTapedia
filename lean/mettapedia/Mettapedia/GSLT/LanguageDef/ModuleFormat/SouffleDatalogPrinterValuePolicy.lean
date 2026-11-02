import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterPolicy

/-! Identifier policy is preserved by scalar, name and value construction. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Policy

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Datalog

theorem empty_holds : Holds empty := node_holds _ _ (by decide) (by decide) trivial
theorem space_holds : Holds space :=
  node_holds _ _ (by decide) (by decide) ⟨leaf_holds _ _ _, empty_holds, trivial⟩
theorem newline_holds : Holds newline :=
  node_holds _ _ (by decide) (by decide) ⟨leaf_holds _ _ _, empty_holds, trivial⟩
theorem directive_holds : Holds directiveSpace :=
  node_holds _ _ (by decide) (by decide) ⟨leaf_holds _ _ _, empty_holds, trivial⟩

theorem qualified_holds (names : QualifiedName) (pattern : Pattern)
    (built : qualifiedName? names = .ok pattern) : Holds pattern := by
  cases names with
  | nil => cases built
  | cons first rest =>
    cases rest with
    | nil =>
      obtain ⟨head, headRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide) ⟨identifier_holds _ _ headRead, trivial⟩
    | cons second rest =>
      obtain ⟨head, headRead, built⟩ := bind_ok built
      obtain ⟨tail, tailRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide)
        ⟨identifier_holds _ _ headRead, qualified_holds _ _ tailRead, trivial⟩
termination_by names.length

theorem digits_holds (characters : List Char) (pattern : Pattern)
    (built : digits? characters = .ok pattern) : Holds pattern := by
  cases characters with
  | nil => cases built
  | cons first rest =>
    cases rest with
    | nil =>
      obtain ⟨head, headRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide) ⟨scalar_holds _ _ _ headRead, trivial⟩
    | cons second rest =>
      obtain ⟨head, headRead, built⟩ := bind_ok built
      obtain ⟨tail, tailRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide)
        ⟨scalar_holds _ _ _ headRead, digits_holds _ _ tailRead, trivial⟩
termination_by characters.length

theorem escape_holds (character : Char) (label : String) (escaped : escapeLabel? character = some label) :
    Holds (node label []) := by
  have labels : label = "escape-quote" ∨ label = "escape-slash" ∨ label = "escape-newline" ∨
      label = "escape-return" ∨ label = "escape-tab" ∨ label = "escape-bell" ∨
      label = "escape-backspace" ∨ label = "escape-vertical-tab" ∨ label = "escape-formfeed" := by
    unfold escapeLabel? at escaped
    split at escaped <;> try { cases Option.some.inj escaped; simp }
    split at escaped <;> try { cases Option.some.inj escaped; simp }
    cases escaped
  rcases labels with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact node_holds _ _ (by decide) (by decide) trivial

theorem symbol_holds (characters : List Char) (pattern : Pattern)
    (built : symbolBody? characters = .ok pattern) : Holds pattern := by
  cases characters with
  | nil => cases Except.ok.inj built; exact node_holds _ _ (by decide) (by decide) trivial
  | cons first rest =>
    obtain ⟨tail, tailRead, built⟩ := bind_ok built
    have later := symbol_holds rest tail tailRead
    cases escaped : escapeLabel? first with
    | none =>
      simp only [escaped] at built
      obtain ⟨head, headRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide) ⟨scalar_holds _ _ _ headRead, later, trivial⟩
    | some label =>
      simp only [escaped] at built
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide) ⟨escape_holds _ _ escaped, later, trivial⟩
termination_by characters.length

theorem value_holds (value : Mettapedia.Languages.Datalog.Value) (pattern : Pattern)
    (built : value? value = .ok pattern) : Holds pattern := by
  cases value with
  | symbol text =>
    obtain ⟨body, bodyRead, built⟩ := bind_ok built
    cases Except.ok.inj built
    exact node_holds _ _ (by decide) (by decide)
      ⟨node_holds _ _ (by decide) (by decide) ⟨symbol_holds _ _ bodyRead, trivial⟩, trivial⟩
  | number number =>
    by_cases width : Mettapedia.Languages.Datalog.Value.fits64 (.number number) = true
    · simp only [value?, width, ↓reduceIte, bind, Except.bind] at built
      obtain ⟨digits, digitRead, built⟩ := bind_ok built
      by_cases negative : number < 0
      · simp only [negative, ↓reduceIte] at built
        cases Except.ok.inj built
        exact node_holds _ _ (by decide) (by decide)
          ⟨node_holds _ _ (by decide) (by decide) ⟨digits_holds _ _ digitRead, trivial⟩, trivial⟩
      · simp only [negative, ↓reduceIte] at built
        cases Except.ok.inj built
        exact node_holds _ _ (by decide) (by decide)
          ⟨node_holds _ _ (by decide) (by decide) ⟨digits_holds _ _ digitRead, trivial⟩, trivial⟩
    · simp [value?, width, bind, Except.bind] at built
  | unsigned number =>
    by_cases width : Mettapedia.Languages.Datalog.Value.fits64 (.unsigned number) = true
    · simp only [value?, width, ↓reduceIte, bind, Except.bind] at built
      obtain ⟨digits, digitRead, built⟩ := bind_ok built
      cases Except.ok.inj built
      exact node_holds _ _ (by decide) (by decide)
        ⟨node_holds _ _ (by decide) (by decide) ⟨digits_holds _ _ digitRead, trivial⟩, trivial⟩
    · simp [value?, width, bind, Except.bind] at built
  | floating _ => cases built

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Policy
