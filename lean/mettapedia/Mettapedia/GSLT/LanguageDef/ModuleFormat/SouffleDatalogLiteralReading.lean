import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogLiteralMeaning

/-! The executable literal normalization preserves and reflects the
independent character, escape and positional-number source meaning. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

theorem symbol_body_complete {source : Pattern} {characters : List Char} (meaning : SymbolBody source characters) :
    Frontend.symbolBody? source = some characters := by
  induction meaning with
  | empty => rfl
  | scalar printed _ ih => simp [Frontend.symbolBody?,printed,ih]
  | escaped escaped _ ih => simp [Frontend.symbolBody?,escape_complete escaped,ih]

theorem symbol_body_sound (source : Pattern) (characters : List Char) (read : Frontend.symbolBody? source = some characters) :
    SymbolBody source characters := by
  unfold Frontend.symbolBody? at read
  split at read
  · cases Option.some.inj read
    exact .empty
  · rename_i head tail
    change ((CorePrinter.printText? "DlStringScalar" head).bind fun text =>
      match text.toList with
      | [character] => (Frontend.symbolBody? tail).bind fun rest => some (character :: rest)
      | _ => none) = some characters at read
    obtain ⟨text,printed,later⟩ := Option.bind_eq_some_iff.mp read
    cases points : text.toList with
    | nil => simp [points] at later
    | cons character rest =>
      cases rest with
      | cons _ _ => simp [points] at later
      | nil =>
        rw [points] at later
        obtain ⟨rest,tailRead,same⟩ := Option.bind_eq_some_iff.mp later
        have spelling : text = String.singleton character := by
          simpa using congrArg String.ofList points
        rw [← Option.some.inj same]
        exact .scalar (printed.trans (congrArg some spelling)) (symbol_body_sound tail rest tailRead)
  · rename_i head tail
    change ((Frontend.escape? head).bind fun character => (Frontend.symbolBody? tail).bind fun rest =>
      some (character :: rest)) = some characters at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨character,escaped,rest,tailRead,rfl⟩ := read
    exact .escaped (escape_sound head character escaped) (symbol_body_sound tail rest tailRead)
  · cases read
termination_by sizeOf source
decreasing_by all_goals subst_vars; simp_wf; omega

theorem literal_value_complete {label : String} {source : Pattern} {value : Mettapedia.Languages.Datalog.Value}
    (meaning : Literal label source value) : Frontend.value? label source = some (IRCodec.value value) := by
  cases meaning with
  | symbol body => simp [Frontend.value?,symbol_body_complete body]
  | integer source value text spelling digits fits =>
    simp [Frontend.value?,spelling_complete spelling,
      (NumericSpelling.readInteger_exact text value).mpr digits,fits]
  | unsigned source value text spelling digits fits =>
    simp [Frontend.value?,spelling_complete spelling,
      (NumericSpelling.readUnsigned_exact text value).mpr digits,fits]

theorem literal_value_sound (label : String) (source code : Pattern) (read : Frontend.value? label source = some code) :
    ∃ value : Mettapedia.Languages.Datalog.Value, Literal label source value ∧ code = IRCodec.value value := by
  unfold Frontend.value? at read
  split at read
  · rename_i body
    change ((Frontend.symbolBody? body).bind fun characters =>
      some (IRCodec.value (.symbol (String.ofList characters)))) = some code at read
    obtain ⟨characters,parsed,same⟩ := Option.bind_eq_some_iff.mp read
    exact ⟨.symbol (String.ofList characters),.symbol (symbol_body_sound body characters parsed),(Option.some.inj same).symm⟩
  · change ((Frontend.sourceText? source).bind fun spelling => (NumericSpelling.readInteger? spelling).bind fun value =>
      if Mettapedia.Languages.Datalog.Value.fits64 (.number value)
      then some (IRCodec.value (.number value)) else none) = some code at read
    simp only [Option.bind_eq_some_iff] at read
    obtain ⟨spelling,printed,value,parsed,accepted⟩ := read
    split at accepted
    · rename_i fits
      exact ⟨.number value,.integer source value spelling (spelling_sound source spelling printed)
        ((NumericSpelling.readInteger_exact spelling value).mp parsed) fits,(Option.some.inj accepted).symm⟩
    · cases accepted
  · change ((Frontend.sourceText? source).bind fun spelling => (NumericSpelling.readUnsigned? spelling).bind fun value =>
      if Mettapedia.Languages.Datalog.Value.fits64 (.unsigned value)
      then some (IRCodec.value (.unsigned value)) else none) = some code at read
    simp only [Option.bind_eq_some_iff] at read
    obtain ⟨spelling,printed,value,parsed,accepted⟩ := read
    split at accepted
    · rename_i fits
      exact ⟨.unsigned value,.unsigned source value spelling (spelling_sound source spelling printed)
        ((NumericSpelling.readUnsigned_exact spelling value).mp parsed) fits,(Option.some.inj accepted).symm⟩
    · cases accepted
  · cases read

#print axioms symbol_body_complete
#print axioms symbol_body_sound
#print axioms literal_value_complete
#print axioms literal_value_sound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning
