import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontend

/-! Qualified relation names retain their authored component structure.
Identifier spelling is read through the grammar, without re-tokenizing a
printed qualified name. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning

open Mettapedia.OSLF.MeTTaIL Syntax

inductive QualifiedName : Pattern → List String → Prop where
  | one {identifier : Pattern} {text : String} :
      CorePrinter.printText? "DlIdentifier" identifier = some text →
      QualifiedName (.apply "dl-src:qualified-name-one" [identifier]) [text]
  | more {identifier rest : Pattern} {text : String} {names : List String} :
      CorePrinter.printText? "DlIdentifier" identifier = some text → QualifiedName rest names →
      QualifiedName (.apply "dl-src:qualified-name-more" [identifier,rest]) (text :: names)

theorem qualifiedName_complete {source : Pattern} {names : List String}
    (meaning : QualifiedName source names) : Frontend.qualifiedName? source = some names := by
  induction meaning with
  | one printed => simp [Frontend.qualifiedName?, printed]
  | more printed _ ih => simp [Frontend.qualifiedName?, printed, ih]

theorem qualifiedName_sound (source : Pattern) (names : List String)
    (read : Frontend.qualifiedName? source = some names) : QualifiedName source names := by
  unfold Frontend.qualifiedName? at read
  split at read
  · rename_i identifier
    change ((CorePrinter.printText? "DlIdentifier" identifier).bind fun text => some [text]) = some names at read
    obtain ⟨text,printed,same⟩ := Option.bind_eq_some_iff.mp read
    cases Option.some.inj same
    exact .one printed
  · rename_i identifier rest
    change ((CorePrinter.printText? "DlIdentifier" identifier).bind fun text =>
      (Frontend.qualifiedName? rest).bind fun tail => some (text :: tail)) = some names at read
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at read
    obtain ⟨text,printed,tail,remaining,rfl⟩ := read
    exact .more printed (qualifiedName_sound rest tail remaining)
  · cases read
termination_by sizeOf source
decreasing_by all_goals subst_vars; simp_wf; omega

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning
