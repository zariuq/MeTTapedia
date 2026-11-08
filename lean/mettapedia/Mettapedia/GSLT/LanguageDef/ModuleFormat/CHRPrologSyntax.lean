import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxModule

/-! Ground CHR's ordinary Prolog surface extends the shared sentence
grammar with CHR operators and a program sequence. It contributes no CHR
execution rules: interpretation into the independent CHR IR is downstream.
ISO Prolog and SWI-Prolog retain their separate existing profiles. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.Prolog ReaderProfile ReaderOperator

def chrOperators : ReaderOperator.Table := [
  ⟨"<=>", ⟨1180, by decide, by decide⟩, .xfx⟩,
  ⟨"==>", ⟨1180, by decide, by decide⟩, .xfx⟩,
  ⟨"\\", ⟨1100, by decide, by decide⟩, .xfx⟩,
  ⟨"@", ⟨1200, by decide, by decide⟩, .xfx⟩,
  ⟨"chr_constraint", ⟨1150, by decide, by decide⟩, .fx⟩]

/-- SWI's reader with CHR's operators. Double-quoted text reads as an atom
(SWI's `double_quotes=atom`), as C0 names have one atom kind. -/
def profile : Profile := {swi with doubleQuotes := .atom, operators := chrOperators ++ swi.operators}

private def row (name category : String) (sorts : List String) : GrammarRule :=
  { PrologSyntax.row name category (sorts.map Sum.inr) with label := "chr:" ++ name }

def programRows : List GrammarRule := [
  row "program" "ChrSourceProgram" ["ChrSourceSentences"],
  row "sentences-empty" "ChrSourceSentences" ["PlLayout"],
  row "sentences-more" "ChrSourceSentences" ["PlSentence", "ChrSourceSentences"]]

def description : Portable.SyntaxDescription :=
  PrologSyntax.extended profile programRows "ChrSourceProgram" "GroundCHRPrologSource"

def selection := PrologSyntax.selection profile

def module : ModuleSource.Module :=
  { PrologSyntaxModule.moduleWithRows profile programRows "ChrSourceProgram" "GroundCHRPrologSource" with
    imports := [⟨"../../prolog/PrologCommonSyntax.module", "common"⟩] }

theorem prolog_rows_retained : (PrologSyntax.grammar profile).terms ⊆ description.grammar.terms :=
  PrologSyntax.extended_retains_rows profile programRows _ _

theorem swi_operators_retained : swi.operators ⊆ profile.operators := by
  intro operator present
  exact List.mem_append_right _ present

example : chrOperators.any (fun op => op.name == "<=>" && op.priority.value == 1180) = true := by decide
example : !(iso.operators.any (fun op => op.name == "<=>")) := by decide

#print axioms prolog_rows_retained
#print axioms swi_operators_retained

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSyntax
