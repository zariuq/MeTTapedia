import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxExport
import Mettapedia.GSLT.Parsing.SourcePacketActions

/-! Direct ParserPack data for the shared native reader. This exports the
already compiled plan and source-packet actions without recompiling a second
presentation. Native recognition and forest completeness retain their own
qualification obligations. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxNativePlan

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ParserProfileSemantics GrammarConstructorActions
open SourceSyntaxExport

def production (label resultSort : String) (items : List PackItem) (action : Action) : Term :=
  .application "pp-production"
    [.application "pp-label" [state resultSort,.string label],state resultSort,
     linked "pp-items-cons" "pp-items-nil" (items.map item),action.encode]

def lexical (row : CompiledLexicalProduction) : Term :=
  production row.label row.resultSort [.terminal row.matcher] (SourcePacketActions.lexical row.label)

def structural (row : CompiledStructuralProduction) : Term :=
  production row.label row.resultSort row.items (SourcePacketActions.structural row.label row.childSlots)

/-- Native roots already require the complete input span. Keeping the authored
start category avoids an extra production outside the semantic inventory. -/
def productions (plan : CompiledParserPackPlan) : List Term :=
  plan.lexical.productions.map lexical ++ plan.structural.map structural

def canonicalRows (rows : List Term) : List String :=
  (rows.map Term.render).mergeSort (· ≤ ·)

theorem canonicalRows_perm (rows : List Term) : List.Perm (canonicalRows rows) (rows.map Term.render) :=
  List.mergeSort_perm _ _

theorem canonicalRows_member (rows : List Term) (text : String) :
    text ∈ canonicalRows rows ↔ ∃ row ∈ rows, row.render = text := by
  simp [canonicalRows]

def directFilter : SourceSyntax.FamilyFilter → Term
  | .rejectWords sort words => .application "reject-words"
      [state sort,linked "LCons" "LNil" (words.map fun word =>
        linked "LCons" "LNil" (word.toList.map fun scalar => .natural scalar.toNat))]
  | .maximalToken sort points openers => .application "maximal-token"
      [state sort,linked "LCons" "LNil" (points.map .natural),
       linked "LCons" "LNil" (openers.map fun word =>
         linked "LCons" "LNil" (word.toList.map fun scalar => .natural scalar.toNat))]
  | .maximalExcept sort points openers => .application "maximal-except"
      [state sort,linked "LCons" "LNil" (points.map .natural),
       linked "LCons" "LNil" (openers.map fun word =>
         linked "LCons" "LNil" (word.toList.map fun scalar => .natural scalar.toNat))]

def exportDescription (description : Portable.SyntaxDescription) (filters : List SourceSyntax.FamilyFilter)
    (output : System.FilePath) : IO Unit := do
  let some plan := SourceSyntaxExport.plan? description
    | throw (IO.userError "source syntax cannot be compiled to the shared parser plan")
  let missing := missingCategories plan
  unless missing.isEmpty do throw (IO.userError ("missing source category definitions: " ++ String.intercalate ", " missing))
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "direct-productions.terms")
    (String.intercalate "\n" (canonicalRows (productions plan)) ++ "\n")
  IO.FS.writeFile (output / "direct-classes.terms")
    (String.intercalate "\n" (canonicalRows (plan.lexical.classes.flatMap classClauses)) ++ "\n")
  IO.FS.writeFile (output / "direct-start.term") (state plan.lexical.startSort).render
  IO.FS.writeFile (output / "direct-selection.term")
    (Term.application "source-selection-v1" [linked "LCons" "LNil" (filters.map directFilter)]).render
  IO.FS.writeFile (output / "syntax-description.metta") (Portable.renderSyntax description)
  IO.println s!"exported direct parser plan: {plan.lexical.productions.length} lexical, {plan.structural.length} structural rows"

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxNativePlan
