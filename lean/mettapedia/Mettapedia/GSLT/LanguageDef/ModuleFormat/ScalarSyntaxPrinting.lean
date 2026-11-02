import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxReification

/-! The source printer consumes only retained constructor/scalar data.
Its correspondence proof reads the original source judgment. Exact spelling,
layout and comments survive; no input slice or derivation is consulted by
the printing computation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax LanguageDefScalarPrinter PresentationExprSemantics

def lexicalPrinter (description : Description) (sort : String) : Option (Pattern → Option (List Nat)) :=
  (lexicalRow? description sort).map fun row pattern => (readLeaf? description row pattern).map (· :: [])

def printScalars? (description : Description) (sort : String) (pattern : Pattern) : Option (List Nat) :=
  DeclaredConstructorPrinter.print? description.grammar stringScalars (lexicalPrinter description) sort pattern

def printText? (description : Description) (sort : String) (pattern : Pattern) : Option String :=
  (printScalars? description sort pattern).map fun points => String.ofList (points.map Char.ofNat)

variable {input : List Nat}

mutual
  theorem print_reify (description : Description) (shape : Shape description)
      {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt (fun text => some (stringScalars text))
        description.profile description.grammar input sort start stop tree) :
      printScalars? description sort (reify description source) = some (render source) :=
    match source with
    | @DerivesAt.lexical _ _ _ _ _ point row _ formed => by
      change DeclaredConstructorPrinter.print? description.grammar stringScalars (lexicalPrinter description)
        (description.profile.states.get row).resultSort (leaf description row point formed) = some [point]
      have selected : lexicalPrinter description (description.profile.states.get row).resultSort =
          some (fun pattern => (readLeaf? description row pattern).map (· :: [])) := by
        unfold lexicalPrinter
        rw [shape.lexicalUnique row]
        rfl
      have printed : DeclaredConstructorPrinter.print? description.grammar stringScalars (lexicalPrinter description)
          (description.profile.states.get row).resultSort (leaf description row point formed) =
          (readLeaf? description row (leaf description row point formed)).map (· :: []) := by
        unfold leaf wordLeaf
        exact DeclaredConstructorPrinter.print?_lexical _ _ _ _ _ _ _ selected
      rw [printed, readLeaf?_leaf]
      rfl
    | .structural row body => by
      simp only [printScalars?, reify, DeclaredConstructorPrinter.print?, lexicalPrinter,
        shape.structuralSort _ (List.get_mem _ row), Option.map_none,
        shape.constructorUnique _ (List.get_mem _ row)]
      exact printItems_reify description shape body
    termination_by structural source

  theorem printItems_reify (description : Description) (shape : Shape description)
      {rule : GrammarRule} {items : List SyntaxItem} {start stop : Nat} {children : List CST}
      (source : ItemsDeriveAt (fun text => some (stringScalars text))
        description.profile description.grammar input rule items start stop children) :
      DeclaredConstructorPrinter.printItems? description.grammar stringScalars (lexicalPrinter description)
        rule items (reifyItems description source) = some (renderItems source) :=
    match source with
    | .nil => by simp [DeclaredConstructorPrinter.printItems?, reifyItems, renderItems]
    | .terminal decoded _ rest => by
      simp only [Option.some.injEq] at decoded
      simp [DeclaredConstructorPrinter.printItems?, reifyItems,
        printItems_reify description shape rest, renderItems, ← decoded]
    | .nonterminal lookup head rest => by
      simp only [DeclaredConstructorPrinter.printItems?, reifyItems, lookup]
      have first := print_reify description shape head
      simp only [printScalars?] at first
      simp [first, printItems_reify description shape rest, renderItems]
    termination_by structural source
end

theorem full_scalars (description : Description) (shape : Shape description) {sort : String} {tree : CST}
    (source : DerivesAt (fun text => some (stringScalars text)) description.profile description.grammar input
      sort 0 input.length tree) : printScalars? description sort (reify description source) = some input := by
  rw [print_reify description shape source, full_source source]

theorem full_text (description : Description) (shape : Shape description) {text sort : String} {tree : CST}
    (source : DerivesAt (fun text => some (stringScalars text)) description.profile description.grammar (stringScalars text)
      sort 0 (stringScalars text).length tree) : printText? description sort (reify description source) = some text := by
  simp only [printText?, full_scalars description shape source, Option.map_some]
  congr 1
  simp [stringScalars, List.map_map, Function.comp_def]

#print axioms print_reify
#print axioms printItems_reify
#print axioms full_scalars
#print axioms full_text

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
