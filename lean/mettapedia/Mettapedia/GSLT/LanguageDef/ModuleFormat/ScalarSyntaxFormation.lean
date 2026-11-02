import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxPrinting
import Mettapedia.GSLT.Parsing.DeclaredPrinterTotality

/-! Source-core formation is stated from grammar rows, parameter sorts and
lexical class membership. Every formed term prints through the declared
printer; formation does not assume that the printer has already succeeded. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing DeclaredConstructorPrinter

mutual
  inductive Formed (description : Description) : String → Pattern → Prop where
    | scalar (row : Fin description.profile.states.length) (point : Nat)
        (allowed : description.profile.ClassEvidence (description.profile.states.get row).className point) :
        Formed description (description.profile.states.get row).resultSort (leaf description row point allowed)
    | constructor (row : Fin description.grammar.terms.length) (children : List Pattern)
        (arguments : ArgumentsFormed description (description.grammar.terms.get row).params children) :
        Formed description (description.grammar.terms.get row).category
          (.apply (description.grammar.terms.get row).label children)

  inductive ArgumentsFormed (description : Description) : List TermParam → List Pattern → Prop where
    | nil : ArgumentsFormed description [] []
    | cons {name sort : String} {first : Pattern} {parameters : List TermParam} {children : List Pattern}
        (head : Formed description sort first) (tail : ArgumentsFormed description parameters children) :
        ArgumentsFormed description (.simple name (.base sort) :: parameters) (first :: children)
end

theorem constructor_formed (description : Description) (row : Fin description.grammar.terms.length)
    (sort label : String) (parameters : List TermParam) (children : List Pattern)
    (signature : ((description.grammar.terms.get row).category, (description.grammar.terms.get row).label,
      (description.grammar.terms.get row).params) = (sort, label, parameters))
    (arguments : ArgumentsFormed description parameters children) :
    Formed description sort (.apply label children) := by
  have categoryEq : (description.grammar.terms.get row).category = sort := congrArg Prod.fst signature
  have labelEq : (description.grammar.terms.get row).label = label := congrArg (fun entry => entry.2.1) signature
  have parametersEq : (description.grammar.terms.get row).params = parameters := congrArg (fun entry => entry.2.2) signature
  have actual : ArgumentsFormed description (description.grammar.terms.get row).params children := by
    rw [parametersEq]; exact arguments
  have built := Formed.constructor row children actual
  simpa only [categoryEq, labelEq] using built

theorem formed_prints (description : Description) (shape : Shape description)
    {sort : String} {pattern : Pattern} (formed : Formed description sort pattern) :
    ∃ text, printScalars? description sort pattern = some text := by
  induction formed using Formed.rec
    (motive_2 := fun parameters children _ =>
      List.Forall₂ (ArgumentPrintable description.grammar LanguageDefScalarPrinter.stringScalars
        (lexicalPrinter description)) parameters children) with
  | scalar row point allowed =>
    have selected : lexicalPrinter description (description.profile.states.get row).resultSort =
        some (fun pattern => (readLeaf? description row pattern).map (· :: [])) := by
      simp only [lexicalPrinter, shape.lexicalUnique row, Option.map_some]
    refine ⟨[point], ?_⟩
    unfold printScalars? leaf wordLeaf
    rw [print?_lexical _ _ _ _ _ _ _ selected]
    change (readLeaf? description row (leaf description row point allowed)).map (· :: []) = _
    rw [readLeaf?_leaf]
    rfl
  | constructor row children arguments ih =>
    unfold printScalars?
    rw [print?_structural _ _ _ _ _ _ _
      (by simp only [lexicalPrinter, shape.structuralSort _ (List.get_mem _ row), Option.map_none])
      (shape.constructorUnique _ (List.get_mem _ row))]
    exact items_total _ _ _ _ _ _ _ (shape.parameterOrder _ (List.get_mem _ row)) ih
  | nil => exact .nil
  | @cons name sort first parameters children head tail printed later =>
    exact .cons ⟨name, sort, rfl, printed⟩ later

theorem formed_prints_text (description : Description) (shape : Shape description)
    {sort : String} {pattern : Pattern} (formed : Formed description sort pattern) :
    ∃ text, printText? description sort pattern = some text := by
  obtain ⟨points, printed⟩ := formed_prints description shape formed
  exact ⟨String.ofList (points.map Char.ofNat), by simp [printText?, printed]⟩

#print axioms formed_prints
#print axioms formed_prints_text

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
