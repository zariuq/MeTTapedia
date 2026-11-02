import Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter

/-! Compositional equations for printing actual authored constructor rows.
Lexical lookup, row selection and parameter sorts remain explicit. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives

theorem print?_structural (language : LanguageDef) (literal : String → List Nat)
    (lexical : LexicalPrinter) (sort label : String) (children : List Pattern) (row : GrammarRule)
    (structural : lexical sort = none) (selected : constructor? language label sort = some row) :
    print? language literal lexical sort (.apply label children) =
      printItems? language literal lexical row row.syntaxPattern children := by
  rw [print?,structural,selected]
  rfl

theorem print?_unary (language : LanguageDef) (literal : String → List Nat)
    (lexical : LexicalPrinter) (sort label parameter childSort : String) (child : Pattern) (row : GrammarRule)
    (structural : lexical sort = none) (selected : constructor? language label sort = some row)
    (layout : row.syntaxPattern = [.nonTerminal parameter])
    (parameterSort : paramSort? row parameter = some childSort) :
    print? language literal lexical sort (.apply label [child]) = print? language literal lexical childSort child := by
  rw [print?_structural _ _ _ _ _ _ _ structural selected,layout]
  simp [printItems?,parameterSort]

theorem print?_binary (language : LanguageDef) (literal : String → List Nat)
    (lexical : LexicalPrinter) (sort label firstParameter secondParameter firstSort secondSort : String)
    (first second : Pattern) (row : GrammarRule)
    (structural : lexical sort = none) (selected : constructor? language label sort = some row)
    (layout : row.syntaxPattern = [.nonTerminal firstParameter,.nonTerminal secondParameter])
    (firstParameterSort : paramSort? row firstParameter = some firstSort)
    (secondParameterSort : paramSort? row secondParameter = some secondSort) :
    print? language literal lexical sort (.apply label [first,second]) = (do
      let left ← print? language literal lexical firstSort first
      let right ← print? language literal lexical secondSort second
      pure (left ++ right)) := by
  rw [print?_structural _ _ _ _ _ _ _ structural selected,layout]
  simp only [printItems?,firstParameterSort,secondParameterSort,Option.bind_eq_bind,Option.bind_some]
  simp

#print axioms print?_unary
#print axioms print?_binary

end Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter
