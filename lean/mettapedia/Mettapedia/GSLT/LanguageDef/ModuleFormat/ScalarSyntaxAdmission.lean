import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxReader
import Mettapedia.GSLT.Parsing.GrammarArgumentLayoutLaws

/-! Finite admission of a source-syntax description. The same checker is
used for imported modules and runtime grammar data; it checks declaration
facts and constructs the existing parser/shape certificates. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing GrammarArgumentLayout DeclaredConstructorPrinter

def checkShape (description : Description) : Bool :=
  description.grammar.terms.all (fun row =>
    decide (parameters? row row.syntaxPattern = some row.params) &&
    decide (row.category ∈ description.grammar.types) &&
    decide (lexicalRow? description row.category = none) &&
    decide (constructor? description.grammar row.label row.category = some row)) &&
  (List.finRange description.profile.states.length).all (fun row =>
    decide ((description.profile.states.get row).resultSort ∈ description.grammar.types) &&
    decide (lexicalRow? description (description.profile.states.get row).resultSort = some row))

theorem checkShape_exact (description : Description) : checkShape description = true ↔ Shape description := by
  simp only [checkShape, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_finRange, forall_true_left]
  constructor
  · rintro ⟨structural,lexical⟩
    have ordered : ∀ row ∈ description.grammar.terms, parameters? row row.syntaxPattern = some row.params :=
      fun row member => ((structural row member).1.1).1
    refine ⟨ordered,fun row member => not_bare_of_parameters row (ordered row member),?_,?_,?_,?_,?_⟩
    · exact fun row member => ((structural row member).1.1).2
    · exact fun row => (lexical row).1
    · exact fun row => (lexical row).2
    · exact fun row member => (structural row member).1.2
    · exact fun row member => (structural row member).2
  · intro shape
    exact ⟨fun row member => ⟨⟨⟨shape.parameterOrder row member,shape.categoryDeclared row member⟩,
      shape.structuralSort row member⟩,shape.constructorUnique row member⟩,
      fun row => ⟨shape.lexicalDeclared row,shape.lexicalUnique row⟩⟩

structure Admitted (description : Description) where
  parser : Parser description
  shape : Shape description

def admit? (description : Description) : Option (Admitted description) := do
  let parser ← compileParser? description
  if checked : checkShape description = true then
    some ⟨parser,(checkShape_exact description).mp checked⟩
  else none

theorem admit?_isSome (description : Description) :
    (admit? description).isSome = true ↔
      (compileParser? description).isSome = true ∧ Shape description := by
  cases parser : compileParser? description with
  | none => simp [admit?,parser]
  | some parser =>
      by_cases checked : checkShape description = true
      · simp [admit?,parser,checked,(checkShape_exact description).mp checked]
      · simp [admit?,parser,checked,← checkShape_exact description]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
