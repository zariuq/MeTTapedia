import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
import Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

/-! Original source derivations reify into the composed syntax core with
closed sorting. The construction retains every source constructor and
lexical scalar, independently of a runtime-language lowering. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax PresentationExprSemantics GrammarArgumentLayout

variable {literalScalars? : String → Option (List Nat)} {input : List Nat}

mutual
  def reify (description : Description) {sort : String} {start stop : Nat} {tree : CST} :
      DerivesAt literalScalars? description.profile description.grammar input sort start stop tree → Pattern
    | .lexical row _ formed => leaf description row _ formed
    | .structural row body => .apply (description.grammar.terms.get row).label (reifyItems description body)

  def reifyItems (description : Description) {rule : GrammarRule} {items : List SyntaxItem}
      {start stop : Nat} {children : List CST} :
      ItemsDeriveAt literalScalars? description.profile description.grammar input
        rule items start stop children → List Pattern
    | .nil => []
    | .terminal _ _ rest => reifyItems description rest
    | .nonterminal _ head rest => reify description head :: reifyItems description rest
end

mutual
  theorem reify_typed (description : Description) (shape : Shape description)
      {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt literalScalars? description.profile description.grammar input sort start stop tree) :
      HasType (language description) FreeTypeContext.empty [] (reify description source) (.base sort) :=
    match source with
    | .lexical row _ formed => leaf_typed description row _ formed
    | .structural row body =>
        .constructor (source_rows description (List.get_mem _ row))
          (shape.notBare _ (List.get_mem _ row))
          (reifyItems_typed description shape body (shape.parameterOrder _ (List.get_mem _ row)))
    termination_by structural source

  theorem reifyItems_typed (description : Description) (shape : Shape description)
      {rule : GrammarRule} {items : List SyntaxItem} {start stop : Nat} {children : List CST}
      {expected : List TermParam}
      (source : ItemsDeriveAt literalScalars? description.profile description.grammar input
        rule items start stop children) (layout : parameters? rule items = some expected) :
      ArgumentsHaveTypes (language description) FreeTypeContext.empty [] (reifyItems description source) expected :=
    match source with
    | .nil => by cases layout; exact .nil
    | .terminal _ _ rest => reifyItems_typed description shape rest layout
    | .nonterminal lookup head rest => by
      rename_i actualStop parameter resultSort middle childTree restItems restChildren
      cases tailLayout : parameters? rule restItems with
      | none => simp [parameters?, lookup, tailLayout] at layout
      | some tail =>
          simp [parameters?, lookup, tailLayout] at layout
          subst expected
          exact .cons trivial rfl (reify_typed description shape head)
            (reifyItems_typed description shape rest tailLayout)
    termination_by structural source
end

mutual
  theorem reify_shape (description : Description) {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt literalScalars? description.profile description.grammar input sort start stop tree) :
      isObjectPattern (reify description source) = true ∧
        (reify description source).hasCanonicalBinderMetadata = true :=
    match source with
    | .lexical _ _ _ => ⟨rfl, rfl⟩
    | .structural _ body => reifyItems_shape description body
    termination_by structural source

  theorem reifyItems_shape (description : Description) {rule : GrammarRule} {items : List SyntaxItem}
      {start stop : Nat} {children : List CST}
      (source : ItemsDeriveAt literalScalars? description.profile description.grammar input rule items start stop children) :
      isObjectPatternList (reifyItems description source) = true ∧
        Pattern.hasCanonicalBinderMetadataList (reifyItems description source) = true :=
    match source with
    | .nil => ⟨rfl, rfl⟩
    | .terminal _ _ rest => reifyItems_shape description rest
    | .nonterminal _ head rest => by
      obtain ⟨headObject, headCanonical⟩ := reify_shape description head
      obtain ⟨tailObject, tailCanonical⟩ := reifyItems_shape description rest
      exact ⟨by simp only [reifyItems, isObjectPatternList, headObject, tailObject, Bool.and_self],
        by simp only [reifyItems, Pattern.hasCanonicalBinderMetadataList, headCanonical, tailCanonical, Bool.and_self]⟩
    termination_by structural source
end

theorem source_sort_declared (description : Description) (shape : Shape description)
    {sort : String} {start stop : Nat} {tree : CST}
    (source : DerivesAt literalScalars? description.profile description.grammar input sort start stop tree) :
    sort ∈ (language description).types := by
  have retained : ∀ name : String, name ∈ description.grammar.types → name ∈ (language description).types := by
    intro name member
    change name ∈ (description.grammar.types ++ Radix16Codec.language.types).map TypeDecl.name
    rw [List.map_append]
    exact List.mem_append_left _ member
  cases source with
  | lexical row => exact retained _ (shape.lexicalDeclared row)
  | structural row => exact retained _ (shape.categoryDeclared _ (List.get_mem _ row))

def closedTerm (description : Description) (shape : Shape description)
    {sort : String} {start stop : Nat} {tree : CST}
    (source : DerivesAt literalScalars? description.profile description.grammar input sort start stop tree) :
    ClosedTerm (language description) ⟨sort, source_sort_declared description shape source⟩ :=
  ⟨reify description source, by
    have typed := reify_typed description shape source
    have safe : ScopeSafe (language description) (reify description source) := typed.isWellScopedAt
    obtain ⟨object, canonical⟩ := reify_shape description source
    exact ⟨typed, ground_of_closed_sorting (sort := ⟨sort, source_sort_declared description shape source⟩) typed object safe,
      canonical, object, safe⟩⟩

#print axioms reify_typed
#print axioms reifyItems_typed
#print axioms reify_shape
#print axioms source_sort_declared
#print axioms closedTerm

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
