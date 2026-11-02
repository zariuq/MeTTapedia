import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxPrinting
import Mettapedia.GSLT.Parsing.DeclaredConstructorReifier

/-! Executable CST construction into the retained source core. The source
derivation proves sorting and exact readback, while the published term is
computed from CST data rather than from a proof object. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax PresentationExprSemantics

def lexicalLeaf? (description : Description) (row : Fin description.profile.states.length) : CST → Option Pattern
  | .node label start stop [.terminal [point] before after] =>
      if label = (description.profile.states.get row).ruleLabel ∧ before = start ∧
          after = stop ∧ stop = start + 1 then
        if formed : description.profile.ClassEvidence (description.profile.states.get row).className point then
          some (leaf description row point formed) else none
      else none
  | _ => none

def lexicalDecoder (description : Description) (sort : String) : Option (CST → Option Pattern) :=
  (lexicalRow? description sort).map (lexicalLeaf? description)

def lowerCST? (description : Description) (sort : String) (tree : CST) : Option Pattern :=
  DeclaredConstructorReifier.lower? description.grammar (lexicalDecoder description) sort tree

variable {literalScalars? : String → Option (List Nat)} {input : List Nat}

mutual
  theorem lowerCST_source (description : Description) (shape : Shape description)
      {sort : String} {start stop : Nat} {tree : CST}
      (source : DerivesAt literalScalars? description.profile description.grammar input sort start stop tree) :
      lowerCST? description sort tree = some (reify description source) :=
    match source with
    | @DerivesAt.lexical _ _ _ _ start point row _ formed => by
      change DeclaredConstructorReifier.lower? description.grammar (lexicalDecoder description)
        (description.profile.states.get row).resultSort
          (.node (description.profile.states.get row).ruleLabel start (start + 1)
            [.terminal [point] start (start + 1)]) = some (leaf description row point formed)
      have selected : lexicalDecoder description (description.profile.states.get row).resultSort =
          some (lexicalLeaf? description row) := by
        simp only [lexicalDecoder, shape.lexicalUnique row, Option.map_some]
      rw [DeclaredConstructorReifier.lower?_lexical _ _ _ _ _ _ _ _ selected]
      have normalized : description.profile.ClassEvidence description.profile.states[row.val].className point := formed
      simp [lexicalLeaf?, normalized]
    | .structural row body => by
      simp only [lowerCST?, DeclaredConstructorReifier.lower?, lexicalDecoder,
        shape.structuralSort _ (List.get_mem _ row), Option.map_none,
        shape.constructorUnique _ (List.get_mem _ row)]
      change ((DeclaredConstructorReifier.lowerItems? description.grammar (lexicalDecoder description)
        (description.grammar.terms.get row) (description.grammar.terms.get row).syntaxPattern _).bind
          fun values => some (Pattern.apply (description.grammar.terms.get row).label values)) =
            some (Pattern.apply (description.grammar.terms.get row).label (reifyItems description body))
      rw [lowerCSTItems_source description shape body]
      rfl
    termination_by structural source

  theorem lowerCSTItems_source (description : Description) (shape : Shape description)
      {rule : GrammarRule} {items : List SyntaxItem} {start stop : Nat} {children : List CST}
      (source : ItemsDeriveAt literalScalars? description.profile description.grammar input rule items start stop children) :
      DeclaredConstructorReifier.lowerItems? description.grammar (lexicalDecoder description) rule items children =
        some (reifyItems description source) :=
    match source with
    | .nil => by simp [DeclaredConstructorReifier.lowerItems?, reifyItems]
    | .terminal _ _ rest => by
      simpa only [DeclaredConstructorReifier.lowerItems?, reifyItems] using lowerCSTItems_source description shape rest
    | .nonterminal lookup head rest => by
      have first := lowerCST_source description shape head
      simp only [lowerCST?] at first
      simp [DeclaredConstructorReifier.lowerItems?, lookup, first, lowerCSTItems_source description shape rest, reifyItems]
    termination_by structural source
end

def checkedTerm (description : Description) (shape : Shape description) {sort : String} {start stop : Nat} (tree : CST)
    (source : Nonempty (DerivesAt literalScalars? description.profile description.grammar input sort start stop tree)) :
    ClosedTerm (language description) ⟨sort, by
      obtain ⟨witness⟩ := source
      exact source_sort_declared description shape witness⟩ :=
  ⟨(lowerCST? description sort tree).get (by
      obtain ⟨witness⟩ := source
      rw [lowerCST_source description shape witness]
      rfl), by
    obtain ⟨witness⟩ := source
    have available : (lowerCST? description sort tree).isSome = true := by
      rw [lowerCST_source description shape witness]; rfl
    have same : (lowerCST? description sort tree).get available = reify description witness := by
      apply Option.some.inj
      exact (Option.some_get _).trans (lowerCST_source description shape witness)
    rw [same]
    exact (closedTerm description shape witness).property⟩

theorem checkedTerm_lower (description : Description) (shape : Shape description) {sort : String} {start stop : Nat}
    (tree : CST) (source : Nonempty (DerivesAt literalScalars? description.profile description.grammar input sort start stop tree)) :
    lowerCST? description sort tree = some (checkedTerm description shape tree source).val := (Option.some_get _).symm

#print axioms lowerCST_source
#print axioms lowerCSTItems_source
#print axioms checkedTerm
#print axioms checkedTerm_lower

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
