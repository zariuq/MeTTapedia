import Mettapedia.GSLT.LanguageDef.ModuleFormat.Radix16Scalar
import Mettapedia.GSLT.Parsing.GrammarArgumentLayout
import Mettapedia.GSLT.Parsing.DeclaredConstructorPrinter

/-! A source-syntax core composes authored grammar constructors with the
shared scalar codec. Runtime lowering is a separate projection: this core
retains lexical spelling and source declarations. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Parsing ParserProfileSemantics GrammarArgumentLayout
open DeclaredConstructorPrinter

structure Description where
  grammar : LanguageDef
  profile : ParserProfileLayer
  leafPrefix : String

def scalarRule (labelPrefix : String) (state : LexicalStateDecl) : GrammarRule where
  label := labelPrefix ++ state.resultSort
  category := state.resultSort
  params := [.simple "point" (.base "R16Word24")]
  syntaxPattern := []

def language (description : Description) : LanguageDef :=
  {description.grammar with
    name := description.grammar.name ++ "ScalarCore"
    types := description.grammar.types ++ Radix16Codec.language.types
    terms := description.grammar.terms ++ Radix16Codec.language.terms ++
      description.profile.states.map (scalarRule description.leafPrefix)}

def lexicalRow? (description : Description) (sort : String) : Option (Fin description.profile.states.length) :=
  match (List.finRange description.profile.states.length).filter
      (fun row => (description.profile.states.get row).resultSort == sort) with
  | [row] => some row
  | _ => none

/-- The certificate contains finite facts about the actual declarations.
It assumes no parsing, reification, printing or execution theorem. -/
structure Shape (description : Description) : Prop where
  parameterOrder : ∀ row ∈ description.grammar.terms, parameters? row row.syntaxPattern = some row.params
  notBare : ∀ row ∈ description.grammar.terms, ¬ UsesBareCollection row
  categoryDeclared : ∀ row ∈ description.grammar.terms, row.category ∈ description.grammar.types
  lexicalDeclared : ∀ row : Fin description.profile.states.length,
    (description.profile.states.get row).resultSort ∈ description.grammar.types
  lexicalUnique : ∀ row : Fin description.profile.states.length,
    lexicalRow? description (description.profile.states.get row).resultSort = some row
  structuralSort : ∀ row ∈ description.grammar.terms, lexicalRow? description row.category = none
  constructorUnique : ∀ row ∈ description.grammar.terms,
    constructor? description.grammar row.label row.category = some row

theorem source_rows (description : Description) : description.grammar.terms ⊆ (language description).terms := by
  intro row member
  exact List.mem_append_left _ (List.mem_append_left _ member)

theorem radix_rows (description : Description) : Radix16Codec.language.terms ⊆ (language description).terms := by
  intro row member
  exact List.mem_append_left _ (List.mem_append_right _ member)

def wordLeaf (description : Description) (row : Fin description.profile.states.length)
    (point : Fin (16 ^ 6)) : Pattern :=
  .apply (description.leafPrefix ++ (description.profile.states.get row).resultSort) [Radix16Codec.encode point]

theorem wordLeaf_typed (description : Description) (row : Fin description.profile.states.length)
    (point : Fin (16 ^ 6)) :
    HasType (language description) FreeTypeContext.empty [] (wordLeaf description row point)
      (.base (description.profile.states.get row).resultSort) := by
  have member : scalarRule description.leafPrefix (description.profile.states.get row) ∈ (language description).terms := by
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, List.get_mem _ row, rfl⟩)
  exact .constructor member (by simp [UsesBareCollection, GrammarRule.bareParams, scalarRule])
    (.cons trivial rfl (HasType.of_terms_subset (radix_rows description) (Radix16Codec.encode_typed point)) .nil)

def leaf (description : Description) (row : Fin description.profile.states.length) (point : Nat)
    (formed : description.profile.ClassEvidence (description.profile.states.get row).className point) : Pattern :=
  wordLeaf description row ⟨point, Radix16Scalar.scalar_word_bound point
    (Radix16Scalar.classEvidence_scalar _ _ _ formed)⟩

theorem leaf_typed (description : Description) (row : Fin description.profile.states.length) (point : Nat)
    (formed : description.profile.ClassEvidence (description.profile.states.get row).className point) :
    HasType (language description) FreeTypeContext.empty [] (leaf description row point formed)
      (.base (description.profile.states.get row).resultSort) := wordLeaf_typed _ _ _

def readLeaf? (description : Description) (row : Fin description.profile.states.length) : Pattern → Option Nat
  | .apply label [word] =>
      if label = description.leafPrefix ++ (description.profile.states.get row).resultSort then do
        let point ← Radix16Scalar.decode? word
        if description.profile.ClassEvidence (description.profile.states.get row).className point then some point else none
      else none
  | _ => none

theorem readLeaf?_leaf (description : Description) (row : Fin description.profile.states.length) (point : Nat)
    (formed : description.profile.ClassEvidence (description.profile.states.get row).className point) :
    readLeaf? description row (leaf description row point formed) = some point := by
  have scalar := Radix16Scalar.classEvidence_scalar _ _ _ formed
  have normalized : description.profile.ClassEvidence description.profile.states[row.val].className point := formed
  simp [readLeaf?, leaf, wordLeaf, Radix16Scalar.decode?, Radix16Codec.decode?_encode, scalar, normalized]

#print axioms wordLeaf_typed
#print axioms leaf_typed
#print axioms readLeaf?_leaf

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
