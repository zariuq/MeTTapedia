import Mathlib.CategoryTheory.Functor.Basic
import Mettapedia.OSLF.Framework.CarrierUniverseSignature

/-!
# Functoriality of the per-carrier universe signature

A structural language map sends the two universe codes at carrier `X`
to the corresponding codes at the mapped carrier.  The reversible generated
namespace extends this action to all constructor strings while fixing foreign
names.  This supplies an ordinary structural morphism between the generated
signatures and proves identity and composition on the nose.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open CategoryTheory

namespace CarrierUniverseSignature

/-- Map generated universe-code labels by a carrier-name action; preserve
every label outside the generated namespace. -/
def mapLabel (sortMap : String → String) (name : String) : String :=
  match decode? name with
  | some (code, carrier) => label code (sortMap carrier)
  | none => name

@[simp]
theorem mapLabel_label (sortMap : String → String)
    (code : Code) (carrier : String) :
    mapLabel sortMap (label code carrier) = label code (sortMap carrier) := by
  simp [mapLabel]

@[simp]
theorem mapLabel_id : mapLabel _root_.id = _root_.id := by
  funext name
  cases decoded : decode? name with
  | none => simp [mapLabel, decoded]
  | some entry =>
      rcases entry with ⟨code, carrier⟩
      rw [show name = label code carrier by
        exact (label_of_decode_eq_some decoded).symm]
      simp

@[simp]
theorem mapLabel_comp (first second : String → String) :
    mapLabel (second ∘ first) = mapLabel second ∘ mapLabel first := by
  funext name
  cases decoded : decode? name with
  | none => simp [mapLabel, decoded]
  | some entry =>
      rcases entry with ⟨code, carrier⟩
      rw [show name = label code carrier by
        exact (label_of_decode_eq_some decoded).symm]
      simp

/-- Symbol action induced on the standalone universe-code signature. -/
def symbols (sourceSymbols : PresentationSymbols) : PresentationSymbols where
  sort := sourceSymbols.sort
  constructor := mapLabel sourceSymbols.sort
  relation := sourceSymbols.relation
  equation := sourceSymbols.equation
  rewrite := sourceSymbols.rewrite

@[simp]
theorem symbols_id : symbols PresentationSymbols.id = PresentationSymbols.id := by
  ext name <;> simp [symbols, PresentationSymbols.id]

@[simp]
theorem symbols_comp (first second : PresentationSymbols) :
    symbols (PresentationSymbols.comp first second) =
      PresentationSymbols.comp (symbols first) (symbols second) := by
  ext name <;> simp [symbols, PresentationSymbols.comp]

@[simp]
theorem map_rule (sourceSymbols : PresentationSymbols)
    (code : Code) (carrier : String) :
    mapGrammarRule (symbols sourceSymbols) (rule code carrier) =
      rule code (sourceSymbols.sort carrier) := by
  cases code <;>
    simp only [mapGrammarRule, symbols, rule, mapLabel_label, List.map_nil]

/-- A mapped authored carrier name remains an authored carrier name. -/
theorem mapped_typeName_mem
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {carrier : String}
    (membership : carrier ∈ source.language.typeNames) :
    morphism.symbols.sort carrier ∈ target.language.typeNames := by
  obtain ⟨declaration, declarationMembership, declarationName⟩ :=
    List.mem_map.mp membership
  have mappedMembership :=
    morphism.mapsTypes declaration declarationMembership
  apply List.mem_map.mpr
  refine ⟨mapTypeDecl morphism.symbols declaration, mappedMembership, ?_⟩
  simpa [mapTypeDecl] using congrArg morphism.symbols.sort declarationName

/-- Structural map between generated universe-code signatures. -/
def mapMorphism
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) :
    StructuralMorphism (validatedLanguage source) (validatedLanguage target) where
  symbols := symbols morphism.symbols
  mapsTypes declaration membership := by
    exact morphism.mapsTypes declaration membership
  mapsTerms declaration membership := by
    change declaration ∈ terms source at membership
    change mapGrammarRule (symbols morphism.symbols) declaration ∈ terms target
    unfold terms termsFor at membership ⊢
    obtain ⟨carrier, carrierMembership, localMembership⟩ :=
      List.mem_flatMap.mp membership
    have localCases : declaration = rule .star carrier ∨
        declaration = rule .box carrier := by
      simpa using localMembership
    rcases localCases with rfl | rfl
    · apply List.mem_flatMap.mpr
      refine ⟨morphism.symbols.sort carrier,
        mapped_typeName_mem morphism carrierMembership, ?_⟩
      simp [map_rule]
    · apply List.mem_flatMap.mpr
      refine ⟨morphism.symbols.sort carrier,
        mapped_typeName_mem morphism carrierMembership, ?_⟩
      simp [map_rule]
  mapsEquations equation membership := by
    exact (List.not_mem_nil membership).elim
  mapsRewrites rewrite membership := by
    exact (List.not_mem_nil membership).elim

/-- Per-carrier universe-code generation is a functor on validated structural
languages. -/
def functor :
    CategoryTheory.Functor ValidatedLanguageDef ValidatedLanguageDef where
  obj := validatedLanguage
  map := mapMorphism
  map_id source := by
    apply StructuralMorphism.ext
    exact symbols_id
  map_comp earlier later := by
    apply StructuralMorphism.ext
    exact symbols_comp earlier.symbols later.symbols

/-! ## Positive and negative controls -/

namespace FunctorCanary

/-- Foreign constructor labels remain outside the generated namespace. -/
theorem foreign_label_fixed (sortMap : String → String) :
    mapLabel sortMap "foreign" = "foreign" := by
  rfl

/-- Carrier renaming acts on both universe-code families. -/
theorem renaming_maps_both_codes (rename : String → String)
    (carrier : String) :
    mapLabel rename (label .star carrier) = label .star (rename carrier) ∧
      mapLabel rename (label .box carrier) = label .box (rename carrier) := by
  simp

/-- The generated map cannot confuse the two universe-code families. -/
theorem mapped_star_ne_mapped_box (rename : String → String)
    (first second : String) :
    mapLabel rename (label .star first) ≠
      mapLabel rename (label .box second) := by
  simp only [mapLabel_label]
  exact star_label_ne_box_label _ _

end FunctorCanary

#print axioms mapLabel_id
#print axioms mapLabel_comp
#print axioms symbols_comp
#print axioms mapped_typeName_mem
#print axioms mapMorphism
#print axioms functor
#print axioms FunctorCanary.foreign_label_fixed
#print axioms FunctorCanary.mapped_star_ne_mapped_box

end CarrierUniverseSignature

end Mettapedia.OSLF.Framework
