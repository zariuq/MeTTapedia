import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-! An identity-symbol map observes membership of the four declaration lists.
Order and positions remain in the exact source and target values. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

structure DeclarationInclusion (source target : LanguageDef) : Prop where
  types : source.types ⊆ target.types
  terms : source.terms ⊆ target.terms
  equations : source.equations ⊆ target.equations
  rewrites : source.rewrites ⊆ target.rewrites

namespace StructuralMorphism

/-- Keep the original symbols and carry each declaration to its occurrence as
an element of the target list. -/
abbrev ofDeclarationInclusion {source target : ValidatedLanguageDef}
    (included : DeclarationInclusion source.language target.language) :
    StructuralMorphism source target where
  symbols := LanguageDefSymbolMap.id
  mapsTypes _ member := by
    rw [mapTypeDecl_id]
    exact included.types member
  mapsTerms _ member := by
    rw [mapGrammarRule_id]
    exact included.terms member
  mapsEquations _ member := by
    rw [Mettapedia.GSLT.LanguageDef.mapEquation_id]
    exact included.equations member
  mapsRewrites _ member := by
    rw [mapRewriteRule_id]
    exact included.rewrites member

@[simp] theorem ofDeclarationInclusion_symbols {source target : ValidatedLanguageDef}
    (included : DeclarationInclusion source.language target.language) :
    (ofDeclarationInclusion included).symbols = LanguageDefSymbolMap.id := rfl

/-- The identity action determines exactly which declaration inclusions are
available. Each side still names the original language values. -/
theorem declarationInclusion_iff {source target : ValidatedLanguageDef} :
    DeclarationInclusion source.language target.language ↔
      ∃ map : StructuralMorphism source target, map.symbols = LanguageDefSymbolMap.id := by
  constructor
  · intro included
    exact ⟨ofDeclarationInclusion included, rfl⟩
  · rintro ⟨map, same⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro declaration member
      have mapped := map.mapsTypes declaration member
      rw [same, mapTypeDecl_id] at mapped
      exact mapped
    · intro rule member
      have mapped := map.mapsTerms rule member
      rw [same, mapGrammarRule_id] at mapped
      exact mapped
    · intro equation member
      have mapped := map.mapsEquations equation member
      rw [same, Mettapedia.GSLT.LanguageDef.mapEquation_id] at mapped
      exact mapped
    · intro rewrite member
      have mapped := map.mapsRewrites rewrite member
      rw [same, mapRewriteRule_id] at mapped
      exact mapped

end StructuralMorphism
end Mettapedia.GSLT.LanguageDef
