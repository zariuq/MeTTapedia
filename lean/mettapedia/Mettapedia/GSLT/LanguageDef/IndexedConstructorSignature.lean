import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Intrinsically sorted generated constructor signatures

Large generated carriers should not repeatedly search a string-valued type
table merely to prove that every constructor row is well sorted.  This module
stores constructor result and parameter sorts as finite indices into the one
authored type list, then proves once that projection to `LanguageDef` passes
the ordinary structural validator whenever type and constructor names are
duplicate-free.

The result is still the ordinary five-field `LanguageDef`; this is an authored
schema for generating it, not a second checker or runtime representation.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace IndexedConstructorSignature

/-- One named parameter whose sort is intrinsically in the supplied type
table. -/
structure Parameter (types : List TypeDecl) where
  name : String
  typeIndex : Fin types.length

/-- One constructor whose result and parameter sorts are intrinsically in the
supplied type table. -/
structure Constructor (types : List TypeDecl) where
  label : String
  categoryIndex : Fin types.length
  params : List (Parameter types)

def Parameter.toTermParam {types : List TypeDecl}
    (parameter : Parameter types) : TermParam :=
  .simple parameter.name (.base (types.get parameter.typeIndex).name)

def Constructor.toGrammarRule {types : List TypeDecl}
    (constructor : Constructor types) : GrammarRule := {
  label := constructor.label
  category := (types.get constructor.categoryIndex).name
  params := constructor.params.map Parameter.toTermParam
  syntaxPattern := []
  evalPolicy? := none
}

/-- Project an intrinsically sorted constructor schema to the ordinary
five-field language definition. -/
def language (name : String) (types : List TypeDecl)
    (constructors : List (Constructor types)) : LanguageDef := {
  name := name
  types := types
  terms := constructors.map Constructor.toGrammarRule
  equations := []
  rewrites := []
}

@[simp]
theorem language_typeNames (name : String) (types : List TypeDecl)
    (constructors : List (Constructor types)) :
    (language name types constructors).typeNames = types.map (·.name) := by
  rfl

@[simp]
theorem language_termLabels (name : String) (types : List TypeDecl)
    (constructors : List (Constructor types)) :
    ((language name types constructors).terms.map (·.label)) =
      constructors.map (·.label) := by
  simp [language, Constructor.toGrammarRule, List.map_map]

private theorem constructor_category_mem
    {name : String} {types : List TypeDecl}
    {constructors : List (Constructor types)}
    (constructor : Constructor types) :
    (Constructor.toGrammarRule constructor).category ∈
      (language name types constructors).typeNames := by
  simp only [Constructor.toGrammarRule, language_typeNames]
  exact List.mem_map.mpr
    ⟨types.get constructor.categoryIndex,
      List.get_mem types constructor.categoryIndex, rfl⟩

private theorem parameter_type_mem
    {name : String} {types : List TypeDecl}
    {constructors : List (Constructor types)}
    (parameter : Parameter types) :
    (types.get parameter.typeIndex).name ∈
      (language name types constructors).typeNames := by
  simp only [language_typeNames]
  exact List.mem_map.mpr
    ⟨types.get parameter.typeIndex,
      List.get_mem types parameter.typeIndex, rfl⟩

/-- Intrinsic sorting reduces full structural validation to the two genuinely
global obligations: unique type names and unique constructor labels. -/
theorem language_validate
    (name : String) (types : List TypeDecl)
    (constructors : List (Constructor types))
    (typeNamesNodup : (types.map (·.name)).Nodup)
    (constructorLabelsNodup : (constructors.map (·.label)).Nodup) :
    (language name types constructors).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  · rfl
  · rfl
  · simpa using typeNamesNodup
  · simpa using constructorLabelsNodup
  · intro term termMembership
    rcases List.mem_map.mp termMembership with
      ⟨constructor, _, rfl⟩
    exact constructor_category_mem constructor
  · intro term termMembership parameter parameterMembership
      typeName typeNameMembership
    rcases List.mem_map.mp termMembership with
      ⟨constructor, _, rfl⟩
    rcases List.mem_map.mp parameterMembership with
      ⟨indexedParameter, _, rfl⟩
    simp only [Parameter.toTermParam, TermParam.typeExpr,
      TypeExpr.baseNames, List.mem_singleton] at typeNameMembership
    subst typeName
    exact parameter_type_mem indexedParameter
  · intro term termMembership
    rcases List.mem_map.mp termMembership with
      ⟨constructor, _, rfl⟩
    exact Or.inl rfl

/-! ## Positive and negative controls -/

namespace Canary

private def types : List TypeDecl := ["indexed:A", "indexed:B"]

private def first : Constructor types := {
  label := "indexed:first"
  categoryIndex := ⟨0, by decide⟩
  params := [{ name := "value", typeIndex := ⟨1, by decide⟩ }]
}

private def second : Constructor types := {
  label := "indexed:second"
  categoryIndex := ⟨1, by decide⟩
  params := []
}

def validLanguage : LanguageDef := language "indexed-canary" types [first, second]

theorem valid_language : validLanguage.validate = [] := by
  apply language_validate <;> decide +kernel

def duplicateConstructorLanguage : LanguageDef :=
  language "indexed-duplicate-constructor" types [first, first]

theorem duplicate_constructor_rejected :
    duplicateConstructorLanguage.validate ≠ [] := by
  intro valid
  have nodup := LanguageDef.constructorLabels_nodup_of_validate_eq_nil
    duplicateConstructorLanguage valid
  simp [duplicateConstructorLanguage, language, first,
    Constructor.toGrammarRule] at nodup

private def duplicateTypes : List TypeDecl := ["indexed:A", "indexed:A"]

def duplicateTypeLanguage : LanguageDef :=
  language "indexed-duplicate-type" duplicateTypes []

theorem duplicate_type_rejected : duplicateTypeLanguage.validate ≠ [] := by
  intro valid
  have nodup := LanguageDef.typeNames_nodup_of_validate_eq_nil
    duplicateTypeLanguage valid
  simp [duplicateTypeLanguage, language, duplicateTypes,
    LanguageDef.typeNames, TypeDecl.plain] at nodup

end Canary

#print axioms language_validate
#print axioms Canary.valid_language
#print axioms Canary.duplicate_constructor_rejected
#print axioms Canary.duplicate_type_rejected

end IndexedConstructorSignature

end Mettapedia.GSLT.LanguageDef
