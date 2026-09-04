import Mettapedia.OSLF.Framework.DisplayedContextProfile

/-!
# Structural transport of displayed context profiles

Constructor renaming changes neither free-variable names nor their authored
order.  Sort renaming acts only on the types assigned to those names.  These
laws make the contextual parameter profile of a generated modal constructor
functorial, rather than an opaque recomputation in the target language.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

namespace DisplayedContextProfile

/-- Structural constructor mapping preserves rule-local free-variable
support, including order and multiplicity. -/
theorem mapPattern_preserves_freeFvarNames
    (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    (mapPattern symbols pattern).freeFvarNames = pattern.freeFvarNames := by
  induction pattern using Pattern.inductionOn with
  | hbvar => rfl
  | hfvar => rfl
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map,
        Pattern.freeFvarNames, List.flatMap_map]
      exact List.flatMap_congr inductionHypothesis
  | hlambda => simp_all [mapPattern, Pattern.freeFvarNames]
  | hmultiLambda => simp_all [mapPattern, Pattern.freeFvarNames]
  | hsubst => simp_all [mapPattern, Pattern.freeFvarNames]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map,
        Pattern.freeFvarNames, List.flatMap_map]
      rw [List.flatMap_congr inductionHypothesis]

/-- Structural context mapping preserves the fixed-frame variable support
exactly. -/
theorem externalFreeFvarNames_mapOneHoleContext
    (symbols : LanguageDefSymbolMap) (context : OneHoleContext) :
    externalFreeFvarNames (CIGSLT.mapOneHoleContext symbols context) =
      externalFreeFvarNames context := by
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simp only [CIGSLT.mapOneHoleContext, externalFreeFvarNames,
        List.flatMap_map]
      rw [List.flatMap_congr (fun pattern _ =>
          mapPattern_preserves_freeFvarNames symbols pattern),
        List.flatMap_congr (fun pattern _ =>
          mapPattern_preserves_freeFvarNames symbols pattern),
        inductionHypothesis]
  | lambda binder inner inductionHypothesis =>
      simpa [CIGSLT.mapOneHoleContext, externalFreeFvarNames] using
        inductionHypothesis
  | multiLambda arity binders inner inductionHypothesis =>
      simpa [CIGSLT.mapOneHoleContext, externalFreeFvarNames] using
        inductionHypothesis
  | substBody inner replacement inductionHypothesis =>
      simp [CIGSLT.mapOneHoleContext, externalFreeFvarNames,
        inductionHypothesis,
        mapPattern_preserves_freeFvarNames symbols replacement]
  | substReplacement body inner inductionHypothesis =>
      simp [CIGSLT.mapOneHoleContext, externalFreeFvarNames,
        inductionHypothesis,
        mapPattern_preserves_freeFvarNames symbols body]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp only [CIGSLT.mapOneHoleContext, externalFreeFvarNames,
        List.flatMap_map]
      rw [List.flatMap_congr (fun pattern _ =>
          mapPattern_preserves_freeFvarNames symbols pattern),
        List.flatMap_congr (fun pattern _ =>
          mapPattern_preserves_freeFvarNames symbols pattern),
        inductionHypothesis]

/-- Transported occurrence typing retains exactly the same fixed-context
variable names. -/
theorem variableNames_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typing : DisplayedRewriteTyping source) :
    variableNames (typing.map morphism) = variableNames typing := by
  unfold variableNames
  change (externalFreeFvarNames
      (CIGSLT.mapOneHoleContext morphism.symbols typing.site.context)).eraseDups =
    (externalFreeFvarNames typing.site.context).eraseDups
  rw [externalFreeFvarNames_mapOneHoleContext]

/-- First-match context lookup commutes with structural sort mapping. -/
theorem variableType?_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typing : DisplayedRewriteTyping source) (name : String) :
    variableType? (typing.map morphism) name =
      (variableType? typing name).map
        (mapTypeExpr morphism.symbols) := by
  unfold variableType?
  change FreeTypeContext.ofList
      (DisplayedRewriteSite.map morphism typing.site).rewrite.typeContext name =
    Option.map (mapTypeExpr morphism.symbols)
      (FreeTypeContext.ofList typing.site.rewrite.typeContext name)
  rw [DisplayedRewriteSite.map_rewrite]
  change FreeTypeContext.ofList
      (mapTypeContext morphism.symbols typing.site.rewrite.typeContext) name = _
  rw [FreeTypeContext.ofList_mapTypeContext]
  rfl

/-- The complete fixed-context binding profile maps pointwise in its carrier
coordinate while preserving names and row order. -/
theorem bindings_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typing : DisplayedRewriteTyping source) :
    bindings (typing.map morphism) =
      (bindings typing).map fun binding =>
        (binding.1, mapTypeExpr morphism.symbols binding.2) := by
  unfold bindings
  rw [variableNames_map morphism typing]
  generalize variableNames typing = names
  induction names with
  | nil => rfl
  | cons name names inductionHypothesis =>
      simp only [List.filterMap_cons]
      rw [variableType?_map morphism typing name]
      cases lookup : variableType? typing name with
      | none =>
          simp [inductionHypothesis]
      | some type =>
          simp [inductionHypothesis]

/-- Contextual carrier roots map pointwise under structural sort mapping. -/
theorem carrierTypes_map
    {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (typing : DisplayedRewriteTyping source) :
    carrierTypes (typing.map morphism) =
      (carrierTypes typing).map (mapTypeExpr morphism.symbols) := by
  simp [carrierTypes, bindings_map, List.map_map, Function.comp_def]

/-! ## Positive and negative controls -/

namespace TransportCanary

private def context : OneHoleContext :=
  .apply "displayed-context-transport:pair"
    [.fvar "left"] .hole [.fvar "right"]

private def renameConstructors : LanguageDefSymbolMap where
  sort := _root_.id
  constructor := fun name => "renamed:" ++ name
  relation := _root_.id
  equation := _root_.id
  rewrite := _root_.id

/-- Constructor renaming leaves the contextual parameter support intact. -/
theorem constructor_rename_preserves_external_variables :
    externalFreeFvarNames
        (CIGSLT.mapOneHoleContext renameConstructors context) =
      ["left", "right"] := by
  rw [externalFreeFvarNames_mapOneHoleContext]
  simp [context, externalFreeFvarNames, Pattern.freeFvarNames]

/-- Focus-local variables remain excluded after structural transport. -/
theorem focus_variable_still_absent :
    "focus" ∉ externalFreeFvarNames
      (CIGSLT.mapOneHoleContext renameConstructors context) := by
  rw [externalFreeFvarNames_mapOneHoleContext]
  simp [context, externalFreeFvarNames, Pattern.freeFvarNames]

end TransportCanary

#print axioms mapPattern_preserves_freeFvarNames
#print axioms externalFreeFvarNames_mapOneHoleContext
#print axioms variableNames_map
#print axioms variableType?_map
#print axioms bindings_map
#print axioms carrierTypes_map
#print axioms TransportCanary.constructor_rename_preserves_external_variables
#print axioms TransportCanary.focus_variable_still_absent

end DisplayedContextProfile

end Mettapedia.OSLF.Framework
