import Mettapedia.GSLT.LanguageDef.CostRegionTree
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion

/-!
# Typing shapes of certified Cost boundaries

A certified boundary retains a complete target-language typing derivation.
Inverting that derivation exposes the result-type shape forced by the
boundary content, without depending on any particular source language.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

namespace CertifiedCostRegionBoundary

/-- A certified application boundary always inhabits an authored base fibre.
The category is determined by the constructor selected in its retained typing
derivation. -/
theorem exists_targetType_eq_base_of_application
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {targetSupport : List TypeExpr}
    {targetType : TypeExpr} {label : String} {arguments : List Pattern}
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport targetType (.apply label arguments)) :
    ∃ category,
      boundary.typed.boundary.targetType = .base category := by
  have typed := boundary.typed.contentTyped
  rw [boundary.content_eq] at typed
  obtain ⟨rule, _membership, _labelEq, _notBare, typeEq, _argumentsTyped⟩ :=
    hasType_apply_inversion typed
  exact ⟨rule.category, typeEq⟩

/-- A certified collection boundary records the precise typing dichotomy:
either it has a structural collection fibre, or an authored bare-collection
rule gives it a base fibre.  In particular, collection syntax alone does not
justify treating the boundary as base-typed. -/
theorem targetType_collection_or_base_of_collection
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {targetSupport : List TypeExpr}
    {targetType : TypeExpr} {collectionType : CollType}
    {elements : List Pattern} {rest : Option String}
    (boundary : CertifiedCostRegionBoundary source color targetFree
      targetSupport targetType (.collection collectionType elements rest)) :
    (∃ elementType,
        boundary.typed.boundary.targetType =
          .collection collectionType elementType) ∨
      (∃ category,
        boundary.typed.boundary.targetType = .base category) := by
  have typed := boundary.typed.contentTyped
  rw [boundary.content_eq] at typed
  rcases hasType_collection_inversion typed with structural | bare
  · obtain ⟨elementType, typeEq, _elementsTyped⟩ := structural
    exact Or.inl ⟨elementType, typeEq⟩
  · obtain ⟨rule, _parameterName, _elementType, _membership,
      _parameterShape, typeEq, _elementsTyped⟩ := bare
    exact Or.inr ⟨rule.category, typeEq⟩

end CertifiedCostRegionBoundary

end Mettapedia.GSLT.LanguageDef
