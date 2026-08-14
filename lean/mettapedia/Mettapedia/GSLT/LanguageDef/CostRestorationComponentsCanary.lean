import Mettapedia.GSLT.LanguageDef.CostHereditaryTransportAtoms

/-!
# Restoration-component canaries for Cost semantic atoms

Restoration observes the target support and normalized value of an atom.
Complete semantic keys additionally retain source-fibre provenance and target
typing.  These canaries pin the distinction needed when a normalized foreign
boundary becomes a direct source variable.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

private def sourceVariableKey : CostStaticAtomKey where
  sourceType := .base "Name"
  sourceSupport := []
  targetType := .base "Name"
  targetSupport := []
  normal := .fvar "x"

private def boundaryVariableKey : CostStaticAtomKey where
  sourceType := .base "Name"
  sourceSupport := [.base "Proc"]
  targetType := .base "Name"
  targetSupport := []
  normal := .fvar "x"

/-- Two atoms may have exactly the restoration components used by
substitution while retaining different complete semantic keys. -/
theorem restorationComponents_can_agree_when_keys_differ :
    sourceVariableKey.targetSupport = boundaryVariableKey.targetSupport ∧
      sourceVariableKey.normal = boundaryVariableKey.normal ∧
      sourceVariableKey ≠ boundaryVariableKey := by
  decide

/-- A retagged source variable cannot share a complete semantic key with a
boundary that retains nonempty authored support.  In particular, normalized
value equality alone cannot justify common-slot coalescing. -/
theorem sourceFVar_key_ne_boundaryValue_key_of_sourceSupport_ne_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (name : String) (sourceType targetType : TypeExpr)
    (targetLookup : targetFree name = some targetType)
    (decodedType :
      decodeCostStaticTypeExpr source color targetType = some sourceType)
    (boundary : TypedCostRegionBoundary source color targetFree)
    (value : ReflectiveWellSorted.OpenPattern
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      boundary.boundary.targetSupport boundary.boundary.targetType)
    (sourceSupportNonempty : boundary.boundary.support ≠ []) :
    (TypedCostStaticAtom.ofSourceFVar name sourceType targetType targetLookup
        decodedType).key ≠
      (TypedCostStaticAtom.ofBoundaryValue boundary value).key := by
  intro keyEquality
  apply sourceSupportNonempty
  have supportEquality := congrArg CostStaticAtomKey.sourceSupport keyEquality
  simpa [TypedCostStaticAtom.ofSourceFVar,
    TypedCostStaticAtom.ofBoundaryValue] using supportEquality.symm

end Mettapedia.GSLT.LanguageDef
