import Mettapedia.GSLT.LanguageDef.Cost.RegionPlanAbstractionRenaming
import Mettapedia.GSLT.LanguageDef.Cost.RegionPositionalSourceTyping

/-!
# Positional restoration on the actual retained static source fibre

Every existing region node produces a source term in the established finite
profile fibre, using its occurrence tokens. Its metadata and quotation scope
come from the actual plan. The existing mapped/binder-reinserted supported
action then restores any independent current-value vector in the exact target
carrier. This construction alone does not identify normalized occurrence
origins or establish closure of the iterated Cost object.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CostStaticRegionNode
open Mettapedia.OSLF.MeTTaIL.Syntax
open CostRegionPlanAbstraction
open CostRegionBoundaryEvidence.OccurrenceRestoration

variable {source : CIGSLT} {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}

/-- The existing source fibre, populated from the real plan using exact finite
occurrence names. Choice selects only a typing proof, not a normal form. -/
noncomputable def positionalSourceTerm (node : CostStaticRegionNode source color targetFree) :
    CostStaticSourceTerm source color (sourceContext node.boundaryTable) (support node.boundaryTable)
      node.sourceBound node.targetBound node.sourceSort := by
  have typedSafe := positional_supportedSafe node.plan
  let typed := Classical.choose typedSafe
  have safe := Classical.choose_spec typedSafe
  let term : ReflectiveWellSorted.OpenTerm source.reflection.1
      source.theory.presentation.presentation.language (sourceContext node.boundaryTable)
      node.sourceBound node.sourceSort :=
    ⟨pattern node.plan CostRegionBoundaryEvidence.OccurrenceTokens.token,
      ⟨typed.toHasType,
      (pattern_canonicalBinderMetadata node.plan).trans
        (node.plan.abstractPattern_canonicalBinderMetadata node.term.2.2.1),
      (pattern_isObjectPattern node.plan).trans (node.plan.abstractPattern_object node.term.2.2.2.1),
      typed.toHasType.isWellScopedAt⟩,
      by
        intro declaration membership
        rw [pattern_binderSafeAt]
        exact node.plan.abstractPattern_reflectiveScopeSafeAt declaration membership⟩
  exact ⟨term, typed, safe⟩

@[simp] theorem positionalSourceTerm_pattern (node : CostStaticRegionNode source color targetFree) :
    node.positionalSourceTerm.term.1 =
      pattern node.plan CostRegionBoundaryEvidence.OccurrenceTokens.token := rfl

/-- Restore independent current occurrences through the established action,
retaining the node's complete target binder context and empty sealed suffix. -/
noncomputable def positionalActAvailable (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree node.boundaryTable) :
    WellSorted.AvailableOpenPattern source.costWholeReflectionProfile source.costWholeLanguage
      targetFree node.targetBound [] (.base (color.mapLangSort source node.sourceSort).1) :=
  node.positionalSourceTerm.actAvailable node.thinning
    (sourceSupportedAssignment node.boundaryTable node.plan.boundaryTable_fiberCoherent values) rfl rfl

/-- The action's readout is exactly the common positional fold followed by
existing static mapping, binder reinsertion and reflective substitution. -/
@[simp] theorem positionalActAvailable_pattern (node : CostStaticRegionNode source color targetFree)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree node.boundaryTable) :
    (node.positionalActAvailable values).pattern =
      ReflectiveContextSupport.substitute source.costWholeReflectionProfile
        (support node.boundaryTable) (assignment node.boundaryTable values) node.targetBound
        (node.thinning.thickenAmbientBVars 0
          (mapPattern (color.symbols source)
            (pattern node.plan CostRegionBoundaryEvidence.OccurrenceTokens.token))) := rfl

end Mettapedia.GSLT.LanguageDef.CostStaticRegionNode
