import Mettapedia.GSLT.LanguageDef.Cost.RegionPlanAbstractionTyping
import Mettapedia.GSLT.LanguageDef.Cost.RegionOccurrenceRestoration

/-!
# Typed source skeletons with independent occurrence tokens

The source free context decodes genuine source parameters and assigns each
existing occurrence token its certified source sort. All naming premises are
proved from finite lookup. Target-fiber compatibility uses the type-image law
already constructed by the actual retained plan; it imposes no equality on
current values at repeated keys.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CostRegionBoundaryEvidence.OccurrenceRestoration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open CostRegionPlanAbstraction

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : WellSorted.FreeTypeContext} {occurrences : List CostRegionOccurrence}

/-- Decode source-variable sorts; read boundary sorts at exact retained positions. -/
def sourceContext (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences) :
    WellSorted.FreeTypeContext :=
  fun name => match decodeCostRegionSourceVariableName name with
    | some original => (targetFree original).bind (CostStaticTypeImage.decode source.theory color)
    | none => (OccurrenceTokens.lookup table.entries.length name).map
        (fun slot => (table.entries.get slot).boundary.type)

@[simp] theorem sourceContext_sourceVariable
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences) (name : String) :
    sourceContext table (costRegionSourceVariableName name) =
      (targetFree name).bind (CostStaticTypeImage.decode source.theory color) := by
  simp only [sourceContext, decodeCostRegionSourceVariableName_encode]

@[simp] theorem sourceContext_token
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences)
    (slot : Fin table.entries.length) :
    sourceContext table (OccurrenceTokens.token slot) = some (table.entries.get slot).boundary.type := by
  simp only [sourceContext, decodeSource_token, OccurrenceTokens.lookup_token, Option.map_some]

/-- Every actual finite token has exactly its table's source sort and target support. -/
theorem token_namesValid
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences) :
    NamesValid table (sourceContext table) (support table) OccurrenceTokens.token := by
  intro slot
  let tableSlot := slot.cast (LanguageDef.TypedCostRegionBoundaryTable.entries_length table).symm
  exact ⟨sourceContext_token table tableSlot, support_token table tableSlot⟩

/-- Construct source typing and reflective support safety for every existing
retained region plan, including nonempty binder support and quotation resets. -/
theorem positional_supportedSafe
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
      sourceAvailable outer term sourceType) :
    ∃ typed : WellSorted.HasTypeWithConstructors source.theory.presentation.presentation.language
        (· ∈ source.continuationRetyping.wrappedLabels)
        (sourceContext plan.boundaryTable) sourceBound
        (pattern plan OccurrenceTokens.token) sourceType,
      typed.toHasType.ReflectiveSupportSafeAt source.reflection.1 (support plan.boundaryTable)
        sourceAvailable (mapTypeExpr (color.symbols source)) := by
  apply pattern_supportedSafe plan (sourceContext plan.boundaryTable) (support plan.boundaryTable)
    _ (support_sourceVariable plan.boundaryTable) OccurrenceTokens.token
    (token_namesValid plan.boundaryTable)
  intro name type lookup
  rw [sourceContext_sourceVariable, lookup]
  exact CostStaticTypeImage.decode_mapTypeExpr source.theory color type

/-- A certified source sort maps back to the real target free context. The
per-entry premise is type-image compatibility, not current-value coherence. -/
theorem map_sourceContext_lookup
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences)
    (coherent : table.FiberCoherent) {name : String} {type : TypeExpr}
    (lookup : sourceContext table name = some type) :
    freeContext table name = some (mapTypeExpr (color.symbols source) type) := by
  cases decoded : decodeCostRegionSourceVariableName name with
  | some original =>
      have boundLookup : (targetFree original).bind (CostStaticTypeImage.decode source.theory color) = some type := by
        simpa only [sourceContext, decoded] using lookup
      obtain ⟨targetType, targetLookup, recovered⟩ := Option.bind_eq_some_iff.mp boundLookup
      have restored := CostStaticTypeImage.mapTypeExpr_decode source.theory color recovered
      simpa only [freeContext, decoded, restored] using targetLookup
  | none =>
      cases selected : OccurrenceTokens.lookup table.entries.length name with
      | none => simp only [sourceContext, decoded, selected, Option.map_none] at lookup; cases lookup
      | some slot =>
          have typeEqual : (table.entries.get slot).boundary.type = type := by
            simpa only [sourceContext, decoded, selected, Option.map_some, Option.some.injEq] using lookup
          have mapped := coherent.typeMap (table.entries.get slot) (List.get_mem _ _)
          rw [typeEqual] at mapped
          simp only [freeContext, decoded, OccurrenceTokens.freeContext, selected, Option.map_some, mapped]

/-- Actual plans construct the target type-image compatibility used above. -/
theorem plan_map_sourceContext_lookup
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
      sourceAvailable outer term sourceType)
    {name : String} {type : TypeExpr} (lookup : sourceContext plan.boundaryTable name = some type) :
    freeContext plan.boundaryTable name = some (mapTypeExpr (color.symbols source) type) :=
  map_sourceContext_lookup plan.boundaryTable plan.boundaryTable_fiberCoherent lookup

/-- The mapped source context is a subcontext of the independently certified
restoration domain. No origin is recovered from an immutable key. -/
theorem mappedSourceContext_lookup
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences)
    (coherent : table.FiberCoherent) {name : String} {type : TypeExpr}
    (lookup : ((sourceContext table).map (color.symbols source)) name = some type) :
    freeContext table name = some type := by
  obtain ⟨sourceType, sourceLookup, rfl⟩ := Option.map_eq_some_iff.mp lookup
  exact map_sourceContext_lookup table coherent sourceLookup

/-- Restrict the constructed restoration assignment to the exact mapped
source context used by static typing transport. -/
def sourceSupportedAssignment
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences)
    (coherent : table.FiberCoherent)
    (values : LanguageDef.TypedCostRegionBoundaryTable.Values source color targetFree table) :
    WellSorted.SupportedOpenAssignment source.costWholeReflectionProfile source.costWholeLanguage
      ((sourceContext table).map (color.symbols source)) targetFree (support table) where
  assignment := assignment table values
  typed := fun lookup => (supportedAssignment table values).typed
    (mappedSourceContext_lookup table coherent lookup)
  canonicalBinderMetadata := fun lookup => (supportedAssignment table values).canonicalBinderMetadata
    (mappedSourceContext_lookup table coherent lookup)
  objectPattern := fun lookup => (supportedAssignment table values).objectPattern
    (mappedSourceContext_lookup table coherent lookup)
  reflectiveScopeSafe := fun lookup => (supportedAssignment table values).reflectiveScopeSafe
    (mappedSourceContext_lookup table coherent lookup)

/-- Map and reinsert the actual planner's source skeleton. The target support
is retained verbatim, including foreign-color binders and quotation resets. -/
theorem positional_mappedThickened_supportedSafe
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr} {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
      sourceAvailable outer term sourceType) :
    ∃ typed : WellSorted.HasType source.costWholeLanguage
        ((sourceContext plan.boundaryTable).map (color.symbols source)) targetBound
        (thinning.thickenAmbientBVars 0
          (mapPattern (color.symbols source) (pattern plan OccurrenceTokens.token)))
        (mapTypeExpr (color.symbols source) sourceType),
      typed.ReflectiveSupportSafeAt source.costWholeReflectionProfile (support plan.boundaryTable)
        sourceAvailable := by
  obtain ⟨sourceTyped, sourceSafe⟩ := positional_supportedSafe plan
  obtain ⟨mappedTyped, mappedSafe⟩ := sourceSafe.mapCostStatic source color sourceTyped.constructorsWithin
  refine ⟨?_, ?_⟩
  · simpa only [List.nil_append, List.length_nil] using
      mappedTyped.thickenAmbientBVars (inner := []) thinning
  · exact (mappedSafe.thickenAmbientBVars (inner := []) thinning).castTyping

end Mettapedia.GSLT.LanguageDef.CostRegionBoundaryEvidence.OccurrenceRestoration
