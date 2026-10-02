import Mettapedia.GSLT.LanguageDef.Cost.RegionOccurrenceRestoration
import Mettapedia.GSLT.LanguageDef.ReflectiveSupportRenaming

/-!
# Scope and metadata of positional region skeletons

The positional skeleton has the same constructor and binder shape as the
existing retained skeleton. Forgetting finite tokens to their immutable keys
is an actual free-variable renaming. This map need not be injective; it is used
only to transport shape properties, not to reconstruct independent values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CostRegionPlanAbstraction
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

mutual
  theorem pattern_renameFVars {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext} {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr}
      (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
        sourceAvailable outer term sourceType)
      (names : Fin plan.occurrences.length → String) (rename : String → String)
      (sourceNames : ∀ name, rename (costRegionSourceVariableName name) = costRegionSourceVariableName name) :
      Pattern.renameFVars rename (pattern plan names) = pattern plan (fun slot => rename (names slot)) := by
    cases plan with
    | bvar | boundaryApplication | boundaryCollection =>
        simp only [pattern, Pattern.renameFVars]
    | fvar => simp only [pattern, Pattern.renameFVars, sourceNames]
    | application constructor rendered current preimage notBare children =>
        simp only [CostStaticRegionPlan.occurrences] at names ⊢
        simpa only [pattern, Pattern.renameFVars] using
          congrArg (Pattern.apply preimage.sourceConstructor.1.label)
            (arguments_renameFVars children names rename sourceNames)
    | @lambda _ _ _ _ _ binder _ _ _ body =>
        simp only [CostStaticRegionPlan.occurrences] at names ⊢
        simpa only [pattern, Pattern.renameFVars] using
          congrArg (Pattern.lambda binder) (pattern_renameFVars body names rename sourceNames)
    | @multiLambda _ _ _ _ _ arity binders _ _ _ body =>
        simp only [CostStaticRegionPlan.occurrences] at names ⊢
        simpa only [pattern, Pattern.renameFVars] using
          congrArg (Pattern.multiLambda arity binders) (pattern_renameFVars body names rename sourceNames)
    | @collection _ _ _ _ _ kind terms rest type choice selected children =>
        simp only [CostStaticRegionPlan.occurrences] at names ⊢
        simpa only [pattern, Pattern.renameFVars] using
          congrArg (fun body => Pattern.collection kind body (rest.map costRegionSourceVariableName))
            (elements_renameFVars children names rename sourceNames)


  theorem arguments_renameFVars {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext} {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext} {wireName : String}
      {before terms : List Pattern} {parameters : List TermParam}
      (plan : CostStaticArgumentPlan source color targetFree sourceBound targetBound thinning
        sourceAvailable outer wireName before terms parameters)
      (names : Fin plan.occurrences.length → String) (rename : String → String)
      (sourceNames : ∀ name, rename (costRegionSourceVariableName name) = costRegionSourceVariableName name) :
      (arguments plan names).map (Pattern.renameFVars rename) = arguments plan (fun slot => rename (names slot)) := by
    cases plan with
    | nil => rfl
    | cons representation parameterType head tail =>
        simp only [CostStaticArgumentPlan.occurrences] at names ⊢
        simp only [arguments, List.map_cons]
        exact congrArg₂ List.cons
          (pattern_renameFVars (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable) head (fun slot => names (leftSlot head.occurrences tail.occurrences slot)) rename sourceNames)
          (arguments_renameFVars (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable) tail (fun slot => names (rightSlot head.occurrences tail.occurrences slot)) rename sourceNames)


  theorem elements_renameFVars {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext} {sourceBound targetBound : List TypeExpr}
      {thinning : CostStaticBinderThinning source color sourceBound targetBound}
      {sourceAvailable : List TypeExpr} {outer : OneHoleContext} {kind : CollType}
      {before terms : List Pattern} {rest : Option String} {sourceElementType : TypeExpr}
      (plan : CostStaticElementPlan source color targetFree sourceBound targetBound thinning
        sourceAvailable outer kind before terms rest sourceElementType)
      (names : Fin plan.occurrences.length → String) (rename : String → String)
      (sourceNames : ∀ name, rename (costRegionSourceVariableName name) = costRegionSourceVariableName name) :
      (elements plan names).map (Pattern.renameFVars rename) = elements plan (fun slot => rename (names slot)) := by
    cases plan with
    | nil => rfl
    | cons head tail =>
        simp only [CostStaticElementPlan.occurrences] at names ⊢
        simp only [elements, List.map_cons]
        exact congrArg₂ List.cons
          (pattern_renameFVars (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable) head (fun slot => names (leftSlot head.occurrences tail.occurrences slot)) rename sourceNames)
          (elements_renameFVars (sourceBound := sourceBound) (targetBound := targetBound)
            (thinning := thinning) (sourceAvailable := sourceAvailable) tail (fun slot => names (rightSlot head.occurrences tail.occurrences slot)) rename sourceNames)
end

open CostRegionBoundaryEvidence

/-- Forget a finite token to its historical immutable key, preserving genuine
source names. An unadmitted name is tagged as an ordinary source variable,
so later literal restoration keeps it unchanged. This is intentionally not
an occurrence-origin inverse. -/
def keyProjection {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {occurrences : List CostRegionOccurrence}
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences) (name : String) : String :=
  match decodeCostRegionSourceVariableName name with
  | some _ => name
  | none => match OccurrenceTokens.lookup table.entries.length name with
    | some slot => costRegionBoundaryVariableName (table.entries.get slot).boundary
    | none => costRegionSourceVariableName name

@[simp] theorem keyProjection_sourceVariable {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {occurrences : List CostRegionOccurrence}
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences) (name : String) :
    keyProjection table (costRegionSourceVariableName name) = costRegionSourceVariableName name := by
  simp only [keyProjection, decodeCostRegionSourceVariableName_encode]

@[simp] theorem keyProjection_token {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext} {occurrences : List CostRegionOccurrence}
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences)
    (slot : Fin table.entries.length) :
    keyProjection table (OccurrenceTokens.token slot) =
      costRegionBoundaryVariableName (table.entries.get slot).boundary := by
  simp only [keyProjection, OccurrenceRestoration.decodeSource_token, OccurrenceTokens.lookup_token]

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : WellSorted.FreeTypeContext} {sourceBound targetBound : List TypeExpr}
  {thinning : CostStaticBinderThinning source color sourceBound targetBound}
  {sourceAvailable : List TypeExpr} {outer : OneHoleContext} {term : Pattern} {sourceType : TypeExpr}

/-- The genuine positional skeleton maps to the independently defined old
skeleton even when several positions have the same immutable boundary key. -/
theorem pattern_projectTokens
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
      sourceAvailable outer term sourceType) :
    Pattern.renameFVars (keyProjection plan.boundaryTable) (pattern plan OccurrenceTokens.token) =
      plan.abstractPattern := by
  rw [pattern_renameFVars _ _ _ (keyProjection_sourceVariable plan.boundaryTable)]
  have names : (fun slot => keyProjection plan.boundaryTable (OccurrenceTokens.token slot)) = keyNames plan.boundaryTable := by
    funext slot
    let tableSlot := slot.cast (LanguageDef.TypedCostRegionBoundaryTable.entries_length plan.boundaryTable).symm
    exact keyProjection_token plan.boundaryTable tableSlot
  rw [names, pattern_keyNames]

/-- Token choice cannot change binder annotations. -/
theorem pattern_canonicalBinderMetadata
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
      sourceAvailable outer term sourceType) :
    (pattern plan OccurrenceTokens.token).hasCanonicalBinderMetadata =
      plan.abstractPattern.hasCanonicalBinderMetadata := by
  rw [← pattern_projectTokens plan, Pattern.hasCanonicalBinderMetadata_renameFVars]

/-- Token choice cannot create explicit substitutions or collection rests. -/
theorem pattern_isObjectPattern
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
      sourceAvailable outer term sourceType) :
    WellSorted.isObjectPattern (pattern plan OccurrenceTokens.token) =
      WellSorted.isObjectPattern plan.abstractPattern := by
  rw [← pattern_projectTokens plan, WellSorted.isObjectPattern_renameFVars]

/-- Quotation resets and all bound indices are retained exactly. -/
theorem pattern_binderSafeAt
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound thinning
      sourceAvailable outer term sourceType) (quoteConstructor : String) (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt quoteConstructor depth
        (pattern plan OccurrenceTokens.token) =
      Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt quoteConstructor depth plan.abstractPattern := by
  rw [← pattern_projectTokens plan, binderSafeAt_renameFVars]

end Mettapedia.GSLT.LanguageDef.CostRegionPlanAbstraction
