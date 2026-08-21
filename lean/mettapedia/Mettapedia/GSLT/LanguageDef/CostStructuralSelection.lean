import Mettapedia.GSLT.LanguageDef.StructuralSelection
import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

/-!
# Structural selection through Cost transports

Cost elaboration transports patterns through ambient-binder reinsertion and
through finite semantic-atom reification.  These operations preserve every
recursive pattern position, even though their actions on names need not be
injective.  This module reflects selected target positions through those
transports while retaining the exact source context and binder depth.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

namespace Selects

/-- Reflect a selected position through certified ambient-binder
reinsertion.  `holeDepth` is the exact depth accumulated by the source
context, not a depth reconstructed from the target payload. -/
theorem exists_preimage_thickenAmbientBVars
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (depth : Nat) {sourceRoot targetPayload : Pattern}
    {targetContext : OneHoleContext}
    (selected : Selects targetPayload targetContext
      (thinning.thickenAmbientBVars depth sourceRoot)) :
    ∃ sourcePayload sourceContext holeDepth,
      Selects sourcePayload sourceContext sourceRoot ∧
      ContextSubstitution.renameAmbientContextAt thinning.toTargetIndex depth
          sourceContext = (targetContext, holeDepth) ∧
      thinning.thickenAmbientBVars holeDepth sourcePayload = targetPayload := by
  have selected' : Selects targetPayload targetContext
      (ContextSubstitution.renameAmbientBVarsAt thinning.toTargetIndex depth
        sourceRoot) := by
    rw [← thinning.thickenAmbientBVars_eq_renameAmbientBVarsAt]
    exact selected
  obtain ⟨sourcePayload, sourceContext, holeDepth, sourceSelected,
      contextEquality, payloadEquality⟩ :=
    Selects.exists_preimage_renameAmbientBVarsAt thinning.toTargetIndex depth
      selected'
  exact ⟨sourcePayload, sourceContext, holeDepth, sourceSelected,
    contextEquality, by
      rw [thinning.thickenAmbientBVars_eq_renameAmbientBVarsAt]
      exact payloadEquality⟩

end Selects

namespace CostStaticAtomEnvironment

private theorem object_of_mem_objectList {patterns : List Pattern}
    {pattern : Pattern} (membership : pattern ∈ patterns)
    (objects : WellSorted.isObjectPatternList patterns = true) :
    WellSorted.isObjectPattern pattern = true := by
  induction patterns with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      simp only [WellSorted.isObjectPatternList, Bool.and_eq_true] at objects
      simp only [List.mem_cons] at membership
      rcases membership with rfl | inTail
      · exact objects.1
      · exact inductionHypothesis inTail objects.2

/-- Environment reification is exactly structural free-variable renaming. -/
@[simp]
theorem reify_eq_renameFVars
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ∀ pattern,
      environment.reify pattern =
        Pattern.renameFVars environment.reifyName pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [reify, Pattern.renameFVars]
  | hfvar name => simp [reify, Pattern.renameFVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [reify, Pattern.renameFVars, Pattern.apply.injEq, true_and]
      exact List.map_congr_left inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simp [reify, Pattern.renameFVars, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [reify, Pattern.renameFVars, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [reify, Pattern.renameFVars, bodyInduction, replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [reify, Pattern.renameFVars, Pattern.collection.injEq,
        true_and, and_true]
      exact List.map_congr_left inductionHypothesis

/-- Every free-variable name in the reification of an object pattern comes
from an original free-variable name.  The object premise excludes collection
tails, which are metavariable names and are intentionally not reified. -/
theorem exists_originalName_of_mem_freeFvarNames_reify_of_object
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ∀ (pattern : Pattern), WellSorted.isObjectPattern pattern = true →
      ∀ {name}, name ∈ (environment.reify pattern).freeFvarNames →
        ∃ originalName, originalName ∈ pattern.freeFvarNames ∧
          environment.reifyName originalName = name := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro object name membership
      rw [environment.reify_eq_renameFVars] at membership
      simp [Pattern.renameFVars, Pattern.freeFvarNames] at membership
  | hfvar originalName =>
      intro object name membership
      rw [environment.reify_eq_renameFVars] at membership
      simp [Pattern.renameFVars, Pattern.freeFvarNames] at membership
      exact ⟨originalName, by simp [Pattern.freeFvarNames], membership.symm⟩
  | happly constructor arguments inductionHypothesis =>
      intro object name membership
      simp only [CostStaticAtomEnvironment.reify, Pattern.freeFvarNames,
        List.mem_flatMap] at membership ⊢
      obtain ⟨reifiedArgument, reifiedMembership, nameMembership⟩ := membership
      obtain ⟨argument, argumentMembership, argumentEq⟩ :=
        List.mem_map.mp reifiedMembership
      subst reifiedArgument
      have argumentsObject : WellSorted.isObjectPatternList arguments = true := by
        simpa [WellSorted.isObjectPattern] using object
      have argumentObject : WellSorted.isObjectPattern argument = true :=
        object_of_mem_objectList argumentMembership argumentsObject
      obtain ⟨originalName, originalMembership, reifiedName⟩ :=
        inductionHypothesis argument argumentMembership argumentObject
          nameMembership
      exact ⟨originalName, ⟨argument, argumentMembership, originalMembership⟩,
        reifiedName⟩
  | hlambda binder body inductionHypothesis =>
      intro object name membership
      rw [environment.reify_eq_renameFVars] at membership
      simp only [Pattern.renameFVars, Pattern.freeFvarNames] at membership
      rw [← environment.reify_eq_renameFVars] at membership
      obtain ⟨originalName, originalMembership, reifiedName⟩ :=
        inductionHypothesis (by
          simpa [WellSorted.isObjectPattern] using object) membership
      exact ⟨originalName, by simpa [Pattern.freeFvarNames] using
        originalMembership, reifiedName⟩
  | hmultiLambda arity binders body inductionHypothesis =>
      intro object name membership
      rw [environment.reify_eq_renameFVars] at membership
      simp only [Pattern.renameFVars, Pattern.freeFvarNames] at membership
      rw [← environment.reify_eq_renameFVars] at membership
      obtain ⟨originalName, originalMembership, reifiedName⟩ :=
        inductionHypothesis (by
          simpa [WellSorted.isObjectPattern] using object) membership
      exact ⟨originalName, by simpa [Pattern.freeFvarNames] using
        originalMembership, reifiedName⟩
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro object
      simp [WellSorted.isObjectPattern] at object
  | hcollection collectionType elements rest inductionHypothesis =>
      intro object name membership
      have objectParts : rest = none ∧
          WellSorted.isObjectPatternList elements = true := by
        simpa [WellSorted.isObjectPattern] using object
      cases objectParts.1
      simp only [CostStaticAtomEnvironment.reify, Pattern.freeFvarNames,
        Option.toList_none, List.append_nil, List.mem_flatMap] at membership ⊢
      obtain ⟨reifiedElement, reifiedMembership, nameMembership⟩ := membership
      obtain ⟨element, elementMembership, elementEq⟩ :=
        List.mem_map.mp reifiedMembership
      subst reifiedElement
      have elementObject : WellSorted.isObjectPattern element = true :=
        object_of_mem_objectList elementMembership objectParts.2
      obtain ⟨originalName, originalMembership, reifiedName⟩ :=
        inductionHypothesis element elementMembership elementObject nameMembership
      exact ⟨originalName, ⟨element, elementMembership, originalMembership⟩,
        reifiedName⟩

/-- Environment reification acts on the fixed syntax of a one-hole context
by the same free-variable renaming as it acts on patterns. -/
@[simp]
theorem reifyContext_eq_renameFVarsContext
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ∀ context,
      environment.reifyContext context =
        StructuralPatternAction.renameFVarsContext environment.reifyName
          context := by
  intro context
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simp [reifyContext, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | lambda binder inner inductionHypothesis =>
      simp [reifyContext, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp [reifyContext, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp [reifyContext, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp [reifyContext, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp [reifyContext, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]

end CostStaticAtomEnvironment

namespace Selects

/-- Reflect a selected semantic-atom occurrence through one finite atom
environment.  The source spelling is existential because quotient slots may
coalesce distinct source names. -/
theorem exists_preimage_environmentReify
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {sourceRoot targetPayload : Pattern} {targetContext : OneHoleContext}
    (selected : Selects targetPayload targetContext
      (environment.reify sourceRoot)) :
    ∃ sourcePayload sourceContext,
      Selects sourcePayload sourceContext sourceRoot ∧
      environment.reifyContext sourceContext = targetContext ∧
      environment.reify sourcePayload = targetPayload := by
  have selected' : Selects targetPayload targetContext
      (Pattern.renameFVars environment.reifyName sourceRoot) := by
    rw [← environment.reify_eq_renameFVars]
    exact selected
  obtain ⟨sourcePayload, sourceContext, sourceSelected, contextEquality,
      payloadEquality⟩ :=
    Selects.exists_preimage_renameFVars environment.reifyName selected'
  exact ⟨sourcePayload, sourceContext, sourceSelected,
    (environment.reifyContext_eq_renameFVarsContext sourceContext).trans
      contextEquality,
    (environment.reify_eq_renameFVars sourcePayload).trans payloadEquality⟩

end Selects

namespace CostStaticAtomKeyCospan

/-- Direct common-cospan reification is structural free-variable renaming by
the selected endpoint leg. -/
@[simp]
theorem reifyWith_eq_renameFVars
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length) :
    ∀ pattern,
      cospan.reifyWith resolve leg pattern =
        Pattern.renameFVars (cospan.reifyNameWith resolve leg) pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [reifyWith, Pattern.renameFVars]
  | hfvar name => simp [reifyWith_fvar, Pattern.renameFVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [reifyWith, Pattern.renameFVars, Pattern.apply.injEq, true_and]
      exact List.map_congr_left inductionHypothesis
  | hlambda binder body inductionHypothesis =>
      simp [reifyWith, Pattern.renameFVars, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [reifyWith, Pattern.renameFVars, inductionHypothesis]
  | hsubst body replacement bodyInduction replacementInduction =>
      simp [reifyWith, Pattern.renameFVars, bodyInduction,
        replacementInduction]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [reifyWith, Pattern.renameFVars, Pattern.collection.injEq,
        true_and, and_true]
      exact List.map_congr_left inductionHypothesis

/-- Common-cospan context reification uses the same endpoint renaming as its
pattern action. -/
@[simp]
theorem reifyContextWith_eq_renameFVarsContext
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length) :
    ∀ context,
      reifyContextWith cospan resolve leg context =
        StructuralPatternAction.renameFVarsContext
          (cospan.reifyNameWith resolve leg) context := by
  intro context
  induction context with
  | hole => rfl
  | apply constructor before inner after inductionHypothesis =>
      simp [reifyContextWith, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | lambda binder inner inductionHypothesis =>
      simp [reifyContextWith, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | multiLambda arity binders inner inductionHypothesis =>
      simp [reifyContextWith, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | substBody inner replacement inductionHypothesis =>
      simp [reifyContextWith, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | substReplacement body inner inductionHypothesis =>
      simp [reifyContextWith, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]
  | collection collectionType before inner after rest inductionHypothesis =>
      simp [reifyContextWith, StructuralPatternAction.renameFVarsContext,
        inductionHypothesis]

end CostStaticAtomKeyCospan

namespace Selects

/-- Reflect a selected occurrence through one endpoint leg of a common atom
cospan, retaining the exact reified fixed context. -/
theorem exists_preimage_cospanReifyWith
    {leftCount rightCount endpointCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (resolve : String → Option (Fin endpointCount))
    (leg : Fin endpointCount → Fin cospan.commonKeys.length)
    {sourceRoot targetPayload : Pattern} {targetContext : OneHoleContext}
    (selected : Selects targetPayload targetContext
      (cospan.reifyWith resolve leg sourceRoot)) :
    ∃ sourcePayload sourceContext,
      Selects sourcePayload sourceContext sourceRoot ∧
      cospan.reifyContextWith resolve leg sourceContext = targetContext ∧
      cospan.reifyWith resolve leg sourcePayload = targetPayload := by
  have selected' : Selects targetPayload targetContext
      (Pattern.renameFVars (cospan.reifyNameWith resolve leg) sourceRoot) := by
    rw [← cospan.reifyWith_eq_renameFVars]
    exact selected
  obtain ⟨sourcePayload, sourceContext, sourceSelected, contextEquality,
      payloadEquality⟩ :=
    Selects.exists_preimage_renameFVars
      (cospan.reifyNameWith resolve leg) selected'
  exact ⟨sourcePayload, sourceContext, sourceSelected,
    (cospan.reifyContextWith_eq_renameFVarsContext resolve leg sourceContext
      ).trans contextEquality,
    (cospan.reifyWith_eq_renameFVars resolve leg sourcePayload).trans
      payloadEquality⟩

end Selects

/-- Positive canary: exact hole depth is retained beneath both a lambda and
a multiple binder during ambient-binder reinsertion. -/
theorem nestedBinderSelection_holeDepth :
    (ContextSubstitution.renameAmbientContextAt (fun n => n + 1) 0
      (.lambda "x" (.multiLambda 2 ["y", "z"]
        (.apply "pair" [] .hole [])))).2 = 3 := by
  rfl

end Mettapedia.GSLT.LanguageDef
