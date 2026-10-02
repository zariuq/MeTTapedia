import Mettapedia.GSLT.LanguageDef.Cost.RegionPositionalAction
import Mettapedia.GSLT.LanguageDef.CostFvarAlignedCanonicalization

/-!
# Original-value round trip for positional retained restoration

The established free-variable alignment transports through symbol mapping,
ambient binder reinsertion and reflective supported substitution. Instantiating
that relation with the positional-to-key projection proves the original-vector
round trip without adding another restoration traversal. Current independent
values still use finite positions; key projection is only a proof device for
the original vector.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A structural free-variable renaming has graph alignment, regardless of
whether distinct names coalesce. -/
theorem FvarAligned.of_renameFVars (rename : String → String) (term : Pattern) :
    FvarAligned (fun first second => second = rename first) term (Pattern.renameFVars rename term) := by
  induction term using Pattern.inductionOn with
  | hbvar index => simpa only [Pattern.renameFVars] using (FvarAligned.bvar index)
  | hfvar name =>
      simp only [Pattern.renameFVars]
      exact .fvar rfl
  | happly constructor arguments ih =>
      rw [Pattern.renameFVars]
      apply FvarAligned.apply
      apply FvarAlignedList.ofForall₂
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      exact ih
  | hlambda binder body ih => simpa only [Pattern.renameFVars] using FvarAligned.lambda binder ih
  | hmultiLambda arity binders body ih =>
      simpa only [Pattern.renameFVars] using FvarAligned.multiLambda arity binders ih
  | hsubst body replacement bodyIH replacementIH =>
      simpa only [Pattern.renameFVars] using FvarAligned.subst bodyIH replacementIH
  | hcollection kind elements rest ih =>
      rw [Pattern.renameFVars]
      apply FvarAligned.collection
      apply FvarAlignedList.ofForall₂
      rw [List.forall₂_map_right_iff, List.forall₂_same]
      exact ih

namespace CostRegionBoundaryEvidence.OccurrenceRestoration
open CostRegionPlanAbstraction

variable {source : CIGSLT} {color : CostStaticColor}
  {targetFree : WellSorted.FreeTypeContext} {occurrences : List CostRegionOccurrence}

/-- Positional access to the existing original vector returns that exact
occurrence's original content, including at repeated keys. -/
theorem get_original_content
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences)
    (slot : Fin table.entries.length) :
    (TypedCostRegionBoundaryTable.Values.get table
      (LanguageDef.TypedCostRegionBoundaryTable.Values.original table) slot).1 =
        (table.entries.get slot).boundary.content := by
  induction table with
  | nil => exact Fin.elim0 slot
  | cons boundary content tail ih =>
      refine Fin.cases ?_ ?_ slot
      · rfl
      · intro tailSlot
        exact ih tailSlot

/-- Original positional values agree with old restoration after projection.
The total unadmitted fallback restores a literal source variable on both sides. -/
theorem original_assignment_projection
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences) (name : String) :
    assignment table (LanguageDef.TypedCostRegionBoundaryTable.Values.original table) name =
      table.restorationAssignment (keyProjection table name) := by
  cases decoded : decodeCostRegionSourceVariableName name with
  | some original =>
      simp only [assignment, keyProjection, decoded, LanguageDef.TypedCostRegionBoundaryTable.restorationAssignment]
  | none =>
      cases selected : OccurrenceTokens.lookup table.entries.length name with
      | none =>
          simp only [assignment, keyProjection, decoded, OccurrenceTokens.assignment, selected,
            LanguageDef.TypedCostRegionBoundaryTable.restorationAssignment_sourceVariable]
      | some slot =>
          simp only [assignment, keyProjection, decoded, OccurrenceTokens.assignment, selected]
          rw [get_original_content,
            table.restorationAssignment_boundaryVariable (table.entries.get slot) (List.get_mem _ _)]

/-- The same projection carries exactly the quote-visible binder support. -/
theorem support_projection
    (table : LanguageDef.TypedCostRegionBoundaryTable source color targetFree occurrences) (name : String) :
    support table name = table.restorationSupport (keyProjection table name) := by
  cases decoded : decodeCostRegionSourceVariableName name with
  | some original =>
      simp only [support, keyProjection, decoded, LanguageDef.TypedCostRegionBoundaryTable.restorationSupport]
  | none =>
      cases selected : OccurrenceTokens.lookup table.entries.length name with
      | none =>
          simp only [support, keyProjection, decoded, OccurrenceTokens.support, selected,
            LanguageDef.TypedCostRegionBoundaryTable.restorationSupport_sourceVariable]
      | some slot =>
          simp only [support, keyProjection, decoded, OccurrenceTokens.support, selected]
          exact (table.restorationSupport_boundaryVariable (table.entries.get slot) (List.get_mem _ _)).symm

end CostRegionBoundaryEvidence.OccurrenceRestoration

namespace CostStaticRegionNode
open CostRegionPlanAbstraction CostRegionBoundaryEvidence.OccurrenceRestoration

variable {source : CIGSLT} {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}

/-- General original-vector restoration on the existing actual node. Its
source skeleton, metadata, scope and binder thinning all come from that node. -/
theorem positionalActAvailable_original (node : CostStaticRegionNode source color targetFree) :
    (node.positionalActAvailable (TypedCostRegionBoundaryTable.Values.original node.boundaryTable)).pattern =
      node.term.1 := by
  have aligned := FvarAligned.of_renameFVars (keyProjection node.boundaryTable)
    (pattern node.plan CostRegionBoundaryEvidence.OccurrenceTokens.token)
  have projected : Pattern.renameFVars (keyProjection node.boundaryTable)
      (pattern node.plan CostRegionBoundaryEvidence.OccurrenceTokens.token) = node.plan.abstractPattern := by
    simpa only [CostStaticRegionNode.boundaryTable] using pattern_projectTokens node.plan
  rw [projected] at aligned
  have thickened := (aligned.mapPattern (color.symbols source)).thickenAmbientBVars node.thinning 0
  have same := thickened.substituteAt_eq source.costWholeReflectionProfile
    (support node.boundaryTable) node.boundaryTable.restorationSupport
    (assignment node.boundaryTable (TypedCostRegionBoundaryTable.Values.original node.boundaryTable))
    node.boundaryTable.restorationAssignment (by
      intro first second related depth
      subst second
      simp only [ReflectiveContextSupport.substituteAt, original_assignment_projection, support_projection])
    node.targetBound.length
  rw [positionalActAvailable_pattern]
  change ReflectiveContextSupport.substituteAt _ _ _ _ _ = _
  rw [same]
  have original := node.restoreMappedSkeleton_eq_term
  simpa only [TypedCostRegionBoundaryTable.restoreSupportedSkeleton,
    ReflectiveContextSupport.substitute, node.skeleton_pattern] using original

end CostStaticRegionNode
end Mettapedia.GSLT.LanguageDef
