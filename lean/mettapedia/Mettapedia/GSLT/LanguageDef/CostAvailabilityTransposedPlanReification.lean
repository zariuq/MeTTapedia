import Mettapedia.GSLT.LanguageDef.CostAvailabilityTransposedSemanticAtoms
import Mettapedia.GSLT.LanguageDef.CostCanonicalOccurrenceTraceRecursive
import Mettapedia.GSLT.LanguageDef.CostStaticPlanBoundaryFibers

/-!
# Reifying availability-transposed static-plan skeletons

The static planner retains exact boundary positions, while semantic-atom
environments rename authored parameters into endpoint-local atom names.  This
module gives the structural eliminator between those layers.  Only the two
leaf forms need semantic evidence; every constructor and ordered list spine
is transported without rebuilding or comparing boundary names.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

namespace CostStaticBinderThinning

/-- Erased source-to-target index computation.  It is the total companion of
`targetToSourceIndex?`, depending only on the target context rather than on a
particular intrinsic thinning witness. -/
def sourceToTargetIndex (source : CIGSLT) (color : CostStaticColor) :
    List TypeExpr → Nat → Nat
  | [], index => index
  | targetType :: targetBound, index =>
      match decodeCostStaticTypeExpr source color targetType with
      | none => sourceToTargetIndex source color targetBound index + 1
      | some _ =>
          match index with
          | 0 => 0
          | index + 1 =>
              sourceToTargetIndex source color targetBound index + 1

/-- Intrinsic source-index embedding erases to the target-context-only
computation. -/
theorem toTargetIndex_eq_sourceToTargetIndex
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound)
    (index : Nat) :
    thinning.toTargetIndex index =
      sourceToTargetIndex source color targetBound index := by
  induction thinning generalizing index with
  | nil => rfl
  | mapped sourceType tail inductionHypothesis =>
      cases index <;>
        simp [toTargetIndex, sourceToTargetIndex, inductionHypothesis,
          decodeCostStaticTypeExpr_mapTypeExpr]
  | foreign targetType rejected tail inductionHypothesis =>
      simp [toTargetIndex, sourceToTargetIndex, inductionHypothesis, rejected]

/-- Appending a target-context suffix does not move any decoded source index
already selected from the front. -/
theorem sourceToTargetIndex_append_of_lt
    (source : CIGSLT) (color : CostStaticColor)
    (front suffix : List TypeExpr) {index : Nat}
    (inside : index < (sourceContextOfTarget source color front).length) :
    sourceToTargetIndex source color (front ++ suffix) index =
      sourceToTargetIndex source color front index := by
  induction front generalizing index with
  | nil => simp [sourceContextOfTarget] at inside
  | cons targetType front inductionHypothesis =>
      cases decoded : decodeCostStaticTypeExpr source color targetType with
      | none =>
          simp only [sourceContextOfTarget, decoded] at inside
          simpa [sourceToTargetIndex, decoded] using
            inductionHypothesis inside
      | some sourceType =>
          cases index with
          | zero => simp [sourceToTargetIndex, decoded]
          | succ index =>
              simp only [sourceContextOfTarget, decoded, List.length_cons,
                Nat.succ_lt_succ_iff] at inside
              simpa [sourceToTargetIndex, decoded] using
                inductionHypothesis inside

/-- Proof-relevant specialization of front stability. -/
theorem ofTargetThinning_append_toTargetIndex_of_lt
    (source : CIGSLT) (color : CostStaticColor)
    (front suffix : List TypeExpr) {index : Nat}
    (inside : index < (sourceContextOfTarget source color front).length) :
    (ofTargetThinning source color (front ++ suffix)).toTargetIndex index =
      (ofTargetThinning source color front).toTargetIndex index := by
  rw [toTargetIndex_eq_sourceToTargetIndex,
    toTargetIndex_eq_sourceToTargetIndex]
  exact sourceToTargetIndex_append_of_lt source color front suffix inside

/-- The corresponding local-binder embedding is unchanged on every index
scoped in the decoded prefix. -/
theorem ofTargetThinning_append_embedIndexAt_of_lt
    (source : CIGSLT) (color : CostStaticColor)
    (front suffix : List TypeExpr) (depth index : Nat)
    (inside : index < depth +
      (sourceContextOfTarget source color front).length) :
    (ofTargetThinning source color (front ++ suffix)).embedIndexAt
        depth index =
      (ofTargetThinning source color front).embedIndexAt depth index := by
  unfold embedIndexAt
  by_cases insideDepth : index < depth
  · simp [insideDepth]
  · simp only [if_neg insideDepth]
    congr 1
    apply ofTargetThinning_append_toTargetIndex_of_lt
    omega

/-- Binder reinsertion is therefore prefix-stable on a pattern scoped in the
decoded prefix.  This is the exact thinning law needed when an availability
suffix is moved into a static node's target binder context. -/
theorem thickenAmbientBVars_ofTargetThinning_append_eq_of_scoped
    (source : CIGSLT) (color : CostStaticColor)
    (front suffix : List TypeExpr) (depth : Nat) (pattern : Pattern)
    (wellScoped : pattern.isWellScopedAt
      (depth + (sourceContextOfTarget source color front).length) = true) :
    (ofTargetThinning source color (front ++ suffix)).thickenAmbientBVars
        depth pattern =
      (ofTargetThinning source color front).thickenAmbientBVars
        depth pattern := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      simp only [Pattern.isWellScopedAt, decide_eq_true_eq] at wellScoped
      simpa only [thickenAmbientBVars, Pattern.bvar.injEq] using
        ofTargetThinning_append_embedIndexAt_of_lt source color front suffix
          depth index wellScoped
  | hfvar name => simp [thickenAmbientBVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at wellScoped
      rw [Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
        at wellScoped
      simp only [thickenAmbientBVars, Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership depth
        (wellScoped argument membership)
  | hlambda binder body inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at wellScoped
      simp only [thickenAmbientBVars, Pattern.lambda.injEq, true_and]
      apply inductionHypothesis (depth + 1)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using wellScoped
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at wellScoped
      simp only [thickenAmbientBVars, Pattern.multiLambda.injEq, true_and]
      apply inductionHypothesis (depth + arity)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using wellScoped
  | hsubst body replacement bodyInduction replacementInduction =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at wellScoped
      simp only [thickenAmbientBVars, Pattern.subst.injEq]
      constructor
      · apply bodyInduction (depth + 1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          wellScoped.1
      · exact replacementInduction depth wellScoped.2
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Pattern.isWellScopedAt] at wellScoped
      rw [Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
        at wellScoped
      simp only [thickenAmbientBVars, Pattern.collection.injEq, true_and]
      constructor
      · apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership depth
          (wellScoped element membership)
      · trivial

/-- Propositionally spelling the large target context as a front plus suffix
does not change the prefix-stability result.  Keeping this cast outside a
dependent region node avoids rewriting through the node's typed fields. -/
theorem thickenAmbientBVars_ofTargetThinning_eq_append_of_scoped
    (source : CIGSLT) (color : CostStaticColor)
    (front suffix largeTarget : List TypeExpr)
    (targetEq : largeTarget = front ++ suffix)
    (depth : Nat) (pattern : Pattern)
    (wellScoped : pattern.isWellScopedAt
      (depth + (sourceContextOfTarget source color front).length) = true) :
    (ofTargetThinning source color largeTarget).thickenAmbientBVars
        depth pattern =
      (ofTargetThinning source color front).thickenAmbientBVars
        depth pattern := by
  subst largeTarget
  exact thickenAmbientBVars_ofTargetThinning_append_eq_of_scoped source color
    front suffix depth pattern wellScoped

end CostStaticBinderThinning

namespace ReflectiveContextSupport.AvailabilityTransposedRestoresTogether

mutual
  /-- Applying one binder thinning to both endpoints preserves structural
  availability alignment.  The same positional embedding acts on both bound
  leaves; free-variable restoration certificates are retained verbatim. -/
  def AvailabilityTransposedPatternAligned.thickenAmbientBVars
      {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
      {smallSupport largeSupport : ContextSupport.Support}
      {smallAssignment largeAssignment : ContextSupport.Assignment}
      {ambient : List TypeExpr}
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      (depth : Nat) :
      ∀ {regime small large},
        AvailabilityTransposedPatternAligned profile smallSupport
          smallAssignment largeSupport largeAssignment ambient regime small
            large →
        AvailabilityTransposedPatternAligned profile smallSupport
          smallAssignment largeSupport largeAssignment ambient regime
          (thinning.thickenAmbientBVars depth small)
          (thinning.thickenAmbientBVars depth large)
    | _, _, _, .fvar smallName largeName restores reexposes => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          AvailabilityTransposedPatternAligned.fvar smallName largeName
            restores reexposes
    | regime, _, _, .bvar _ index => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          AvailabilityTransposedPatternAligned.bvar
            (profile := profile) (smallSupport := smallSupport)
            (smallAssignment := smallAssignment)
            (largeSupport := largeSupport)
            (largeAssignment := largeAssignment) (ambient := ambient)
            regime (thinning.embedIndexAt depth index)
    | regime, _, _, .apply _ constructor arguments => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          AvailabilityTransposedPatternAligned.apply regime constructor
            (AvailabilityTransposedPatternAlignedList.thickenAmbientBVars
              thinning depth arguments)
    | regime, _, _, .lambda _ binder body => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          AvailabilityTransposedPatternAligned.lambda regime binder
            (AvailabilityTransposedPatternAligned.thickenAmbientBVars
              thinning (depth + 1) body)
    | regime, _, _, .multiLambda _ arity binders body => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          AvailabilityTransposedPatternAligned.multiLambda regime arity
            binders
            (AvailabilityTransposedPatternAligned.thickenAmbientBVars
              thinning (depth + arity) body)
    | regime, _, _, .subst _ body replacement => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          AvailabilityTransposedPatternAligned.subst regime
            (AvailabilityTransposedPatternAligned.thickenAmbientBVars
              thinning (depth + 1) body)
            (AvailabilityTransposedPatternAligned.thickenAmbientBVars
              thinning depth replacement)
    | regime, _, _, .collection _ collectionType rest elements => by
        simpa only [CostStaticBinderThinning.thickenAmbientBVars] using
          AvailabilityTransposedPatternAligned.collection regime
            collectionType rest
            (AvailabilityTransposedPatternAlignedList.thickenAmbientBVars
              thinning depth elements)

  /-- Listwise companion of common binder thinning. -/
  def AvailabilityTransposedPatternAlignedList.thickenAmbientBVars
      {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
      {smallSupport largeSupport : ContextSupport.Support}
      {smallAssignment largeAssignment : ContextSupport.Assignment}
      {ambient : List TypeExpr}
      {source : CIGSLT} {color : CostStaticColor}
      {sourceBound targetBound : List TypeExpr}
      (thinning : CostStaticBinderThinning source color sourceBound targetBound)
      (depth : Nat) :
      ∀ {regime small large},
        AvailabilityTransposedPatternAlignedList profile smallSupport
          smallAssignment largeSupport largeAssignment ambient regime small
            large →
        AvailabilityTransposedPatternAlignedList profile smallSupport
          smallAssignment largeSupport largeAssignment ambient regime
          (small.map (thinning.thickenAmbientBVars depth))
          (large.map (thinning.thickenAmbientBVars depth))
    | regime, _, _, .nil _ => .nil regime
    | regime, _, _, .cons _ head tail =>
        .cons regime
          (AvailabilityTransposedPatternAligned.thickenAmbientBVars thinning
            depth head)
          (AvailabilityTransposedPatternAlignedList.thickenAmbientBVars
            thinning depth tail)
end

end ReflectiveContextSupport.AvailabilityTransposedRestoresTogether

namespace CostStaticRegionNode

/-- Authored-frame availability alignment transports through the actual Cost
symbol map and the endpoint binder thinnings to the generated target frames.
The large endpoint may append ambient target binders, but scopedness and the
front-stability theorem ensure that no existing bound occurrence is moved. -/
theorem reifyTargetFrame_availabilityTransposedAligned
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (smallNode largeNode : CostStaticRegionNode source color targetFree)
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallNode.boundaryTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeNode.boundaryTable}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallNode.boundaryTable smallValues smallNode.skeleton.1}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeNode.boundaryTable largeValues largeNode.skeleton.1}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
    (targetBoundEq : largeNode.targetBound =
      smallNode.targetBound ++ ambient)
    (sourceAligned :
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
        source.reflection.1
        smallEnvironment.restorationSupport
        smallEnvironment.restorationAssignment
        largeEnvironment.restorationSupport
        largeEnvironment.restorationAssignment ambient regime
        (smallNode.reifiedSourceFrame smallEnvironment).1
        (largeNode.reifiedSourceFrame largeEnvironment).1) :
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      source.costWholeReflectionProfile
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient regime
      (smallNode.reifyTargetFrame smallEnvironment)
      (largeNode.reifyTargetFrame largeEnvironment) := by
  let mapped :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.mapPattern
      (color.symbols source)
      (fun constructor =>
        reflectiveIsQuoteConstructor_mapCostStatic source color constructor)
      sourceAligned
  let smallMappedTerm :=
    (smallNode.reifiedSourceFrame smallEnvironment).toCore.mapCostStatic
      (smallNode.reifiedSourceFrame_supported smallEnvironment) color
  have smallMappedScoped :
      (mapPattern (color.symbols source)
          (smallNode.reifiedSourceFrame smallEnvironment).1).isWellScopedAt
        smallNode.sourceBound.length = true := by
    change
      (mapPattern (color.symbols source)
          (smallNode.reifiedSourceFrame smallEnvironment).toCore.1).isWellScopedAt
        smallNode.sourceBound.length = true
    simpa only [smallMappedTerm, WellSorted.OpenTerm.mapCostStatic_pattern,
      List.length_map] using smallMappedTerm.2.1.isWellScopedAt
  have largeMappedScoped :
      (mapPattern (color.symbols source)
          (largeNode.reifiedSourceFrame largeEnvironment).1).isWellScopedAt
        smallNode.sourceBound.length = true := by
    rw [← mapped.isWellScopedAt_eq smallNode.sourceBound.length]
    exact smallMappedScoped
  have largeThinningEq :
      largeNode.thinning.thickenAmbientBVars 0
          (mapPattern (color.symbols source)
            (largeNode.reifiedSourceFrame largeEnvironment).1) =
        smallNode.thinning.thickenAmbientBVars 0
          (mapPattern (color.symbols source)
            (largeNode.reifiedSourceFrame largeEnvironment).1) := by
    exact
      CostStaticBinderThinning.thickenAmbientBVars_ofTargetThinning_eq_append_of_scoped
        source color smallNode.targetBound ambient largeNode.targetBound
          targetBoundEq 0 _ (by
          simpa only [Nat.zero_add] using largeMappedScoped)
  rw [smallNode.reifyTargetFrame_eq_map_reifiedSourceFrame,
    largeNode.reifyTargetFrame_eq_map_reifiedSourceFrame, largeThinningEq]
  exact
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.thickenAmbientBVars
      smallNode.thinning 0 mapped

end CostStaticRegionNode

namespace CostRegionBoundaryTrees.NormalizedAvailabilitySuffix

/-- Equal positional normal-form vectors identify the exact pair of selected
children.  The finite positions may have different proof components, but
their natural indices must agree. -/
theorem getEntry_normal_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {normalizeStatic : CostStaticRegionNormalizer source}
    {ambient : List TypeExpr} {occurrences : List CostRegionOccurrence}
    {smallTable largeTable : TypedCostRegionBoundaryTable source color
      targetFree occurrences}
    {smallTrees : CostRegionBoundaryTrees source targetFree color smallTable}
    {largeTrees : CostRegionBoundaryTrees source targetFree color largeTable}
    (related : CostRegionBoundaryTrees.NormalizedAvailabilitySuffix
      normalizeStatic ambient smallTable largeTable smallTrees largeTrees)
    (smallPosition : Fin smallTable.entries.length)
    (largePosition : Fin largeTable.entries.length)
    (positionEq : smallPosition.1 = largePosition.1) :
    ((smallTrees.getEntry smallPosition).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern =
      ((largeTrees.getEntry largePosition).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern := by
  rcases related with ⟨tables, normalForms⟩
  induction tables with
  | nil => exact Fin.elim0 smallPosition
  | cons head tail inductionHypothesis =>
      cases smallTrees with
      | cons smallHead smallTail =>
          cases largeTrees with
          | cons largeHead largeTail =>
              simp only [CostRegionBoundaryTrees.normalizedPatterns,
                List.cons.injEq] at normalForms
              induction smallPosition using Fin.cases with
              | zero =>
                  have largeZero : largePosition = ⟨0, by simp⟩ := by
                    apply Fin.ext
                    exact positionEq.symm
                  subst largePosition
                  exact normalForms.1
              | succ smallPrevious =>
                  induction largePosition using Fin.cases with
                  | zero => simp at positionEq
                  | succ largePrevious =>
                      exact inductionHypothesis smallPrevious largePrevious
                        (Nat.succ.inj positionEq) normalForms.2

end CostRegionBoundaryTrees.NormalizedAvailabilitySuffix

namespace CostRegionBoundaryTrees

/-- Looking up an ordered normalized-pattern vector at an actual table
position returns the compact normal form of the proof-relevant child stored
at that position. -/
theorem normalizedPatterns_getElem?_getEntry
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (normalizeStatic : CostStaticRegionNormalizer source)
    (trees : CostRegionBoundaryTrees source targetFree color table)
    (position : Fin table.entries.length) :
    (trees.normalizedPatterns normalizeStatic)[position.1]? =
      some ((trees.getEntry position).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern := by
  induction table with
  | nil =>
      cases trees
      exact Fin.elim0 position
  | cons boundary content tail inductionHypothesis =>
      cases trees with
      | cons head trees =>
          induction position using Fin.cases with
          | zero => rfl
          | succ previous => exact inductionHypothesis trees previous

/-- Equal ordered normal-form vectors identify children at equal positions,
even when the two forests were independently indexed by equal occurrence
lists. -/
theorem getEntry_normal_eq_of_normalizedPatterns_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {normalizeStatic : CostStaticRegionNormalizer source}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    (smallTrees : CostRegionBoundaryTrees source targetFree color smallTable)
    (largeTrees : CostRegionBoundaryTrees source targetFree color largeTable)
    (normalForms : smallTrees.normalizedPatterns normalizeStatic =
      largeTrees.normalizedPatterns normalizeStatic)
    (smallPosition : Fin smallTable.entries.length)
    (largePosition : Fin largeTable.entries.length)
    (positionEq : smallPosition.1 = largePosition.1) :
    ((smallTrees.getEntry smallPosition).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern =
      ((largeTrees.getEntry largePosition).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern := by
  have selected := congrArg (fun patterns => patterns[smallPosition.1]?)
    normalForms
  rw [smallTrees.normalizedPatterns_getElem?_getEntry normalizeStatic
    smallPosition] at selected
  rw [positionEq,
    largeTrees.normalizedPatterns_getElem?_getEntry normalizeStatic
      largePosition] at selected
  exact Option.some.inj selected

end CostRegionBoundaryTrees

namespace CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross

/-- Assemble the heterogeneous forest certificate from the exact planner
table relation and equality of the recursively normalized child selected at
each common position.  This is the positional producer used by a whole-tree
induction; duplicate or coalesced boundary names never enter the statement. -/
theorem of_getEntry_normal_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {normalizeStatic : CostStaticRegionNormalizer source}
    {ambient : List TypeExpr}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallTrees : CostRegionBoundaryTrees source targetFree color smallTable}
    {largeTrees : CostRegionBoundaryTrees source targetFree color largeTable}
    (occurrencesEq : smallOccurrences = largeOccurrences)
    (tables : TypedCostRegionBoundaryTable.AvailabilitySuffix ambient
      (TypedCostRegionBoundaryTable.cast occurrencesEq smallTable) largeTable)
    (normalEq : ∀
        (smallPosition : Fin smallTable.entries.length)
        (largePosition : Fin largeTable.entries.length),
      smallPosition.1 = largePosition.1 →
      ((smallTrees.getEntry smallPosition).tree.normalize
          (normalizeStatic := normalizeStatic)).pattern =
        ((largeTrees.getEntry largePosition).tree.normalize
          (normalizeStatic := normalizeStatic)).pattern) :
    CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      normalizeStatic ambient smallTable largeTable smallTrees largeTrees := by
  have entriesLength : smallTable.entries.length =
      largeTable.entries.length := by
    rw [TypedCostRegionBoundaryTable.entries_length,
      TypedCostRegionBoundaryTable.entries_length, occurrencesEq]
  refine ⟨occurrencesEq, tables, List.ext_getElem? (fun position => ?_)⟩
  by_cases smallInside : position < smallTable.entries.length
  · have largeInside : position < largeTable.entries.length := by
      simpa [entriesLength] using smallInside
    let smallPosition : Fin smallTable.entries.length :=
      ⟨position, smallInside⟩
    let largePosition : Fin largeTable.entries.length :=
      ⟨position, largeInside⟩
    calc
      (smallTrees.normalizedPatterns normalizeStatic)[position]? =
          some ((smallTrees.getEntry smallPosition).tree.normalize
            (normalizeStatic := normalizeStatic)).pattern :=
        smallTrees.normalizedPatterns_getElem?_getEntry normalizeStatic
          smallPosition
      _ = some ((largeTrees.getEntry largePosition).tree.normalize
            (normalizeStatic := normalizeStatic)).pattern := by
        exact congrArg some (normalEq smallPosition largePosition rfl)
      _ = (largeTrees.normalizedPatterns normalizeStatic)[position]? :=
        (largeTrees.normalizedPatterns_getElem?_getEntry normalizeStatic
          largePosition).symm
  · have largeOutside : ¬ position < largeTable.entries.length := by
      simpa [entriesLength] using smallInside
    rw [List.getElem?_eq_none (by
        simpa using smallInside),
      List.getElem?_eq_none (by
        simpa using largeOutside)]

/-- Heterogeneous positional forests still identify the normalized children
selected at equal natural positions.  The proof uses the retained ordered
normal-form vectors directly; it never resolves a serialized boundary name. -/
theorem getEntry_normal_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {normalizeStatic : CostStaticRegionNormalizer source}
    {ambient : List TypeExpr}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallTrees : CostRegionBoundaryTrees source targetFree color smallTable}
    {largeTrees : CostRegionBoundaryTrees source targetFree color largeTable}
    (related : CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      normalizeStatic ambient smallTable largeTable smallTrees largeTrees)
    (smallPosition : Fin smallTable.entries.length)
    (largePosition : Fin largeTable.entries.length)
    (positionEq : smallPosition.1 = largePosition.1) :
    ((smallTrees.getEntry smallPosition).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern =
      ((largeTrees.getEntry largePosition).tree.normalize
        (normalizeStatic := normalizeStatic)).pattern := by
  exact CostRegionBoundaryTrees.getEntry_normal_eq_of_normalizedPatterns_eq
    smallTrees largeTrees related.normalizedPatterns_eq smallPosition
      largePosition positionEq

end CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross

namespace CostStaticAbstractPatternAlignment

mutual
  /-- Interpret an exact abstract-skeleton alignment through two semantic-atom
  environments.  Each callback is indexed by every parameter occurring in
  its conclusion: authored source name, or the paired finite boundary
  positions together with their positional equality. -/
  def reifyAligned
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {smallOccurrences largeOccurrences : List CostRegionOccurrence}
      {smallTable : TypedCostRegionBoundaryTable source color targetFree
        smallOccurrences}
      {largeTable : TypedCostRegionBoundaryTable source color targetFree
        largeOccurrences}
      {smallValues : TypedCostRegionBoundaryTable.Values source color
        targetFree smallTable}
      {largeValues : TypedCostRegionBoundaryTable.Values source color
        targetFree largeTable}
      {smallRoot largeRoot : Pattern}
      {smallInventory : CostStaticParameterInventory source color targetFree
        smallTable smallValues smallRoot}
      {largeInventory : CostStaticParameterInventory source color targetFree
        largeTable largeValues largeRoot}
      (smallEnvironment : CostStaticAtomEnvironment source color targetFree
        smallInventory)
      (largeEnvironment : CostStaticAtomEnvironment source color targetFree
        largeInventory)
      {ambient : List TypeExpr}
      (sourceLeaf : ∀ regime name,
        costRegionSourceVariableName name ∈ smallRoot.freeFvarNames →
        costRegionSourceVariableName name ∈ largeRoot.freeFvarNames →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          source.reflection.1
          smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (.fvar (smallEnvironment.reifyName
            (costRegionSourceVariableName name)))
          (.fvar (largeEnvironment.reifyName
            (costRegionSourceVariableName name))))
      (boundaryLeaf : ∀ regime
          (smallPosition : Fin smallTable.entries.length)
          (largePosition : Fin largeTable.entries.length),
        smallPosition.1 = largePosition.1 →
        CostStaticAvailabilityAt ambient regime
          (smallTable.entries.get smallPosition).boundary.targetSupport
          (largeTable.entries.get largePosition).boundary.targetSupport →
        costRegionBoundaryVariableName
            (smallTable.entries.get smallPosition).boundary ∈
          smallRoot.freeFvarNames →
        costRegionBoundaryVariableName
            (largeTable.entries.get largePosition).boundary ∈
          largeRoot.freeFvarNames →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          source.reflection.1
          smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (.fvar (smallEnvironment.reifyName
            (costRegionBoundaryVariableName
              (smallTable.entries.get smallPosition).boundary)))
          (.fvar (largeEnvironment.reifyName
            (costRegionBoundaryVariableName
              (largeTable.entries.get largePosition).boundary)))) :
      ∀ {regime : CostStaticAvailabilityRegime}
          {smallPattern largePattern : Pattern},
        CostStaticAbstractPatternAlignment smallTable.entries
            largeTable.entries ambient regime smallPattern largePattern →
        (∀ name, name ∈ smallPattern.freeFvarNames →
          name ∈ smallRoot.freeFvarNames) →
        (∀ name, name ∈ largePattern.freeFvarNames →
          name ∈ largeRoot.freeFvarNames) →
          ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
            source.reflection.1
            smallEnvironment.restorationSupport
            smallEnvironment.restorationAssignment
            largeEnvironment.restorationSupport
            largeEnvironment.restorationAssignment ambient regime
            (smallEnvironment.reify smallPattern)
            (largeEnvironment.reify largePattern)
    | _, _, _, .bvar regime index, _, _ => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.bvar
            (profile := source.reflection.1)
            (smallSupport := smallEnvironment.restorationSupport)
            (smallAssignment := smallEnvironment.restorationAssignment)
            (largeSupport := largeEnvironment.restorationSupport)
            (largeAssignment := largeEnvironment.restorationAssignment)
            (ambient := ambient) regime index)
    | _, _, _, .sourceFVar regime name, smallMem, largeMem => by
        simpa only [CostStaticAtomEnvironment.reify] using
          sourceLeaf regime name
            (smallMem _ (by simp [Pattern.freeFvarNames]))
            (largeMem _ (by simp [Pattern.freeFvarNames]))
    | _, _, _, .boundary regime smallPosition largePosition position_eq support,
        smallMem, largeMem => by
        simpa only [CostStaticAtomEnvironment.reify] using
          boundaryLeaf regime smallPosition largePosition position_eq support
            (smallMem _ (by simp [Pattern.freeFvarNames]))
            (largeMem _ (by simp [Pattern.freeFvarNames]))
    | _, _, _, .apply regime constructor arguments, smallMem, largeMem => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.apply
            regime constructor
            (CostStaticAbstractPatternListAlignment.reifyAligned
              smallEnvironment largeEnvironment sourceLeaf boundaryLeaf
              arguments
              (fun name membership => smallMem name (by
                simpa only [Pattern.freeFvarNames] using membership))
              (fun name membership => largeMem name (by
                simpa only [Pattern.freeFvarNames] using membership))))
    | _, _, _, .lambda regime binder body, smallMem, largeMem => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.lambda
            regime binder
            (reifyAligned smallEnvironment largeEnvironment sourceLeaf
              boundaryLeaf body
              (fun name membership => smallMem name (by
                simpa only [Pattern.freeFvarNames] using membership))
              (fun name membership => largeMem name (by
                simpa only [Pattern.freeFvarNames] using membership))))
    | _, _, _, .multiLambda regime arity binders body, smallMem, largeMem => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.multiLambda
            regime arity binders
            (reifyAligned smallEnvironment largeEnvironment sourceLeaf
              boundaryLeaf body
              (fun name membership => smallMem name (by
                simpa only [Pattern.freeFvarNames] using membership))
              (fun name membership => largeMem name (by
                simpa only [Pattern.freeFvarNames] using membership))))
    | _, _, _, .collection regime collectionType rest elements,
        smallMem, largeMem => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.collection
            regime collectionType (rest.map costRegionSourceVariableName)
            (CostStaticAbstractPatternListAlignment.reifyAligned
              smallEnvironment largeEnvironment sourceLeaf boundaryLeaf
              elements
              (fun name membership => smallMem name (by
                simp only [Pattern.freeFvarNames, List.mem_append]
                exact Or.inl membership))
              (fun name membership => largeMem name (by
                simp only [Pattern.freeFvarNames, List.mem_append]
                exact Or.inl membership))))

  /-- Ordered-list companion of `reifyAligned`. -/
  def CostStaticAbstractPatternListAlignment.reifyAligned
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {smallOccurrences largeOccurrences : List CostRegionOccurrence}
      {smallTable : TypedCostRegionBoundaryTable source color targetFree
        smallOccurrences}
      {largeTable : TypedCostRegionBoundaryTable source color targetFree
        largeOccurrences}
      {smallValues : TypedCostRegionBoundaryTable.Values source color
        targetFree smallTable}
      {largeValues : TypedCostRegionBoundaryTable.Values source color
        targetFree largeTable}
      {smallRoot largeRoot : Pattern}
      {smallInventory : CostStaticParameterInventory source color targetFree
        smallTable smallValues smallRoot}
      {largeInventory : CostStaticParameterInventory source color targetFree
        largeTable largeValues largeRoot}
      (smallEnvironment : CostStaticAtomEnvironment source color targetFree
        smallInventory)
      (largeEnvironment : CostStaticAtomEnvironment source color targetFree
        largeInventory)
      {ambient : List TypeExpr}
      (sourceLeaf : ∀ regime name,
        costRegionSourceVariableName name ∈ smallRoot.freeFvarNames →
        costRegionSourceVariableName name ∈ largeRoot.freeFvarNames →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          source.reflection.1
          smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (.fvar (smallEnvironment.reifyName
            (costRegionSourceVariableName name)))
          (.fvar (largeEnvironment.reifyName
            (costRegionSourceVariableName name))))
      (boundaryLeaf : ∀ regime
          (smallPosition : Fin smallTable.entries.length)
          (largePosition : Fin largeTable.entries.length),
        smallPosition.1 = largePosition.1 →
        CostStaticAvailabilityAt ambient regime
          (smallTable.entries.get smallPosition).boundary.targetSupport
          (largeTable.entries.get largePosition).boundary.targetSupport →
        costRegionBoundaryVariableName
            (smallTable.entries.get smallPosition).boundary ∈
          smallRoot.freeFvarNames →
        costRegionBoundaryVariableName
            (largeTable.entries.get largePosition).boundary ∈
          largeRoot.freeFvarNames →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          source.reflection.1
          smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (.fvar (smallEnvironment.reifyName
            (costRegionBoundaryVariableName
              (smallTable.entries.get smallPosition).boundary)))
          (.fvar (largeEnvironment.reifyName
            (costRegionBoundaryVariableName
              (largeTable.entries.get largePosition).boundary)))) :
      ∀ {regime : CostStaticAvailabilityRegime}
          {smallPatterns largePatterns : List Pattern},
        CostStaticAbstractPatternListAlignment smallTable.entries
            largeTable.entries ambient regime smallPatterns largePatterns →
        (∀ name, name ∈ smallPatterns.flatMap Pattern.freeFvarNames →
          name ∈ smallRoot.freeFvarNames) →
        (∀ name, name ∈ largePatterns.flatMap Pattern.freeFvarNames →
          name ∈ largeRoot.freeFvarNames) →
          ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAlignedList
            source.reflection.1
            smallEnvironment.restorationSupport
            smallEnvironment.restorationAssignment
            largeEnvironment.restorationSupport
            largeEnvironment.restorationAssignment ambient regime
            (smallPatterns.map smallEnvironment.reify)
            (largePatterns.map largeEnvironment.reify)
    | _, _, _, .nil regime, _, _ => .nil regime
    | _, _, _, .cons regime head tail, smallMem, largeMem =>
        .cons regime
          (reifyAligned smallEnvironment largeEnvironment sourceLeaf
            boundaryLeaf head
            (fun name membership => smallMem name (by
              simp only [List.flatMap_cons, List.mem_append]
              exact Or.inl membership))
            (fun name membership => largeMem name (by
              simp only [List.flatMap_cons, List.mem_append]
              exact Or.inl membership)))
          (CostStaticAbstractPatternListAlignment.reifyAligned
            smallEnvironment largeEnvironment sourceLeaf boundaryLeaf
            tail
            (fun name membership => smallMem name (by
              simp only [List.flatMap_cons, List.mem_append]
              exact Or.inr membership))
            (fun name membership => largeMem name (by
              simp only [List.flatMap_cons, List.mem_append]
              exact Or.inr membership)))
end

/-- Add one exact occurrence to the head of a pattern list. -/
private def CostStaticFVarListOccurrence.ofHead
    {head : Pattern} {tail : List Pattern}
    (occurrence : CostStaticFVarOccurrence head) :
    CostStaticFVarListOccurrence (head :: tail) where
  position := 0
  occurrence := occurrence

@[simp]
private theorem CostStaticFVarListOccurrence.ofHead_name
    {head : Pattern} {tail : List Pattern}
    (occurrence : CostStaticFVarOccurrence head) :
    (CostStaticFVarListOccurrence.ofHead
      (tail := tail) occurrence).occurrence.name = occurrence.name :=
  rfl

@[simp]
private theorem CostStaticFVarListOccurrence.ofHead_context
    {head : Pattern} {tail : List Pattern}
    (occurrence : CostStaticFVarOccurrence head) :
    (CostStaticFVarListOccurrence.ofHead
      (tail := tail) occurrence).occurrence.context = occurrence.context :=
  rfl

/-- Shift one exact tail occurrence through a newly prepended list member. -/
private def CostStaticFVarListOccurrence.ofTail
    {head : Pattern} {tail : List Pattern}
    (occurrence : CostStaticFVarListOccurrence tail) :
    CostStaticFVarListOccurrence (head :: tail) where
  position := Fin.succ occurrence.position
  occurrence := by simpa using occurrence.occurrence

@[simp]
private theorem CostStaticFVarListOccurrence.ofTail_name
    {head : Pattern} {tail : List Pattern}
    (occurrence : CostStaticFVarListOccurrence tail) :
    (CostStaticFVarListOccurrence.ofTail
      (head := head) occurrence).occurrence.name =
        occurrence.occurrence.name := by
  rfl

@[simp]
private theorem CostStaticFVarListOccurrence.ofTail_context
    {head : Pattern} {tail : List Pattern}
    (occurrence : CostStaticFVarListOccurrence tail) :
    (CostStaticFVarListOccurrence.ofTail
      (head := head) occurrence).occurrence.context =
        occurrence.occurrence.context := by
  rfl

mutual
  /-- Interpret an abstract-skeleton alignment while retaining the exact root
  occurrence selected at every leaf.  The leaf callbacks are token-complete:
  every name, table position, support regime, and structural zipper appearing
  in their conclusions is determined by their arguments. -/
  def reifyAlignedAtOccurrences
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {smallOccurrences largeOccurrences : List CostRegionOccurrence}
      {smallTable : TypedCostRegionBoundaryTable source color targetFree
        smallOccurrences}
      {largeTable : TypedCostRegionBoundaryTable source color targetFree
        largeOccurrences}
      {smallValues : TypedCostRegionBoundaryTable.Values source color
        targetFree smallTable}
      {largeValues : TypedCostRegionBoundaryTable.Values source color
        targetFree largeTable}
      {smallRoot largeRoot : Pattern}
      {smallInventory : CostStaticParameterInventory source color targetFree
        smallTable smallValues smallRoot}
      {largeInventory : CostStaticParameterInventory source color targetFree
        largeTable largeValues largeRoot}
      (smallEnvironment : CostStaticAtomEnvironment source color targetFree
        smallInventory)
      (largeEnvironment : CostStaticAtomEnvironment source color targetFree
        largeInventory)
      {ambient : List TypeExpr}
      {rootRegime : CostStaticAvailabilityRegime}
      (sourceLeaf : ∀ regime name
          (smallOccurrence : CostStaticFVarOccurrence smallRoot)
          (largeOccurrence : CostStaticFVarOccurrence largeRoot),
        smallOccurrence.name = costRegionSourceVariableName name →
        largeOccurrence.name = costRegionSourceVariableName name →
        CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
            smallOccurrence.context = regime →
        CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
            largeOccurrence.context = regime →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          source.reflection.1
          smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (.fvar (smallEnvironment.reifyName
            (costRegionSourceVariableName name)))
          (.fvar (largeEnvironment.reifyName
            (costRegionSourceVariableName name))))
      (boundaryLeaf : ∀ regime
          (smallPosition : Fin smallTable.entries.length)
          (largePosition : Fin largeTable.entries.length),
        smallPosition.1 = largePosition.1 →
        CostStaticAvailabilityAt ambient regime
          (smallTable.entries.get smallPosition).boundary.targetSupport
          (largeTable.entries.get largePosition).boundary.targetSupport →
        (smallOccurrence : CostStaticFVarOccurrence smallRoot) →
        (largeOccurrence : CostStaticFVarOccurrence largeRoot) →
        smallOccurrence.name = costRegionBoundaryVariableName
          (smallTable.entries.get smallPosition).boundary →
        largeOccurrence.name = costRegionBoundaryVariableName
          (largeTable.entries.get largePosition).boundary →
        CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
            smallOccurrence.context = regime →
        CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
            largeOccurrence.context = regime →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          source.reflection.1
          smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (.fvar (smallEnvironment.reifyName
            (costRegionBoundaryVariableName
              (smallTable.entries.get smallPosition).boundary)))
          (.fvar (largeEnvironment.reifyName
            (costRegionBoundaryVariableName
              (largeTable.entries.get largePosition).boundary)))) :
      ∀ {regime : CostStaticAvailabilityRegime}
          {smallPattern largePattern : Pattern},
        CostStaticAbstractPatternAlignment smallTable.entries
            largeTable.entries ambient regime smallPattern largePattern →
        (smallEmbed : (occurrence : CostStaticFVarOccurrence smallPattern) →
          { rootOccurrence : CostStaticFVarOccurrence smallRoot //
            rootOccurrence.name = occurrence.name }) →
        (largeEmbed : (occurrence : CostStaticFVarOccurrence largePattern) →
          { rootOccurrence : CostStaticFVarOccurrence largeRoot //
            rootOccurrence.name = occurrence.name }) →
        (∀ occurrence : CostStaticFVarOccurrence smallPattern,
          CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
              (smallEmbed occurrence).1.context =
            CostStaticAvailabilityRegime.atContext source.reflection.1 regime
              occurrence.context) →
        (∀ occurrence : CostStaticFVarOccurrence largePattern,
          CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
              (largeEmbed occurrence).1.context =
            CostStaticAvailabilityRegime.atContext source.reflection.1 regime
              occurrence.context) →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          source.reflection.1
          smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (smallEnvironment.reify smallPattern)
          (largeEnvironment.reify largePattern)
    | _, _, _, .bvar regime index, _, _, _, _ => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.bvar
            (profile := source.reflection.1)
            (smallSupport := smallEnvironment.restorationSupport)
            (smallAssignment := smallEnvironment.restorationAssignment)
            (largeSupport := largeEnvironment.restorationSupport)
            (largeAssignment := largeEnvironment.restorationAssignment)
            (ambient := ambient) regime index)
    | _, _, _, .sourceFVar regime name, smallEmbed, largeEmbed,
        smallPath, largePath => by
        let smallLocal : CostStaticFVarOccurrence
            (.fvar (costRegionSourceVariableName name)) :=
          ⟨_, .hole, .here⟩
        let largeLocal : CostStaticFVarOccurrence
            (.fvar (costRegionSourceVariableName name)) :=
          ⟨_, .hole, .here⟩
        simpa only [CostStaticAtomEnvironment.reify] using
          sourceLeaf regime name (smallEmbed smallLocal).1
            (largeEmbed largeLocal).1
            (by simpa [smallLocal] using (smallEmbed smallLocal).2)
            (by simpa [largeLocal] using (largeEmbed largeLocal).2)
            (by simpa [smallLocal, CostStaticAvailabilityRegime.atContext]
              using smallPath smallLocal)
            (by simpa [largeLocal, CostStaticAvailabilityRegime.atContext]
              using largePath largeLocal)
    | _, _, _, .boundary regime smallPosition largePosition positionEq support,
        smallEmbed, largeEmbed, smallPath, largePath => by
        let smallLocal : CostStaticFVarOccurrence
            (.fvar (costRegionBoundaryVariableName
              (smallTable.entries.get smallPosition).boundary)) :=
          ⟨_, .hole, .here⟩
        let largeLocal : CostStaticFVarOccurrence
            (.fvar (costRegionBoundaryVariableName
              (largeTable.entries.get largePosition).boundary)) :=
          ⟨_, .hole, .here⟩
        simpa only [CostStaticAtomEnvironment.reify] using
          boundaryLeaf regime smallPosition largePosition positionEq support
            (smallEmbed smallLocal).1 (largeEmbed largeLocal).1
            (by simpa [smallLocal] using (smallEmbed smallLocal).2)
            (by simpa [largeLocal] using (largeEmbed largeLocal).2)
            (by simpa [smallLocal, CostStaticAvailabilityRegime.atContext]
              using smallPath smallLocal)
            (by simpa [largeLocal, CostStaticAvailabilityRegime.atContext]
              using largePath largeLocal)
    | _, _, _, .apply regime constructor arguments, smallEmbed, largeEmbed,
        smallPath, largePath => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.apply
            regime constructor
            (CostStaticAbstractPatternListAlignment.reifyAlignedAtOccurrences
              smallEnvironment largeEnvironment sourceLeaf boundaryLeaf
              arguments
              (fun occurrence => by
                let nested := occurrence.inApply constructor
                let root := smallEmbed nested
                exact ⟨root.1, root.2.trans (by rfl)⟩)
              (fun occurrence => by
                let nested := occurrence.inApply constructor
                let root := largeEmbed nested
                exact ⟨root.1, root.2.trans (by rfl)⟩)
              (fun occurrence => by
                let nested := occurrence.inApply constructor
                simpa [nested, CostStaticFVarListOccurrence.inApply,
                  CostStaticAvailabilityRegime.atContext] using
                  smallPath nested)
              (fun occurrence => by
                let nested := occurrence.inApply constructor
                simpa [nested, CostStaticFVarListOccurrence.inApply,
                  CostStaticAvailabilityRegime.atContext] using
                  largePath nested)))
    | _, _, _, .lambda regime binder body, smallEmbed, largeEmbed,
        smallPath, largePath => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.lambda
            regime binder
            (reifyAlignedAtOccurrences smallEnvironment largeEnvironment
              sourceLeaf boundaryLeaf body
              (fun occurrence => by
                let nested := occurrence.inContext (.lambda binder .hole)
                let root := smallEmbed nested
                exact ⟨root.1, root.2.trans (by rfl)⟩)
              (fun occurrence => by
                let nested := occurrence.inContext (.lambda binder .hole)
                let root := largeEmbed nested
                exact ⟨root.1, root.2.trans (by rfl)⟩)
              (fun occurrence => by
                let nested := occurrence.inContext (.lambda binder .hole)
                simpa [nested, CostStaticFVarOccurrence.inContext,
                  CostStaticAvailabilityRegime.atContext_comp,
                  CostStaticAvailabilityRegime.atContext] using
                  smallPath nested)
              (fun occurrence => by
                let nested := occurrence.inContext (.lambda binder .hole)
                simpa [nested, CostStaticFVarOccurrence.inContext,
                  CostStaticAvailabilityRegime.atContext_comp,
                  CostStaticAvailabilityRegime.atContext] using
                  largePath nested)))
    | _, _, _, .multiLambda regime arity binders body,
        smallEmbed, largeEmbed, smallPath, largePath => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.multiLambda
            regime arity binders
            (reifyAlignedAtOccurrences smallEnvironment largeEnvironment
              sourceLeaf boundaryLeaf body
              (fun occurrence => by
                let nested := occurrence.inContext
                  (.multiLambda arity binders .hole)
                let root := smallEmbed nested
                exact ⟨root.1, root.2.trans (by rfl)⟩)
              (fun occurrence => by
                let nested := occurrence.inContext
                  (.multiLambda arity binders .hole)
                let root := largeEmbed nested
                exact ⟨root.1, root.2.trans (by rfl)⟩)
              (fun occurrence => by
                let nested := occurrence.inContext
                  (.multiLambda arity binders .hole)
                simpa [nested, CostStaticFVarOccurrence.inContext,
                  CostStaticAvailabilityRegime.atContext_comp,
                  CostStaticAvailabilityRegime.atContext] using
                  smallPath nested)
              (fun occurrence => by
                let nested := occurrence.inContext
                  (.multiLambda arity binders .hole)
                simpa [nested, CostStaticFVarOccurrence.inContext,
                  CostStaticAvailabilityRegime.atContext_comp,
                  CostStaticAvailabilityRegime.atContext] using
                  largePath nested)))
    | _, _, _, .collection regime collectionType rest elements,
        smallEmbed, largeEmbed, smallPath, largePath => by
        simpa only [CostStaticAtomEnvironment.reify] using
          (ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.collection
            regime collectionType (rest.map costRegionSourceVariableName)
            (CostStaticAbstractPatternListAlignment.reifyAlignedAtOccurrences
              smallEnvironment largeEnvironment sourceLeaf boundaryLeaf
              elements
              (fun occurrence => by
                let nested := occurrence.inCollection collectionType
                  (rest.map costRegionSourceVariableName)
                let root := smallEmbed nested
                exact ⟨root.1, root.2.trans (by rfl)⟩)
              (fun occurrence => by
                let nested := occurrence.inCollection collectionType
                  (rest.map costRegionSourceVariableName)
                let root := largeEmbed nested
                exact ⟨root.1, root.2.trans (by rfl)⟩)
              (fun occurrence => by
                let nested := occurrence.inCollection collectionType
                  (rest.map costRegionSourceVariableName)
                simpa [nested, CostStaticFVarListOccurrence.inCollection,
                  CostStaticAvailabilityRegime.atContext] using
                  smallPath nested)
              (fun occurrence => by
                let nested := occurrence.inCollection collectionType
                  (rest.map costRegionSourceVariableName)
                simpa [nested, CostStaticFVarListOccurrence.inCollection,
                  CostStaticAvailabilityRegime.atContext] using
                  largePath nested)))

  /-- Ordered-list companion of exact occurrence interpretation. -/
  def CostStaticAbstractPatternListAlignment.reifyAlignedAtOccurrences
      {source : CIGSLT} {color : CostStaticColor}
      {targetFree : WellSorted.FreeTypeContext}
      {smallOccurrences largeOccurrences : List CostRegionOccurrence}
      {smallTable : TypedCostRegionBoundaryTable source color targetFree
        smallOccurrences}
      {largeTable : TypedCostRegionBoundaryTable source color targetFree
        largeOccurrences}
      {smallValues : TypedCostRegionBoundaryTable.Values source color
        targetFree smallTable}
      {largeValues : TypedCostRegionBoundaryTable.Values source color
        targetFree largeTable}
      {smallRoot largeRoot : Pattern}
      {smallInventory : CostStaticParameterInventory source color targetFree
        smallTable smallValues smallRoot}
      {largeInventory : CostStaticParameterInventory source color targetFree
        largeTable largeValues largeRoot}
      (smallEnvironment : CostStaticAtomEnvironment source color targetFree
        smallInventory)
      (largeEnvironment : CostStaticAtomEnvironment source color targetFree
        largeInventory)
      {ambient : List TypeExpr}
      {rootRegime : CostStaticAvailabilityRegime}
      (sourceLeaf : ∀ regime name
          (smallOccurrence : CostStaticFVarOccurrence smallRoot)
          (largeOccurrence : CostStaticFVarOccurrence largeRoot),
        smallOccurrence.name = costRegionSourceVariableName name →
        largeOccurrence.name = costRegionSourceVariableName name →
        CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
            smallOccurrence.context = regime →
        CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
            largeOccurrence.context = regime →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          source.reflection.1 smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (.fvar (smallEnvironment.reifyName
            (costRegionSourceVariableName name)))
          (.fvar (largeEnvironment.reifyName
            (costRegionSourceVariableName name))))
      (boundaryLeaf : ∀ regime
          (smallPosition : Fin smallTable.entries.length)
          (largePosition : Fin largeTable.entries.length),
        smallPosition.1 = largePosition.1 →
        CostStaticAvailabilityAt ambient regime
          (smallTable.entries.get smallPosition).boundary.targetSupport
          (largeTable.entries.get largePosition).boundary.targetSupport →
        (smallOccurrence : CostStaticFVarOccurrence smallRoot) →
        (largeOccurrence : CostStaticFVarOccurrence largeRoot) →
        smallOccurrence.name = costRegionBoundaryVariableName
          (smallTable.entries.get smallPosition).boundary →
        largeOccurrence.name = costRegionBoundaryVariableName
          (largeTable.entries.get largePosition).boundary →
        CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
            smallOccurrence.context = regime →
        CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
            largeOccurrence.context = regime →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
          source.reflection.1 smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (.fvar (smallEnvironment.reifyName
            (costRegionBoundaryVariableName
              (smallTable.entries.get smallPosition).boundary)))
          (.fvar (largeEnvironment.reifyName
            (costRegionBoundaryVariableName
              (largeTable.entries.get largePosition).boundary)))) :
      ∀ {regime : CostStaticAvailabilityRegime}
          {smallPatterns largePatterns : List Pattern},
        CostStaticAbstractPatternListAlignment smallTable.entries
            largeTable.entries ambient regime smallPatterns largePatterns →
        (smallEmbed : (occurrence : CostStaticFVarListOccurrence smallPatterns) →
          { rootOccurrence : CostStaticFVarOccurrence smallRoot //
            rootOccurrence.name = occurrence.occurrence.name }) →
        (largeEmbed : (occurrence : CostStaticFVarListOccurrence largePatterns) →
          { rootOccurrence : CostStaticFVarOccurrence largeRoot //
            rootOccurrence.name = occurrence.occurrence.name }) →
        (∀ occurrence : CostStaticFVarListOccurrence smallPatterns,
          CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
              (smallEmbed occurrence).1.context =
            CostStaticAvailabilityRegime.atContext source.reflection.1 regime
              occurrence.occurrence.context) →
        (∀ occurrence : CostStaticFVarListOccurrence largePatterns,
          CostStaticAvailabilityRegime.atContext source.reflection.1 rootRegime
              (largeEmbed occurrence).1.context =
            CostStaticAvailabilityRegime.atContext source.reflection.1 regime
              occurrence.occurrence.context) →
        ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAlignedList
          source.reflection.1 smallEnvironment.restorationSupport
          smallEnvironment.restorationAssignment
          largeEnvironment.restorationSupport
          largeEnvironment.restorationAssignment ambient regime
          (smallPatterns.map smallEnvironment.reify)
          (largePatterns.map largeEnvironment.reify)
    | _, _, _, .nil regime, _, _, _, _ => .nil regime
    | _, _, _, .cons regime head tail, smallEmbed, largeEmbed,
        smallPath, largePath =>
        .cons regime
          (reifyAlignedAtOccurrences smallEnvironment largeEnvironment
            sourceLeaf boundaryLeaf head
            (fun occurrence => by
              let root := smallEmbed
                (CostStaticFVarListOccurrence.ofHead occurrence)
              exact ⟨root.1, root.2.trans (by rfl)⟩)
            (fun occurrence => by
              let root := largeEmbed
                (CostStaticFVarListOccurrence.ofHead occurrence)
              exact ⟨root.1, root.2.trans (by rfl)⟩)
            (fun occurrence => by
              change CostStaticAvailabilityRegime.atContext
                  source.reflection.1 rootRegime
                    (smallEmbed
                      (CostStaticFVarListOccurrence.ofHead occurrence)).1.context =
                CostStaticAvailabilityRegime.atContext
                  source.reflection.1 regime occurrence.context
              simpa using
                smallPath (CostStaticFVarListOccurrence.ofHead occurrence))
            (fun occurrence => by
              change CostStaticAvailabilityRegime.atContext
                  source.reflection.1 rootRegime
                    (largeEmbed
                      (CostStaticFVarListOccurrence.ofHead occurrence)).1.context =
                CostStaticAvailabilityRegime.atContext
                  source.reflection.1 regime occurrence.context
              simpa using
                largePath (CostStaticFVarListOccurrence.ofHead occurrence)))
          (CostStaticAbstractPatternListAlignment.reifyAlignedAtOccurrences
            smallEnvironment largeEnvironment sourceLeaf boundaryLeaf tail
            (fun occurrence => by
              let root := smallEmbed
                (CostStaticFVarListOccurrence.ofTail occurrence)
              exact ⟨root.1, root.2.trans (by rfl)⟩)
            (fun occurrence => by
              let root := largeEmbed
                (CostStaticFVarListOccurrence.ofTail occurrence)
              exact ⟨root.1, root.2.trans (by rfl)⟩)
            (fun occurrence => by
              change CostStaticAvailabilityRegime.atContext
                  source.reflection.1 rootRegime
                    (smallEmbed
                      (CostStaticFVarListOccurrence.ofTail occurrence)).1.context =
                CostStaticAvailabilityRegime.atContext
                  source.reflection.1 regime occurrence.occurrence.context
              simpa using
                smallPath (CostStaticFVarListOccurrence.ofTail occurrence))
            (fun occurrence => by
              change CostStaticAvailabilityRegime.atContext
                  source.reflection.1 rootRegime
                    (largeEmbed
                      (CostStaticFVarListOccurrence.ofTail occurrence)).1.context =
                CostStaticAvailabilityRegime.atContext
                  source.reflection.1 regime occurrence.occurrence.context
              simpa using
                largePath (CostStaticFVarListOccurrence.ofTail occurrence)))
end

/-- A source-variable leaf is always transportable.  Membership tokens tie
the callback to actual occurrences in both endpoint roots; the finite
environments then expose the rigid source variable recorded by those slots. -/
theorem sourceFVar_reifyAligned
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    {smallValues : TypedCostRegionBoundaryTable.Values source color targetFree
      smallTable}
    {largeValues : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable}
    {smallRoot largeRoot : Pattern}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallTable smallValues smallRoot}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeTable largeValues largeRoot}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr} (regime : CostStaticAvailabilityRegime)
    (name : String)
    (smallMembership : costRegionSourceVariableName name ∈
      smallRoot.freeFvarNames)
    (largeMembership : costRegionSourceVariableName name ∈
      largeRoot.freeFvarNames)
    (smallObject : WellSorted.isObjectPattern smallRoot = true)
    (largeObject : WellSorted.isObjectPattern largeRoot = true) :
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      source.reflection.1
      smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient regime
      (.fvar (smallEnvironment.reifyName
        (costRegionSourceVariableName name)))
      (.fvar (largeEnvironment.reifyName
        (costRegionSourceVariableName name))) := by
  obtain ⟨smallOccurrence, smallName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
      smallMembership smallObject
  obtain ⟨largeOccurrence, largeName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
      largeMembership largeObject
  obtain ⟨smallSlot, smallSelectedOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (smallEnvironment.slotOfName?_isSome_of_occurrence smallOccurrence)
  obtain ⟨largeSlot, largeSelectedOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (largeEnvironment.slotOfName?_isSome_of_occurrence largeOccurrence)
  have smallSelected : smallEnvironment.slotOfName?
      (costRegionSourceVariableName name) = some smallSlot := by
    simpa only [smallName] using smallSelectedOccurrence
  have largeSelected : largeEnvironment.slotOfName?
      (costRegionSourceVariableName name) = some largeSlot := by
    simpa only [largeName] using largeSelectedOccurrence
  have smallNormal : (smallEnvironment.atomValue smallSlot).key.normal =
      .fvar name := by
    calc
      (smallEnvironment.atomValue smallSlot).key.normal =
          smallValues.assignment smallTable smallOccurrence.name :=
        smallEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
          smallOccurrence smallSlot smallSelectedOccurrence
      _ = smallValues.assignment smallTable
          (costRegionSourceVariableName name) :=
        congrArg (smallValues.assignment smallTable) smallName
      _ = .fvar name := smallValues.assignment_sourceVariable name
  have largeNormal : (largeEnvironment.atomValue largeSlot).key.normal =
      .fvar name := by
    calc
      (largeEnvironment.atomValue largeSlot).key.normal =
          largeValues.assignment largeTable largeOccurrence.name :=
        largeEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
          largeOccurrence largeSlot largeSelectedOccurrence
      _ = largeValues.assignment largeTable
          (costRegionSourceVariableName name) :=
        congrArg (largeValues.assignment largeTable) largeName
      _ = .fvar name := largeValues.assignment_sourceVariable name
  simpa [CostStaticAtomEnvironment.reifyName, smallSelected, largeSelected]
    using
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.atomNamesRigid
        (profile := source.reflection.1)
        smallEnvironment largeEnvironment regime smallSlot largeSlot name
          smallNormal largeNormal

/-- A positional boundary leaf is transportable once the two recursive child
normal forms agree and the same leaf can be re-exposed at the outer regime.
The latter is the recursive induction hypothesis needed only after a
quote/drop cancellation; ordinary exposed leaves use the planner's exact
support equation directly. -/
theorem boundary_reifyAligned
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    (smallTrees : CostRegionBoundaryTrees source targetFree color smallTable)
    (largeTrees : CostRegionBoundaryTrees source targetFree color largeTable)
    {smallRoot largeRoot : Pattern}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallTable
      (smallTrees.normalizeValues (normalizeStatic := kernel.normalize))
      smallRoot}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeTable
      (largeTrees.normalizeValues (normalizeStatic := kernel.normalize))
      largeRoot}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
    (smallPosition : Fin smallTable.entries.length)
    (largePosition : Fin largeTable.entries.length)
    (_positionEq : smallPosition.1 = largePosition.1)
    (supportAt : CostStaticAvailabilityAt ambient regime
      (smallTable.entries.get smallPosition).boundary.targetSupport
      (largeTable.entries.get largePosition).boundary.targetSupport)
    (smallMembership : costRegionBoundaryVariableName
        (smallTable.entries.get smallPosition).boundary ∈
      smallRoot.freeFvarNames)
    (largeMembership : costRegionBoundaryVariableName
        (largeTable.entries.get largePosition).boundary ∈
      largeRoot.freeFvarNames)
    (smallObject : WellSorted.isObjectPattern smallRoot = true)
    (largeObject : WellSorted.isObjectPattern largeRoot = true)
    (normalEq :
      ((smallTrees.getEntry smallPosition).tree.normalizedBoundaryValue
        kernel).1 =
      ((largeTrees.getEntry largePosition).tree.normalizedBoundaryValue
        kernel).1)
    (reexposes : regime = .sealed →
      (smallTable.entries.get smallPosition).boundary.targetSupport ≠ [] →
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
        source.reflection.1 smallEnvironment.restorationSupport
        smallEnvironment.restorationAssignment
        largeEnvironment.restorationSupport
        largeEnvironment.restorationAssignment ambient .exposed
        (.fvar (smallEnvironment.reifyName
          (costRegionBoundaryVariableName
            (smallTable.entries.get smallPosition).boundary)))
        (.fvar (largeEnvironment.reifyName
          (costRegionBoundaryVariableName
            (largeTable.entries.get largePosition).boundary)))) :
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      source.reflection.1 smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient regime
      (.fvar (smallEnvironment.reifyName
        (costRegionBoundaryVariableName
          (smallTable.entries.get smallPosition).boundary)))
      (.fvar (largeEnvironment.reifyName
        (costRegionBoundaryVariableName
          (largeTable.entries.get largePosition).boundary))) := by
  obtain ⟨smallOccurrence, smallName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
      smallMembership smallObject
  obtain ⟨largeOccurrence, largeName⟩ :=
    CostStaticFVarOccurrence.exists_of_mem_freeFvarNames_of_object
      largeMembership largeObject
  obtain ⟨smallSlot, smallSelectedOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (smallEnvironment.slotOfName?_isSome_of_occurrence smallOccurrence)
  obtain ⟨largeSlot, largeSelectedOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (largeEnvironment.slotOfName?_isSome_of_occurrence largeOccurrence)
  have smallTreeName : smallOccurrence.name = costRegionBoundaryVariableName
      (smallTrees.getEntry smallPosition).boundary.boundary := by
    rw [smallTrees.getEntry_boundary smallPosition]
    exact smallName
  have largeTreeName : largeOccurrence.name = costRegionBoundaryVariableName
      (largeTrees.getEntry largePosition).boundary.boundary := by
    rw [largeTrees.getEntry_boundary largePosition]
    exact largeName
  have smallSelected : smallEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        (smallTable.entries.get smallPosition).boundary) = some smallSlot := by
    rw [← smallName]
    exact smallSelectedOccurrence
  have largeSelected : largeEnvironment.slotOfName?
      (costRegionBoundaryVariableName
        (largeTable.entries.get largePosition).boundary) = some largeSlot := by
    rw [← largeName]
    exact largeSelectedOccurrence
  have smallReifyName : smallEnvironment.reifyName
      (costRegionBoundaryVariableName
        (smallTable.entries.get smallPosition).boundary) =
      smallEnvironment.atomName smallSlot := by
    simp only [CostStaticAtomEnvironment.reifyName, smallSelected]
  have largeReifyName : largeEnvironment.reifyName
      (costRegionBoundaryVariableName
        (largeTable.entries.get largePosition).boundary) =
      largeEnvironment.atomName largeSlot := by
    simp only [CostStaticAtomEnvironment.reifyName, largeSelected]
  have smallAtom :=
    smallEnvironment.atomValue_eq_normalizedBoundaryValue_of_getEntry
      unambiguous smallTrees smallPosition smallOccurrence smallTreeName smallSlot
        smallSelectedOccurrence
  have largeAtom :=
    largeEnvironment.atomValue_eq_normalizedBoundaryValue_of_getEntry
      unambiguous largeTrees largePosition largeOccurrence largeTreeName largeSlot
        largeSelectedOccurrence
  have atomSupport : CostStaticAvailabilityAt ambient regime
      (smallEnvironment.atomValue smallSlot).key.targetSupport
      (largeEnvironment.atomValue largeSlot).key.targetSupport := by
    rw [smallAtom, largeAtom]
    simpa only [TypedCostStaticAtom.ofBoundaryValue,
      smallTrees.getEntry_boundary smallPosition,
      largeTrees.getEntry_boundary largePosition] using supportAt
  have atomNormal : (smallEnvironment.atomValue smallSlot).key.normal =
      (largeEnvironment.atomValue largeSlot).key.normal := by
    rw [smallAtom, largeAtom]
    simpa only [TypedCostStaticAtom.ofBoundaryValue] using normalEq
  by_cases smallSupportNil :
      (smallTable.entries.get smallPosition).boundary.targetSupport = []
  · have atomSupportNil :
        (smallEnvironment.atomValue smallSlot).key.targetSupport = [] := by
      rw [smallAtom]
      simpa only [TypedCostStaticAtom.ofBoundaryValue,
        smallTrees.getEntry_boundary smallPosition] using smallSupportNil
    have aligned :=
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.atomNamesAt_of_smallTargetSupport_nil
        (profile := source.reflection.1) (ambient := ambient)
        smallEnvironment largeEnvironment regime smallSlot largeSlot
          atomSupportNil atomNormal
    rw [smallReifyName, largeReifyName]
    exact aligned
  have exposedAtoms : regime = .sealed →
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
        source.reflection.1 smallEnvironment.restorationSupport
        smallEnvironment.restorationAssignment
        largeEnvironment.restorationSupport
        largeEnvironment.restorationAssignment ambient .exposed
        (.fvar (smallEnvironment.atomName smallSlot))
        (.fvar (largeEnvironment.atomName largeSlot)) := by
    intro sealed
    rw [← smallReifyName, ← largeReifyName]
    exact reexposes sealed smallSupportNil
  have aligned :=
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned.atomNamesAt
      smallEnvironment largeEnvironment smallSlot largeSlot atomSupport
        atomNormal exposedAtoms
  rw [smallReifyName, largeReifyName]
  exact aligned

/-- Interpret a complete positional planner certificate using the actual
recursive boundary forests.  Source variables close rigidly; boundary
variables use the forest's positional normal-form equality, leaving only the
quote-cancellation re-exposure fact to the recursive caller. -/
theorem reifyAligned_of_normalizedBoundaryTrees
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    {smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences}
    {largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences}
    (smallTrees : CostRegionBoundaryTrees source targetFree color smallTable)
    (largeTrees : CostRegionBoundaryTrees source targetFree color largeTable)
    {smallRoot largeRoot : Pattern}
    {smallInventory : CostStaticParameterInventory source color targetFree
      smallTable
      (smallTrees.normalizeValues (normalizeStatic := kernel.normalize))
      smallRoot}
    {largeInventory : CostStaticParameterInventory source color targetFree
      largeTable
      (largeTrees.normalizeValues (normalizeStatic := kernel.normalize))
      largeRoot}
    (smallEnvironment : CostStaticAtomEnvironment source color targetFree
      smallInventory)
    (largeEnvironment : CostStaticAtomEnvironment source color targetFree
      largeInventory)
    {ambient : List TypeExpr} {regime : CostStaticAvailabilityRegime}
    (forests : CostRegionBoundaryTrees.NormalizedAvailabilitySuffixAcross
      kernel.normalize ambient smallTable largeTable smallTrees largeTrees)
    (alignment : CostStaticAbstractPatternAlignment smallTable.entries
      largeTable.entries ambient regime smallRoot largeRoot)
    (smallObject : WellSorted.isObjectPattern smallRoot = true)
    (largeObject : WellSorted.isObjectPattern largeRoot = true)
    (boundaryReexposes : ∀ (current : CostStaticAvailabilityRegime)
        (smallPosition : Fin smallTable.entries.length)
        (largePosition : Fin largeTable.entries.length),
      smallPosition.1 = largePosition.1 →
      current = CostStaticAvailabilityRegime.sealed →
      (smallTable.entries.get smallPosition).boundary.targetSupport ≠ [] →
      ReflectiveContextSupport.AvailabilityTransposedRestoresTogether
        source.reflection.1 smallEnvironment.restorationSupport
        smallEnvironment.restorationAssignment
        largeEnvironment.restorationSupport
        largeEnvironment.restorationAssignment ambient .exposed
        (.fvar (smallEnvironment.reifyName
          (costRegionBoundaryVariableName
            (smallTable.entries.get smallPosition).boundary)))
        (.fvar (largeEnvironment.reifyName
          (costRegionBoundaryVariableName
            (largeTable.entries.get largePosition).boundary)))) :
    ReflectiveContextSupport.AvailabilityTransposedRestoresTogether.AvailabilityTransposedPatternAligned
      source.reflection.1 smallEnvironment.restorationSupport
      smallEnvironment.restorationAssignment
      largeEnvironment.restorationSupport
      largeEnvironment.restorationAssignment ambient regime
      (smallEnvironment.reify smallRoot)
      (largeEnvironment.reify largeRoot) := by
  exact reifyAligned smallEnvironment largeEnvironment
    (fun current name smallMembership largeMembership =>
      sourceFVar_reifyAligned smallEnvironment largeEnvironment current name
        smallMembership largeMembership smallObject largeObject)
    (fun current smallPosition largePosition positionEq supportAt
        smallMembership largeMembership =>
      boundary_reifyAligned unambiguous smallTrees largeTrees smallEnvironment
        largeEnvironment smallPosition largePosition positionEq supportAt
        smallMembership largeMembership smallObject largeObject
        (forests.getEntry_normal_eq smallPosition largePosition positionEq)
        (boundaryReexposes current smallPosition largePosition positionEq))
    alignment (fun _ membership => membership)
      (fun _ membership => membership)

end CostStaticAbstractPatternAlignment

end Mettapedia.GSLT.LanguageDef
