import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex

/-!
# Direct common-apex constructors for matched rho frames

Common semantic names are implementation details of the finite atom cospan.
Two names may differ because their retained supports differ, even when their
closed normalized values agree.  This module starts the matched-frame closure
at the semantic boundary: unequal names are related by what their assignments
restore, rather than by syntactic equality.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A reflection-certified object typed with no ambient binders may be placed
under any outer binder context without changing its raw pattern.  The
generic root weakening supplies typing and quote safety; closedness makes
its de Bruijn lift inert. -/
theorem ReflectiveWellSorted.OpenPatternWellSorted.extendOuterOfClosed
    {profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile}
    {language : LanguageDef} {free : WellSorted.FreeTypeContext}
    {pattern : Pattern} {type : TypeExpr}
    (wellSorted : ReflectiveWellSorted.OpenPatternWellSorted profile language
      free [] type pattern)
    (outer : List TypeExpr) :
    ReflectiveWellSorted.OpenPatternWellSorted profile language free outer
      type pattern := by
  let closed : ReflectiveWellSorted.OpenPattern profile language free [] type :=
    ⟨pattern, wellSorted⟩
  let weakened := closed.weakenRoot outer
  have patternEq : weakened.1 = pattern := by
    change Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0 outer.length
        pattern = pattern
    exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
      wellSorted.1.1.isWellScopedAt
  have widened : ReflectiveWellSorted.OpenPatternWellSorted profile language
      free (outer ++ []) type pattern := by
    rw [← patternEq]
    exact weakened.2
  simpa only [List.append_nil] using widened

namespace RhoMatchedStaticFramesApex

/-- Normalizing the head of a finite boundary forest makes that normalized
pattern the value selected by the head boundary's collision-free name. -/
theorem normalizeValues_assignment_head
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrence : CostRegionOccurrence}
    {occurrences : List CostRegionOccurrence}
    {boundary : TypedCostRegionBoundary source color targetFree}
    {content : boundary.boundary.content = occurrence.content}
    {tail : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (head : CostRegionTree source targetFree
      boundary.boundary.targetSupport [] boundary.boundary.content
        boundary.boundary.targetType)
    (children : CostRegionBoundaryTrees source targetFree color tail)
    (normalizeStatic : CostStaticRegionNormalizer source) :
    ((CostRegionBoundaryTrees.cons head children).normalizeValues
        (normalizeStatic := normalizeStatic)).assignment
        (.cons boundary content tail)
        (costRegionBoundaryVariableName boundary.boundary) =
      (head.normalize (normalizeStatic := normalizeStatic)).pattern := by
  simp only [CostRegionBoundaryTrees.normalizeValues]
  unfold TypedCostRegionBoundaryTable.Values.assignment
  rw [decodeCostRegionSourceVariableName_boundary]
  unfold TypedCostRegionBoundaryTable.Values.resolve
  simp only [if_pos]

/-- An atom normalized in the sealed (empty-support) regime is closed at
ambient depth zero.  This supplies the exact scopedness premise used when the
same value is compared with an exposed atom carrying a larger support. -/
theorem atomNormalScopedAtZero_of_targetSupport_nil
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount)
    (sealed : (environment.atomValue slot).key.targetSupport = []) :
    (environment.atomValue slot).key.normal.isWellScopedAt 0 = true := by
  have normalWellScoped :=
    (environment.atomValue slot).normalTyped.isWellScopedAt
  rw [sealed] at normalWellScoped
  exact normalWellScoped

/-- Two common-reified atom occurrences with the same closed normalized value
form a semantic leaf, even when their complete keys and common names differ. -/
theorem atom_of_scopedNormalEq
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source leftColor
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source rightColor
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source leftColor targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source rightColor targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source leftColor targetFree leftInventory)
    (right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (normalEq : (left.atomValue leftSlot).key.normal =
      (right.atomValue rightSlot).key.normal)
    (normalScoped :
      (left.atomValue leftSlot).key.normal.isWellScopedAt 0 = true)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot))) := by
  apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
  apply PatternLeafAligned.leaf
  intro currentDepth
  exact CostStaticAtomEnvironment.substituteAt_commonReifiedAtom_eq_of_scoped_normal
    left right leftSlot rightSlot normalEq normalScoped currentDepth

/-- A sealed left atom specializes `atom_of_scopedNormalEq` by recovering
closedness from its typed target fibre. -/
theorem atom_of_leftTargetSupportNil
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source leftColor
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source rightColor
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source leftColor targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source rightColor targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source leftColor targetFree leftInventory)
    (right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (normalEq : (left.atomValue leftSlot).key.normal =
      (right.atomValue rightSlot).key.normal)
    (sealed : (left.atomValue leftSlot).key.targetSupport = [])
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot))) := by
  exact atom_of_scopedNormalEq left right leftSlot rightSlot normalEq
    (atomNormalScopedAtZero_of_targetSupport_nil left leftSlot sealed)
    declaration depth

/-- Right-oriented companion of `atom_of_leftTargetSupportNil`. -/
theorem atom_of_rightTargetSupportNil
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source leftColor
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source rightColor
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source leftColor targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source rightColor targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source leftColor targetFree leftInventory)
    (right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (normalEq : (left.atomValue leftSlot).key.normal =
      (right.atomValue rightSlot).key.normal)
    (sealed : (right.atomValue rightSlot).key.targetSupport = [])
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith left.lookupAtom? cospan.leftSlot
        (.fvar (left.atomName leftSlot)))
      (cospan.reifyWith right.lookupAtom? cospan.rightSlot
        (.fvar (right.atomName rightSlot))) := by
  have rightScoped :=
    atomNormalScopedAtZero_of_targetSupport_nil right rightSlot sealed
  have leftScoped :
      (left.atomValue leftSlot).key.normal.isWellScopedAt 0 = true := by
    simpa only [normalEq] using rightScoped
  exact atom_of_scopedNormalEq left right leftSlot rightSlot normalEq leftScoped
    declaration depth

/-- Two atom occurrences with the same closed normalized value form a rigid
unary common-restoration apex, even when their complete keys and common names
differ.  The constructor is the leaf case needed when canonical Quote/Drop
exposes a boundary under different retained supports. -/
theorem rigidUnary_of_scopedNormalEq
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source leftColor
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source rightColor
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source leftColor targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source rightColor targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source leftColor targetFree leftInventory)
    (right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (normalEq : (left.atomValue leftSlot).key.normal =
      (right.atomValue rightSlot).key.normal)
    (normalScoped :
      (left.atomValue leftSlot).key.normal.isWellScopedAt 0 = true)
    (declaration : ReflectivePresentationDecl) (constructor : String)
    (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (.apply constructor
        [cospan.reifyWith left.lookupAtom? cospan.leftSlot
          (.fvar (left.atomName leftSlot))])
      (.apply constructor
        [cospan.reifyWith right.lookupAtom? cospan.rightSlot
          (.fvar (right.atomName rightSlot))]) := by
  apply CostStaticAtomKeyCospan.CommonRestorationApex.apply constructor
  exact .cons
    (atom_of_scopedNormalEq left right leftSlot rightSlot normalEq normalScoped
      declaration _)
    (.nil _)

/-- A sealed left atom and an atom with the same normalized value form the
rigid unary apex directly.  Closedness is recovered from the sealed atom's
typed target fibre rather than repeated by the caller. -/
theorem rigidUnary_of_leftTargetSupportNil
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source leftColor
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source rightColor
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source leftColor targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source rightColor targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source leftColor targetFree leftInventory)
    (right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (normalEq : (left.atomValue leftSlot).key.normal =
      (right.atomValue rightSlot).key.normal)
    (sealed : (left.atomValue leftSlot).key.targetSupport = [])
    (declaration : ReflectivePresentationDecl) (constructor : String)
    (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (.apply constructor
        [cospan.reifyWith left.lookupAtom? cospan.leftSlot
          (.fvar (left.atomName leftSlot))])
      (.apply constructor
        [cospan.reifyWith right.lookupAtom? cospan.rightSlot
          (.fvar (right.atomName rightSlot))]) := by
  exact rigidUnary_of_scopedNormalEq left right leftSlot rightSlot normalEq
    (atomNormalScopedAtZero_of_targetSupport_nil left leftSlot sealed)
    declaration constructor depth

/-- Right-oriented companion of `rigidUnary_of_leftTargetSupportNil`. -/
theorem rigidUnary_of_rightTargetSupportNil
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source leftColor targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source rightColor targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source leftColor
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source rightColor
      targetFree rightTable}
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source leftColor targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source rightColor targetFree
      rightTable rightValues rightRoot}
    (left : CostStaticAtomEnvironment source leftColor targetFree leftInventory)
    (right : CostStaticAtomEnvironment source rightColor targetFree
      rightInventory)
    (leftSlot : Fin left.atomCount) (rightSlot : Fin right.atomCount)
    (normalEq : (left.atomValue leftSlot).key.normal =
      (right.atomValue rightSlot).key.normal)
    (sealed : (right.atomValue rightSlot).key.targetSupport = [])
    (declaration : ReflectivePresentationDecl) (constructor : String)
    (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (.apply constructor
        [cospan.reifyWith left.lookupAtom? cospan.leftSlot
          (.fvar (left.atomName leftSlot))])
      (.apply constructor
        [cospan.reifyWith right.lookupAtom? cospan.rightSlot
          (.fvar (right.atomName rightSlot))]) := by
  have rightNormalWellScoped :=
    atomNormalScopedAtZero_of_targetSupport_nil right rightSlot sealed
  have leftNormalWellScoped :
      (left.atomValue leftSlot).key.normal.isWellScopedAt 0 = true := by
    simpa only [normalEq] using rightNormalWellScoped
  exact rigidUnary_of_scopedNormalEq left right leftSlot rightSlot normalEq
    leftNormalWellScoped declaration constructor depth

end RhoMatchedStaticFramesApex

namespace CostStaticPlanStopped

/-- Two stopped boundary occurrences form a semantic leaf when their exact
selected child normals agree, even if their retained supports and complete
semantic keys differ.

The stopped views and embeddings select the actual recursive children.  The
only cross-child premise is equality of the normal patterns computed by those
children; static-decomposition unambiguity then identifies each selected
environment atom with its positional child value.  A sealed left atom supplies
the closedness needed by the depth-uniform restoration terminal. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_of_normalEq
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (normalEq :
      ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern =
        ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern)
    (sealed :
      (leftEnvironment.atomValue leftSlot).key.targetSupport = [])
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  have leftAtom := left.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEmbedding
      leftTrees leftEnvironment leftSlot leftSelected
  have rightAtom := right.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition rightEmbedding
      rightTrees rightEnvironment rightSlot rightSelected
  have leftNormal := congrArg (fun atom => atom.key.normal) leftAtom
  have rightNormal := congrArg (fun atom => atom.key.normal) rightAtom
  have atomNormalEq :
      (leftEnvironment.atomValue leftSlot).key.normal =
        (rightEnvironment.atomValue rightSlot).key.normal := by
    calc
      (leftEnvironment.atomValue leftSlot).key.normal =
          ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
            (normalizeStatic :=
              rhoHereditaryNormalizationKernel.normalize)).pattern := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue,
          CostRegionTree.normalizedBoundaryValue_pattern] using leftNormal
      _ = ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
            (normalizeStatic :=
              rhoHereditaryNormalizationKernel.normalize)).pattern :=
        normalEq
      _ = (rightEnvironment.atomValue rightSlot).key.normal := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue,
          CostRegionTree.normalizedBoundaryValue_pattern] using rightNormal.symm
  exact RhoMatchedStaticFramesApex.atom_of_leftTargetSupportNil
    leftEnvironment rightEnvironment leftSlot rightSlot atomNormalEq sealed
      declaration depth

/-- Right-sealed companion of
`selectedEnvironmentAtoms_commonRestorationApex_of_normalEq`.

The exact selected child normals again determine the two environment values;
this orientation recovers closedness from the right atom instead. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_of_rightNormalEq
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (normalEq :
      ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern =
        ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern)
    (sealed :
      (rightEnvironment.atomValue rightSlot).key.targetSupport = [])
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  have leftAtom := left.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEmbedding
      leftTrees leftEnvironment leftSlot leftSelected
  have rightAtom := right.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition rightEmbedding
      rightTrees rightEnvironment rightSlot rightSelected
  have leftNormal := congrArg (fun atom => atom.key.normal) leftAtom
  have rightNormal := congrArg (fun atom => atom.key.normal) rightAtom
  have atomNormalEq :
      (leftEnvironment.atomValue leftSlot).key.normal =
        (rightEnvironment.atomValue rightSlot).key.normal := by
    calc
      (leftEnvironment.atomValue leftSlot).key.normal =
          ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
            (normalizeStatic :=
              rhoHereditaryNormalizationKernel.normalize)).pattern := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue,
          CostRegionTree.normalizedBoundaryValue_pattern] using leftNormal
      _ = ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
            (normalizeStatic :=
              rhoHereditaryNormalizationKernel.normalize)).pattern :=
        normalEq
      _ = (rightEnvironment.atomValue rightSlot).key.normal := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue,
          CostRegionTree.normalizedBoundaryValue_pattern] using rightNormal.symm
  exact RhoMatchedStaticFramesApex.atom_of_rightTargetSupportNil
    leftEnvironment rightEnvironment leftSlot rightSlot atomNormalEq sealed
      declaration depth

/-- Two stopped boundary occurrences with equal retained target support form
a semantic restoration leaf as soon as their exact selected child normals
agree.  Unlike the sealed variants, this theorem does not need closedness:
the supported substitution observes the same weakening offset on both sides.

The complete semantic keys may still differ in provenance or source type;
only the support and normalized value components executed by restoration are
identified. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_of_sameSupportNormalEq
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (normalEq :
      ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern =
        ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern)
    (supportEq : left.certified.typed.boundary.targetSupport =
      right.certified.typed.boundary.targetSupport)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  have leftAtom := left.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition leftEmbedding
      leftTrees leftEnvironment leftSlot leftSelected
  have rightAtom := right.environmentAtom_eq_selectedTree
    (kernel := rhoHereditaryNormalizationKernel)
    CostCanonicalLaws.rho_unambiguousStaticDecomposition rightEmbedding
      rightTrees rightEnvironment rightSlot rightSelected
  have leftSupport := congrArg (fun atom => atom.key.targetSupport) leftAtom
  have rightSupport := congrArg (fun atom => atom.key.targetSupport) rightAtom
  have atomSupportEq :
      (leftEnvironment.atomValue leftSlot).key.targetSupport =
        (rightEnvironment.atomValue rightSlot).key.targetSupport := by
    calc
      (leftEnvironment.atomValue leftSlot).key.targetSupport =
          left.certified.typed.boundary.targetSupport := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue] using leftSupport
      _ = right.certified.typed.boundary.targetSupport := supportEq
      _ = (rightEnvironment.atomValue rightSlot).key.targetSupport := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue] using rightSupport.symm
  have leftNormal := congrArg (fun atom => atom.key.normal) leftAtom
  have rightNormal := congrArg (fun atom => atom.key.normal) rightAtom
  have atomNormalEq :
      (leftEnvironment.atomValue leftSlot).key.normal =
        (rightEnvironment.atomValue rightSlot).key.normal := by
    calc
      (leftEnvironment.atomValue leftSlot).key.normal =
          ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
            (normalizeStatic :=
              rhoHereditaryNormalizationKernel.normalize)).pattern := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue,
          CostRegionTree.normalizedBoundaryValue_pattern] using leftNormal
      _ = ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
            (normalizeStatic :=
              rhoHereditaryNormalizationKernel.normalize)).pattern := normalEq
      _ = (rightEnvironment.atomValue rightSlot).key.normal := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue,
          CostRegionTree.normalizedBoundaryValue_pattern] using rightNormal.symm
  apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
  apply PatternLeafAligned.leaf
  intro restoreDepth
  exact
    leftEnvironment.substituteAt_commonReifiedAtom_eq_of_restorationComponents
      rightEnvironment leftSlot rightSlot atomSupportEq atomNormalEq
        restoreDepth

/-- Lift an already established semantic atom apex through the exact stopped
plan contexts.  This separates the structural context transport from the
particular reason the selected leaves restore together. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_through_contexts_of_atomApex
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (atomApex :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        declaration holeDepth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot)))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))))
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := rhoCIGSLT) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify
          (left.skeletonContext.fill
            (.fvar left.boundaryOccurrence.name))))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify
          (right.skeletonContext.fill
            (.fvar right.boundaryOccurrence.name)))) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let lifted := contexts.fill atomApex
  have leftFilled := cospan.reifyEnvironmentContext_fill leftEnvironment
    cospan.leftSlot left.skeletonContext
      (.fvar left.boundaryOccurrence.name)
  have rightFilled := cospan.reifyEnvironmentContext_fill rightEnvironment
    cospan.rightSlot right.skeletonContext
      (.fvar right.boundaryOccurrence.name)
  have leftSelectedAtBoundary :
      leftEnvironment.slotOfName?
          (costRegionBoundaryVariableName left.certified.typed.boundary) =
        some leftSlot := by
    simpa only [left.boundaryOccurrence_name] using leftSelected
  have rightSelectedAtBoundary :
      rightEnvironment.slotOfName?
          (costRegionBoundaryVariableName right.certified.typed.boundary) =
        some rightSlot := by
    simpa only [right.boundaryOccurrence_name] using rightSelected
  have leftHole :
      leftEnvironment.reify (.fvar left.boundaryOccurrence.name) =
        .fvar (leftEnvironment.atomName leftSlot) := by
    simp [CostStaticAtomEnvironment.reify,
      CostStaticAtomEnvironment.reifyName, leftSelectedAtBoundary]
  have rightHole :
      rightEnvironment.reify (.fvar right.boundaryOccurrence.name) =
        .fvar (rightEnvironment.atomName rightSlot) := by
    simp [CostStaticAtomEnvironment.reify,
      CostStaticAtomEnvironment.reifyName, rightSelectedAtBoundary]
  rw [leftHole] at leftFilled
  rw [rightHole] at rightFilled
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftFilled rightFilled lifted

/-- Complete-root companion of
`selectedEnvironmentAtoms_commonRestorationApex_through_contexts_of_atomApex`.
The stopped equalities are used only for the final endpoint casts. -/
noncomputable def selectedRoots_commonRestorationApex_of_atomApex
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values rhoCIGSLT color
      targetFree rightTable}
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable leftValues leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable rightValues rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (atomApex :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
        declaration holeDepth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot)))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))))
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := rhoCIGSLT) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let filled :=
    selectedEnvironmentAtoms_commonRestorationApex_through_contexts_of_atomApex
      left right leftEnvironment rightEnvironment leftSlot leftSelected
        rightSlot rightSelected declaration depth holeDepth atomApex contexts
  have leftSkeletonEq :
      left.skeletonContext.fill (.fvar left.boundaryOccurrence.name) =
        leftRootAbstract := by
    simpa only [left.boundaryOccurrence_name] using left.abstract_eq.symm
  have rightSkeletonEq :
      right.skeletonContext.fill (.fvar right.boundaryOccurrence.name) =
        rightRootAbstract := by
    simpa only [right.boundaryOccurrence_name] using right.abstract_eq.symm
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (congrArg (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot)
      (congrArg leftEnvironment.reify leftSkeletonEq))
    (congrArg (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot)
      (congrArg rightEnvironment.reify rightSkeletonEq))
    filled

/-- Lift an unequal-support stopped/stopped semantic leaf through the exact
independently reified plan contexts.

The caller supplies only structural context alignment.  The selected child
normal equality and the sealed-side disjunction construct the semantic leaf;
the stopped witnesses and embeddings retain the two actual occurrences. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_through_contexts_of_normalEq
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (normalEq :
      ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern =
        ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern)
    (sealed :
      (leftEnvironment.atomValue leftSlot).key.targetSupport = [] ∨
        (rightEnvironment.atomValue rightSlot).key.targetSupport = [])
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := rhoCIGSLT) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify
          (left.skeletonContext.fill
            (.fvar left.boundaryOccurrence.name))))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify
          (right.skeletonContext.fill
            (.fvar right.boundaryOccurrence.name)))) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let leaf : CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
      declaration holeDepth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
    rcases sealed with leftSealed | rightSealed
    · exact selectedEnvironmentAtoms_commonRestorationApex_of_normalEq
        left right leftEmbedding rightEmbedding leftTrees rightTrees
          leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
          rightSelected normalEq leftSealed declaration holeDepth
    · exact selectedEnvironmentAtoms_commonRestorationApex_of_rightNormalEq
        left right leftEmbedding rightEmbedding leftTrees rightTrees
          leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
          rightSelected normalEq rightSealed declaration holeDepth
  let lifted := contexts.fill leaf
  have leftFilled := cospan.reifyEnvironmentContext_fill leftEnvironment
    cospan.leftSlot left.skeletonContext
      (.fvar left.boundaryOccurrence.name)
  have rightFilled := cospan.reifyEnvironmentContext_fill rightEnvironment
    cospan.rightSlot right.skeletonContext
      (.fvar right.boundaryOccurrence.name)
  have leftSelectedAtBoundary :
      leftEnvironment.slotOfName?
          (costRegionBoundaryVariableName left.certified.typed.boundary) =
        some leftSlot := by
    simpa only [left.boundaryOccurrence_name] using leftSelected
  have rightSelectedAtBoundary :
      rightEnvironment.slotOfName?
          (costRegionBoundaryVariableName right.certified.typed.boundary) =
        some rightSlot := by
    simpa only [right.boundaryOccurrence_name] using rightSelected
  have leftHole :
      leftEnvironment.reify (.fvar left.boundaryOccurrence.name) =
        .fvar (leftEnvironment.atomName leftSlot) := by
    simp [CostStaticAtomEnvironment.reify,
      CostStaticAtomEnvironment.reifyName, leftSelectedAtBoundary]
  have rightHole :
      rightEnvironment.reify (.fvar right.boundaryOccurrence.name) =
        .fvar (rightEnvironment.atomName rightSlot) := by
    simp [CostStaticAtomEnvironment.reify,
      CostStaticAtomEnvironment.reifyName, rightSelectedAtBoundary]
  rw [leftHole] at leftFilled
  rw [rightHole] at rightFilled
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftFilled rightFilled lifted

/-- Complete-root companion of the unequal-support context lift.

The stored stopped equalities perform the final endpoint casts after every
semantic and structural step has already been justified. -/
noncomputable def selectedRoots_commonRestorationApex_of_normalEq
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped rhoCIGSLT color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped rhoCIGSLT color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable rhoCIGSLT color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees rhoCIGSLT targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      leftTable
      (leftTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      rightTable
      (rightTrees.normalizeValues
        (normalizeStatic := rhoHereditaryStaticNormalizer))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (normalEq :
      ((left.selectedTreeFromForest leftEmbedding leftTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern =
        ((right.selectedTreeFromForest rightEmbedding rightTrees).normalize
          (normalizeStatic :=
            rhoHereditaryNormalizationKernel.normalize)).pattern)
    (sealed :
      (leftEnvironment.atomValue leftSlot).key.targetSupport = [] ∨
        (rightEnvironment.atomValue rightSlot).key.targetSupport = [])
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := rhoCIGSLT) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let filled :=
    selectedEnvironmentAtoms_commonRestorationApex_through_contexts_of_normalEq
      left right leftEmbedding rightEmbedding leftTrees rightTrees leftEnvironment
        rightEnvironment leftSlot leftSelected rightSlot rightSelected normalEq
        sealed declaration depth holeDepth contexts
  have leftSkeletonEq :
      left.skeletonContext.fill (.fvar left.boundaryOccurrence.name) =
        leftRootAbstract := by
    simpa only [left.boundaryOccurrence_name] using left.abstract_eq.symm
  have rightSkeletonEq :
      right.skeletonContext.fill (.fvar right.boundaryOccurrence.name) =
        rightRootAbstract := by
    simpa only [right.boundaryOccurrence_name] using right.abstract_eq.symm
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (congrArg (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot)
      (congrArg leftEnvironment.reify leftSkeletonEq))
    (congrArg (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot)
      (congrArg rightEnvironment.reify rightSkeletonEq))
    filled

end CostStaticPlanStopped

namespace RhoMatchedStaticFramesCut

/-- A semantic apex closes a matched-frame cut at the selected parent root. -/
noncomputable def ofApex
    {targetFree : WellSorted.FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree LanguageDefContinuedInteraction.rhoCIGSLT
      targetFree available outer leftPattern type}
    {right : CostRegionTree LanguageDefContinuedInteraction.rhoCIGSLT
      targetFree available outer rightPattern type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (apex : RhoMatchedStaticFramesApex leftView rightView) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.RhoMatchedStaticFramesCut
      (left := left) (right := right) (color := color) leftView rightView :=
  .terminal apex

end RhoMatchedStaticFramesCut

namespace RhoCanonicalStaticPairSemanticCut

/-- A same-colour restoration apex closes the provider's aligned arm without
requiring ordinary canonical equality of the common atomized frames. -/
noncomputable def matchedOfApex
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree LanguageDefContinuedInteraction.rhoCIGSLT
      targetFree available outer leftPattern type}
    {right : CostRegionTree LanguageDefContinuedInteraction.rhoCIGSLT
      targetFree available outer rightPattern type}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (roots : Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.CanonicalRootAligned
      (costStaticReflectivePresentationDecl
        LanguageDefContinuedInteraction.rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern rightPattern)
    (apex : RhoMatchedStaticFramesApex leftView rightView) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.aligned color leftView rightView roots) :=
  .matched leftView rightView roots
    (RhoMatchedStaticFramesCut.ofApex leftView rightView apex)

end RhoCanonicalStaticPairSemanticCut

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
