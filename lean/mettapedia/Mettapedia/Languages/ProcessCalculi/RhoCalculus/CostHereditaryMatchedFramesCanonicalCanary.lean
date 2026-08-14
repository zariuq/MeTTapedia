import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesRestorationApex
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalInversion

/-!
# Matched-frame canonicality boundary canary

Raw endpoint canonical equality does not imply ordinary canonical equality of
the atomized common frames.  A boundary sealed by an authored quote is
planned at empty support, while the same exposed boundary is planned at the
ambient support.  Those supports are part of the semantic atom key, so the
two occurrences receive distinct common names even though their restored
values agree.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace CostHereditaryMatchedFramesCanonicalCanary

def declaration : ReflectivePresentationDecl :=
  costStaticReflectivePresentationDecl rhoCIGSLT .base
    rhoReflectivePresentation.toReflectivePresentationDecl

def wrappedValue : Pattern :=
  .apply (costWrappedConstructorName "NQuote")
    [.apply (costWrappedConstructorName "PZero") []]

def ambientType : TypeExpr := .base (costBaseSortName "Name")

def leftPattern : Pattern :=
  .apply (costBaseConstructorName "PDrop")
    [.apply (costBaseConstructorName "NQuote")
      [.apply (costBaseConstructorName "PDrop") [wrappedValue]]]

def rightPattern : Pattern :=
  .apply (costBaseConstructorName "PDrop") [wrappedValue]

theorem endpoint_canonical :
    canonicalize declaration leftPattern =
      canonicalize declaration rightPattern := by
  decide

theorem left_not_collapsing : ¬ CollapsingRoot declaration leftPattern := by
  intro collapsing
  rcases collapsing with ⟨arguments, equality⟩ | ⟨elements, equality⟩
  · exact absurd (Pattern.apply.inj equality).1 (by decide)
  · exact Pattern.noConfusion equality

theorem right_not_collapsing : ¬ CollapsingRoot declaration rightPattern := by
  intro collapsing
  rcases collapsing with ⟨arguments, equality⟩ | ⟨elements, equality⟩
  · exact absurd (Pattern.apply.inj equality).1 (by decide)
  · exact Pattern.noConfusion equality

theorem leftWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [ambientType]
      (.base (costBaseSortName "Proc")) leftPattern :=
  (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [ambientType]
    (.base (costBaseSortName "Proc")) leftPattern).mp (by decide)

theorem rightWellSorted :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [ambientType]
      (.base (costBaseSortName "Proc")) rightPattern :=
  (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [ambientType]
    (.base (costBaseSortName "Proc")) rightPattern).mp (by decide)

def leftCoreTerm : WellSorted.OpenTerm rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [ambientType]
      (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) :=
  ⟨leftPattern, leftWellSorted.1⟩

def rightCoreTerm : WellSorted.OpenTerm rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [ambientType]
      (CostStaticColor.base.mapLangSort rhoCIGSLT rhoProc) :=
  ⟨rightPattern, rightWellSorted.1⟩

def leftPlan :=
  (buildCostStaticRegionPlan? rhoCIGSLT .base FreeTypeContext.empty
    (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base
      [ambientType]) [ambientType]
    (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [ambientType])
    [ambientType] .hole leftPattern (.base "Proc")).get (by decide)

def rightPlan :=
  (buildCostStaticRegionPlan? rhoCIGSLT .base FreeTypeContext.empty
    (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base
      [ambientType]) [ambientType]
    (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [ambientType])
    [ambientType] .hole rightPattern (.base "Proc")).get (by decide)

theorem leftPlan_rootStatic : leftPlan.isStaticRoot = true := by decide

theorem rightPlan_rootStatic : rightPlan.isStaticRoot = true := by decide

def leftBoundary : TypedCostRegionBoundary rhoCIGSLT .base
    FreeTypeContext.empty := leftPlan.boundaryTable.entries[0]'(by decide)

def rightBoundary : TypedCostRegionBoundary rhoCIGSLT .base
    FreeTypeContext.empty := rightPlan.boundaryTable.entries[0]'(by decide)

theorem leftPlan_abstractPattern : leftPlan.abstractPattern =
    .apply "PDrop"
      [.apply "NQuote"
        [.apply "PDrop"
          [.fvar (costRegionBoundaryVariableName leftBoundary.boundary)]]] := by
  rfl

theorem rightPlan_abstractPattern : rightPlan.abstractPattern =
    .apply "PDrop"
      [.fvar (costRegionBoundaryVariableName rightBoundary.boundary)] := by
  rfl

theorem leftBoundary_targetSupport : leftBoundary.boundary.targetSupport = [] :=
  rfl

theorem rightBoundary_targetSupport :
    rightBoundary.boundary.targetSupport = [ambientType] := rfl

noncomputable def leftNode :
    CostStaticRegionNode rhoCIGSLT .base FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan (sourceSort := rhoProc) leftCoreTerm leftPlan
    leftPlan_rootStatic

noncomputable def rightNode :
    CostStaticRegionNode rhoCIGSLT .base FreeTypeContext.empty :=
  CostStaticRegionNode.ofPlan (sourceSort := rhoProc) rightCoreTerm rightPlan
    rightPlan_rootStatic

theorem wrappedValueWellSortedSealed :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [] ambientType wrappedValue :=
  (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [] ambientType wrappedValue).mp
      (by decide)

theorem wrappedValueWellSortedExposed :
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      FreeTypeContext.empty [ambientType] ambientType wrappedValue :=
  (ReflectiveWellSorted.checkOpenPatternWellSorted_eq_true_iff
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [ambientType] ambientType
    wrappedValue).mp (by decide)

noncomputable def leftChild : CostRegionTree rhoCIGSLT FreeTypeContext.empty
    [] [] wrappedValue ambientType :=
  (CostRegionTree.build? (source := rhoCIGSLT)
    (targetFree := FreeTypeContext.empty) [] [] wrappedValue
      ambientType).get
    (CostRegionTree.build?_isSome_of_wellSorted wrappedValueWellSortedSealed)

noncomputable def rightChild : CostRegionTree rhoCIGSLT FreeTypeContext.empty
    [ambientType] [] wrappedValue ambientType :=
  (CostRegionTree.build? (source := rhoCIGSLT)
    (targetFree := FreeTypeContext.empty) [ambientType] [] wrappedValue
      ambientType).get
    (CostRegionTree.build?_isSome_of_wellSorted
      wrappedValueWellSortedExposed)

noncomputable abbrev leftChildren : CostRegionBoundaryTrees rhoCIGSLT
    FreeTypeContext.empty .base leftNode.finiteBoundaryTable :=
  .cons leftChild .nil

noncomputable abbrev rightChildren : CostRegionBoundaryTrees rhoCIGSLT
    FreeTypeContext.empty .base rightNode.finiteBoundaryTable :=
  .cons rightChild .nil

noncomputable def leftTree : CostRegionTree rhoCIGSLT FreeTypeContext.empty
    [ambientType] [] leftPattern (.base (costBaseSortName "Proc")) :=
  .static leftNode leftChildren

noncomputable def rightTree : CostRegionTree rhoCIGSLT FreeTypeContext.empty
    [ambientType] [] rightPattern (.base (costBaseSortName "Proc")) :=
  .static rightNode rightChildren

noncomputable def leftView : leftTree.StaticRootView .base where
  node := leftNode
  children := leftChildren
  patternEq := rfl
  availableEq := rfl
  typeEq := rfl
  treeEq := rfl

noncomputable def rightView : rightTree.StaticRootView .base where
  node := rightNode
  children := rightChildren
  patternEq := rfl
  availableEq := rfl
  typeEq := rfl
  treeEq := rfl

theorem endpoint_roots_aligned :
    CanonicalRootAligned declaration leftPattern rightPattern := by
  apply CanonicalRootAligned.apply (by decide)
  exact .cons (by decide) .nil

noncomputable def leftValues := leftChildren.normalizeValues
  (normalizeStatic := rhoHereditaryStaticNormalizer)

noncomputable def rightValues := rightChildren.normalizeValues
  (normalizeStatic := rhoHereditaryStaticNormalizer)

noncomputable def leftInventory :=
  (leftNode.semanticAtomEnvironment leftValues).1

noncomputable def rightInventory :=
  (rightNode.semanticAtomEnvironment rightValues).1

noncomputable def leftEnvironment :=
  CostStaticAtomEnvironment.ofInventory leftInventory

noncomputable def rightEnvironment :=
  CostStaticAtomEnvironment.ofInventory rightInventory

noncomputable def cospan :=
  leftEnvironment.semanticKeyCospan rightEnvironment

/-- The same closed boundary value normalizes identically in the sealed and
exposed reflective-availability fibres used by the counterexample. -/
theorem boundary_child_normals_equal :
    (leftChild.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
    (rightChild.normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  let pair : CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel FreeTypeContext.empty [ambientType] []
        wrappedValue wrappedValue ambientType :=
    { leftTree := rightChild
      rightTree := rightChild
      alignment := .refl rightChild }
  exact RhoMatchedBoundaryLeaf.normalize_pattern_eq_of_leftSealed_pair
    leftChild rightChild (by decide) (by decide) pair

theorem leftNode_skeleton_pattern : leftNode.skeleton.1 =
    .apply "PDrop"
      [.apply "NQuote"
        [.apply "PDrop"
          [.fvar (costRegionBoundaryVariableName leftBoundary.boundary)]]] := by
  rfl

theorem rightNode_skeleton_pattern : rightNode.skeleton.1 =
    .apply "PDrop"
      [.fvar (costRegionBoundaryVariableName rightBoundary.boundary)] := by
  rfl

theorem leftBoundary_mem :
    leftBoundary ∈ leftNode.boundaryTable.entries := by
  change leftBoundary ∈ leftPlan.boundaryTable.entries
  simp [leftBoundary]

theorem rightBoundary_mem :
    rightBoundary ∈ rightNode.boundaryTable.entries := by
  change rightBoundary ∈ rightPlan.boundaryTable.entries
  simp [rightBoundary]

/-- Positional indices of the sole recursive boundary children. -/
def leftTableIndex : Fin leftNode.boundaryTable.entries.length :=
  ⟨0, by
    change 0 < leftPlan.boundaryTable.entries.length
    decide⟩

def rightTableIndex : Fin rightNode.boundaryTable.entries.length :=
  ⟨0, by
    change 0 < rightPlan.boundaryTable.entries.length
    decide⟩

theorem leftTableIndex_boundary :
    (leftChildren.getEntry leftTableIndex).boundary = leftBoundary := by
  rw [CostRegionBoundaryTrees.getEntry_boundary]
  change leftPlan.boundaryTable.entries.get _ =
    leftPlan.boundaryTable.entries.get _
  congr 1

theorem rightTableIndex_boundary :
    (rightChildren.getEntry rightTableIndex).boundary = rightBoundary := by
  rw [CostRegionBoundaryTrees.getEntry_boundary]
  change rightPlan.boundaryTable.entries.get _ =
    rightPlan.boundaryTable.entries.get _
  congr 1

/-- Positional lookup reaches the left boundary child without unfolding the
dependent finite table. -/
theorem leftTableIndex_normal :
    ((leftChildren.getEntry leftTableIndex).tree.normalizedBoundaryValue
      rhoHereditaryNormalizationKernel).1 =
      (leftChild.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  let reindexed := (leftChildren.getEntry leftTableIndex).tree.reindexBoundary
    leftTableIndex_boundary
  have normalizedEq := CostRegionTree.normalize_pattern_eq_of_unambiguous
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoHereditaryNormalizationKernel reindexed leftChild
      leftBoundary.contentObjectPattern
  calc
    ((leftChildren.getEntry leftTableIndex).tree.normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 =
      (reindexed.normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 :=
      (CostRegionTree.reindexBoundary_normalizedBoundaryValue
        leftTableIndex_boundary _).symm
    _ = (leftChild.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      exact normalizedEq

/-- Exposed-side companion of `leftTableIndex_normal`. -/
theorem rightTableIndex_normal :
    ((rightChildren.getEntry rightTableIndex).tree.normalizedBoundaryValue
      rhoHereditaryNormalizationKernel).1 =
      (rightChild.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  let reindexed :=
    (rightChildren.getEntry rightTableIndex).tree.reindexBoundary
      rightTableIndex_boundary
  have normalizedEq := CostRegionTree.normalize_pattern_eq_of_unambiguous
    CostCanonicalLaws.rho_unambiguousStaticDecomposition
    rhoHereditaryNormalizationKernel reindexed rightChild
      rightBoundary.contentObjectPattern
  calc
    ((rightChildren.getEntry rightTableIndex).tree.normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 =
      (reindexed.normalizedBoundaryValue
        rhoHereditaryNormalizationKernel).1 :=
      (CostRegionTree.reindexBoundary_normalizedBoundaryValue
        rightTableIndex_boundary _).symm
    _ = (rightChild.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      exact normalizedEq

/-- The two boundary atoms carry the same hereditary normal value even
though their complete keys retain different target supports. -/
theorem boundary_atom_normals_equal
    (leftSlot : Fin leftEnvironment.atomCount)
    (rightSlot : Fin rightEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftBoundary.boundary) = some leftSlot)
    (rightSelected : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName rightBoundary.boundary) =
        some rightSlot) :
    (leftEnvironment.atomValue leftSlot).key.normal =
      (rightEnvironment.atomValue rightSlot).key.normal := by
  have leftNameMem : costRegionBoundaryVariableName leftBoundary.boundary ∈
      leftNode.skeleton.1.freeFvarNames := by
    rw [leftNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  have rightNameMem : costRegionBoundaryVariableName rightBoundary.boundary ∈
      rightNode.skeleton.1.freeFvarNames := by
    rw [rightNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftOccurrence, leftOccurrenceName⟩ :=
    leftNode.skeleton_fvar_covered _ leftNameMem
  obtain ⟨rightOccurrence, rightOccurrenceName⟩ :=
    rightNode.skeleton_fvar_covered _ rightNameMem
  have leftSelectedAtOccurrence :
      leftEnvironment.slotOfName? leftOccurrence.name = some leftSlot := by
    simpa [leftOccurrenceName] using leftSelected
  have rightSelectedAtOccurrence :
      rightEnvironment.slotOfName? rightOccurrence.name = some rightSlot := by
    simpa [rightOccurrenceName] using rightSelected
  have leftOccurrenceBoundary : leftOccurrence.name =
      costRegionBoundaryVariableName
        (leftChildren.getEntry leftTableIndex).boundary.boundary := by
    rw [leftTableIndex_boundary, leftOccurrenceName]
  have rightOccurrenceBoundary : rightOccurrence.name =
      costRegionBoundaryVariableName
        (rightChildren.getEntry rightTableIndex).boundary.boundary := by
    rw [rightTableIndex_boundary, rightOccurrenceName]
  have leftAtom :=
    CostStaticAtomEnvironment.atomValue_eq_normalizedBoundaryValue_of_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition leftChildren
        leftEnvironment
        leftTableIndex leftOccurrence leftOccurrenceBoundary leftSlot
          leftSelectedAtOccurrence
  have rightAtom :=
    CostStaticAtomEnvironment.atomValue_eq_normalizedBoundaryValue_of_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition rightChildren
        rightEnvironment
        rightTableIndex rightOccurrence rightOccurrenceBoundary rightSlot
          rightSelectedAtOccurrence
  have leftNormal := congrArg (fun atom => atom.key.normal) leftAtom
  have rightNormal := congrArg (fun atom => atom.key.normal) rightAtom
  calc
    (leftEnvironment.atomValue leftSlot).key.normal =
        (leftChild.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
      simpa only [TypedCostStaticAtom.ofBoundaryValue,
        leftTableIndex_normal] using leftNormal
    _ = (rightChild.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
      boundary_child_normals_equal
    _ = (rightEnvironment.atomValue rightSlot).key.normal := by
      simpa only [TypedCostStaticAtom.ofBoundaryValue,
        rightTableIndex_normal] using rightNormal.symm

/-- The left selected atom is precisely the quote-sealed boundary atom. -/
theorem left_atom_targetSupport_nil
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftBoundary.boundary) =
        some leftSlot) :
    (leftEnvironment.atomValue leftSlot).key.targetSupport = [] := by
  have leftNameMem : costRegionBoundaryVariableName leftBoundary.boundary ∈
      leftNode.skeleton.1.freeFvarNames := by
    rw [leftNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftOccurrence, leftOccurrenceName⟩ :=
    leftNode.skeleton_fvar_covered _ leftNameMem
  have leftSelectedAtOccurrence :
      leftEnvironment.slotOfName? leftOccurrence.name = some leftSlot := by
    simpa [leftOccurrenceName] using leftSelected
  have leftOccurrenceBoundary : leftOccurrence.name =
      costRegionBoundaryVariableName
        (leftChildren.getEntry leftTableIndex).boundary.boundary := by
    rw [leftTableIndex_boundary, leftOccurrenceName]
  have leftAtom :=
    CostStaticAtomEnvironment.atomValue_eq_normalizedBoundaryValue_of_getEntry
      (kernel := rhoHereditaryNormalizationKernel)
      CostCanonicalLaws.rho_unambiguousStaticDecomposition leftChildren
        leftEnvironment
        leftTableIndex leftOccurrence leftOccurrenceBoundary leftSlot
          leftSelectedAtOccurrence
  have supportEq := congrArg (fun atom => atom.key.targetSupport) leftAtom
  simpa only [TypedCostStaticAtom.ofBoundaryValue, leftTableIndex_boundary,
    leftBoundary_targetSupport] using supportEq

/-- The unique boundary occurrences select distinct common names because
their complete semantic keys retain unequal target supports. -/
theorem exists_boundary_slots_with_distinct_common_names :
    ∃ (leftSlot : Fin leftEnvironment.atomCount)
      (rightSlot : Fin rightEnvironment.atomCount),
      leftEnvironment.slotOfName?
          (costRegionBoundaryVariableName leftBoundary.boundary) =
        some leftSlot ∧
      rightEnvironment.slotOfName?
          (costRegionBoundaryVariableName rightBoundary.boundary) =
        some rightSlot ∧
      cospan.commonAtomName (cospan.leftSlot leftSlot) ≠
        cospan.commonAtomName (cospan.rightSlot rightSlot) := by
  have leftNameMem : costRegionBoundaryVariableName leftBoundary.boundary ∈
      leftNode.skeleton.1.freeFvarNames := by
    rw [leftNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  have rightNameMem : costRegionBoundaryVariableName rightBoundary.boundary ∈
      rightNode.skeleton.1.freeFvarNames := by
    rw [rightNode_skeleton_pattern]
    simp [Pattern.freeFvarNames]
  obtain ⟨leftOccurrence, leftOccurrenceName⟩ :=
    leftNode.skeleton_fvar_covered _ leftNameMem
  obtain ⟨rightOccurrence, rightOccurrenceName⟩ :=
    rightNode.skeleton_fvar_covered _ rightNameMem
  obtain ⟨leftSlot, leftSelectedAtOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (leftEnvironment.slotOfName?_isSome_of_occurrence leftOccurrence)
  obtain ⟨rightSlot, rightSelectedAtOccurrence⟩ :=
    Option.isSome_iff_exists.mp
      (rightEnvironment.slotOfName?_isSome_of_occurrence rightOccurrence)
  have leftSelected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftBoundary.boundary) =
        some leftSlot := by
    simpa [leftOccurrenceName] using leftSelectedAtOccurrence
  have rightSelected : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName rightBoundary.boundary) =
        some rightSlot := by
    simpa [rightOccurrenceName] using rightSelectedAtOccurrence
  have leftSupport :
      (leftEnvironment.atomValue leftSlot).key.targetSupport = [] := by
    calc
      (leftEnvironment.atomValue leftSlot).key.targetSupport =
          leftNode.boundaryTable.sourceSupport leftOccurrence.name :=
        leftEnvironment.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
          leftOccurrence leftSlot leftSelectedAtOccurrence
      _ = leftNode.boundaryTable.sourceSupport
          (costRegionBoundaryVariableName leftBoundary.boundary) := by
        rw [leftOccurrenceName]
      _ = leftBoundary.boundary.targetSupport :=
        leftNode.boundaryTable.sourceSupport_boundaryVariable leftBoundary
          leftBoundary_mem
      _ = [] := leftBoundary_targetSupport
  have rightSupport :
      (rightEnvironment.atomValue rightSlot).key.targetSupport =
        [ambientType] := by
    calc
      (rightEnvironment.atomValue rightSlot).key.targetSupport =
          rightNode.boundaryTable.sourceSupport rightOccurrence.name :=
        rightEnvironment.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
          rightOccurrence rightSlot rightSelectedAtOccurrence
      _ = rightNode.boundaryTable.sourceSupport
          (costRegionBoundaryVariableName rightBoundary.boundary) := by
        rw [rightOccurrenceName]
      _ = rightBoundary.boundary.targetSupport :=
        rightNode.boundaryTable.sourceSupport_boundaryVariable rightBoundary
          rightBoundary_mem
      _ = [ambientType] := rightBoundary_targetSupport
  have keysNe : (leftEnvironment.atomValue leftSlot).key ≠
      (rightEnvironment.atomValue rightSlot).key := by
    intro keysEq
    have supportsEq := congrArg CostStaticAtomKey.targetSupport keysEq
    rw [leftSupport, rightSupport] at supportsEq
    exact absurd supportsEq (by decide)
  refine ⟨leftSlot, rightSlot, leftSelected, rightSelected, ?_⟩
  intro namesEq
  apply keysNe
  exact (cospan.crossExtensional leftSlot rightSlot).mp
    (cospan.commonAtomName_injective namesEq)

theorem left_common_source_frame
    (leftSlot : Fin leftEnvironment.atomCount)
    (selected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftBoundary.boundary) = some leftSlot) :
    cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
        leftNode.skeleton.toCore.1 =
      .apply "PDrop"
        [.apply "NQuote"
          [.apply "PDrop"
            [.fvar (cospan.commonAtomName (cospan.leftSlot leftSlot))]]] := by
  calc
    cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
        leftNode.skeleton.toCore.1 =
      cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
        (.apply "PDrop"
          [.apply "NQuote"
            [.apply "PDrop"
              [.fvar
                (costRegionBoundaryVariableName leftBoundary.boundary)]]]) :=
      congrArg (cospan.reifyWith leftEnvironment.slotOfName?
        cospan.leftSlot) leftNode_skeleton_pattern
    _ = _ := by
      simp [Pattern.renameFVars, CostStaticAtomKeyCospan.reifyNameWith,
        selected]

theorem right_common_source_frame
    (rightSlot : Fin rightEnvironment.atomCount)
    (selected : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName rightBoundary.boundary) =
        some rightSlot) :
    cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
        rightNode.skeleton.toCore.1 =
      .apply "PDrop"
        [.fvar (cospan.commonAtomName (cospan.rightSlot rightSlot))] := by
  calc
    cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
        rightNode.skeleton.toCore.1 =
      cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
        (.apply "PDrop"
          [.fvar
            (costRegionBoundaryVariableName rightBoundary.boundary)]) :=
      congrArg (cospan.reifyWith rightEnvironment.slotOfName?
        cospan.rightSlot) rightNode_skeleton_pattern
    _ = _ := by
      simp [Pattern.renameFVars, CostStaticAtomKeyCospan.reifyNameWith,
        selected]

/-- Endpoint-keyed form before common-cospan reification. -/
theorem left_endpoint_frame_keyed
    (leftSlot : Fin leftEnvironment.atomCount)
    (selected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftBoundary.boundary) = some leftSlot) :
    leftNode.canonicalizeReifiedTargetFrame leftEnvironment declaration =
      .apply (costBaseConstructorName "PDrop")
        [.fvar (leftEnvironment.atomName leftSlot)] := by
  have reifiedFrame : (leftNode.reifiedSourceFrame leftEnvironment).1 =
      .apply "PDrop"
        [.apply "NQuote"
          [.apply "PDrop"
            [.fvar (leftEnvironment.atomName leftSlot)]]] := by
    rw [leftNode.reifiedSourceFrame_pattern]
    calc
      leftEnvironment.reify leftNode.skeleton.1 =
          leftEnvironment.reify
            (.apply "PDrop"
              [.apply "NQuote"
                [.apply "PDrop"
                  [.fvar (costRegionBoundaryVariableName
                    leftBoundary.boundary)]]]) :=
        congrArg leftEnvironment.reify leftNode_skeleton_pattern
      _ = _ := by
        simp [Pattern.renameFVars, CostStaticAtomEnvironment.reifyName, selected]
  unfold declaration
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    leftNode leftEnvironment, reifiedFrame]
  simp [CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
    mapPatternList_eq_map, CostStaticColor.symbols, costBaseStaticSymbols,
    costBasePresentationSymbols, rhoReflectivePresentation,
    canonicalizeByDepths, canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- Exposed endpoint-keyed companion. -/
theorem right_endpoint_frame_keyed
    (rightSlot : Fin rightEnvironment.atomCount)
    (selected : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName rightBoundary.boundary) =
        some rightSlot) :
    rightNode.canonicalizeReifiedTargetFrame rightEnvironment declaration =
      .apply (costBaseConstructorName "PDrop")
        [.fvar (rightEnvironment.atomName rightSlot)] := by
  have reifiedFrame : (rightNode.reifiedSourceFrame rightEnvironment).1 =
      .apply "PDrop"
        [.fvar (rightEnvironment.atomName rightSlot)] := by
    rw [rightNode.reifiedSourceFrame_pattern]
    calc
      rightEnvironment.reify rightNode.skeleton.1 =
          rightEnvironment.reify
            (.apply "PDrop"
              [.fvar (costRegionBoundaryVariableName
                rightBoundary.boundary)]) :=
        congrArg rightEnvironment.reify rightNode_skeleton_pattern
      _ = _ := by
        simp [Pattern.renameFVars, CostStaticAtomEnvironment.reifyName, selected]
  unfold declaration
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    rightNode rightEnvironment, reifiedFrame]
  simp [CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
    mapPatternList_eq_map, CostStaticColor.symbols, costBaseStaticSymbols,
    costBasePresentationSymbols, rhoReflectivePresentation,
    canonicalizeByDepths, canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- The sealed endpoint has the expected keyed source canonical form before
constructor mapping and ambient-binder reinsertion. -/
theorem left_source_frame_keyed
    (leftSlot : Fin leftEnvironment.atomCount)
    (selected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftBoundary.boundary) = some leftSlot) :
    canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt leftNode
          leftEnvironment)
        rhoReflectivePresentation leftNode.targetBound.length 0
        (leftNode.reifiedSourceFrame leftEnvironment).1 =
      .apply "PDrop" [.fvar (leftEnvironment.atomName leftSlot)] := by
  have reifiedFrame : (leftNode.reifiedSourceFrame leftEnvironment).1 =
      .apply "PDrop"
        [.apply "NQuote"
          [.apply "PDrop"
            [.fvar (leftEnvironment.atomName leftSlot)]]] := by
    rw [leftNode.reifiedSourceFrame_pattern]
    calc
      leftEnvironment.reify leftNode.skeleton.1 =
          leftEnvironment.reify
            (.apply "PDrop"
              [.apply "NQuote"
                [.apply "PDrop"
                  [.fvar (costRegionBoundaryVariableName
                    leftBoundary.boundary)]]]) :=
        congrArg leftEnvironment.reify leftNode_skeleton_pattern
      _ = _ := by
        simp [Pattern.renameFVars, CostStaticAtomEnvironment.reifyName,
          selected]
  rw [reifiedFrame]
  simp [rhoReflectivePresentation, canonicalizeByDepths,
    canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- Exposed source-frame companion. -/
theorem right_source_frame_keyed
    (rightSlot : Fin rightEnvironment.atomCount)
    (selected : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName rightBoundary.boundary) =
        some rightSlot) :
    canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightNode
          rightEnvironment)
        rhoReflectivePresentation rightNode.targetBound.length 0
        (rightNode.reifiedSourceFrame rightEnvironment).1 =
      .apply "PDrop" [.fvar (rightEnvironment.atomName rightSlot)] := by
  have reifiedFrame : (rightNode.reifiedSourceFrame rightEnvironment).1 =
      .apply "PDrop"
        [.fvar (rightEnvironment.atomName rightSlot)] := by
    rw [rightNode.reifiedSourceFrame_pattern]
    calc
      rightEnvironment.reify rightNode.skeleton.1 =
          rightEnvironment.reify
            (.apply "PDrop"
              [.fvar (costRegionBoundaryVariableName
                rightBoundary.boundary)]) :=
        congrArg rightEnvironment.reify rightNode_skeleton_pattern
      _ = _ := by
        simp [Pattern.renameFVars, CostStaticAtomEnvironment.reifyName,
          selected]
  rw [reifiedFrame]
  simp [rhoReflectivePresentation, canonicalizeByDepths,
    canonicalizeListByDepths,
    Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

theorem left_common_frame_canonical
    (leftSlot : Fin leftEnvironment.atomCount)
    (selected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftBoundary.boundary) = some leftSlot) :
    canonicalize declaration
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftNode.reifyTargetFrame leftEnvironment)) =
      .apply (costBaseConstructorName "PDrop")
        [.fvar (cospan.commonAtomName (cospan.leftSlot leftSlot))] := by
  rw [CostStaticAtomEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton]
  rw [leftNode.mappedThickenedSkeleton_pattern]
  calc
    canonicalize declaration
        (cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
          (leftNode.thinning.thickenAmbientBVars 0
            (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
              leftNode.skeleton.toCore.1))) =
      canonicalize declaration
        (leftNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
            (cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
              leftNode.skeleton.toCore.1))) :=
      congrArg (canonicalize declaration)
        (cospan.reifyWith_mappedThickened leftEnvironment.slotOfName?
          cospan.leftSlot leftNode.thinning 0 leftNode.skeleton.toCore.1)
    _ = canonicalize declaration
        (leftNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
            (.apply "PDrop"
              [.apply "NQuote"
                [.apply "PDrop"
                  [.fvar (cospan.commonAtomName
                    (cospan.leftSlot leftSlot))]]]))) :=
      congrArg (fun pattern => canonicalize declaration
        (leftNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT) pattern)))
        (left_common_source_frame leftSlot selected)
    _ = _ := by
      simp only [CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
        mapPatternList_eq_map,
        CostStaticColor.symbols, costBaseStaticSymbols,
        costBasePresentationSymbols, List.map_cons, List.map_nil]
      let name := cospan.commonAtomName (cospan.leftSlot leftSlot)
      have dropNeQuote : declaration.dropConstructor ≠
          declaration.quoteConstructor := by decide
      change canonicalize declaration
          (.apply declaration.dropConstructor
            [.apply declaration.quoteConstructor
              [.apply declaration.dropConstructor [.fvar name]]]) =
        .apply declaration.dropConstructor [.fvar name]
      rw [canonicalize_apply_of_ne_quote declaration dropNeQuote]
      simp only [List.map_cons, List.map_nil]
      rw [canonicalize_quote_drop declaration dropNeQuote]
      simp [canonicalize]

theorem right_common_frame_canonical
    (rightSlot : Fin rightEnvironment.atomCount)
    (selected : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName rightBoundary.boundary) =
        some rightSlot) :
    canonicalize declaration
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightNode.reifyTargetFrame rightEnvironment)) =
      .apply (costBaseConstructorName "PDrop")
        [.fvar (cospan.commonAtomName (cospan.rightSlot rightSlot))] := by
  rw [CostStaticAtomEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton]
  rw [rightNode.mappedThickenedSkeleton_pattern]
  calc
    canonicalize declaration
        (cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
          (rightNode.thinning.thickenAmbientBVars 0
            (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
              rightNode.skeleton.toCore.1))) =
      canonicalize declaration
        (rightNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
            (cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
              rightNode.skeleton.toCore.1))) :=
      congrArg (canonicalize declaration)
        (cospan.reifyWith_mappedThickened rightEnvironment.slotOfName?
          cospan.rightSlot rightNode.thinning 0 rightNode.skeleton.toCore.1)
    _ = canonicalize declaration
        (rightNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
            (.apply "PDrop"
              [.fvar (cospan.commonAtomName
                (cospan.rightSlot rightSlot))]))) :=
      congrArg (fun pattern => canonicalize declaration
        (rightNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT) pattern)))
        (right_common_source_frame rightSlot selected)
    _ = _ := by
      simp only [CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
        mapPatternList_eq_map,
        CostStaticColor.symbols, costBaseStaticSymbols,
        costBasePresentationSymbols, List.map_cons, List.map_nil]
      let name := cospan.commonAtomName (cospan.rightSlot rightSlot)
      have dropNeQuote : declaration.dropConstructor ≠
          declaration.quoteConstructor := by decide
      change canonicalize declaration
          (.apply declaration.dropConstructor [.fvar name]) =
        .apply declaration.dropConstructor [.fvar name]
      rw [canonicalize_apply_of_ne_quote declaration dropNeQuote]
      simp [canonicalize]

/-- The keyed canonicalizer exposes the sealed-side boundary as the rigid
drop of its common semantic name. -/
theorem left_common_frame_keyed
    (leftSlot : Fin leftEnvironment.atomCount)
    (selected : leftEnvironment.slotOfName?
      (costRegionBoundaryVariableName leftBoundary.boundary) = some leftSlot) :
    canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration leftNode.targetBound.length
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftNode.reifyTargetFrame leftEnvironment)) =
      .apply (costBaseConstructorName "PDrop")
        [.fvar (cospan.commonAtomName (cospan.leftSlot leftSlot))] := by
  rw [CostStaticAtomEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton]
  rw [leftNode.mappedThickenedSkeleton_pattern]
  calc
    canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration leftNode.targetBound.length
        (cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
          (leftNode.thinning.thickenAmbientBVars 0
            (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
              leftNode.skeleton.toCore.1))) =
      canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration leftNode.targetBound.length
        (leftNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
            (cospan.reifyWith leftEnvironment.slotOfName? cospan.leftSlot
              leftNode.skeleton.toCore.1))) :=
      congrArg (canonicalizeByAt
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
          leftNode.targetBound.length)
        (cospan.reifyWith_mappedThickened leftEnvironment.slotOfName?
          cospan.leftSlot leftNode.thinning 0 leftNode.skeleton.toCore.1)
    _ = canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration leftNode.targetBound.length
        (leftNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
            (.apply "PDrop"
              [.apply "NQuote"
                [.apply "PDrop"
                  [.fvar (cospan.commonAtomName
                    (cospan.leftSlot leftSlot))]]]))) :=
      congrArg (fun pattern => canonicalizeByAt
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
          leftNode.targetBound.length
        (leftNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT) pattern)))
        (left_common_source_frame leftSlot selected)
    _ = _ := by
      simp only [CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
        mapPatternList_eq_map, CostStaticColor.symbols, costBaseStaticSymbols,
        costBasePresentationSymbols, List.map_cons, List.map_nil]
      let name := cospan.commonAtomName (cospan.leftSlot leftSlot)
      change canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration 1
          (.apply (costBaseConstructorName "PDrop")
            [.apply (costBaseConstructorName "NQuote")
              [.apply (costBaseConstructorName "PDrop") [.fvar name]]]) =
        .apply (costBaseConstructorName "PDrop") [.fvar name]
      have quoteEq : costBaseConstructorName "NQuote" =
          declaration.quoteConstructor := by decide
      have dropEq : costBaseConstructorName "PDrop" =
          declaration.dropConstructor := by decide
      simp [canonicalizeByAt, canonicalizeListByAt, quoteEq, dropEq,
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

/-- Exposed-side keyed canonical form. -/
theorem right_common_frame_keyed
    (rightSlot : Fin rightEnvironment.atomCount)
    (selected : rightEnvironment.slotOfName?
      (costRegionBoundaryVariableName rightBoundary.boundary) =
        some rightSlot) :
    canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration rightNode.targetBound.length
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightNode.reifyTargetFrame rightEnvironment)) =
      .apply (costBaseConstructorName "PDrop")
        [.fvar (cospan.commonAtomName (cospan.rightSlot rightSlot))] := by
  rw [CostStaticAtomEnvironment.reifyWith_reifyTargetFrame_eq_mappedThickenedSkeleton]
  rw [rightNode.mappedThickenedSkeleton_pattern]
  calc
    canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration rightNode.targetBound.length
        (cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
          (rightNode.thinning.thickenAmbientBVars 0
            (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
              rightNode.skeleton.toCore.1))) =
      canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration rightNode.targetBound.length
        (rightNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
            (cospan.reifyWith rightEnvironment.slotOfName? cospan.rightSlot
              rightNode.skeleton.toCore.1))) :=
      congrArg (canonicalizeByAt
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
          rightNode.targetBound.length)
        (cospan.reifyWith_mappedThickened rightEnvironment.slotOfName?
          cospan.rightSlot rightNode.thinning 0 rightNode.skeleton.toCore.1)
    _ = canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        declaration rightNode.targetBound.length
        (rightNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
            (.apply "PDrop"
              [.fvar (cospan.commonAtomName
                (cospan.rightSlot rightSlot))]))) :=
      congrArg (fun pattern => canonicalizeByAt
        (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration
          rightNode.targetBound.length
        (rightNode.thinning.thickenAmbientBVars 0
          (mapPattern (CostStaticColor.base.symbols rhoCIGSLT) pattern)))
        (right_common_source_frame rightSlot selected)
    _ = _ := by
      simp only [CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
        mapPatternList_eq_map, CostStaticColor.symbols, costBaseStaticSymbols,
        costBasePresentationSymbols, List.map_cons, List.map_nil]
      let name := cospan.commonAtomName (cospan.rightSlot rightSlot)
      change canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
          declaration 1
          (.apply (costBaseConstructorName "PDrop") [.fvar name]) =
        .apply (costBaseConstructorName "PDrop") [.fvar name]
      have dropNeQuote : costBaseConstructorName "PDrop" ≠
          declaration.quoteConstructor := by decide
      simp [canonicalizeByAt, canonicalizeListByAt, dropNeQuote,
        Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.finishNormalizeReflectiveApply]

theorem leftShape : CostStaticRootShape rhoCIGSLT leftPattern
    (.base (costBaseSortName "Proc")) :=
  .application .base _ rfl rfl

theorem rightShape : CostStaticRootShape rhoCIGSLT rightPattern
    (.base (costBaseSortName "Proc")) :=
  .application .base _ rfl rfl

/-- The executable trees are forced into the same-colour aligned arm. -/
theorem exists_aligned_views :
    ∃ (color : CostStaticColor)
      (_leftView : leftTree.StaticRootView color)
      (_rightView : rightTree.StaticRootView color),
        CanonicalRootAligned declaration leftPattern rightPattern := by
  exact ⟨.base, leftView, rightView, endpoint_roots_aligned⟩

/-- Raw canonical equality fails for the concrete same-colour static views. -/
theorem aligned_views_not_frame_canonical :
    ¬ RhoMatchedStaticFramesCanonical leftView rightView := by
  intro canonical
  obtain ⟨leftSlot, rightSlot, leftSelected, rightSelected, namesNe⟩ :=
    exists_boundary_slots_with_distinct_common_names
  change canonicalize declaration
      (RhoCommonRestorationApex.commonReifiedTargetFrame leftNode
        leftEnvironment cospan cospan.leftSlot cospan.leftCommutes).1.1 =
    canonicalize declaration
      (RhoCommonRestorationApex.commonReifiedTargetFrame rightNode
        rightEnvironment cospan cospan.rightSlot cospan.rightCommutes).1.1 at canonical
  rw [RhoCommonRestorationApex.commonReifiedTargetFrame_pattern,
    RhoCommonRestorationApex.commonReifiedTargetFrame_pattern,
    left_common_frame_canonical leftSlot leftSelected,
    right_common_frame_canonical rightSlot rightSelected] at canonical
  have argumentsEq :
      [Pattern.fvar (cospan.commonAtomName (cospan.leftSlot leftSlot))] =
        [Pattern.fvar (cospan.commonAtomName (cospan.rightSlot rightSlot))] :=
    (Pattern.apply.inj canonical).2
  have atomsEq :
      Pattern.fvar (cospan.commonAtomName (cospan.leftSlot leftSlot)) =
        Pattern.fvar (cospan.commonAtomName (cospan.rightSlot rightSlot)) :=
    (List.cons.inj argumentsEq).1
  exact namesNe (Pattern.fvar.inj atomsEq)

/-- The false target, stated at the existential actual-view interface used by
the provider dispatch. -/
theorem exists_aligned_views_not_frame_canonical :
    ∃ (color : CostStaticColor)
      (leftView : leftTree.StaticRootView color)
      (rightView : rightTree.StaticRootView color),
        CanonicalRootAligned declaration leftPattern rightPattern ∧
          ¬ RhoMatchedStaticFramesCanonical leftView rightView := by
  exact ⟨.base, leftView, rightView, endpoint_roots_aligned,
    aligned_views_not_frame_canonical⟩

/-- The false common-name equality is already unnecessary at the source
canonical boundary: the rigid drop constructor is shared, while the two
endpoint atom names are related by their restored values. -/
theorem aligned_views_have_source_canonical_alignment :
    let relation : Pattern → Pattern → Prop := fun leftLeaf rightLeaf =>
      ∀ depth,
        ReflectiveContextSupport.RestoresTogether
          rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
            cospan.commonAssignment
            (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
              (leftNode.thinning.thickenAmbientBVars depth
                (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
                  leftLeaf)))
            (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
              (rightNode.thinning.thickenAmbientBVars depth
                (mapPattern (CostStaticColor.base.symbols rhoCIGSLT)
                  rightLeaf)))
    PatternLeafAligned relation
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt leftNode
          leftEnvironment)
        rhoReflectivePresentation leftNode.targetBound.length 0
        (leftNode.reifiedSourceFrame leftEnvironment).1)
      (canonicalizeByDepths
        (CostStaticRegionNode.sourceSemanticPatternKeyAt rightNode
          rightEnvironment)
        rhoReflectivePresentation rightNode.targetBound.length 0
        (rightNode.reifiedSourceFrame rightEnvironment).1) := by
  obtain ⟨leftSlot, rightSlot, leftSelected, rightSelected, _namesNe⟩ :=
    exists_boundary_slots_with_distinct_common_names
  have normalEq := boundary_atom_normals_equal leftSlot rightSlot
    leftSelected rightSelected
  have sealed := left_atom_targetSupport_nil leftSlot leftSelected
  have normalScoped :=
    RhoMatchedStaticFramesApex.atomNormalScopedAtZero_of_targetSupport_nil
      leftEnvironment leftSlot sealed
  rw [left_source_frame_keyed leftSlot leftSelected,
    right_source_frame_keyed rightSlot rightSelected]
  apply PatternLeafAligned.apply
  exact .cons (.leaf (fun _sourceDepth restoreDepth => by
    simpa [CostStaticBinderThinning.thickenAmbientBVars, mapPattern,
      CostStaticColor.symbols, costBaseStaticSymbols,
      costBasePresentationSymbols, CostStaticAtomKeyCospan.reifyWith,
      Pattern.renameFVars, CostStaticAtomKeyCospan.reifyNameWith,
      CostStaticAtomEnvironment.lookupAtom?_atomName, cospan] using
        CostStaticAtomEnvironment.substituteAt_commonReifiedAtom_eq_of_scoped_normal
          leftEnvironment rightEnvironment leftSlot rightSlot normalEq
            normalScoped restoreDepth)) .nil

/-- The generic source-to-target reducer closes the counterexample without
ever identifying its unequal common atom names. -/
theorem aligned_views_have_restoration_alignment_via_source :
    RhoStaticFramesRestorationAligned leftView rightView := by
  apply RhoStaticFramesRestorationAligned.ofSourceCanonicalAlignment
    leftView rightView
  simpa [leftView, rightView, leftValues, rightValues, leftInventory,
    rightInventory, leftEnvironment, rightEnvironment, cospan] using
      aligned_views_have_source_canonical_alignment

/-- The refuting sealed/exposed pair still has the exact endpoint restoration
alignment consumed by the corrected matched-frame adapter. -/
theorem aligned_views_have_restoration_alignment :
    RhoStaticFramesRestorationAligned leftView rightView :=
  aligned_views_have_restoration_alignment_via_source

/-- The corrected adapter accepts the very pair that refutes common-frame
canonical equality. -/
noncomputable def aligned_views_have_restoration_apex_via_alignment :
    RhoMatchedStaticFramesApex leftView rightView :=
  RhoMatchedStaticFramesApex.ofRestorationAligned leftView rightView
    aligned_views_have_restoration_alignment

/-- The same reachable pair refuting raw frame canonicality nevertheless has
the semantic common-restoration apex required by generator alignment. -/
theorem aligned_views_have_restoration_apex :
    RhoMatchedStaticFramesApex leftView rightView := by
  obtain ⟨leftSlot, rightSlot, leftSelected, rightSelected, _namesNe⟩ :=
    exists_boundary_slots_with_distinct_common_names
  have normalEq := boundary_atom_normals_equal leftSlot rightSlot
    leftSelected rightSelected
  have sealed := left_atom_targetSupport_nil leftSlot leftSelected
  have leaf := RhoMatchedStaticFramesApex.rigidUnary_of_leftTargetSupportNil
    leftEnvironment rightEnvironment leftSlot rightSlot normalEq sealed
      declaration (costBaseConstructorName "PDrop")
        leftNode.targetBound.length
  change CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT cospan
    declaration
    leftNode.targetBound.length
    (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      declaration leftNode.targetBound.length
      (RhoCommonRestorationApex.commonReifiedTargetFrame leftNode
        leftEnvironment cospan cospan.leftSlot cospan.leftCommutes).1.1)
    (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
      declaration rightNode.targetBound.length
      (RhoCommonRestorationApex.commonReifiedTargetFrame rightNode
        rightEnvironment cospan cospan.rightSlot cospan.rightCommutes).1.1)
  rw [RhoCommonRestorationApex.commonReifiedTargetFrame_pattern,
    RhoCommonRestorationApex.commonReifiedTargetFrame_pattern,
    left_common_frame_keyed leftSlot leftSelected,
    right_common_frame_keyed rightSlot rightSelected]
  simpa [cospan, CostStaticAtomKeyCospan.reifyWith,
    Pattern.renameFVars, CostStaticAtomKeyCospan.reifyNameWith,
    CostStaticAtomEnvironment.lookupAtom?_atomName] using leaf

/-- Paired regression canary: representation-level equality fails exactly
where semantic restoration still succeeds. -/
theorem frame_canonical_false_but_apex_true :
    ¬ RhoMatchedStaticFramesCanonical leftView rightView ∧
      RhoMatchedStaticFramesApex leftView rightView := by
  constructor
  · exact aligned_views_not_frame_canonical
  · exact aligned_views_have_restoration_apex_via_alignment

/-- The semantic apex closes the exact matched-frame cut consumed downstream. -/
noncomputable def aligned_views_have_restoration_cut :
    RhoMatchedStaticFramesCut leftView rightView :=
  RhoMatchedStaticFramesCut.ofRestorationAligned leftView rightView
    aligned_views_have_restoration_alignment

/-- The reachable counterexample is accepted by the provider's semantic
matched arm without recovering the refuted common-frame equality. -/
noncomputable def aligned_pair_has_semantic_cut :
    RhoCanonicalStaticPairSemanticCut .base leftTree rightTree
      (.aligned .base leftView rightView endpoint_roots_aligned) :=
  RhoCanonicalStaticPairSemanticCut.matchedOfRestorationAligned leftView
    rightView endpoint_roots_aligned
      aligned_views_have_restoration_alignment

/-- Eliminating the semantic cut produces the exact hereditary pair
elaboration required by the static recursion. -/
noncomputable def aligned_pair_elaboration :
    CostCanonicalPairElaboration rhoCIGSLT rhoHereditaryNormalizationKernel
      FreeTypeContext.empty [ambientType] [] leftPattern rightPattern
        (.base (costBaseSortName "Proc")) :=
  aligned_pair_has_semantic_cut.toPairElaboration

/-- The semantic route proves equality of the selected executor's compact
normal forms on the same pair that refutes common-frame canonical equality. -/
theorem aligned_pair_normalize_pattern_eq :
    (aligned_pair_elaboration.leftTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (aligned_pair_elaboration.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
  aligned_pair_elaboration.normalize_pattern_eq

/-- End-to-end regression: representation-level canonical equality is false,
while the semantic route proves the exact compact equality consumers need. -/
theorem frame_canonical_false_but_pair_normalize_eq :
    ¬ RhoMatchedStaticFramesCanonical leftView rightView ∧
      (aligned_pair_elaboration.leftTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
        (aligned_pair_elaboration.rightTree.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  exact ⟨aligned_views_not_frame_canonical, aligned_pair_normalize_pattern_eq⟩

/-- The two compiled planners retain one boundary at unequal target support. -/
theorem planner_supports_differ :
    let leftPlan := buildCostStaticRegionPlan? rhoCIGSLT .base
      FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base
        [ambientType]) [ambientType]
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [ambientType])
      [ambientType] .hole leftPattern (.base "Proc")
    let rightPlan := buildCostStaticRegionPlan? rhoCIGSLT .base
      FreeTypeContext.empty
      (CostStaticBinderThinning.sourceContextOfTarget rhoCIGSLT .base
        [ambientType]) [ambientType]
      (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT .base [ambientType])
      [ambientType] .hole rightPattern (.base "Proc")
    (leftPlan.get (by decide)).boundaryTable.entries.map
        (·.boundary.targetSupport) = [[]] ∧
      (rightPlan.get (by decide)).boundaryTable.entries.map
        (·.boundary.targetSupport) = [[ambientType]] := by
  decide

end CostHereditaryMatchedFramesCanonicalCanary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
