import Mettapedia.GSLT.LanguageDef.CostElaborationTransport
import Mettapedia.GSLT.LanguageDef.CostSemanticAtomTreeAlignment
import Mettapedia.GSLT.LanguageDef.CostStaticPlanPairAlignment

/-!
# Semantic atoms transported by a lawful static-plan edge

A lawful static-plan edge carries a contravariant pullback from every target
boundary occurrence to a source occurrence in the same complete fibre.  If
the corresponding recursive child trees are hereditarily aligned, their
normalized boundary values therefore induce exactly the same semantic atom.

This is the finite child-to-parent joint required before a static transport
can be closed at the common restoration apex.  It does not assume that the
two parent skeletons, inventories, or final normal forms are equal.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

namespace CostRegionTree

/-- Under structural unambiguity, any two proof-relevant trees of the same
typed compact pattern have the same exact normalized pattern, at arbitrary
types and binder splits.  This is the all-fibres form of compact chooser
coherence used by recursive boundary lookup. -/
theorem normalize_pattern_eq_of_unambiguous
    {source : CIGSLT}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    (kernel : CostStaticNormalizationKernel source)
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (first second : CostRegionTree source targetFree available outer pattern
      type)
    (object : WellSorted.isObjectPattern pattern = true) :
    (first.normalize (normalizeStatic := kernel.normalize)).pattern =
      (second.normalize (normalizeStatic := kernel.normalize)).pattern := by
  obtain ⟨built, builtEq⟩ := first.exists_build?_eq_some_of_tree object
  have builtFuelEq : CostRegionTree.buildFuel? (source := source)
      (targetFree := targetFree) (costRegionPatternWeight pattern + 1)
        available outer pattern type = some built := by
    simpa only [CostRegionTree.build?] using builtEq
  have firstEq := CostRegionTree.normalize_pattern_eq_of_buildFuel
    unambiguous (normalizeStatic := kernel.normalize)
      (costRegionPatternWeight pattern + 1) first builtFuelEq
  have secondEq := CostRegionTree.normalize_pattern_eq_of_buildFuel
    unambiguous (normalizeStatic := kernel.normalize)
      (costRegionPatternWeight pattern + 1) second builtFuelEq
  exact firstEq.trans secondEq.symm

end CostRegionTree

namespace CostRegionBoundaryTrees

/-- The boundary projection of an actual dependent child agrees with the
proof-free decoration selected at the same finite position. -/
theorem getDecoration_boundary
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table)
    (index : Fin trees.decorations.length) :
    (trees.getDecoration index).boundary.boundary =
      (trees.decorations.get index).1 :=
  congrArg Prod.fst (trees.getDecoration_decoration index)

/-- The proof-free decoration vector and the proof-relevant table contain
exactly the same finite occurrence positions.  Keeping this equality named
lets downstream pullbacks select a child by its table position without
searching for an equal boundary value. -/
@[simp]
theorem decorations_length_eq_entries_length
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    trees.decorations.length = table.entries.length :=
  match trees with
  | .nil => rfl
  | .cons _ children => congrArg Nat.succ
      children.decorations_length_eq_entries_length

/-- Select a proof-relevant child by the corresponding position of the typed
boundary table.  The cast is only between the recursively proved equal
lengths; occurrence identity remains the supplied finite position. -/
def getEntry
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table)
    (index : Fin table.entries.length) :
    CostRegionBoundaryTreeEntry source targetFree color :=
  trees.getDecoration
    (Fin.cast (trees.decorations_length_eq_entries_length).symm index)

/-- Table-position selection recovers the exact typed boundary stored at that
position.  This is stronger than equality of serialized boundary keys and is
therefore safe in the presence of duplicate equal entries. -/
theorem getEntry_boundary
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table)
    (index : Fin table.entries.length) :
    (trees.getEntry index).boundary = table.entries.get index :=
  match trees, index with
  | .nil, index => Fin.elim0 index
  | .cons _ _, ⟨0, _⟩ => rfl
  | .cons _ children, ⟨position + 1, inBounds⟩ =>
      children.getEntry_boundary
        ⟨position, Nat.lt_of_succ_lt_succ inBounds⟩

/-- Every target child of a lawful static-plan edge denotes the same semantic
atom as its pulled-back source child once the two child trees are aligned.
The edge supplies occurrence transport and same-fibre evidence; the child
alignment supplies equality of normalized compact values. -/
theorem alignedPullbackAtom_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {staticLift : CostStaticPlanLift source}
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {first second : CostStaticPlanDecoration source}
    (planStep : staticLift.Edge first second leftTrees.decorations
      rightTrees.decorations)
    (children : ∀ targetIndex,
      CostRegionTreeNormalizationAlignment source kernel targetFree
        (leftTrees.getDecoration
          ((staticLift.boundaryMap planStep).pullback targetIndex)).tree
        (rightTrees.getDecoration targetIndex).tree)
    (targetIndex : Fin rightTrees.decorations.length) :
    TypedCostStaticAtom.ofBoundaryValue
        (leftTrees.getDecoration
          ((staticLift.boundaryMap planStep).pullback targetIndex)).boundary
        (CostRegionTree.normalizedBoundaryValue kernel
          (leftTrees.getDecoration
            ((staticLift.boundaryMap planStep).pullback targetIndex)).tree) =
      TypedCostStaticAtom.ofBoundaryValue
        (rightTrees.getDecoration targetIndex).boundary
        (CostRegionTree.normalizedBoundaryValue kernel
          (rightTrees.getDecoration targetIndex).tree) := by
  let sourceIndex := (staticLift.boundaryMap planStep).pullback targetIndex
  have sameFiber := (staticLift.boundaryMap planStep).preservesFiber targetIndex
  have leftBoundary := leftTrees.getDecoration_boundary sourceIndex
  have rightBoundary := rightTrees.getDecoration_boundary targetIndex
  rw [← leftBoundary, ← rightBoundary] at sameFiber
  exact CostRegionTree.alignedBoundaryAtom_eq sameFiber
    (children targetIndex)

/-- The source semantic atoms observed through a boundary pullback, in target
occurrence order.  A non-injective pullback deliberately repeats an atom;
discarded source occurrences deliberately do not appear. -/
def pulledBackNormalizedAtoms
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {staticLift : CostStaticPlanLift source}
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {first second : CostStaticPlanDecoration source}
    (planStep : staticLift.Edge first second leftTrees.decorations
      rightTrees.decorations) :
    List (TypedCostStaticAtom source color targetFree) :=
  List.ofFn fun targetIndex : Fin rightTrees.decorations.length =>
    TypedCostStaticAtom.ofBoundaryValue
      (leftTrees.getDecoration
        ((staticLift.boundaryMap planStep).pullback targetIndex)).boundary
      (CostRegionTree.normalizedBoundaryValue kernel
        (leftTrees.getDecoration
          ((staticLift.boundaryMap planStep).pullback targetIndex)).tree)

/-- Target semantic atoms in their retained occurrence order. -/
def normalizedAtoms
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    List (TypedCostStaticAtom source color targetFree) :=
  List.ofFn fun index : Fin trees.decorations.length =>
    TypedCostStaticAtom.ofBoundaryValue
      (trees.getDecoration index).boundary
      (CostRegionTree.normalizedBoundaryValue kernel
        (trees.getDecoration index).tree)

/-- Recursive child alignment identifies the whole target-indexed semantic
atom list with the source list pulled back along the lawful plan edge.

This is the finite nonlinear form of `alignedPullbackAtom_eq`: duplication is
visible as repetition in the left list, while discarded source occurrences
are absent from both sides. -/
theorem pulledBackNormalizedAtoms_eq_normalizedAtoms
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {staticLift : CostStaticPlanLift source}
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {first second : CostStaticPlanDecoration source}
    (planStep : staticLift.Edge first second leftTrees.decorations
      rightTrees.decorations)
    (children : ∀ targetIndex,
      CostRegionTreeNormalizationAlignment source kernel targetFree
        (leftTrees.getDecoration
          ((staticLift.boundaryMap planStep).pullback targetIndex)).tree
        (rightTrees.getDecoration targetIndex).tree) :
    pulledBackNormalizedAtoms (kernel := kernel) leftTrees rightTrees planStep =
      normalizedAtoms (kernel := kernel) rightTrees := by
  apply List.ofFn_inj.mpr
  funext targetIndex
  exact alignedPullbackAtom_eq leftTrees rightTrees planStep children
    targetIndex

/-- Lookup in a child-normalized value vector realizes the semantic atom of
the selected proof-relevant child.  If an equal boundary key occurs earlier
in the table, the finite resolver deliberately selects that earlier value;
structural unambiguity proves that the two decompositions of the same compact
boundary content normalize identically.  Thus positional multiplicity is
retained by the forest while name lookup remains semantically extensional. -/
theorem exists_resolve_normalizedAtom_eq_getDecoration
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    ∀ index : Fin trees.decorations.length,
      ∃ resolved : TypedCostRegionBoundaryTable.Values.Resolved source color
          targetFree,
        (trees.normalizeValues
            (normalizeStatic := kernel.normalize)).resolve table
              (costRegionBoundaryVariableName
                (trees.getDecoration index).boundary.boundary) =
            some resolved ∧
          TypedCostStaticAtom.ofBoundaryValue resolved.1 resolved.2 =
      TypedCostStaticAtom.ofBoundaryValue
              (trees.getDecoration index).boundary
              ((trees.getDecoration index).tree.normalizedBoundaryValue
                kernel) :=
  match trees with
  | .nil => fun index => Fin.elim0 index
  | @CostRegionBoundaryTrees.cons _ _ color occurrence occurrences boundary
      content tail head children => fun index =>
      Fin.cases (by
        refine ⟨
          ⟨boundary, head.normalizedBoundaryValue kernel⟩,
          ?_, rfl⟩
        simp [CostRegionBoundaryTrees.normalizeValues,
          TypedCostRegionBoundaryTable.Values.resolve,
          CostRegionBoundaryTrees.getDecoration]
        apply Subtype.ext
        rfl) (fun tailIndex => by
        obtain ⟨resolved, resolution, atomEq⟩ :=
          children.exists_resolve_normalizedAtom_eq_getDecoration unambiguous
            tailIndex
        by_cases keyEq :
            costRegionBoundaryVariableName
                (children.getDecoration tailIndex).boundary.boundary =
              costRegionBoundaryVariableName boundary.boundary
        · have rawBoundaryEq :
              (children.getDecoration tailIndex).boundary.boundary =
                boundary.boundary :=
            costRegionBoundaryVariableName_injective keyEq
          have boundaryEq :
              (children.getDecoration tailIndex).boundary = boundary :=
            TypedCostRegionBoundary.ext rawBoundaryEq
          have object : isObjectPattern boundary.boundary.content = true :=
            boundary.contentObjectPattern
          have normalEq :
              (head.normalizedBoundaryValue kernel).1 =
                ((children.getDecoration tailIndex).tree.normalizedBoundaryValue
                  kernel).1 := by
            cases boundaryEq
            exact CostRegionTree.normalize_pattern_eq_of_unambiguous
              unambiguous kernel head
                (children.getDecoration tailIndex).tree
                  object
          have sameFiber : CostRegionBoundary.SameFiber boundary.boundary
              (children.getDecoration tailIndex).boundary.boundary := by
            rw [boundaryEq]
          have headAtomEq :
              TypedCostStaticAtom.ofBoundaryValue boundary
                  (head.normalizedBoundaryValue kernel) =
                TypedCostStaticAtom.ofBoundaryValue
                  (children.getDecoration tailIndex).boundary
                  ((children.getDecoration tailIndex).tree.normalizedBoundaryValue
                    kernel) := by
            apply TypedCostStaticAtom.ext
            exact TypedCostStaticAtom.ofBoundaryValue_key_eq_of_sameFiber
              (head.normalizedBoundaryValue kernel)
              ((children.getDecoration tailIndex).tree.normalizedBoundaryValue
                kernel)
              sameFiber normalEq
          refine ⟨
            ⟨boundary, head.normalizedBoundaryValue kernel⟩,
            ?_, ?_⟩
          · simp [CostRegionBoundaryTrees.normalizeValues,
              TypedCostRegionBoundaryTable.Values.resolve,
              CostRegionBoundaryTrees.getDecoration, keyEq]
            apply Subtype.ext
            rfl
          · simpa [CostRegionBoundaryTrees.getDecoration] using headAtomEq
        · refine ⟨resolved, ?_, atomEq⟩
          simpa [CostRegionBoundaryTrees.normalizeValues,
            TypedCostRegionBoundaryTable.Values.resolve,
            CostRegionBoundaryTrees.getDecoration, keyEq] using resolution)
        index
  termination_by trees.weight
  decreasing_by
    simp [CostRegionBoundaryTrees.weight]
    omega

end CostRegionBoundaryTrees

namespace CostRegionTree

/-- Transport a recursive boundary tree along equality of its complete typed
boundary.  This packages the support, content, and type casts as one proof-
relevant operation instead of asking downstream restoration proofs to
reconstruct three correlated transports. -/
def reindexBoundary
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor}
    {first second : TypedCostRegionBoundary source color targetFree}
    (boundaryEq : first = second)
    (tree : CostRegionTree source targetFree first.boundary.targetSupport []
      first.boundary.content first.boundary.targetType) :
    CostRegionTree source targetFree second.boundary.targetSupport []
      second.boundary.content second.boundary.targetType := by
  cases boundaryEq
  exact tree

/-- Complete-boundary reindexing preserves hereditary normalization. -/
theorem reindexBoundary_normalizedBoundaryValue
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {first second : TypedCostRegionBoundary source color targetFree}
    (boundaryEq : first = second)
    (tree : CostRegionTree source targetFree first.boundary.targetSupport []
      first.boundary.content first.boundary.targetType) :
    ((tree.reindexBoundary boundaryEq).normalizedBoundaryValue kernel).1 =
      (tree.normalizedBoundaryValue kernel).1 := by
  cases boundaryEq
  rfl

end CostRegionTree

namespace CostRegionTreeNormalizationAlignment

/-- Transport both endpoints of a hereditary child alignment along complete
typed-boundary equalities. -/
def reindexBoundaries
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {leftFirst leftSecond rightFirst rightSecond :
      TypedCostRegionBoundary source color targetFree}
    {left : CostRegionTree source targetFree
      leftFirst.boundary.targetSupport [] leftFirst.boundary.content
      leftFirst.boundary.targetType}
    {right : CostRegionTree source targetFree
      rightFirst.boundary.targetSupport [] rightFirst.boundary.content
      rightFirst.boundary.targetType}
    (leftEq : leftFirst = leftSecond) (rightEq : rightFirst = rightSecond)
    (alignment : CostRegionTreeNormalizationAlignment source kernel targetFree
      left right) :
    CostRegionTreeNormalizationAlignment source kernel targetFree
      (left.reindexBoundary leftEq) (right.reindexBoundary rightEq) := by
  cases leftEq
  cases rightEq
  exact alignment

end CostRegionTreeNormalizationAlignment

namespace CostStaticAtomEnvironment

/-- A successful boundary-value lookup determines the exact semantic atom
selected by the corresponding rigid parameter name.  This is the local
realization joint between a finite child-value vector and the deduplicated
atom environment: occurrence position is retained until the final semantic
quotient, while equal names remain name-extensional. -/
theorem atomValue_eq_of_boundaryResolution
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (occurrence : CostStaticFVarOccurrence root)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot)
    (notSource : decodeCostRegionSourceVariableName occurrence.name = none)
    (resolved : TypedCostRegionBoundaryTable.Values.Resolved source color
      targetFree)
    (resolution : values.resolve table occurrence.name = some resolved) :
    environment.atomValue slot =
      TypedCostStaticAtom.ofBoundaryValue resolved.1 resolved.2 := by
  rw [environment.atomValue_of_slotOfName?_eq_some occurrence slot selected]
  let parameter : CostStaticParameterOccurrence source color targetFree table
      values root := .boundary occurrence notSource resolved resolution
  change
    (inventory.occurrenceAt
      (inventory.positionOf occurrence)).atom = parameter.atom
  apply CostStaticParameterOccurrence.atom_eq_of_name_eq
  exact congrArg CostStaticFVarOccurrence.name
    (inventory.fvarOccurrence_occurrenceAt_positionOf occurrence)

/-- A semantic slot selected by the rigid name of an actual recursive child
contains exactly that child's hereditary normalized atom.  Duplicate boundary
keys are harmless: the finite resolver may choose an earlier occurrence, and
structural unambiguity identifies the two normalized compact values before
the atom quotient is observed. -/
theorem atomValue_eq_normalizedBoundaryValue_of_getDecoration
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table)
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      (trees.normalizeValues (normalizeStatic := kernel.normalize)) root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (index : Fin trees.decorations.length)
    (occurrence : CostStaticFVarOccurrence root)
    (nameEq : occurrence.name = costRegionBoundaryVariableName
      (trees.getDecoration index).boundary.boundary)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    environment.atomValue slot =
      TypedCostStaticAtom.ofBoundaryValue
        (trees.getDecoration index).boundary
        ((trees.getDecoration index).tree.normalizedBoundaryValue kernel) := by
  obtain ⟨resolved, resolution, atomEq⟩ :=
    trees.exists_resolve_normalizedAtom_eq_getDecoration unambiguous index
  have notSource :
      decodeCostRegionSourceVariableName occurrence.name = none := by
    rw [nameEq]
    exact decodeCostRegionSourceVariableName_boundary _
  have resolutionAtOccurrence :
      (trees.normalizeValues
          (normalizeStatic := kernel.normalize)).resolve table
        occurrence.name = some resolved := by
    rw [nameEq]
    exact resolution
  exact (environment.atomValue_eq_of_boundaryResolution occurrence slot
    selected notSource resolved resolutionAtOccurrence).trans atomEq

/-- Table-indexed form of the child-to-environment joint.  This is the form
consumed by a proof-relevant keep/skip embedding: the selected child is found
by its finite table position, never by equality search. -/
theorem atomValue_eq_normalizedBoundaryValue_of_getEntry
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table)
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      (trees.normalizeValues (normalizeStatic := kernel.normalize)) root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (index : Fin table.entries.length)
    (occurrence : CostStaticFVarOccurrence root)
    (nameEq : occurrence.name = costRegionBoundaryVariableName
      (trees.getEntry index).boundary.boundary)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    environment.atomValue slot =
      TypedCostStaticAtom.ofBoundaryValue
        (trees.getEntry index).boundary
        ((trees.getEntry index).tree.normalizedBoundaryValue kernel) := by
  exact environment.atomValue_eq_normalizedBoundaryValue_of_getDecoration
    unambiguous trees
      (Fin.cast (trees.decorations_length_eq_entries_length).symm index)
      occurrence nameEq slot selected

/-- Reindexing an actual child to an equal typed table entry does not change
the semantic atom realized by its parent environment.  Keeping the equality
explicit packages the correlated support/content/type transports in one
place. -/
theorem atomValue_eq_normalizedBoundaryValue_of_reindexedGetEntry
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table)
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      (trees.normalizeValues (normalizeStatic := kernel.normalize)) root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (index : Fin table.entries.length)
    (boundary : TypedCostRegionBoundary source color targetFree)
    (boundaryEq : (trees.getEntry index).boundary = boundary)
    (occurrence : CostStaticFVarOccurrence root)
    (nameEq : occurrence.name = costRegionBoundaryVariableName
      boundary.boundary)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    environment.atomValue slot =
      TypedCostStaticAtom.ofBoundaryValue boundary
        (((trees.getEntry index).tree.reindexBoundary boundaryEq).normalizedBoundaryValue
          kernel) := by
  cases boundaryEq
  exact environment.atomValue_eq_normalizedBoundaryValue_of_getEntry
    unambiguous trees index occurrence nameEq slot selected

/-- Equal endpoint semantic keys select the same slot in the canonical common
quotient, so their internal atom names restore identically at every binder
depth.  The statement permits different static colours and retains both
endpoint occurrence namespaces; only the complete evaluated key is
identified. -/
theorem substituteAt_commonReifiedAtom_eq_of_key_eq
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
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
    (keyEq : (left.atomValue leftSlot).key =
      (right.atomValue rightSlot).key)
    (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith left.lookupAtom? cospan.leftSlot
          (.fvar (left.atomName leftSlot))) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith right.lookupAtom? cospan.rightSlot
          (.fvar (right.atomName rightSlot))) := by
  let cospan := left.semanticKeyCospan right
  have slotEq : cospan.leftSlot leftSlot = cospan.rightSlot rightSlot :=
    (left.semanticKeyCospan_crossExtensional right leftSlot rightSlot).2 keyEq
  simp [cospan, CostStaticAtomKeyCospan.reifyWith, slotEq]

/-- Restoration of two canonical atom names needs only the components that
the substitution operation observes: target support and normalized value.
The source fibre and target type may still differ, so the two atoms need not
occupy one semantic-key slot in the common cospan.

This weaker terminal is essential when a foreign boundary disappears and
its normalized child becomes a direct source variable.  Provenance and
typing remain in the endpoint atoms; restoration compares only the data it
actually executes. -/
theorem substituteAt_commonReifiedAtom_eq_of_restorationComponents
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
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
    (supportEq : (left.atomValue leftSlot).key.targetSupport =
      (right.atomValue rightSlot).key.targetSupport)
    (normalEq : (left.atomValue leftSlot).key.normal =
      (right.atomValue rightSlot).key.normal)
    (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith left.lookupAtom? cospan.leftSlot
          (.fvar (left.atomName leftSlot))) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith right.lookupAtom? cospan.rightSlot
          (.fvar (right.atomName rightSlot))) := by
  let cospan := left.semanticKeyCospan right
  simp only [CostStaticAtomKeyCospan.reifyWith,
    CostStaticAtomEnvironment.lookupAtom?_atomName,
    CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
    CostStaticAtomKeyCospan.commonSupport_commonAtomName,
    ReflectiveContextSupport.substituteAt]
  rw [show cospan.commonKeys.get (cospan.leftSlot leftSlot) =
      (left.atomValue leftSlot).key from cospan.leftCommutes leftSlot]
  rw [show cospan.commonKeys.get (cospan.rightSlot rightSlot) =
      (right.atomValue rightSlot).key from cospan.rightCommutes rightSlot]
  rw [supportEq, normalEq]

/-- Restoration of two canonical atom names may ignore unequal target-support
lengths when their common normalized value is closed with respect to bound
indices.  This is the precise support-transport law needed when a boundary
below an ordinary binder becomes a direct source variable: the proof-relevant
supports remain distinct, but weakening either copy of the closed value is
inert.

The scoping premise is load-bearing.  It deliberately excludes bound-variable
values, whose de Bruijn indices can change under unequal support shifts. -/
theorem substituteAt_commonReifiedAtom_eq_of_scoped_normal
    {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : FreeTypeContext}
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
    (depth : Nat) :
    let cospan := left.semanticKeyCospan right
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith left.lookupAtom? cospan.leftSlot
          (.fvar (left.atomName leftSlot))) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith right.lookupAtom? cospan.rightSlot
          (.fvar (right.atomName rightSlot))) := by
  let cospan := left.semanticKeyCospan right
  simp only [CostStaticAtomKeyCospan.reifyWith,
    CostStaticAtomEnvironment.lookupAtom?_atomName,
    CostStaticAtomKeyCospan.commonAssignment_commonAtomName,
    CostStaticAtomKeyCospan.commonSupport_commonAtomName,
    ReflectiveContextSupport.substituteAt]
  rw [show cospan.commonKeys.get (cospan.leftSlot leftSlot) =
      (left.atomValue leftSlot).key from cospan.leftCommutes leftSlot]
  rw [show cospan.commonKeys.get (cospan.rightSlot rightSlot) =
      (right.atomValue rightSlot).key from cospan.rightCommutes rightSlot]
  rw [normalEq]
  have rightScoped :
      (right.atomValue rightSlot).key.normal.isWellScopedAt 0 = true := by
    simpa only [normalEq] using normalScoped
  rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
        rightScoped,
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
        rightScoped]

end CostStaticAtomEnvironment

namespace TypedCostRegionBoundaryTable.Values

/-- Retagged source variables are restored literally and independently of
the finite boundary values. -/
@[simp]
theorem assignment_sourceVariable
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      table)
    (name : String) :
    values.assignment table (costRegionSourceVariableName name) =
      .fvar name := by
  simp [TypedCostRegionBoundaryTable.Values.assignment]

end TypedCostRegionBoundaryTable.Values

namespace CostStaticRegionNode

/-- The semantic-atom environment seen by a static node after all of its
boundary children have been normalized by the selected hereditary kernel.

Keeping this construction named prevents local root-closure certificates
from having to repeat (and accidentally respell) the dependent
`normalizeValues`/inventory projection. -/
noncomputable def normalizationEnvironment
    {source : CIGSLT} (normalizeStatic : CostStaticRegionNormalizer source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    (children : CostRegionBoundaryTrees source targetFree color
      node.finiteBoundaryTable) :
    CostStaticAtomEnvironment source color targetFree
      (node.semanticAtomEnvironment
        (children.normalizeValues
          (normalizeStatic := normalizeStatic))).1 :=
  (node.semanticAtomEnvironment
    (children.normalizeValues (normalizeStatic := normalizeStatic))).1
    |> CostStaticAtomEnvironment.ofInventory

end CostStaticRegionNode

namespace CostStaticPlanContextInventoryView

/-- Replay a retained context-view position into the full finite forest and
return the actual proof-relevant recursive child at that position. -/
def selectedTreeFromForest
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {payload rootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      rootAbstract table.entries)
    (trees : CostRegionBoundaryTrees source targetFree color table)
    (index : Fin view.view.retainedEntries.length) :
    CostRegionTree source targetFree
      (view.view.retainedEntries.get index).boundary.targetSupport []
      (view.view.retainedEntries.get index).boundary.content
      (view.view.retainedEntries.get index).boundary.targetType := by
  let position := view.entryEmbedding.position index
  have boundaryEq : (trees.getEntry position).boundary =
      view.view.retainedEntries.get index :=
    (trees.getEntry_boundary position).trans
      (view.entryEmbedding.position_get index)
  exact (trees.getEntry position).tree.reindexBoundary boundaryEq

/-- The semantic atom selected by a retained context-view boundary stores
exactly the hereditary normal form of the proof-relevant child replayed from
the full forest.  This is the one-environment form of the boundary transport
joint: it exposes the normalized value without introducing a second parent
environment or assuming an equality at the restoration apex. -/
theorem selectedBoundaryAtom_normal_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {payload rootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      rootAbstract table.entries)
    (trees : CostRegionBoundaryTrees source targetFree color table)
    {inventory : CostStaticParameterInventory source color targetFree table
      (trees.normalizeValues (normalizeStatic := kernel.normalize))
      rootAbstract}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (index : Fin view.view.retainedEntries.length)
    (occurrence : CostStaticFVarOccurrence rootAbstract)
    (nameEq : occurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    (environment.atomValue slot).key.normal =
      ((view.selectedTreeFromForest trees index).normalizedBoundaryValue
        kernel).1 := by
  let position := view.entryEmbedding.position index
  have boundaryEq : (trees.getEntry position).boundary =
      view.view.retainedEntries.get index :=
    (trees.getEntry_boundary position).trans
      (view.entryEmbedding.position_get index)
  have atomEq :=
    environment.atomValue_eq_normalizedBoundaryValue_of_reindexedGetEntry
      unambiguous trees position (view.view.retainedEntries.get index)
      boundaryEq occurrence nameEq slot selected
  calc
    (environment.atomValue slot).key.normal =
        (((trees.getEntry position).tree.reindexBoundary
          boundaryEq).normalizedBoundaryValue kernel).1 := by
      simpa only [TypedCostStaticAtom.ofBoundaryValue] using
        congrArg (fun atom => atom.key.normal) atomEq
    _ = ((trees.getEntry position).tree.normalizedBoundaryValue kernel).1 :=
      CostRegionTree.reindexBoundary_normalizedBoundaryValue boundaryEq _
    _ = ((view.selectedTreeFromForest trees index).normalizedBoundaryValue
        kernel).1 := by
      symm
      unfold selectedTreeFromForest
      exact CostRegionTree.reindexBoundary_normalizedBoundaryValue _ _

/-- The semantic atom selected by a retained context-view boundary carries
exactly that proof-relevant boundary's target support.  This is the support
companion of `selectedBoundaryAtom_normal_eq`: both facts are recovered from
the same replayable finite position, so neither duplicate boundary spellings
nor equal normalized values can change which occurrence was selected. -/
theorem selectedBoundaryAtom_targetSupport_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {payload rootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      rootAbstract table.entries)
    (trees : CostRegionBoundaryTrees source targetFree color table)
    {inventory : CostStaticParameterInventory source color targetFree table
      (trees.normalizeValues (normalizeStatic := kernel.normalize))
      rootAbstract}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (index : Fin view.view.retainedEntries.length)
    (occurrence : CostStaticFVarOccurrence rootAbstract)
    (nameEq : occurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? occurrence.name = some slot) :
    (environment.atomValue slot).key.targetSupport =
      (view.view.retainedEntries.get index).boundary.targetSupport := by
  let position := view.entryEmbedding.position index
  have boundaryEq : (trees.getEntry position).boundary =
      view.view.retainedEntries.get index :=
    (trees.getEntry_boundary position).trans
      (view.entryEmbedding.position_get index)
  have atomEq :=
    environment.atomValue_eq_normalizedBoundaryValue_of_reindexedGetEntry
      unambiguous trees position (view.view.retainedEntries.get index)
      boundaryEq occurrence nameEq slot selected
  simpa only [TypedCostStaticAtom.ofBoundaryValue] using
    congrArg (fun atom => atom.key.targetSupport) atomEq

/-- A stopped boundary whose selected child normalizes to a direct source
variable restores exactly like that source variable in another parent atom
environment.  The selected child is recovered from its replayable finite
position; duplicate boundary names are handled by static-decomposition
unambiguity, never by equality search.

The boundary's target support must be empty.  This is the structural fact
provided by a reflective quote reset in the Cost-rho use case, and it is the
precise condition needed to agree with a direct source variable. -/
theorem selectedBoundaryAtom_restoresAsSourceVariable
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {payload leftRootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      leftRootAbstract leftTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRoot}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (index : Fin view.view.retainedEntries.length)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (name : String)
    (rightNameEq : rightOccurrence.name = costRegionSourceVariableName name)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName? leftOccurrence.name =
      some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName? rightOccurrence.name =
      some rightSlot)
    (targetSupportEmpty :
      (view.view.retainedEntries.get index).boundary.targetSupport = [])
    (childNormal :
      ((view.selectedTreeFromForest leftTrees index).normalizedBoundaryValue
        kernel).1 = .fvar name)
    (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot))) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))) := by
  let position := view.entryEmbedding.position index
  have boundaryEq : (leftTrees.getEntry position).boundary =
      view.view.retainedEntries.get index :=
    (leftTrees.getEntry_boundary position).trans
      (view.entryEmbedding.position_get index)
  have leftAtom :=
    leftEnvironment.atomValue_eq_normalizedBoundaryValue_of_reindexedGetEntry
      unambiguous leftTrees position (view.view.retainedEntries.get index)
      boundaryEq leftOccurrence leftNameEq leftSlot leftSelected
  have leftSupport : (leftEnvironment.atomValue leftSlot).key.targetSupport =
      (view.view.retainedEntries.get index).boundary.targetSupport :=
    congrArg (fun atom => atom.key.targetSupport) leftAtom
  have leftNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      ((view.selectedTreeFromForest leftTrees index).normalizedBoundaryValue
        kernel).1 := by
    calc
      (leftEnvironment.atomValue leftSlot).key.normal =
          (((leftTrees.getEntry position).tree.reindexBoundary
            boundaryEq).normalizedBoundaryValue kernel).1 := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue] using
          congrArg (fun atom => atom.key.normal) leftAtom
      _ = ((leftTrees.getEntry position).tree.normalizedBoundaryValue
          kernel).1 :=
        CostRegionTree.reindexBoundary_normalizedBoundaryValue boundaryEq _
      _ = ((view.selectedTreeFromForest leftTrees index
          ).normalizedBoundaryValue kernel).1 := by
        symm
        unfold selectedTreeFromForest
        exact CostRegionTree.reindexBoundary_normalizedBoundaryValue _ _
  have rightSupport :
      (rightEnvironment.atomValue rightSlot).key.targetSupport = [] := by
    rw [rightEnvironment.atomValue_targetSupport_eq_sourceSupport_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightSelected, rightNameEq]
    simp
  have rightNormal : (rightEnvironment.atomValue rightSlot).key.normal =
      .fvar name := by
    rw [rightEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightSelected, rightNameEq]
    exact rightValues.assignment_sourceVariable name
  exact leftEnvironment.substituteAt_commonReifiedAtom_eq_of_restorationComponents
    rightEnvironment leftSlot rightSlot
      (leftSupport.trans (targetSupportEmpty.trans rightSupport.symm))
      (leftNormal.trans (childNormal.trans rightNormal.symm)) depth

/-- Support-independent form of
`selectedBoundaryAtom_restoresAsSourceVariable`.

The boundary may retain a nonempty target binder suffix.  The normalized
child and the direct source-variable atom both contain the same free variable,
so weakening is inert and their unequal support lengths cannot affect the
restored result.  This is the form required below ordinary rho input binders. -/
theorem selectedBoundaryAtom_restoresAsSourceVariable_supportIndependent
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {payload leftRootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      leftRootAbstract leftTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRoot}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (index : Fin view.view.retainedEntries.length)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (name : String)
    (rightNameEq : rightOccurrence.name = costRegionSourceVariableName name)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName? leftOccurrence.name =
      some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName? rightOccurrence.name =
      some rightSlot)
    (childNormal :
      ((view.selectedTreeFromForest leftTrees index).normalizedBoundaryValue
        kernel).1 = .fvar name)
    (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot))) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))) := by
  let position := view.entryEmbedding.position index
  have boundaryEq : (leftTrees.getEntry position).boundary =
      view.view.retainedEntries.get index :=
    (leftTrees.getEntry_boundary position).trans
      (view.entryEmbedding.position_get index)
  have leftAtom :=
    leftEnvironment.atomValue_eq_normalizedBoundaryValue_of_reindexedGetEntry
      unambiguous leftTrees position (view.view.retainedEntries.get index)
      boundaryEq leftOccurrence leftNameEq leftSlot leftSelected
  have leftNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      ((view.selectedTreeFromForest leftTrees index).normalizedBoundaryValue
        kernel).1 := by
    calc
      (leftEnvironment.atomValue leftSlot).key.normal =
          (((leftTrees.getEntry position).tree.reindexBoundary
            boundaryEq).normalizedBoundaryValue kernel).1 := by
        simpa only [TypedCostStaticAtom.ofBoundaryValue] using
          congrArg (fun atom => atom.key.normal) leftAtom
      _ = ((leftTrees.getEntry position).tree.normalizedBoundaryValue
          kernel).1 :=
        CostRegionTree.reindexBoundary_normalizedBoundaryValue boundaryEq _
      _ = ((view.selectedTreeFromForest leftTrees index
          ).normalizedBoundaryValue kernel).1 := by
        symm
        unfold selectedTreeFromForest
        exact CostRegionTree.reindexBoundary_normalizedBoundaryValue _ _
  have rightNormal : (rightEnvironment.atomValue rightSlot).key.normal =
      .fvar name := by
    rw [rightEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      rightOccurrence rightSlot rightSelected, rightNameEq]
    exact rightValues.assignment_sourceVariable name
  have normalEq : (leftEnvironment.atomValue leftSlot).key.normal =
      (rightEnvironment.atomValue rightSlot).key.normal :=
    leftNormal.trans (childNormal.trans rightNormal.symm)
  apply leftEnvironment.substituteAt_commonReifiedAtom_eq_of_scoped_normal
    rightEnvironment leftSlot rightSlot normalEq
  rw [leftNormal, childNormal]
  rfl

/-- Alignment-driven form of
`selectedBoundaryAtom_restoresAsSourceVariable`.  The selected boundary
child need not be evaluated separately: hereditary alignment with a tree
whose normal form is the source variable supplies the required child normal
form. -/
theorem selectedBoundaryAtom_restoresAsSourceVariable_of_alignment
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {payload leftRootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      leftRootAbstract leftTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRoot}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (index : Fin view.view.retainedEntries.length)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (name : String)
    (rightNameEq : rightOccurrence.name = costRegionSourceVariableName name)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName? leftOccurrence.name =
      some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName? rightOccurrence.name =
      some rightSlot)
    (targetSupportEmpty :
      (view.view.retainedEntries.get index).boundary.targetSupport = [])
    {rightAvailable rightOuter : List TypeExpr} {rightType : TypeExpr}
    (rightTree : CostRegionTree source targetFree rightAvailable rightOuter
      (.fvar name) rightType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (view.selectedTreeFromForest leftTrees index) rightTree)
    (rightNormal :
      (rightTree.normalize (normalizeStatic := kernel.normalize)).pattern =
        .fvar name)
    (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot))) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))) := by
  apply view.selectedBoundaryAtom_restoresAsSourceVariable unambiguous
    leftTrees leftEnvironment rightEnvironment index leftOccurrence leftNameEq
      rightOccurrence name rightNameEq leftSlot leftSelected rightSlot
      rightSelected targetSupportEmpty
  · rw [CostRegionTree.normalizedBoundaryValue_pattern]
    exact children.normalize_pattern_eq.trans rightNormal

/-- Alignment-driven, support-independent boundary/source restoration.
Unlike `selectedBoundaryAtom_restoresAsSourceVariable_of_alignment`, this
form remains valid when the selected boundary sits below ordinary binders and
therefore retains a nonempty target support. -/
theorem selectedBoundaryAtom_restoresAsSourceVariable_of_alignment_supportIndependent
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {payload leftRootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      leftRootAbstract leftTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRoot}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (index : Fin view.view.retainedEntries.length)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (view.view.retainedEntries.get index).boundary)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (name : String)
    (rightNameEq : rightOccurrence.name = costRegionSourceVariableName name)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName? leftOccurrence.name =
      some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName? rightOccurrence.name =
      some rightSlot)
    {rightAvailable rightOuter : List TypeExpr} {rightType : TypeExpr}
    (rightTree : CostRegionTree source targetFree rightAvailable rightOuter
      (.fvar name) rightType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (view.selectedTreeFromForest leftTrees index) rightTree)
    (rightNormal :
      (rightTree.normalize (normalizeStatic := kernel.normalize)).pattern =
        .fvar name)
    (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot))) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))) := by
  apply view.selectedBoundaryAtom_restoresAsSourceVariable_supportIndependent
    unambiguous leftTrees leftEnvironment rightEnvironment index leftOccurrence
      leftNameEq rightOccurrence name rightNameEq leftSlot leftSelected
      rightSlot rightSelected
  rw [CostRegionTree.normalizedBoundaryValue_pattern]
  exact children.normalize_pattern_eq.trans rightNormal

end CostStaticPlanContextInventoryView

namespace CostStaticPlanContextPair

/-- The actual recursive source child selected by a retained target
occurrence's nonlinear pullback.  Selection proceeds through the full typed
source table, so a source occurrence discarded by the left context view is
still available to the semantic closure. -/
def selectedSourceTreeFromForest
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract
      leftTable.entries rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (index : Fin pair.right.view.retainedEntries.length) :
    CostRegionTree source targetFree
      (pair.selectedSourceEntry index).boundary.targetSupport []
      (pair.selectedSourceEntry index).boundary.content
      (pair.selectedSourceEntry index).boundary.targetType := by
  let position := pair.leftEntryIndexAtSource (pair.selectedPullback index)
  have boundaryEq : (leftTrees.getEntry position).boundary =
      pair.selectedSourceEntry index := by
    simpa [CostStaticPlanContextPair.selectedSourceEntry] using
      leftTrees.getEntry_boundary position
  exact (leftTrees.getEntry position).tree.reindexBoundary boundaryEq

/-- The actual recursive target child selected by a retained context-view
entry.  The keep/skip path is replayed into the full target table before the
tree is selected, preserving repeated equal occurrences as distinct
positions. -/
def selectedTargetTreeFromForest
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract
      leftTable.entries rightTable.entries)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    (index : Fin pair.right.view.retainedEntries.length) :
    CostRegionTree source targetFree
      (pair.right.view.retainedEntries.get index).boundary.targetSupport []
      (pair.right.view.retainedEntries.get index).boundary.content
      (pair.right.view.retainedEntries.get index).boundary.targetType := by
  let position := pair.right.entryEmbedding.position index
  have boundaryEq : (rightTrees.getEntry position).boundary =
      pair.right.view.retainedEntries.get index :=
    (rightTrees.getEntry_boundary position).trans
      (pair.right.entryEmbedding.position_get index)
  exact (rightTrees.getEntry position).tree.reindexBoundary boundaryEq

/-- A retained target occurrence and its exact pulled-back source occurrence
induce the same semantic atom whenever their recursive child trees are
hereditarily aligned.  The source child is selected from the full edge
inventory, so this theorem does not assume that it belongs to the left
context view's retained subinventory. -/
theorem alignedSelectedSourceAtom_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    {leftEntries rightEntries :
      List (TypedCostRegionBoundary source color targetFree)}
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (index : Fin pair.right.view.retainedEntries.length)
    (leftTree : CostRegionTree source targetFree
      (pair.selectedSourceEntry index).boundary.targetSupport []
      (pair.selectedSourceEntry index).boundary.content
      (pair.selectedSourceEntry index).boundary.targetType)
    (rightTree : CostRegionTree source targetFree
      (pair.right.view.retainedEntries.get index).boundary.targetSupport []
      (pair.right.view.retainedEntries.get index).boundary.content
      (pair.right.view.retainedEntries.get index).boundary.targetType)
    (alignment : CostRegionTreeNormalizationAlignment source kernel targetFree
      leftTree rightTree) :
    TypedCostStaticAtom.ofBoundaryValue (pair.selectedSourceEntry index)
        (leftTree.normalizedBoundaryValue kernel) =
      TypedCostStaticAtom.ofBoundaryValue
        (pair.right.view.retainedEntries.get index)
        (rightTree.normalizedBoundaryValue kernel) :=
  CostRegionTree.alignedBoundaryAtom_eq
    (pair.selectedSourceEntry_sameFiber index) alignment

/-- Source semantic atoms selected through the full-inventory nonlinear
pullback, listed in retained-target order.  A duplicated source occurrence
therefore appears once for every target occurrence that selects it. -/
def selectedSourceNormalizedAtoms
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    {leftEntries rightEntries :
      List (TypedCostRegionBoundary source color targetFree)}
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (trees : ∀ index : Fin pair.right.view.retainedEntries.length,
      CostRegionTree source targetFree
        (pair.selectedSourceEntry index).boundary.targetSupport []
        (pair.selectedSourceEntry index).boundary.content
        (pair.selectedSourceEntry index).boundary.targetType) :
    List (TypedCostStaticAtom source color targetFree) :=
  List.ofFn fun index =>
    TypedCostStaticAtom.ofBoundaryValue (pair.selectedSourceEntry index)
      ((trees index).normalizedBoundaryValue kernel)

/-- Target semantic atoms in the retained context-view order. -/
def selectedTargetNormalizedAtoms
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    {leftEntries rightEntries :
      List (TypedCostRegionBoundary source color targetFree)}
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (trees : ∀ index : Fin pair.right.view.retainedEntries.length,
      CostRegionTree source targetFree
        (pair.right.view.retainedEntries.get index).boundary.targetSupport []
        (pair.right.view.retainedEntries.get index).boundary.content
        (pair.right.view.retainedEntries.get index).boundary.targetType) :
    List (TypedCostStaticAtom source color targetFree) :=
  List.ofFn fun index =>
    TypedCostStaticAtom.ofBoundaryValue
      (pair.right.view.retainedEntries.get index)
      ((trees index).normalizedBoundaryValue kernel)

/-- Hereditary child alignment identifies the entire retained target atom
list with the full-source inventory pulled back into target order.  This is
the finite nonlinear joint needed by restoration: duplication is explicit,
discard is harmless, and no membership in the left retained subinventory is
assumed. -/
theorem selectedSourceNormalizedAtoms_eq_selectedTargetNormalizedAtoms
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    {leftEntries rightEntries :
      List (TypedCostRegionBoundary source color targetFree)}
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract leftEntries
      rightEntries)
    (leftTrees : ∀ index : Fin pair.right.view.retainedEntries.length,
      CostRegionTree source targetFree
        (pair.selectedSourceEntry index).boundary.targetSupport []
        (pair.selectedSourceEntry index).boundary.content
        (pair.selectedSourceEntry index).boundary.targetType)
    (rightTrees : ∀ index : Fin pair.right.view.retainedEntries.length,
      CostRegionTree source targetFree
        (pair.right.view.retainedEntries.get index).boundary.targetSupport []
        (pair.right.view.retainedEntries.get index).boundary.content
        (pair.right.view.retainedEntries.get index).boundary.targetType)
    (alignments : ∀ index,
      CostRegionTreeNormalizationAlignment source kernel targetFree
        (leftTrees index) (rightTrees index)) :
    pair.selectedSourceNormalizedAtoms (kernel := kernel) leftTrees =
      pair.selectedTargetNormalizedAtoms (kernel := kernel) rightTrees := by
  apply List.ofFn_inj.mpr
  funext index
  exact pair.alignedSelectedSourceAtom_eq index (leftTrees index)
    (rightTrees index) (alignments index)

/-- The full-inventory pullback and an aligned pair of actual recursive
children identify the semantic slots selected in the two parent atom
environments.  This is the stopped-site restoration joint: positional
provenance is used to find the children, then disappears only after their
complete semantic atoms have been proved equal. -/
theorem selectedEnvironmentAtom_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract
      leftTable.entries rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (index : Fin pair.right.view.retainedEntries.length)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (pair.selectedSourceEntry index).boundary)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (rightNameEq : rightOccurrence.name = costRegionBoundaryVariableName
      (pair.right.view.retainedEntries.get index).boundary)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName? leftOccurrence.name =
      some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName? rightOccurrence.name =
      some rightSlot)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (pair.selectedSourceTreeFromForest leftTrees index)
      (pair.selectedTargetTreeFromForest rightTrees index)) :
    leftEnvironment.atomValue leftSlot =
      rightEnvironment.atomValue rightSlot := by
  let sourcePosition :=
    pair.leftEntryIndexAtSource (pair.selectedPullback index)
  have sourceBoundaryEq : (leftTrees.getEntry sourcePosition).boundary =
      pair.selectedSourceEntry index := by
    simpa [CostStaticPlanContextPair.selectedSourceEntry] using
      leftTrees.getEntry_boundary sourcePosition
  let targetPosition := pair.right.entryEmbedding.position index
  have targetBoundaryEq : (rightTrees.getEntry targetPosition).boundary =
      pair.right.view.retainedEntries.get index :=
    (rightTrees.getEntry_boundary targetPosition).trans
      (pair.right.entryEmbedding.position_get index)
  have leftAtom :=
    leftEnvironment.atomValue_eq_normalizedBoundaryValue_of_reindexedGetEntry
      unambiguous leftTrees sourcePosition (pair.selectedSourceEntry index)
      sourceBoundaryEq leftOccurrence leftNameEq leftSlot leftSelected
  have rightAtom :=
    rightEnvironment.atomValue_eq_normalizedBoundaryValue_of_reindexedGetEntry
      unambiguous rightTrees targetPosition
      (pair.right.view.retainedEntries.get index) targetBoundaryEq
      rightOccurrence rightNameEq rightSlot rightSelected
  have childAtom := pair.alignedSelectedSourceAtom_eq index
    (pair.selectedSourceTreeFromForest leftTrees index)
    (pair.selectedTargetTreeFromForest rightTrees index) children
  exact leftAtom.trans (childAtom.trans rightAtom.symm)

/-- The stopped-site atom equality is already strong enough for the common
restoration apex.  After the exact source and target children have been
selected by position and aligned hereditarily, their canonical atom names
restore to the same compact value at every binder depth.

This is the form consumed by restoration-level frame congruence: positional
occurrence identity selects the two atoms, while only their proved semantic
key equality reaches the common cospan. -/
theorem selectedEnvironmentAtoms_restore_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {first second : CostStaticPlanDecoration source}
    {sourceBoundaries targetBoundaries :
      List (CostRegionBoundary × CostTreeDecoration source)}
    {edge : CostStaticPlanEdge source first second sourceBoundaries
      targetBoundaries}
    {leftPayload rightPayload leftRootAbstract rightRootAbstract : Pattern}
    (pair : CostStaticPlanContextPair source color targetFree edge
      leftPayload rightPayload leftRootAbstract rightRootAbstract
      leftTable.entries rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftRoot rightRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRoot}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (index : Fin pair.right.view.retainedEntries.length)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (leftNameEq : leftOccurrence.name = costRegionBoundaryVariableName
      (pair.selectedSourceEntry index).boundary)
    (rightOccurrence : CostStaticFVarOccurrence rightRoot)
    (rightNameEq : rightOccurrence.name = costRegionBoundaryVariableName
      (pair.right.view.retainedEntries.get index).boundary)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName? leftOccurrence.name =
      some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName? rightOccurrence.name =
      some rightSlot)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (pair.selectedSourceTreeFromForest leftTrees index)
      (pair.selectedTargetTreeFromForest rightTrees index))
    (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot))) =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))) := by
  have atomEq := pair.selectedEnvironmentAtom_eq unambiguous leftTrees
    rightTrees leftEnvironment rightEnvironment index leftOccurrence
      leftNameEq rightOccurrence rightNameEq leftSlot leftSelected rightSlot
      rightSelected children
  exact leftEnvironment.substituteAt_commonReifiedAtom_eq_of_key_eq
    rightEnvironment leftSlot rightSlot (congrArg TypedCostStaticAtom.key atomEq)
      depth

end CostStaticPlanContextPair

end Mettapedia.GSLT.LanguageDef
