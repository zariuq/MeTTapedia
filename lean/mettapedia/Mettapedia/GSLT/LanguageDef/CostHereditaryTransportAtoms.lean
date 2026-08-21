import Mettapedia.GSLT.LanguageDef.CostElaborationTransport
import Mettapedia.GSLT.LanguageDef.CostRestorationRelation
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

namespace TypedCostRegionBoundaryTable.Values

/-- Select the proof-relevant boundary and its current value by one exact
finite table position.  Unlike `resolve`, this operation never identifies
two entries merely because their serialized boundary names agree. -/
def getEntry
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      table)
    (index : Fin table.entries.length) :
    TypedCostRegionBoundaryTable.Values.Resolved source color targetFree :=
  match values, index with
  | .nil, index => Fin.elim0 index
  | @TypedCostRegionBoundaryTable.Values.cons _ _ _ _ _ boundary _ tail value
      childValues, index =>
      Fin.cases ⟨boundary, value⟩
        (fun childIndex => getEntry tail childValues childIndex) index

/-- Positional value selection recovers the exact boundary record stored at
that position. -/
theorem getEntry_boundary
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      table)
    (index : Fin table.entries.length) :
    (getEntry table values index).1 = table.entries.get index :=
  match values, index with
  | .nil, index => Fin.elim0 index
  | .cons _ _, ⟨0, _⟩ => rfl
  | @TypedCostRegionBoundaryTable.Values.cons _ _ _ _ _ _ _ tail _
      childValues, ⟨position + 1, inBounds⟩ =>
      getEntry_boundary tail childValues
        ⟨position, Nat.lt_of_succ_lt_succ inBounds⟩

/-- Restrict a boundary-value vector along the exact keep/skip path of an
endpoint-local entry embedding.

The operation is positional rather than key based.  It therefore preserves
the distinction between repeated equal boundary entries and is the value-level
counterpart of `CostRegionBoundaryTrees.restrictAlongEntryEmbedding`. -/
def restrictAlongEntryEmbedding
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} :
    {smallOccurrences largeOccurrences : List CostRegionOccurrence} →
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences) →
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences) →
    CostStaticPlanEntryEmbedding source color targetFree smallTable.entries
      largeTable.entries →
    TypedCostRegionBoundaryTable.Values source color targetFree largeTable →
    TypedCostRegionBoundaryTable.Values source color targetFree smallTable
  | [], _, .nil, largeTable, _embedding, _values => .nil
  | _ :: _, [], .cons smallBoundary smallContent smallTail, .nil,
      embedding, values => by
      cases embedding
  | _ :: _, _ :: _, .cons smallBoundary smallContent smallTail,
      .cons largeBoundary largeContent largeTail, embedding, values => by
      cases values with
      | cons largeValue largeValues =>
          cases embedding with
          | keep tail =>
              exact .cons largeValue
                (restrictAlongEntryEmbedding smallTail largeTail tail
                  largeValues)
          | skip _ tail =>
              exact restrictAlongEntryEmbedding
                (.cons smallBoundary smallContent smallTail) largeTail tail
                  largeValues

/-- Restricting values along the identity embedding retains the original
dependent vector exactly. -/
theorem restrictAlongEntryEmbedding_refl
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      table) :
    restrictAlongEntryEmbedding table table
        (CostStaticPlanEntryEmbedding.refl table.entries) values = values := by
  induction table with
  | nil => cases values; rfl
  | cons boundary content tail inductionHypothesis =>
      cases values with
      | @cons _occurrence _occurrences _boundary content' _tail value
          childValues =>
          have contentEq : content' = content := Subsingleton.elim _ _
          cases contentEq
          change TypedCostRegionBoundaryTable.Values.cons value
              (restrictAlongEntryEmbedding tail tail
                (CostStaticPlanEntryEmbedding.refl tail.entries)
                childValues) =
            TypedCostRegionBoundaryTable.Values.cons value childValues
          rw [inductionHypothesis childValues]

/-- Restriction preserves the current value at every retained finite
position.  The selected occurrence is replayed through the embedding path,
so duplicate equal boundary names cannot redirect the lookup. -/
theorem restrictAlongEntryEmbedding_getEntry
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      smallTable.entries largeTable.entries)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable)
    (index : Fin smallTable.entries.length) :
    getEntry smallTable
        (restrictAlongEntryEmbedding smallTable largeTable embedding values)
        index =
      getEntry largeTable values (embedding.position index) := by
  induction largeTable generalizing smallOccurrences with
  | nil =>
      cases smallTable with
      | nil => exact Fin.elim0 index
      | cons smallBoundary smallContent smallTail => cases embedding
  | cons largeBoundary largeContent largeTail inductionHypothesis =>
      cases values with
      | cons largeValue largeValues =>
          cases smallTable with
          | nil => exact Fin.elim0 index
          | cons smallBoundary smallContent smallTail =>
              cases embedding with
              | keep tail =>
                  induction index using Fin.cases with
                  | zero => rfl
                  | succ previous =>
                      exact inductionHypothesis smallTail tail largeValues
                        previous
              | skip _ tail =>
                  exact inductionHypothesis
                    (.cons smallBoundary smallContent smallTail) tail
                      largeValues index

/-- Nested value restriction and one-shot restriction along the composed
embedding select the same complete dependent entry at every retained finite
position.  This pointwise form avoids quotienting proof-relevant vectors by
an extensional equality while still giving the exact composition law needed
by recursive clients. -/
theorem restrictAlongEntryEmbedding_comp_getEntry
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor}
    {smallOccurrences middleOccurrences largeOccurrences :
      List CostRegionOccurrence}
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (middleTable : TypedCostRegionBoundaryTable source color targetFree
      middleOccurrences)
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (smallToMiddle : CostStaticPlanEntryEmbedding source color targetFree
      smallTable.entries middleTable.entries)
    (middleToLarge : CostStaticPlanEntryEmbedding source color targetFree
      middleTable.entries largeTable.entries)
    (values : TypedCostRegionBoundaryTable.Values source color targetFree
      largeTable)
    (index : Fin smallTable.entries.length) :
    getEntry smallTable
        (restrictAlongEntryEmbedding smallTable middleTable smallToMiddle
          (restrictAlongEntryEmbedding middleTable largeTable middleToLarge
            values)) index =
      getEntry smallTable
        (restrictAlongEntryEmbedding smallTable largeTable
          (smallToMiddle.comp middleToLarge) values) index := by
  rw [restrictAlongEntryEmbedding_getEntry,
    restrictAlongEntryEmbedding_getEntry,
    restrictAlongEntryEmbedding_getEntry,
    CostStaticPlanEntryEmbedding.position_comp]

end TypedCostRegionBoundaryTable.Values

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

/-- Restrict a proof-relevant boundary forest along the exact keep/skip path
of an endpoint-local entry embedding.

This is not lookup by boundary equality.  In particular, two equal boundary
values retained at different positions select the two corresponding child
trees of the large forest.  The occurrence indices of the two tables may be
spelled differently; the embedding relates their typed entry inventories,
which are precisely the indices consumed by the forest. -/
def restrictAlongEntryEmbedding
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} :
    {smallOccurrences largeOccurrences : List CostRegionOccurrence} →
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences) →
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences) →
    CostStaticPlanEntryEmbedding source color targetFree smallTable.entries
      largeTable.entries →
    CostRegionBoundaryTrees source targetFree color largeTable →
    CostRegionBoundaryTrees source targetFree color smallTable
  | [], _, .nil, largeTable, _embedding, _trees => .nil
  | _ :: _, [], .cons smallBoundary smallContent smallTail, .nil,
      embedding, trees => by
      cases embedding
  | _ :: _, _ :: _, .cons smallBoundary smallContent smallTail,
      .cons largeBoundary largeContent largeTail, embedding, trees => by
      cases trees with
      | cons largeHead largeChildren =>
          cases embedding with
          | keep tail =>
              exact .cons largeHead
                (restrictAlongEntryEmbedding smallTail largeTail tail
                  largeChildren)
          | skip _ tail =>
              exact restrictAlongEntryEmbedding
                (.cons smallBoundary smallContent smallTail) largeTail tail
                  largeChildren

/-- Restriction along the identity keep path is definitionally faithful to
the complete forest.  In particular, it neither rebuilds nor reorders any
proof-relevant child. -/
theorem restrictAlongEntryEmbedding_refl
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    (table : TypedCostRegionBoundaryTable source color targetFree occurrences)
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    restrictAlongEntryEmbedding table table
        (CostStaticPlanEntryEmbedding.refl table.entries) trees = trees := by
  induction table with
  | nil => cases trees; rfl
  | cons boundary content tail inductionHypothesis =>
      cases trees with
      | @cons _color _occurrence _occurrences _boundary content' _tail head
          children =>
          have contentEq : content' = content := Subsingleton.elim _ _
          cases contentEq
          change CostRegionBoundaryTrees.cons head
              (restrictAlongEntryEmbedding tail tail
                (CostStaticPlanEntryEmbedding.refl tail.entries) children) =
            CostRegionBoundaryTrees.cons head children
          rw [inductionHypothesis children]

/-- Restriction replays the keep/skip path at the level of actual child
decorations.  The selected child is the one at the embedding's finite
position in the original forest; no equality lookup can redirect a repeated
boundary value to another occurrence. -/
theorem restrictAlongEntryEmbedding_getEntry_decoration
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      smallTable.entries largeTable.entries)
    (trees : CostRegionBoundaryTrees source targetFree color largeTable)
    (index : Fin smallTable.entries.length) :
    ((restrictAlongEntryEmbedding smallTable largeTable embedding trees
        ).getEntry index).decoration =
      (trees.getEntry (embedding.position index)).decoration := by
  induction largeTable generalizing smallOccurrences with
  | nil =>
      cases smallTable with
      | nil => exact Fin.elim0 index
      | cons smallBoundary smallContent smallTail => cases embedding
  | cons largeBoundary largeContent largeTail inductionHypothesis =>
      cases trees with
      | cons largeHead largeChildren =>
          cases smallTable with
          | nil => exact Fin.elim0 index
          | cons smallBoundary smallContent smallTail =>
              cases embedding with
              | keep tail =>
                  induction index using Fin.cases with
                  | zero => rfl
                  | succ previous =>
                      exact inductionHypothesis smallTail tail largeChildren
                        previous
              | skip _ tail =>
                  exact inductionHypothesis
                    (.cons smallBoundary smallContent smallTail) tail
                      largeChildren index

/-- The same positional replay preserves the complete dependent child, not
only its proof-free decoration.  This is the proof-relevant form required by
recursive normalization: the boundary typing evidence and the actual child
tree cross the restriction boundary together. -/
theorem restrictAlongEntryEmbedding_getEntry
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      smallTable.entries largeTable.entries)
    (trees : CostRegionBoundaryTrees source targetFree color largeTable)
    (index : Fin smallTable.entries.length) :
    (restrictAlongEntryEmbedding smallTable largeTable embedding trees
        ).getEntry index =
      trees.getEntry (embedding.position index) := by
  induction largeTable generalizing smallOccurrences with
  | nil =>
      cases smallTable with
      | nil => exact Fin.elim0 index
      | cons smallBoundary smallContent smallTail => cases embedding
  | cons largeBoundary largeContent largeTail inductionHypothesis =>
      cases trees with
      | cons largeHead largeChildren =>
          cases smallTable with
          | nil => exact Fin.elim0 index
          | cons smallBoundary smallContent smallTail =>
              cases embedding with
              | keep tail =>
                  induction index using Fin.cases with
                  | zero => rfl
                  | succ previous =>
                      exact inductionHypothesis smallTail tail largeChildren
                        previous
              | skip _ tail =>
                  exact inductionHypothesis
                    (.cons smallBoundary smallContent smallTail) tail
                      largeChildren index

/-- Nested forest restriction and restriction along the composed embedding
return the identical proof-relevant child at every retained position.  Both
the typed boundary and the actual recursive tree are preserved; equal
decorations at different positions therefore remain distinguishable. -/
theorem restrictAlongEntryEmbedding_comp_getEntry
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor}
    {smallOccurrences middleOccurrences largeOccurrences :
      List CostRegionOccurrence}
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (middleTable : TypedCostRegionBoundaryTable source color targetFree
      middleOccurrences)
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (smallToMiddle : CostStaticPlanEntryEmbedding source color targetFree
      smallTable.entries middleTable.entries)
    (middleToLarge : CostStaticPlanEntryEmbedding source color targetFree
      middleTable.entries largeTable.entries)
    (trees : CostRegionBoundaryTrees source targetFree color largeTable)
    (index : Fin smallTable.entries.length) :
    (restrictAlongEntryEmbedding smallTable middleTable smallToMiddle
        (restrictAlongEntryEmbedding middleTable largeTable middleToLarge
          trees)).getEntry index =
      (restrictAlongEntryEmbedding smallTable largeTable
        (smallToMiddle.comp middleToLarge) trees).getEntry index := by
  rw [restrictAlongEntryEmbedding_getEntry,
    restrictAlongEntryEmbedding_getEntry,
    restrictAlongEntryEmbedding_getEntry,
    CostStaticPlanEntryEmbedding.position_comp]

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

/-- A positionally selected proof-relevant child carries an actual entry of
the finite table. -/
theorem getEntry_mem
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {color : CostStaticColor} {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table)
    (index : Fin table.entries.length) :
    (trees.getEntry index).boundary ∈ table.entries := by
  rw [trees.getEntry_boundary index]
  exact List.get_mem table.entries index

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

/-- Table-indexed normalization lookup recovers the selected child's exact
boundary and compact normal value.  If an equal key occurs earlier, static
decomposition unambiguity identifies the two normalized values; the returned
boundary is still proved to be the one selected by the supplied finite
position. -/
theorem exists_resolve_normalizedValue_eq_getEntry
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (trees : CostRegionBoundaryTrees source targetFree color table)
    (index : Fin table.entries.length) :
    ∃ resolved : TypedCostRegionBoundaryTable.Values.Resolved source color
        targetFree,
      (trees.normalizeValues
          (normalizeStatic := kernel.normalize)).resolve table
            (costRegionBoundaryVariableName
              (trees.getEntry index).boundary.boundary) = some resolved ∧
        resolved.1 = (trees.getEntry index).boundary ∧
        resolved.2.1 =
          ((trees.getEntry index).tree.normalizedBoundaryValue kernel).1 := by
  let decorationIndex : Fin trees.decorations.length :=
    Fin.cast (trees.decorations_length_eq_entries_length).symm index
  obtain ⟨resolved, resolution, atomEq⟩ :=
    trees.exists_resolve_normalizedAtom_eq_getDecoration unambiguous
      decorationIndex
  have selectedEq : trees.getDecoration decorationIndex = trees.getEntry index :=
    rfl
  rw [selectedEq] at resolution atomEq
  have resolvedBoundary : resolved.1 = (trees.getEntry index).boundary := by
    have boundaryMap := TypedCostRegionBoundaryTable.Values.resolve_boundary
      table
      (trees.normalizeValues (normalizeStatic := kernel.normalize))
      (costRegionBoundaryVariableName
        (trees.getEntry index).boundary.boundary)
    rw [resolution] at boundaryMap
    have tableResolution : table.resolve
        (costRegionBoundaryVariableName
          (trees.getEntry index).boundary.boundary) =
        some (trees.getEntry index).boundary :=
      table.resolve_of_mem_entries (trees.getEntry index).boundary
        (trees.getEntry_mem index)
    rw [tableResolution] at boundaryMap
    exact Option.some.inj boundaryMap
  have resolvedNormal : resolved.2.1 =
      ((trees.getEntry index).tree.normalizedBoundaryValue kernel).1 := by
    have keyEq := congrArg (fun atom => atom.key.normal) atomEq
    exact keyEq
  exact ⟨resolved, resolution, resolvedBoundary, resolvedNormal⟩

/-- Restricting a child-normalized forest preserves the assignment at every
boundary name defined by the smaller table.  Repeated equal entries remain
different positions in the two forests; static-decomposition unambiguity is
used only to show that collision-free name lookup observes the same compact
normal value whichever equal occurrence appears first. -/
theorem normalizeValues_assignment_restrict_eq_of_resolve_defined
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      smallTable.entries largeTable.entries)
    (trees : CostRegionBoundaryTrees source targetFree color largeTable)
    (name : String)
    (defined : smallTable.resolve name ≠ none) :
    ((restrictAlongEntryEmbedding smallTable largeTable embedding trees
        ).normalizeValues (normalizeStatic := kernel.normalize)).assignment
          smallTable name =
      (trees.normalizeValues
          (normalizeStatic := kernel.normalize)).assignment largeTable name := by
  cases smallTableResolution : smallTable.resolve name with
  | none => exact (defined smallTableResolution).elim
  | some boundary =>
      have nameEq : name =
          costRegionBoundaryVariableName boundary.boundary :=
        smallTable.name_eq_boundaryVariable_of_resolve_eq_some
          smallTableResolution
      have boundaryMembership : boundary ∈ smallTable.entries :=
        smallTable.mem_entries_of_resolve_eq_some smallTableResolution
      obtain ⟨index, indexEq⟩ := List.get_of_mem boundaryMembership
      let restricted := restrictAlongEntryEmbedding smallTable largeTable
        embedding trees
      have restrictedBoundary : (restricted.getEntry index).boundary =
          boundary :=
        (restricted.getEntry_boundary index).trans indexEq
      obtain ⟨smallResolved, smallResolution, _smallBoundary,
          smallNormal⟩ :=
        restricted.exists_resolve_normalizedValue_eq_getEntry unambiguous index
      let largeIndex := embedding.position index
      obtain ⟨largeResolved, largeResolution, _largeBoundary,
          largeNormal⟩ :=
        trees.exists_resolve_normalizedValue_eq_getEntry unambiguous largeIndex
      have entryEq : restricted.getEntry index =
          trees.getEntry largeIndex :=
        restrictAlongEntryEmbedding_getEntry smallTable largeTable embedding
          trees index
      have smallResolutionAtName :
          (restricted.normalizeValues
              (normalizeStatic := kernel.normalize)).resolve smallTable name =
            some smallResolved := by
        rw [nameEq, ← restrictedBoundary]
        exact smallResolution
      have largeResolutionAtName :
          (trees.normalizeValues
              (normalizeStatic := kernel.normalize)).resolve largeTable name =
            some largeResolved := by
        rw [nameEq, ← restrictedBoundary, entryEq]
        exact largeResolution
      have normalEq : smallResolved.2.1 = largeResolved.2.1 := by
        rw [entryEq] at smallNormal
        exact smallNormal.trans largeNormal.symm
      have decodedName : decodeCostRegionSourceVariableName name = none := by
        rw [nameEq]
        exact decodeCostRegionSourceVariableName_boundary boundary.boundary
      change
        (restricted.normalizeValues
            (normalizeStatic := kernel.normalize)).assignment smallTable name =
          (trees.normalizeValues
            (normalizeStatic := kernel.normalize)).assignment largeTable name
      simp only [TypedCostRegionBoundaryTable.Values.assignment, decodedName]
      rw [smallResolutionAtName, largeResolutionAtName]
      exact normalEq

/-- Positional restriction preserves normalized restoration at any requested
binder depth.  Typing is used only to justify the finite free-name support of
the skeleton; its authored bound context need not coincide with the depth at
which a surrounding caller performs substitution. -/
theorem normalizeValues_substituteAt_restrict_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      smallTable.entries largeTable.entries)
    (trees : CostRegionBoundaryTrees source targetFree color largeTable)
    {typedBound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : WellSorted.HasType source.costWholeLanguage
      smallTable.mappedFreeContext typedBound pattern type)
    (object : WellSorted.isObjectPattern pattern = true)
    (availableDepth : Nat) :
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        smallTable.restorationSupport
        (((restrictAlongEntryEmbedding smallTable largeTable embedding trees
          ).normalizeValues
            (normalizeStatic := kernel.normalize)).assignment smallTable)
        availableDepth pattern =
      ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
        largeTable.restorationSupport
        ((trees.normalizeValues
          (normalizeStatic := kernel.normalize)).assignment largeTable)
        availableDepth pattern := by
  apply ReflectiveContextSupport.substituteAt_eq_of_inputsAgreeOn
  intro name membership
  obtain ⟨freeType, lookup⟩ :=
    typed.freeType_of_mem_freeFvarNames_of_isObjectPattern object membership
  cases decodedName : decodeCostRegionSourceVariableName name with
  | some sourceName =>
      constructor <;>
        simp [TypedCostRegionBoundaryTable.restorationSupport,
          TypedCostRegionBoundaryTable.Values.assignment, decodedName]
  | none =>
      cases smallResolved : smallTable.resolve name with
      | none =>
          simp [TypedCostRegionBoundaryTable.mappedFreeContext, decodedName,
            smallResolved] at lookup
      | some boundary =>
          have defined : smallTable.resolve name ≠ none := by
            simp [smallResolved]
          have tableResolution :=
            smallTable.resolve_eq_of_entries_subset largeTable
              embedding.subset name defined
          have largeResolved : largeTable.resolve name = some boundary := by
            simpa [smallResolved] using tableResolution
          constructor
          · simp [TypedCostRegionBoundaryTable.restorationSupport,
              decodedName, smallResolved, largeResolved]
          · exact normalizeValues_assignment_restrict_eq_of_resolve_defined
              unambiguous smallTable largeTable embedding trees name defined

/-- Restoring a typed object skeleton from a positionally restricted child
forest agrees exactly with restoring it from the root forest.  The theorem
observes only the finite names occurring in the skeleton: retained duplicate
occurrences stay distinct in the proof-relevant forests, while collision-free
lookup is identified extensionally by static-decomposition unambiguity. -/
theorem normalizeValues_restoreSupportedSkeleton_restrict_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {targetFree : FreeTypeContext} {color : CostStaticColor}
    {smallOccurrences largeOccurrences : List CostRegionOccurrence}
    (smallTable : TypedCostRegionBoundaryTable source color targetFree
      smallOccurrences)
    (largeTable : TypedCostRegionBoundaryTable source color targetFree
      largeOccurrences)
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      smallTable.entries largeTable.entries)
    (trees : CostRegionBoundaryTrees source targetFree color largeTable)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : WellSorted.HasType source.costWholeLanguage
      smallTable.mappedFreeContext bound pattern type)
    (object : WellSorted.isObjectPattern pattern = true) :
    ((restrictAlongEntryEmbedding smallTable largeTable embedding trees
        ).normalizeValues
          (normalizeStatic := kernel.normalize)).restoreSupportedSkeleton
            smallTable bound pattern =
      (trees.normalizeValues
          (normalizeStatic := kernel.normalize)).restoreSupportedSkeleton
            largeTable bound pattern := by
  exact normalizeValues_substituteAt_restrict_eq unambiguous smallTable
    largeTable embedding trees typed object bound.length

end CostRegionBoundaryTrees

/-- Normalized restoration of a plan's mapped and thickened abstract is
unchanged when its exact entry embedding is replayed into a larger root
forest.  Objecthood remains an explicit source-side premise; callers with a
semantic admission derive it there rather than making this transport lemma
depend on canonical-stop policy. -/
theorem CostStaticRegionPlan.normalizeValues_restoreMappedAbstract_restrict_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer payload sourceType)
    (payloadObject : WellSorted.isObjectPattern payload = true)
    {rootOccurrences : List CostRegionOccurrence}
    (rootTable : TypedCostRegionBoundaryTable source color targetFree
      rootOccurrences)
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      plan.boundaryTable.entries rootTable.entries)
    (rootTrees : CostRegionBoundaryTrees source targetFree color rootTable) :
    let mappedAbstract := thinning.thickenAmbientBVars 0
      (mapPattern (color.symbols source) plan.abstractPattern)
    ((CostRegionBoundaryTrees.restrictAlongEntryEmbedding
        plan.boundaryTable rootTable embedding rootTrees).normalizeValues
          (normalizeStatic := kernel.normalize)).restoreSupportedSkeleton
            plan.boundaryTable sourceAvailable mappedAbstract =
      (rootTrees.normalizeValues
          (normalizeStatic := kernel.normalize)).restoreSupportedSkeleton
            rootTable sourceAvailable mappedAbstract := by
  dsimp only
  obtain ⟨supported, _safe⟩ :=
    plan.abstractPattern_supportedSafe plan.boundaryTable (by
      intro boundary membership
      exact membership)
  have mapped := supported.mapCostStatic source color
  have transport := plan.boundaryTable.transport_of_fiberCoherent
    plan.boundaryTable_fiberCoherent
  rw [transport.freeContext] at mapped
  have thickened := mapped.thickenAmbientBVars (inner := []) thinning
  simp only [List.nil_append, List.length_nil] at thickened
  apply CostRegionBoundaryTrees.normalizeValues_substituteAt_restrict_eq
    unambiguous plan.boundaryTable rootTable embedding rootTrees thickened
  · rw [thinning.isObjectPattern_thickenAmbientBVars,
      WellSorted.isObjectPattern_mapPattern,
      plan.abstractPattern_object payloadObject]

/-- Replacing every boundary in a plan by its normalized hereditary value
preserves the reflective equation class of the original payload.  The result
is deliberately equation equivalence rather than syntactic equality: child
normalization is semantic, while the plan's original restoration theorem is
syntactic. -/
theorem CostStaticRegionPlan.normalizeValues_restoreMappedAbstract_equationEquiv
    {source : CIGSLT} {normalizeStatic : CostStaticRegionNormalizer source}
    (laws : CostStaticRegionNormalizerLaws source normalizeStatic)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {sourceBound targetBound : List TypeExpr}
    {thinning : CostStaticBinderThinning source color sourceBound targetBound}
    {sourceAvailable : List TypeExpr}
    {outer : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext}
    {payload : Pattern} {sourceType : TypeExpr}
    (plan : CostStaticRegionPlan source color targetFree sourceBound targetBound
      thinning sourceAvailable outer payload sourceType)
    (payloadObject : WellSorted.isObjectPattern payload = true)
    (trees : CostRegionBoundaryTrees source targetFree color
      plan.boundaryTable) :
    let mappedAbstract := thinning.thickenAmbientBVars 0
      (mapPattern (color.symbols source) plan.abstractPattern)
    ReflectiveEquationSemantics.ReflectiveEquationEquiv
      source.costWholeReflectionProfile defaultBasePremises
      source.costWholeLanguage
      ((trees.normalizeValues
        (normalizeStatic := normalizeStatic)).restoreSupportedSkeleton
          plan.boundaryTable sourceAvailable mappedAbstract)
      payload := by
  dsimp only
  obtain ⟨supported, _safe⟩ :=
    plan.abstractPattern_supportedSafe plan.boundaryTable (by
      intro boundary membership
      exact membership)
  have mapped := supported.mapCostStatic source color
  have transport := plan.boundaryTable.transport_of_fiberCoherent
    plan.boundaryTable_fiberCoherent
  rw [transport.freeContext] at mapped
  have thickened := mapped.thickenAmbientBVars (inner := []) thinning
  simp only [List.nil_append, List.length_nil] at thickened
  have valuesEquivalent :
      ((trees.normalizeValues (normalizeStatic := normalizeStatic)
        ).supportedOpenAssignment plan.boundaryTable).Equivalent
        ((TypedCostRegionBoundaryTable.Values.original plan.boundaryTable
          ).supportedOpenAssignment plan.boundaryTable) :=
    trees.normalizeValuesWithStatic_equivalent_original normalizeStatic laws
  have assignmentStep :=
    thickened.equationEquiv_substituteAt_pointwise
      ((trees.normalizeValues (normalizeStatic := normalizeStatic)
        ).supportedOpenAssignment plan.boundaryTable)
      ((TypedCostRegionBoundaryTable.Values.original plan.boundaryTable
        ).supportedOpenAssignment plan.boundaryTable)
      valuesEquivalent sourceAvailable.length
  have assignmentStep' :
      ReflectiveEquationSemantics.ReflectiveEquationEquiv
        source.costWholeReflectionProfile defaultBasePremises
        source.costWholeLanguage
        ((trees.normalizeValues (normalizeStatic := normalizeStatic)
          ).restoreSupportedSkeleton plan.boundaryTable sourceAvailable
            (thinning.thickenAmbientBVars 0
              (mapPattern (color.symbols source) plan.abstractPattern)))
        ((TypedCostRegionBoundaryTable.Values.original plan.boundaryTable
          ).restoreSupportedSkeleton plan.boundaryTable sourceAvailable
            (thinning.thickenAmbientBVars 0
              (mapPattern (color.symbols source) plan.abstractPattern))) := by
    simpa only [
      TypedCostRegionBoundaryTable.Values.supportedOpenAssignment,
      TypedCostRegionBoundaryTable.Values.supportedAssignment,
      TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton,
      ReflectiveContextSupport.substitute,
      WellSorted.SupportSafeOpenPattern.substitute_pattern] using assignmentStep
  have originalRestoration :
      (TypedCostRegionBoundaryTable.Values.original plan.boundaryTable
        ).restoreSupportedSkeleton plan.boundaryTable sourceAvailable
          (thinning.thickenAmbientBVars 0
            (mapPattern (color.symbols source) plan.abstractPattern)) = payload := by
    rw [TypedCostRegionBoundaryTable.Values.restoreSupportedSkeleton_original]
    exact (plan.restoreMappedAbstractPattern plan.boundaryTable
      (by intro boundary membership; exact membership) payloadObject).trans
        plan.recomposePattern_eq
  rw [originalRestoration] at assignmentStep'
  exact assignmentStep'

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
    {leftRoot : Pattern}
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
  have leftName :
      cospan.reifyNameWith left.lookupAtom? cospan.leftSlot
          (left.atomName leftSlot) =
        cospan.commonAtomName (cospan.leftSlot leftSlot) := by
    simp [CostStaticAtomKeyCospan.reifyNameWith,
      left.lookupAtom?_atomName]
  have rightName :
      cospan.reifyNameWith right.lookupAtom? cospan.rightSlot
          (right.atomName rightSlot) =
        cospan.commonAtomName (cospan.rightSlot rightSlot) := by
    simp [CostStaticAtomKeyCospan.reifyNameWith,
      right.lookupAtom?_atomName]
  change ReflectiveContextSupport.substituteAt
      source.costWholeReflectionProfile cospan.commonSupport
        cospan.commonAssignment depth
        (cospan.reifyWith left.lookupAtom? cospan.leftSlot
          (.fvar (left.atomName leftSlot))) =
    ReflectiveContextSupport.substituteAt source.costWholeReflectionProfile
      cospan.commonSupport cospan.commonAssignment depth
        (cospan.reifyWith right.lookupAtom? cospan.rightSlot
          (.fvar (right.atomName rightSlot)))
  rw [cospan.reifyWith_fvar, cospan.reifyWith_fvar, leftName, rightName,
    slotEq]

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
    {leftRoot : Pattern}
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

namespace CertifiedCostRegionBoundary

/-- Two independently certified boundaries in the same observed target fibre
inhabit the same complete semantic-atom fibre.

The contents and occurrence positions may differ.  Source-type and
source-support equality are nevertheless derived from the two executable
certification receipts, rather than inferred from equality of compact normal
forms.  This is the precise boundary needed before recursively aligned child
values may be identified in a parent semantic-key cospan. -/
theorem sameFiber_of_certifies_of_target_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftSupport rightSupport : List TypeExpr}
    {leftType rightType : TypeExpr}
    {leftContent rightContent : Pattern}
    (left : CertifiedCostRegionBoundary source color targetFree
      leftSupport leftType leftContent)
    (right : CertifiedCostRegionBoundary source color targetFree
      rightSupport rightType rightContent)
    (leftCertifies : certifyCostRegionBoundary? source color targetFree
      leftSupport leftType leftContent = some left)
    (rightCertifies : certifyCostRegionBoundary? source color targetFree
      rightSupport rightType rightContent = some right)
    (supportEq : leftSupport = rightSupport)
    (typeEq : leftType = rightType) :
    CostRegionBoundary.SameFiber left.typed.boundary
      right.typed.boundary := by
  have leftTypeMap := certifyCostRegionBoundary?_typeMap leftCertifies
  have rightTypeMap := certifyCostRegionBoundary?_typeMap rightCertifies
  have sourceTypeEq : left.typed.boundary.type =
      right.typed.boundary.type := by
    apply mapTypeExpr_costStatic_injective source color
    exact leftTypeMap.trans (typeEq.trans rightTypeMap.symm)
  have leftSourceSupport :=
    certifyCostRegionBoundary?_sourceSupport leftCertifies
  have rightSourceSupport :=
    certifyCostRegionBoundary?_sourceSupport rightCertifies
  have sourceSupportEq : left.typed.boundary.support =
      right.typed.boundary.support := by
    exact leftSourceSupport.trans
      ((congrArg
        (CostStaticBinderThinning.sourceContextOfTarget source color)
        supportEq).trans rightSourceSupport.symm)
  have targetTypeEq : left.typed.boundary.targetType =
      right.typed.boundary.targetType :=
    left.targetType_eq.trans (typeEq.trans right.targetType_eq.symm)
  have targetSupportEq : left.typed.boundary.targetSupport =
      right.typed.boundary.targetSupport :=
    left.targetSupport_eq.trans (supportEq.trans right.targetSupport_eq.symm)
  exact
    { type_eq := sourceTypeEq
      support_eq := sourceSupportEq
      targetType_eq := targetTypeEq
      targetSupport_eq := targetSupportEq }

end CertifiedCostRegionBoundary

namespace CostStaticPlanStopped

/-- The boundary that intercepts a context traversal remains an exact
positional free-variable occurrence in the root skeleton.  The occurrence is
reconstructed from the stored skeleton context, not by searching for an equal
boundary name; repeated equal boundary values therefore remain distinct at
the context-view layer. -/
def boundaryOccurrence
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (state : CostStaticPlanStopped source color targetFree payload
      rootAbstract) :
    CostStaticFVarOccurrence rootAbstract where
  name := costRegionBoundaryVariableName state.certified.typed.boundary
  context := state.skeletonContext
  selected :=
    Eq.mp
      (congrArg
        (fun root =>
          Mettapedia.OSLF.MeTTaIL.DerivedContexts.Selects
            (.fvar
              (costRegionBoundaryVariableName state.certified.typed.boundary))
            state.skeletonContext root)
        state.abstract_eq).symm
      (Mettapedia.OSLF.MeTTaIL.DerivedContexts.Selects.of_fill
        state.skeletonContext _)

/-- The positional occurrence carries the intercepted boundary's canonical
finite-table name exactly. -/
@[simp]
theorem boundaryOccurrence_name
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (state : CostStaticPlanStopped source color targetFree payload
      rootAbstract) :
    state.boundaryOccurrence.name =
      costRegionBoundaryVariableName state.certified.typed.boundary := by
  rfl

/-- A stopped view retains exactly one occurrence position. -/
def retainedIndex
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (state : CostStaticPlanStopped source color targetFree payload
      rootAbstract) :
    Fin (CostStaticPlanContextView.retainedEntries (.stopped state)).length :=
  ⟨0, by simp [CostStaticPlanContextView.retainedEntries]⟩

/-- Replaying the sole stopped-view position returns the certified boundary
that actually intercepted the traversal. -/
@[simp]
theorem retainedEntries_get_retainedIndex
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (state : CostStaticPlanStopped source color targetFree payload
      rootAbstract) :
    (CostStaticPlanContextView.retainedEntries (.stopped state)).get
        state.retainedIndex = state.certified.typed := by
  rfl

/-- Two stopped traversals whose observed target indices agree carry
boundaries in the same complete source/target fibre.

The source equalities are recovered from the retained executable
certification receipts.  They are not inferred from equality of contents or
compact normal forms, either of which would admit the known wrong-source-
type counterexample. -/
theorem sameFiber_of_target_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped source color targetFree rightPayload
      rightRootAbstract)
    (supportEq : left.boundarySupport = right.boundarySupport)
    (typeEq : left.boundaryType = right.boundaryType) :
    CostRegionBoundary.SameFiber left.certified.typed.boundary
      right.certified.typed.boundary :=
  CertifiedCostRegionBoundary.sameFiber_of_certifies_of_target_eq
    left.certified right.certified left.certifies right.certifies supportEq
      typeEq

/-- Recursively aligned children at two stopped traversals induce exactly the
same parent semantic atom once their target indices agree.  Boundary
contents and occurrence positions remain proof-relevant and may differ. -/
theorem alignedBoundaryAtom_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped source color targetFree rightPayload
      rightRootAbstract)
    (leftTree : CostRegionTree source targetFree
      left.certified.typed.boundary.targetSupport []
      left.certified.typed.boundary.content
      left.certified.typed.boundary.targetType)
    (rightTree : CostRegionTree source targetFree
      right.certified.typed.boundary.targetSupport []
      right.certified.typed.boundary.content
      right.certified.typed.boundary.targetType)
    (supportEq : left.boundarySupport = right.boundarySupport)
    (typeEq : left.boundaryType = right.boundaryType)
    (alignment : CostRegionTreeNormalizationAlignment source kernel
      targetFree leftTree rightTree) :
    TypedCostStaticAtom.ofBoundaryValue left.certified.typed
        (leftTree.normalizedBoundaryValue kernel) =
      TypedCostStaticAtom.ofBoundaryValue right.certified.typed
        (rightTree.normalizedBoundaryValue kernel) :=
  CostRegionTree.alignedBoundaryAtom_eq
    (left.sameFiber_of_target_eq right supportEq typeEq) alignment

end CostStaticPlanStopped

namespace CostStaticPlanContextInventoryView

/-- Restrict the root node's actual recursive child forest to precisely the
proof-relevant table retained by a context view.  This is a structural
projection, not a rebuild: every retained child is selected by the view's
original keep/skip path. -/
def restrictedForest
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {payload rootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      rootAbstract table.entries)
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    CostRegionBoundaryTrees source targetFree color view.view.retainedTable :=
  CostRegionBoundaryTrees.restrictAlongEntryEmbedding view.view.retainedTable
    table view.tableEmbedding trees

/-- Looking up a retained child in the restricted forest returns the exact
dependent child selected by replaying the same view position in the root
forest. -/
theorem restrictedForest_getEntry
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {payload rootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      rootAbstract table.entries)
    (trees : CostRegionBoundaryTrees source targetFree color table)
    (index : Fin view.view.retainedTable.entries.length) :
    (view.restrictedForest trees).getEntry index =
      trees.getEntry (view.tableEmbedding.position index) :=
  CostRegionBoundaryTrees.restrictAlongEntryEmbedding_getEntry
    view.view.retainedTable table view.tableEmbedding trees index

/-- A context view may restore any typed object skeleton from its retained
child forest without changing the result observed in the root forest.  This
is the exact semantic replay law for context descent: the view keeps its
original occurrence positions, while restoration observes only their stable
boundary names and hereditary normal values. -/
theorem restrictedForest_restoreSupportedSkeleton_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {payload rootAbstract : Pattern}
    (view : CostStaticPlanContextInventoryView source color targetFree payload
      rootAbstract table.entries)
    (trees : CostRegionBoundaryTrees source targetFree color table)
    {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    (typed : WellSorted.HasType source.costWholeLanguage
      view.view.retainedTable.mappedFreeContext bound pattern type)
    (object : WellSorted.isObjectPattern pattern = true) :
    ((view.restrictedForest trees).normalizeValues
        (normalizeStatic := kernel.normalize)).restoreSupportedSkeleton
          view.view.retainedTable bound pattern =
      (trees.normalizeValues
        (normalizeStatic := kernel.normalize)).restoreSupportedSkeleton
          table bound pattern :=
  CostRegionBoundaryTrees.normalizeValues_restoreSupportedSkeleton_restrict_eq
    unambiguous view.view.retainedTable table view.tableEmbedding trees typed
      object

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

/-- A stopped boundary aligned with a reached source-variable child is one
mixed leaf of the common restoration apex.

The stopped endpoint is selected by its proof-relevant table occurrence; the
source-variable endpoint is selected by its own skeleton occurrence.  Their
recursive tree alignment supplies the normalized value, and the established
support-independent restoration theorem supplies equality at every binder
depth.  No equality of endpoint boundary identities is assumed. -/
noncomputable def selectedBoundaryAtom_sourceVariable_commonRestorationApex
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
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
  apply PatternLeafAligned.leaf
  intro leafDepth
  exact view.selectedBoundaryAtom_restoresAsSourceVariable_of_alignment_supportIndependent
    unambiguous leftTrees leftEnvironment rightEnvironment index
      leftOccurrence leftNameEq rightOccurrence name rightNameEq leftSlot
      leftSelected rightSlot rightSelected rightTree children rightNormal
      leafDepth

/-- Right-oriented mixed restoration: a reached source-variable child and a
stopped boundary child restore identically in the common semantic namespace.

This is not obtained by silently reversing a canonical cospan.  The two
endpoint environments remain in their original order; the source-variable
normal and the exact replayed boundary normal are compared through the
proof-relevant child alignment. -/
theorem sourceVariable_restoresAsSelectedBoundary_of_alignment_supportIndependent
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {payload rightRootAbstract : Pattern}
    (rightView : CostStaticPlanContextInventoryView source color targetFree
      payload rightRootAbstract rightTable.entries)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {leftRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (name : String)
    (leftNameEq : leftOccurrence.name = costRegionSourceVariableName name)
    (rightIndex : Fin rightView.view.retainedEntries.length)
    (rightOccurrence : CostStaticFVarOccurrence rightRootAbstract)
    (rightNameEq : rightOccurrence.name = costRegionBoundaryVariableName
      (rightView.view.retainedEntries.get rightIndex).boundary)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName? leftOccurrence.name =
      some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName? rightOccurrence.name =
      some rightSlot)
    {leftAvailable leftOuter : List TypeExpr} {leftType : TypeExpr}
    (leftTree : CostRegionTree source targetFree leftAvailable leftOuter
      (.fvar name) leftType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      leftTree (rightView.selectedTreeFromForest rightTrees rightIndex))
    (leftNormal :
      (leftTree.normalize (normalizeStatic := kernel.normalize)).pattern =
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
  have leftAtomNormal : (leftEnvironment.atomValue leftSlot).key.normal =
      .fvar name := by
    rw [leftEnvironment.atomValue_normal_eq_of_slotOfName?_eq_some
      leftOccurrence leftSlot leftSelected, leftNameEq]
    exact leftValues.assignment_sourceVariable name
  have rightAtomNormal : (rightEnvironment.atomValue rightSlot).key.normal =
      ((rightView.selectedTreeFromForest rightTrees rightIndex
        ).normalizedBoundaryValue kernel).1 :=
    rightView.selectedBoundaryAtom_normal_eq unambiguous rightTrees
      rightEnvironment rightIndex rightOccurrence rightNameEq rightSlot
      rightSelected
  have childNormal : (.fvar name : Pattern) =
      ((rightView.selectedTreeFromForest rightTrees rightIndex
        ).normalizedBoundaryValue kernel).1 := by
    rw [← leftNormal]
    exact children.normalize_pattern_eq
  have normalEq : (leftEnvironment.atomValue leftSlot).key.normal =
      (rightEnvironment.atomValue rightSlot).key.normal :=
    leftAtomNormal.trans (childNormal.trans rightAtomNormal.symm)
  apply leftEnvironment.substituteAt_commonReifiedAtom_eq_of_scoped_normal
    rightEnvironment leftSlot rightSlot normalEq
  rw [leftAtomNormal]
  rfl

/-- A reached source-variable child aligned with a stopped boundary child is
the right-oriented mixed leaf of the common restoration apex. -/
noncomputable def sourceVariable_selectedBoundaryAtom_commonRestorationApex
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {payload rightRootAbstract : Pattern}
    (rightView : CostStaticPlanContextInventoryView source color targetFree
      payload rightRootAbstract rightTable.entries)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {leftRoot : Pattern}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRoot}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (leftOccurrence : CostStaticFVarOccurrence leftRoot)
    (name : String)
    (leftNameEq : leftOccurrence.name = costRegionSourceVariableName name)
    (rightIndex : Fin rightView.view.retainedEntries.length)
    (rightOccurrence : CostStaticFVarOccurrence rightRootAbstract)
    (rightNameEq : rightOccurrence.name = costRegionBoundaryVariableName
      (rightView.view.retainedEntries.get rightIndex).boundary)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName? leftOccurrence.name =
      some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName? rightOccurrence.name =
      some rightSlot)
    {leftAvailable leftOuter : List TypeExpr} {leftType : TypeExpr}
    (leftTree : CostRegionTree source targetFree leftAvailable leftOuter
      (.fvar name) leftType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      leftTree (rightView.selectedTreeFromForest rightTrees rightIndex))
    (leftNormal :
      (leftTree.normalize (normalizeStatic := kernel.normalize)).pattern =
        .fvar name)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
  apply PatternLeafAligned.leaf
  intro leafDepth
  exact rightView.sourceVariable_restoresAsSelectedBoundary_of_alignment_supportIndependent
    unambiguous rightTrees leftEnvironment rightEnvironment leftOccurrence
      name leftNameEq rightIndex rightOccurrence rightNameEq leftSlot
      leftSelected rightSlot rightSelected leftTree children leftNormal
      leafDepth

end CostStaticPlanContextInventoryView

namespace CostStaticPlanStopped

/-- Reifying the exact boundary occurrence selected by a stopped traversal
produces the semantic-atom name of the selected quotient slot.  The premise
retains the stopped occurrence; this is not a lookup by boundary value. -/
theorem environment_reify_boundaryOccurrence_eq_atomName
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanStopped source color targetFree payload
      rootAbstract)
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      table}
    {inventory : CostStaticParameterInventory source color targetFree table
      values rootAbstract}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot) :
    environment.reify (.fvar state.boundaryOccurrence.name) =
      .fvar (environment.atomName slot) := by
  have transportedName :=
    environment.reifyOccurrence_name_eq_atomName_of_slotOfName?_eq_some
      state.boundaryOccurrence slot selected
  simpa only [CostStaticAtomEnvironment.reify,
    CostStaticAtomEnvironment.reifyOccurrence_name] using
      congrArg Pattern.fvar transportedName

/-- Replay the sole boundary retained by a stopped traversal into the full
parent forest.  The keep/skip embedding, rather than equality search, selects
the original child occurrence; the resulting tree is reindexed only after the
complete typed boundary has been recovered at that exact position. -/
def selectedTreeFromForest
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (state : CostStaticPlanStopped source color targetFree payload
      rootAbstract)
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      [state.certified.typed] table.entries)
    (trees : CostRegionBoundaryTrees source targetFree color table) :
    CostRegionTree source targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content
      state.certified.typed.boundary.targetType := by
  let position := embedding.position state.retainedIndex
  have boundaryEq : (trees.getEntry position).boundary =
      state.certified.typed := by
    calc
      (trees.getEntry position).boundary = table.entries.get position :=
        trees.getEntry_boundary position
      _ = [state.certified.typed].get state.retainedIndex :=
        embedding.position_get state.retainedIndex
      _ = state.certified.typed := rfl
  exact (trees.getEntry position).tree.reindexBoundary boundaryEq

/-- The parent semantic environment sees a stopped traversal through exactly
the hereditary normal value of the occurrence selected by its replayable
embedding.  Static-decomposition unambiguity is used only to reconcile
duplicate boundary names inside the finite resolver; it never chooses the
occurrence. -/
theorem environmentAtom_eq_selectedTree
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanStopped source color targetFree payload
      rootAbstract)
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    (embedding : CostStaticPlanEntryEmbedding source color targetFree
      [state.certified.typed] table.entries)
    (trees : CostRegionBoundaryTrees source targetFree color table)
    {inventory : CostStaticParameterInventory source color targetFree table
      (trees.normalizeValues (normalizeStatic := kernel.normalize))
      rootAbstract}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot) :
    environment.atomValue slot =
      TypedCostStaticAtom.ofBoundaryValue state.certified.typed
        ((state.selectedTreeFromForest embedding trees).normalizedBoundaryValue
          kernel) := by
  let position := embedding.position state.retainedIndex
  have boundaryEq : (trees.getEntry position).boundary =
      state.certified.typed := by
    calc
      (trees.getEntry position).boundary = table.entries.get position :=
        trees.getEntry_boundary position
      _ = [state.certified.typed].get state.retainedIndex :=
        embedding.position_get state.retainedIndex
      _ = state.certified.typed := rfl
  have atomEq :=
    environment.atomValue_eq_normalizedBoundaryValue_of_reindexedGetEntry
      unambiguous trees position state.certified.typed boundaryEq
      state.boundaryOccurrence rfl slot selected
  simpa only [selectedTreeFromForest] using atomEq

/-- Two independently stopped traversals select equal parent semantic atoms
when their retained certifier receipts establish one fibre and their exact
recursive children align.  Parent tables and occurrence positions may differ;
neither is quotiented before the proof-relevant children have been selected. -/
theorem selectedEnvironmentAtom_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (supportEq : left.boundarySupport = right.boundarySupport)
    (typeEq : left.boundaryType = right.boundaryType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (left.selectedTreeFromForest leftEmbedding leftTrees)
      (right.selectedTreeFromForest rightEmbedding rightTrees)) :
    leftEnvironment.atomValue leftSlot =
      rightEnvironment.atomValue rightSlot := by
  have leftAtom := left.environmentAtom_eq_selectedTree unambiguous
    leftEmbedding leftTrees leftEnvironment leftSlot leftSelected
  have rightAtom := right.environmentAtom_eq_selectedTree unambiguous
    rightEmbedding rightTrees rightEnvironment rightSlot rightSelected
  have childAtom := left.alignedBoundaryAtom_eq right
    (left.selectedTreeFromForest leftEmbedding leftTrees)
    (right.selectedTreeFromForest rightEmbedding rightTrees) supportEq typeEq
      children
  exact leftAtom.trans (childAtom.trans rightAtom.symm)

/-- Exact stopped/stopped atom equality induces equal restoration of their
canonical atom names at every binder depth in the common semantic-key cospan.
Occurrence identity has served its selection role; only the proved complete
semantic key is erased at this final valuation-independent joint. -/
theorem selectedEnvironmentAtoms_restore_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (supportEq : left.boundarySupport = right.boundarySupport)
    (typeEq : left.boundaryType = right.boundaryType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (left.selectedTreeFromForest leftEmbedding leftTrees)
      (right.selectedTreeFromForest rightEmbedding rightTrees))
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
  have atomEq := left.selectedEnvironmentAtom_eq unambiguous right
    leftEmbedding rightEmbedding leftTrees rightTrees leftEnvironment
      rightEnvironment leftSlot leftSelected rightSlot rightSelected supportEq
      typeEq children
  exact leftEnvironment.substituteAt_commonReifiedAtom_eq_of_key_eq
    rightEnvironment leftSlot rightSlot
      (congrArg TypedCostStaticAtom.key atomEq) depth

/-- Two stopped traversals whose exact recursive children align form one
proof-relevant leaf of the common restoration apex.

The endpoint occurrences remain selected by their independent keep/skip
embeddings.  Only after the retained certification receipts establish the
complete common fibre and hereditary alignment establishes the normalized
value do the two endpoint spellings enter the common semantic namespace. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (supportEq : left.boundarySupport = right.boundarySupport)
    (typeEq : left.boundaryType = right.boundaryType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (left.selectedTreeFromForest leftEmbedding leftTrees)
      (right.selectedTreeFromForest rightEmbedding rightTrees))
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (.fvar (leftEnvironment.atomName leftSlot)))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (.fvar (rightEnvironment.atomName rightSlot))) := by
  apply CostStaticAtomKeyCospan.CommonRestorationApex.leafAligned
  apply PatternLeafAligned.leaf
  intro leafDepth
  exact left.selectedEnvironmentAtoms_restore_eq unambiguous right
    leftEmbedding rightEmbedding leftTrees rightTrees leftEnvironment
      rightEnvironment leftSlot leftSelected rightSlot rightSelected supportEq
      typeEq children leafDepth

/-- Lift a stopped/stopped semantic occurrence through independently retained
context spines.

The context alignment retains restoration evidence for every fixed sibling
and exposes one common hole depth.  The exact stopped occurrences and their
certification receipts still select the two semantic atoms; the context layer
may transport those atoms but cannot replace or manufacture them. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_through_contexts
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (supportEq : left.boundarySupport = right.boundarySupport)
    (typeEq : left.boundaryType = right.boundaryType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (left.selectedTreeFromForest leftEmbedding leftTrees)
      (right.selectedTreeFromForest rightEmbedding rightTrees))
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := source) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
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
  let leaf := left.selectedEnvironmentAtoms_commonRestorationApex
    unambiguous right leftEmbedding rightEmbedding leftTrees rightTrees
      leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
      rightSelected supportEq typeEq children declaration holeDepth
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

/-- Lift a stopped/stopped occurrence alignment to the complete atomized
plan roots.  The two stored `abstract_eq` witnesses are the only endpoint
casts: exact occurrence selection, semantic-atom reification, common-cospan
transport, and context filling have already been performed constructively
below them. -/
noncomputable def selectedRoots_commonRestorationApex
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (supportEq : left.boundarySupport = right.boundarySupport)
    (typeEq : left.boundaryType = right.boundaryType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (left.selectedTreeFromForest leftEmbedding leftTrees)
      (right.selectedTreeFromForest rightEmbedding rightTrees))
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := source) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let filled := left.selectedEnvironmentAtoms_commonRestorationApex_through_contexts
    unambiguous right leftEmbedding rightEmbedding leftTrees rightTrees
      leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
      rightSelected supportEq typeEq children declaration depth holeDepth
      contexts
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

/-- Lift the stopped/stopped semantic leaf through an exact shared retained
skeleton context.

This constructor is intentionally conditional on equality of the two
contexts.  It handles the maximal common spine directly; genuinely different
left and right spines remain obligations for the structural pair recursion
rather than being identified by a context cast. -/
noncomputable def selectedEnvironmentAtoms_commonRestorationApex_through_sameContext
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    (leftEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [left.certified.typed] leftTable.entries)
    (rightEmbedding : CostStaticPlanEntryEmbedding source color targetFree
      [right.certified.typed] rightTable.entries)
    (leftTrees : CostRegionBoundaryTrees source targetFree color leftTable)
    (rightTrees : CostRegionBoundaryTrees source targetFree color rightTable)
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable
      (leftTrees.normalizeValues (normalizeStatic := kernel.normalize))
      leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable
      (rightTrees.normalizeValues (normalizeStatic := kernel.normalize))
      rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (supportEq : left.boundarySupport = right.boundarySupport)
    (typeEq : left.boundaryType = right.boundaryType)
    (children : CostRegionTreeNormalizationAlignment source kernel targetFree
      (left.selectedTreeFromForest leftEmbedding leftTrees)
      (right.selectedTreeFromForest rightEmbedding rightTrees))
    (contextEq : left.skeletonContext = right.skeletonContext)
    (declaration : ReflectivePresentationDecl) (depth : Nat) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (left.skeletonContext.fill
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot))))
      (right.skeletonContext.fill
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot)))) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let leaf := left.selectedEnvironmentAtoms_commonRestorationApex
    unambiguous right leftEmbedding rightEmbedding leftTrees rightTrees
      leftEnvironment rightEnvironment leftSlot leftSelected rightSlot
      rightSelected supportEq typeEq children declaration
      (CostStaticAtomKeyCospan.restorationDepthThroughContext source depth
        left.skeletonContext)
  let lifted := CostStaticAtomKeyCospan.CommonRestorationApex.throughContext
    cospan declaration left.skeletonContext depth leaf
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex rfl
    (congrArg
      (fun context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext =>
        context.fill
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (.fvar (rightEnvironment.atomName rightSlot))))
      contextEq) lifted

/-- Lift a selected stopped occurrence on the left and an already closed
reached sub-plan on the right through their independently retained contexts.
The inner apex is the only semantic premise; this constructor performs only
occurrence reification, context composition, and the stored endpoint casts. -/
noncomputable def selectedRoot_reachedRoot_commonRestorationApex
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanStopped source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanReached source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (leftSlot : Fin leftEnvironment.atomCount)
    (leftSelected : leftEnvironment.slotOfName?
      left.boundaryOccurrence.name = some leftSlot)
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (inner :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
        holeDepth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (.fvar (leftEnvironment.atomName leftSlot)))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify right.plan.abstractPattern)))
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := source) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let filled := contexts.fill inner
  have leftFilled := cospan.reifyEnvironmentContext_fill leftEnvironment
    cospan.leftSlot left.skeletonContext
      (.fvar left.boundaryOccurrence.name)
  have rightFilled := cospan.reifyEnvironmentContext_fill rightEnvironment
    cospan.rightSlot right.skeletonContext right.plan.abstractPattern
  have leftHole := left.environment_reify_boundaryOccurrence_eq_atomName
    leftEnvironment leftSlot leftSelected
  rw [leftHole] at leftFilled
  have leftRootEq :
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify
            (left.skeletonContext.fill
              (.fvar left.boundaryOccurrence.name))) =
        cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify leftRootAbstract) :=
    congrArg (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot)
      (congrArg leftEnvironment.reify (by
        simpa only [left.boundaryOccurrence_name] using left.abstract_eq.symm))
  have rightRootEq :
      cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify
            (right.skeletonContext.fill right.plan.abstractPattern)) =
        cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify rightRootAbstract) :=
    congrArg (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot)
      (congrArg rightEnvironment.reify right.abstract_eq.symm)
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (leftFilled.trans leftRootEq) (rightFilled.trans rightRootEq) filled

/-- Right-oriented companion of
`selectedRoot_reachedRoot_commonRestorationApex`: a reached sub-plan on the
left and an exact stopped occurrence on the right are lifted without reversing
or quotienting the endpoint environments. -/
noncomputable def reachedRoot_selectedRoot_commonRestorationApex
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanReached source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanStopped source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (rightSlot : Fin rightEnvironment.atomCount)
    (rightSelected : rightEnvironment.slotOfName?
      right.boundaryOccurrence.name = some rightSlot)
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (inner :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
        holeDepth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify left.plan.abstractPattern))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (.fvar (rightEnvironment.atomName rightSlot))))
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := source) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let filled := contexts.fill inner
  have leftFilled := cospan.reifyEnvironmentContext_fill leftEnvironment
    cospan.leftSlot left.skeletonContext left.plan.abstractPattern
  have rightFilled := cospan.reifyEnvironmentContext_fill rightEnvironment
    cospan.rightSlot right.skeletonContext
      (.fvar right.boundaryOccurrence.name)
  have rightHole := right.environment_reify_boundaryOccurrence_eq_atomName
    rightEnvironment rightSlot rightSelected
  rw [rightHole] at rightFilled
  have leftRootEq :
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify
            (left.skeletonContext.fill left.plan.abstractPattern)) =
        cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify leftRootAbstract) :=
    congrArg (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot)
      (congrArg leftEnvironment.reify left.abstract_eq.symm)
  have rightRootEq :
      cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify
            (right.skeletonContext.fill
              (.fvar right.boundaryOccurrence.name))) =
        cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify rightRootAbstract) :=
    congrArg (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot)
      (congrArg rightEnvironment.reify (by
        simpa only [right.boundaryOccurrence_name] using
          right.abstract_eq.symm))
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (leftFilled.trans leftRootEq) (rightFilled.trans rightRootEq) filled

end CostStaticPlanStopped

namespace CostStaticPlanReached

/-- Build the recursive Cost tree carried by an admitted reached payload in
its exact visible availability fibre.  The reached plan's sealed suffix and
one-hole path belong to the enclosing static context; neither is recast as
part of the payload tree. -/
noncomputable def payloadTreeOfWellSorted
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached source color targetFree payload
      rootAbstract)
    (wellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      reached.sourceAvailable
      (mapTypeExpr (color.symbols source) reached.sourceType) payload) :
    CostRegionTree source targetFree reached.sourceAvailable [] payload
      (mapTypeExpr (color.symbols source) reached.sourceType) :=
  (CostRegionTree.build? (source := source) (targetFree := targetFree)
    reached.sourceAvailable [] payload
      (mapTypeExpr (color.symbols source) reached.sourceType)).get
    (CostRegionTree.build?_isSome_of_wellSorted wellSorted)

/-- Structural unambiguity identifies the normal form of the executable
reached-payload tree with every proof-relevant decomposition of the same
typed payload fibre. -/
theorem payloadTreeOfWellSorted_normalize_eq
    {source : CIGSLT} {kernel : CostStaticNormalizationKernel source}
    (unambiguous : CostStaticRegionNode.UnambiguousStaticDecomposition source)
    {color : CostStaticColor}
    {targetFree : FreeTypeContext} {payload rootAbstract : Pattern}
    (reached : CostStaticPlanReached source color targetFree payload
      rootAbstract)
    (wellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      source.costWholeReflectionProfile source.costWholeLanguage targetFree
      reached.sourceAvailable
      (mapTypeExpr (color.symbols source) reached.sourceType) payload)
    (object : WellSorted.isObjectPattern payload = true)
    (tree : CostRegionTree source targetFree reached.sourceAvailable [] payload
      (mapTypeExpr (color.symbols source) reached.sourceType)) :
    ((reached.payloadTreeOfWellSorted wellSorted).normalize
      (normalizeStatic := kernel.normalize)).pattern =
      (tree.normalize (normalizeStatic := kernel.normalize)).pattern := by
  exact CostRegionTree.normalize_pattern_eq_of_unambiguous unambiguous kernel
    (reached.payloadTreeOfWellSorted wellSorted) tree object

/-- Reifying a reached plan after source-to-target mapping and binder
reinsertion preserves its exact one-hole factorization.  This is a structural
naturality law only: it identifies the retained target spine and payload, but
does not assert that either endpoint admits a restoration apex. -/
theorem environmentReify_mappedThickenedRootAbstract_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached source color targetFree payload
      rootAbstract)
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      table}
    {inventory : CostStaticParameterInventory source color targetFree table
      values rootAbstract}
    (environment : CostStaticAtomEnvironment source color targetFree
      inventory)
    (depth : Nat) :
    environment.reify
        (state.thinning.thickenAmbientBVars depth
          (mapPattern (color.symbols source) rootAbstract)) =
      (environment.reifyContext
          (state.mappedThickenedSkeletonContextAt depth)).fill
        (environment.reify
          (state.thinning.thickenAmbientBVars
            (state.mappedThickenedHoleDepthAt depth)
            (mapPattern (color.symbols source)
              state.plan.abstractPattern))) := by
  let context := state.mappedThickenedSkeletonContextAt depth
  let inner := state.thinning.thickenAmbientBVars
    (state.mappedThickenedHoleDepthAt depth)
    (mapPattern (color.symbols source) state.plan.abstractPattern)
  calc
    environment.reify
          (state.thinning.thickenAmbientBVars depth
            (mapPattern (color.symbols source) rootAbstract)) =
        environment.reify (context.fill inner) :=
      congrArg environment.reify
        (state.mappedThickenedRootAbstract_eq depth)
    _ = (environment.reifyContext context).fill
          (environment.reify inner) :=
      (environment.reifyContext_fill context inner).symm

/-- Moving a reached plan through an endpoint environment and then through a
chosen common semantic-key leg preserves the same mapped/thickened plan
factorization.  The theorem retains the actual endpoint resolver and cospan
leg; in particular, it does not manufacture a paired context or a
`CommonRestorationApex`. -/
theorem commonReify_mappedThickenedRootAbstract_eq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {payload rootAbstract : Pattern}
    (state : CostStaticPlanReached source color targetFree payload
      rootAbstract)
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      table}
    {inventory : CostStaticParameterInventory source color targetFree table
      values rootAbstract}
    (environment : CostStaticAtomEnvironment source color targetFree
      inventory)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount -> CostStaticAtomKey}
    {rightKey : Fin rightCount -> CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leg : Fin environment.atomCount -> Fin cospan.commonKeys.length)
    (depth : Nat) :
    cospan.reifyWith environment.lookupAtom? leg
        (environment.reify
          (state.thinning.thickenAmbientBVars depth
            (mapPattern (color.symbols source) rootAbstract))) =
      (cospan.reifyEnvironmentContext environment leg
          (state.mappedThickenedSkeletonContextAt depth)).fill
        (cospan.reifyWith environment.lookupAtom? leg
          (environment.reify
            (state.thinning.thickenAmbientBVars
              (state.mappedThickenedHoleDepthAt depth)
              (mapPattern (color.symbols source)
                state.plan.abstractPattern)))) := by
  let context := state.mappedThickenedSkeletonContextAt depth
  let inner := state.thinning.thickenAmbientBVars
    (state.mappedThickenedHoleDepthAt depth)
    (mapPattern (color.symbols source) state.plan.abstractPattern)
  calc
    cospan.reifyWith environment.lookupAtom? leg
          (environment.reify
            (state.thinning.thickenAmbientBVars depth
              (mapPattern (color.symbols source) rootAbstract))) =
        cospan.reifyWith environment.lookupAtom? leg
          (environment.reify (context.fill inner)) :=
      congrArg (cospan.reifyWith environment.lookupAtom? leg)
        (congrArg environment.reify
          (state.mappedThickenedRootAbstract_eq depth))
    _ = (cospan.reifyEnvironmentContext environment leg context).fill
          (cospan.reifyWith environment.lookupAtom? leg
            (environment.reify inner)) :=
      (cospan.reifyEnvironmentContext_fill environment leg context inner).symm

/-- Lift a reached/reached apex through the exact source-to-target map,
binder reinsertion, endpoint atom environments, and retained plan contexts.

Unlike `selectedRoots_commonRestorationApex`, this form keeps the mapped and
thickened parent indices visible.  It is therefore suitable for a recursive
caller whose child certificate is stated at the reached target plans rather
than at their untransported source abstracts. -/
noncomputable def mappedThickenedRoots_commonRestorationApex
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanReached source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanReached source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (inner :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
        holeDepth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify
            (left.thinning.thickenAmbientBVars
              (left.mappedThickenedHoleDepthAt depth)
              (mapPattern (color.symbols source)
                left.plan.abstractPattern))))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify
            (right.thinning.thickenAmbientBVars
              (right.mappedThickenedHoleDepthAt depth)
              (mapPattern (color.symbols source)
                right.plan.abstractPattern)))))
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := source) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          (left.mappedThickenedSkeletonContextAt depth))
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          (right.mappedThickenedSkeletonContextAt depth))) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify
          (left.thinning.thickenAmbientBVars depth
            (mapPattern (color.symbols source) leftRootAbstract))))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify
          (right.thinning.thickenAmbientBVars depth
            (mapPattern (color.symbols source) rightRootAbstract)))) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let filled := contexts.fill inner
  have leftFactor := left.commonReify_mappedThickenedRootAbstract_eq
    leftEnvironment cospan cospan.leftSlot depth
  have rightFactor := right.commonReify_mappedThickenedRootAbstract_eq
    rightEnvironment cospan cospan.rightSlot depth
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    leftFactor.symm rightFactor.symm filled

/-- Lift an already established reached/reached child apex through the two
independently retained plan contexts to the complete atomized plan roots.

This is the reached counterpart of stopped-occurrence root lifting.  It adds
no child equality: the supplied inner apex remains the sole semantic evidence,
while the paired context witness accounts for every fixed sibling and the two
stored plan factorizations account for the endpoint casts. -/
noncomputable def selectedRoots_commonRestorationApex
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanReached source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanReached source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (declaration : ReflectivePresentationDecl) (depth holeDepth : Nat)
    (inner :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
        holeDepth
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify left.plan.abstractPattern))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify right.plan.abstractPattern)))
    (contexts :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      CostStaticAtomKeyCospan.CommonRestorationApex.Context
        (source := source) cospan declaration depth holeDepth
        (cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext)
        (cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext)) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let filled := contexts.fill inner
  have leftFilled := cospan.reifyEnvironmentContext_fill leftEnvironment
    cospan.leftSlot left.skeletonContext left.plan.abstractPattern
  have rightFilled := cospan.reifyEnvironmentContext_fill rightEnvironment
    cospan.rightSlot right.skeletonContext right.plan.abstractPattern
  have leftRootEq :
      cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify
            (left.skeletonContext.fill left.plan.abstractPattern)) =
        cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify leftRootAbstract) :=
    congrArg (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot)
      (congrArg leftEnvironment.reify left.abstract_eq.symm)
  have rightRootEq :
      cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify
            (right.skeletonContext.fill right.plan.abstractPattern)) =
        cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify rightRootAbstract) :=
    congrArg (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot)
      (congrArg rightEnvironment.reify right.abstract_eq.symm)
  exact CostStaticAtomKeyCospan.CommonRestorationApex.reindex
    (leftFilled.trans leftRootEq) (rightFilled.trans rightRootEq) filled

/-- Specialize reached/reached root lifting to two contexts that become
literally equal after endpoint atom reification into the common namespace.

The equality is intentionally stated after reification: equal raw contexts
may contain fixed boundary variables whose endpoint spellings differ, while
the common semantic namespace is precisely where such fixed siblings may be
compared.  The computed hole depth records every binder increment and quote
reset on the retained context spine. -/
noncomputable def selectedRoots_commonRestorationApex_of_reifiedContextEq
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {leftPayload leftRootAbstract rightPayload rightRootAbstract : Pattern}
    (left : CostStaticPlanReached source color targetFree leftPayload
      leftRootAbstract)
    (right : CostStaticPlanReached source color targetFree rightPayload
      rightRootAbstract)
    {leftOccurrences rightOccurrences : List CostRegionOccurrence}
    {leftTable : TypedCostRegionBoundaryTable source color targetFree
      leftOccurrences}
    {rightTable : TypedCostRegionBoundaryTable source color targetFree
      rightOccurrences}
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftTable leftValues leftRootAbstract}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightTable rightValues rightRootAbstract}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (declaration : ReflectivePresentationDecl) (depth : Nat)
    (inner :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      let leftContext := cospan.reifyEnvironmentContext leftEnvironment
        cospan.leftSlot left.skeletonContext
      CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
        (CostStaticAtomKeyCospan.restorationDepthThroughContext source depth
          leftContext)
        (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
          (leftEnvironment.reify left.plan.abstractPattern))
        (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
          (rightEnvironment.reify right.plan.abstractPattern)))
    (contextEq :
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      cospan.reifyEnvironmentContext leftEnvironment cospan.leftSlot
          left.skeletonContext =
        cospan.reifyEnvironmentContext rightEnvironment cospan.rightSlot
          right.skeletonContext) :
    let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
    CostStaticAtomKeyCospan.CommonRestorationApex source cospan declaration
      depth
      (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
        (leftEnvironment.reify leftRootAbstract))
      (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
        (rightEnvironment.reify rightRootAbstract)) := by
  let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
  let leftContext := cospan.reifyEnvironmentContext leftEnvironment
    cospan.leftSlot left.skeletonContext
  let rightContext := cospan.reifyEnvironmentContext rightEnvironment
    cospan.rightSlot right.skeletonContext
  have contexts : CostStaticAtomKeyCospan.CommonRestorationApex.Context
      (source := source) cospan declaration depth
        (CostStaticAtomKeyCospan.restorationDepthThroughContext source depth
          leftContext)
        leftContext rightContext := by
    change leftContext = rightContext at contextEq
    exact Eq.ndrec
      (motive := fun context =>
        CostStaticAtomKeyCospan.CommonRestorationApex.Context
          (source := source) cospan declaration depth
            (CostStaticAtomKeyCospan.restorationDepthThroughContext source
              depth leftContext)
            leftContext context)
      (CostStaticAtomKeyCospan.CommonRestorationApex.Context.refl
        cospan declaration depth leftContext)
      contextEq
  exact left.selectedRoots_commonRestorationApex right leftEnvironment
    rightEnvironment declaration depth
      (CostStaticAtomKeyCospan.restorationDepthThroughContext source depth
        leftContext)
      inner contexts

end CostStaticPlanReached

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
