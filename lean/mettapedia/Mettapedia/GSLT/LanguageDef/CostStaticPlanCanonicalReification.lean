import Mettapedia.GSLT.LanguageDef.CostCanonicalStopReifiedCongruence
import Mettapedia.GSLT.LanguageDef.CostStaticPlanCanonicalAlignment

/-!
# Canonical static-plan alignment after semantic-atom reification

The source plan is the structural authority for a static region, while the
source frame used by hereditary normalization has already replaced its finite
boundary parameters by semantic atoms.  This file connects those two views.

Every collapsing stop retains the exact pair of reached source plans and their
root-table embeddings.  Exact authored free variables form the second stop
case, because independently constructed endpoint environments may assign them
different semantic-atom names.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open WellSorted

/-- A reified source-frame stop with its plan-side provenance intact.

The `plan` constructor is the image of one collapsing stop produced by the
paired static plans.  The `sourceFVar` constructor records the rigid free-
variable arm which becomes non-rigid only because the two endpoint
environments may choose different atom names. -/
inductive CostStaticPlanCanonicalReifiedStop
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    (rawStop : Pattern → Pattern → Prop) : Pattern → Pattern → Prop where
  | plan {left right : Pattern}
      (stop : CostStaticPlanCanonicalStop leftNode.plan rightNode.plan
        declaration rawDeclaration rawStop
        left right) :
      CostStaticPlanCanonicalReifiedStop leftNode rightNode leftEnvironment
        rightEnvironment declaration rawDeclaration rawStop
        (leftEnvironment.reify left) (rightEnvironment.reify right)
  | sourceFVar (name : String) :
      CostStaticPlanCanonicalReifiedStop leftNode rightNode leftEnvironment
        rightEnvironment declaration rawDeclaration rawStop
        (.fvar (leftEnvironment.reifyName name))
        (.fvar (rightEnvironment.reifyName name))

namespace CostStaticRegionNode

/-- Transport a raw endpoint alignment to the two authored source skeletons,
retaining exact reached-plan provenance at every reflective stop. -/
noncomputable def sourceCanonicalStopAligned_of_rawAlignment
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : leftNode.sourceSort = rightNode.sourceSort)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop leftNode.term.1
      rightNode.term.1) :
    CanonicalStopAligned declaration
      (CostStaticPlanCanonicalStop leftNode.plan rightNode.plan declaration
        rawDeclaration rawStop)
      leftNode.skeleton.1 rightNode.skeleton.1 := by
  cases leftNode with
  | mk leftTargetBound leftSourceSort leftTerm leftPlan leftRootStatic
      leftSkeleton leftSkeletonPattern leftSupported leftSupportSafe =>
    cases rightNode with
    | mk rightTargetBound rightSourceSort rightTerm rightPlan rightRootStatic
        rightSkeleton rightSkeletonPattern rightSupported rightSupportSafe =>
      cases sameBound
      cases sameSort
      have planAligned :=
        leftPlan.canonicalStopAligned_of_rawAlignment collectionDeterministic
          declaration rawDeclaration rightPlan rfl rawAligned
      simpa only [leftSkeletonPattern, rightSkeletonPattern] using planAligned

/-- Canonically equal same-fibre static nodes induce a stopped structural
alignment of their atom-reified authored frames.

The only transports are equality of the target binder fibre and equality of
the authored result sort.  No equality of semantic environments, concrete
collection choices, reached plans, or boundary occurrences is required. -/
noncomputable def reifiedSourceCanonicalStopAligned_of_rawAlignment
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : leftNode.sourceSort = rightNode.sourceSort)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop leftNode.term.1
      rightNode.term.1) :
    CanonicalStopAligned declaration
      (CostStaticPlanCanonicalReifiedStop leftNode rightNode leftEnvironment
        rightEnvironment declaration rawDeclaration rawStop)
      (leftNode.reifiedSourceFrame leftEnvironment).1
      (rightNode.reifiedSourceFrame rightEnvironment).1 := by
  have planAligned := leftNode.sourceCanonicalStopAligned_of_rawAlignment
    collectionDeterministic declaration rawDeclaration rightNode sameBound
      sameSort rawAligned
  have reified := CanonicalStopAligned.environmentReify leftEnvironment
    rightEnvironment
    (fun stop => CostStaticPlanCanonicalReifiedStop.plan
      (declaration := declaration) stop)
    (fun name => CostStaticPlanCanonicalReifiedStop.sourceFVar
      (declaration := declaration) name)
    planAligned
  simpa only [reifiedSourceFrame_pattern] using reified

/-- Same-declaration specialization built from ordinary canonical equality. -/
noncomputable def reifiedSourceCanonicalStopAligned_of_canonicalize_eq
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration : ReflectivePresentationDecl)
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : leftNode.sourceSort = rightNode.sourceSort)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl source color declaration)
          leftNode.term.1 =
        canonicalize
          (costStaticReflectivePresentationDecl source color declaration)
          rightNode.term.1) :
    CanonicalStopAligned declaration
      (CostStaticPlanCanonicalReifiedStop leftNode rightNode leftEnvironment
        rightEnvironment declaration
        (costStaticReflectivePresentationDecl source color declaration)
        (fun candidateLeft candidateRight =>
          (CollapsingRoot
              (costStaticReflectivePresentationDecl source color declaration)
              candidateLeft ∨
            CollapsingRoot
              (costStaticReflectivePresentationDecl source color declaration)
              candidateRight) ∧
          canonicalize
              (costStaticReflectivePresentationDecl source color declaration)
              candidateLeft =
            canonicalize
              (costStaticReflectivePresentationDecl source color declaration)
              candidateRight))
      (leftNode.reifiedSourceFrame leftEnvironment).1
      (rightNode.reifiedSourceFrame rightEnvironment).1 :=
  leftNode.reifiedSourceCanonicalStopAligned_of_rawAlignment
    collectionDeterministic declaration
    (costStaticReflectivePresentationDecl source color declaration) rightNode
    leftEnvironment rightEnvironment sameBound sameSort
    (canonicalStopAligned_of_canonicalize_eq
      (costStaticReflectivePresentationDecl source color declaration)
      canonical)

/-- Factor canonical source-frame alignment through the exact plan stops.

This is the reusable composition boundary for a language-specific provider:
the generic layer performs plan descent, semantic-atom reification, and keyed
canonical congruence.  The caller supplies only the semantic meaning of an
exact source variable and of one provenance-bearing stopped pair. -/
noncomputable def reifiedSourceCanonicalAlignment_of_rawAlignment
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : leftNode.sourceSort = rightNode.sourceSort)
    {rawStop : Pattern → Pattern → Prop}
    (rawAligned : CanonicalStopAligned rawDeclaration rawStop leftNode.term.1
      rightNode.term.1)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat)
    {relation : Pattern → Pattern → Prop}
    (callback : ∀ callbackAvailable callbackScope {left right},
      CostStaticPlanCanonicalReifiedStop leftNode rightNode leftEnvironment
          rightEnvironment declaration rawDeclaration rawStop left right →
        PatternLeafAligned relation
          (canonicalizeByDepths leftKey declaration callbackAvailable
            callbackScope left)
          (canonicalizeByDepths rightKey declaration callbackAvailable
            callbackScope right)) :
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
        (leftNode.reifiedSourceFrame leftEnvironment).1)
      (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
        (rightNode.reifiedSourceFrame rightEnvironment).1) := by
  let planAligned := leftNode.sourceCanonicalStopAligned_of_rawAlignment
    collectionDeterministic declaration rawDeclaration rightNode sameBound
      sameSort rawAligned
  simpa only [reifiedSourceFrame_pattern] using
    (CanonicalStopAligned.environmentReifyCanonicalizeByDepths
      leftEnvironment rightEnvironment leftKey rightKey declaration
      (fun callbackAvailable callbackScope {_ _} stop =>
        callback callbackAvailable callbackScope
          (CostStaticPlanCanonicalReifiedStop.plan stop))
      (fun callbackAvailable callbackScope name =>
        callback callbackAvailable callbackScope
          (CostStaticPlanCanonicalReifiedStop.sourceFVar name))
      planAligned availableDepth scopeDepth)

/-- Same-declaration specialization of the complete keyed composition. -/
noncomputable def reifiedSourceCanonicalAlignment_of_canonicalize_eq
    {source : CIGSLT} {color : CostStaticColor}
    (collectionDeterministic : CollectionChoiceDeterministic
      source.theory.presentation.presentation.language)
    (declaration : ReflectivePresentationDecl)
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (sameBound : leftNode.targetBound = rightNode.targetBound)
    (sameSort : leftNode.sourceSort = rightNode.sourceSort)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl source color declaration)
          leftNode.term.1 =
        canonicalize
          (costStaticReflectivePresentationDecl source color declaration)
          rightNode.term.1)
    {Key : Type} [LinearOrder Key]
    (leftKey rightKey : Nat → Nat → Pattern → Key)
    (availableDepth scopeDepth : Nat)
    {relation : Pattern → Pattern → Prop}
    (callback : ∀ callbackAvailable callbackScope {left right},
      CostStaticPlanCanonicalReifiedStop leftNode rightNode leftEnvironment
          rightEnvironment declaration
          (costStaticReflectivePresentationDecl source color declaration)
          (fun candidateLeft candidateRight =>
            (CollapsingRoot
                (costStaticReflectivePresentationDecl source color declaration)
                candidateLeft ∨
              CollapsingRoot
                (costStaticReflectivePresentationDecl source color declaration)
                candidateRight) ∧
            canonicalize
                (costStaticReflectivePresentationDecl source color declaration)
                candidateLeft =
              canonicalize
                (costStaticReflectivePresentationDecl source color declaration)
                candidateRight)
          left right →
        PatternLeafAligned relation
          (canonicalizeByDepths leftKey declaration callbackAvailable
            callbackScope left)
          (canonicalizeByDepths rightKey declaration callbackAvailable
            callbackScope right)) :
    PatternLeafAligned relation
      (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
        (leftNode.reifiedSourceFrame leftEnvironment).1)
      (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
        (rightNode.reifiedSourceFrame rightEnvironment).1) :=
  leftNode.reifiedSourceCanonicalAlignment_of_rawAlignment
    collectionDeterministic declaration
    (costStaticReflectivePresentationDecl source color declaration) rightNode
    leftEnvironment rightEnvironment sameBound sameSort
    (canonicalStopAligned_of_canonicalize_eq
      (costStaticReflectivePresentationDecl source color declaration)
      canonical)
    leftKey rightKey availableDepth scopeDepth callback

end CostStaticRegionNode

/-! ## Canary properties -/

/-- A reified authored source variable is always represented explicitly; it
cannot be confused with an exact-spelling rigid free-variable arm. -/
example
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : FreeTypeContext}
    (leftNode rightNode : CostStaticRegionNode source color targetFree)
    {leftValues : TypedCostRegionBoundaryTable.Values source color targetFree
      leftNode.boundaryTable}
    {rightValues : TypedCostRegionBoundaryTable.Values source color targetFree
      rightNode.boundaryTable}
    {leftInventory : CostStaticParameterInventory source color targetFree
      leftNode.boundaryTable leftValues leftNode.skeleton.1}
    {rightInventory : CostStaticParameterInventory source color targetFree
      rightNode.boundaryTable rightValues rightNode.skeleton.1}
    (leftEnvironment : CostStaticAtomEnvironment source color targetFree
      leftInventory)
    (rightEnvironment : CostStaticAtomEnvironment source color targetFree
      rightInventory)
    (declaration rawDeclaration : ReflectivePresentationDecl)
    (rawStop : Pattern → Pattern → Prop) (name : String) :
    CostStaticPlanCanonicalReifiedStop leftNode rightNode leftEnvironment
      rightEnvironment declaration rawDeclaration rawStop
      (.fvar (leftEnvironment.reifyName name))
      (.fvar (rightEnvironment.reifyName name)) :=
  .sourceFVar name

/-- The source-variable constructor cannot itself manufacture a bound
variable endpoint.  Bound-variable cases in the full relation can therefore
only come from a genuine plan stop. -/
theorem costStaticPlanCanonicalReifiedStop_sourceFVar_ne_bvar
    (leftName rightName : String) (index : Nat) :
    (Pattern.fvar leftName, Pattern.fvar rightName) ≠
      (.bvar index, .bvar index) := by
  intro equality
  exact Pattern.noConfusion (congrArg Prod.fst equality)

end Mettapedia.GSLT.LanguageDef
