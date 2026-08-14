import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticDeepAtomExposure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex

/-!
# Deep atom-shell cases for the rho semantic-cut provider

These constructors lift arbitrary finite Quote/Drop and singleton-parallel
shell exposure to the proof-relevant semantic-cut interface.  They preserve
the exact stopped occurrence and invoke the well-founded child callback only
on its certified boundary payload.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace RhoCanonicalStaticPairSemanticCut

/-- Left-oriented semantic cut for a stopped boundary under an arbitrary
finite atom-preserving collapsing shell. -/
noncomputable def leftStoppedAtomShellOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : RhoCanonicalAtomShell state.skeletonContext)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          rightPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.leftCollapsing color leftView collapsing) :=
  .leftEnclosing leftView collapsing
    (RhoCollapsingLeafExposure.stoppedAtomShellOfCloseSmaller left right
      leftView rightWellSorted state entryEmbedding shell boundaryCanonical
      boundarySupport boundaryType closeSmaller)

/-- Right-oriented deep-shell cut.  Only the final child pair is reversed;
the stopped occurrence remains the exact right endpoint occurrence. -/
noncomputable def rightStoppedAtomShellOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (rightView : right.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      rightView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] rightView.node.finiteBoundaryTable.entries)
    (shell : RhoCanonicalAtomShell state.skeletonContext)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          leftPattern)
    (boundarySupport :
      state.certified.typed.boundary.targetSupport = available)
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.rightCollapsing color rightView collapsing) :=
  .rightEnclosing rightView collapsing
    (RhoCollapsingLeafExposure.stoppedAtomShellOfCloseSmaller right left
      rightView leftWellSorted state entryEmbedding shell boundaryCanonical
      boundarySupport boundaryType
      (fun {childAvailable childOuter childLeft childRight childType}
          leftChildWellSorted rightChildWellSorted canonical smaller
          admissible => by
        let paired := Classical.choice
          (closeSmaller (childAvailable := childAvailable)
            (childOuter := childOuter) (leftChild := childRight)
            (rightChild := childLeft) (childType := childType)
            rightChildWellSorted leftChildWellSorted canonical.symm
            (by simpa [Nat.add_comm] using smaller) admissible)
        exact ⟨paired.symm⟩))

/-- Left-oriented quote-reset cut whose terminal structural endpoint is a
source variable.  Unlike the same-support adapter, the stopped boundary may
be sealed at a different availability from the caller. -/
noncomputable def leftStoppedAtomShellSourceVariableOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern : Pattern} {type : TypeExpr} {name : String}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type)
    (leftView : left.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type (.fvar name))
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      leftView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] leftView.node.finiteBoundaryTable.entries)
    (shell : RhoCanonicalAtomShell state.skeletonContext)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          (.fvar name))
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf leftPattern + sizeOf (Pattern.fvar name) →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.leftCollapsing color leftView collapsing) :=
  .leftEnclosing leftView collapsing
    (RhoCollapsingLeafExposure.stoppedAtomShellSourceVariableOfCloseSmaller
      left right leftView rightWellSorted state entryEmbedding shell
      boundaryCanonical boundaryType closeSmaller)

/-- Right-oriented quote-reset source-variable cut. -/
noncomputable def rightStoppedAtomShellSourceVariableOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : FreeTypeContext}
    {available outer : List TypeExpr}
    {rightPattern : Pattern} {type : TypeExpr} {name : String}
    (left : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (rightView : right.StaticRootView color)
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rightPattern)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type (.fvar name))
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      rightView.node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] rightView.node.finiteBoundaryTable.entries)
    (shell : RhoCanonicalAtomShell state.skeletonContext)
    (boundaryCanonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          state.certified.typed.boundary.content =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation)
          (.fvar name))
    (boundaryType : state.certified.typed.boundary.targetType = type)
    (closeSmaller :
      ∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType leftChild →
        ReflectiveWellSorted.OpenPatternWellSorted
            rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
            targetFree childAvailable childType rightChild →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            leftChild =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
              rhoReflectivePresentation)
            rightChild →
        sizeOf leftChild + sizeOf rightChild <
          sizeOf (Pattern.fvar name) + sizeOf rightPattern →
        rhoCanonicalRecursiveTypeDomain.Admissible childType →
        Nonempty (CostCanonicalPairElaboration rhoCIGSLT
          rhoHereditaryNormalizationKernel targetFree childAvailable
          childOuter leftChild rightChild childType)) :
    RhoCanonicalStaticPairSemanticCut declarationColor left right
      (.rightCollapsing color rightView collapsing) :=
  .rightEnclosing rightView collapsing
    (RhoCollapsingLeafExposure.stoppedAtomShellSourceVariableOfCloseSmaller
      right left rightView leftWellSorted state entryEmbedding shell
      boundaryCanonical boundaryType
      (fun {childAvailable childOuter childLeft childRight childType}
          rightChildWellSorted leftChildWellSorted canonical smaller
          admissible => by
        let paired := Classical.choice
          (closeSmaller (childAvailable := childAvailable)
            (childOuter := childOuter) (leftChild := childRight)
            (rightChild := childLeft) (childType := childType)
            leftChildWellSorted rightChildWellSorted canonical.symm
            (by simpa [Nat.add_comm] using smaller) admissible)
        exact ⟨paired.symm⟩))

end RhoCanonicalStaticPairSemanticCut

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
