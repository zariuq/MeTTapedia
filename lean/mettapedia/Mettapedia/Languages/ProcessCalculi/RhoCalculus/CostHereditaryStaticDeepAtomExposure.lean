import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure

/-!
# Deep collapsing-atom exposure for hereditary rho Cost

The static closure layer already eliminates an exposed semantic atom at any
depth.  This module generalizes the syntactic shell certificate from one
Quote/Drop or one singleton parallel to an arbitrary finite nesting of those
two collapsing forms.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A one-hole context built only from rho's two atom-preserving collapsing
shells.  The hole marks the terminal semantic occurrence. -/
inductive RhoCanonicalAtomShell : OneHoleContext → Prop where
  | hole : RhoCanonicalAtomShell .hole
  | quoteDrop {context : OneHoleContext}
      (inner : RhoCanonicalAtomShell context) :
      RhoCanonicalAtomShell
        (.apply rhoReflectivePresentation.quoteConstructor []
          (.apply rhoReflectivePresentation.dropConstructor [] context []) [])
  | parallelSingleton {context : OneHoleContext}
      (inner : RhoCanonicalAtomShell context) :
      RhoCanonicalAtomShell
        (.collection rhoReflectivePresentation.parallelCollection
          [] context [] none)

namespace RhoCanonicalAtomShell

/-- Every nested atom shell collapses to its terminal free variable under
rho's keyed two-depth canonicalizer. -/
theorem canonicalizeByDepths_fill_fvar
    {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key) (name : String) :
    ∀ {context : OneHoleContext}, RhoCanonicalAtomShell context →
      ∀ availableDepth scopeDepth,
        canonicalizeByDepths key rhoReflectivePresentation availableDepth
            scopeDepth (context.fill (.fvar name)) =
          .fvar name := by
  intro context shell
  induction shell with
  | hole =>
      intro availableDepth scopeDepth
      rfl
  | quoteDrop inner inductionHypothesis =>
      intro availableDepth scopeDepth
      simp only [OneHoleContext.fill]
      simp [canonicalizeByDepths, canonicalizeListByDepths,
        finishNormalizeReflectiveApply, inductionHypothesis]
  | parallelSingleton inner inductionHypothesis =>
      intro availableDepth scopeDepth
      simp only [OneHoleContext.fill]
      simp [canonicalizeByDepths, canonicalizeListByDepths,
        normalizeParallelElementsBy, parallelSplice, collapseParallel,
        Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy,
        inductionHypothesis]

/-- Semantic-atom reification changes no constructor in an atom shell. -/
theorem reifyContext_eq_self
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {occurrences : List CostRegionOccurrence}
    {table : TypedCostRegionBoundaryTable source color targetFree occurrences}
    {values : TypedCostRegionBoundaryTable.Values source color targetFree table}
    {root : Pattern}
    {inventory : CostStaticParameterInventory source color targetFree table
      values root}
    (environment : CostStaticAtomEnvironment source color targetFree inventory) :
    ∀ {context : OneHoleContext}, RhoCanonicalAtomShell context →
      environment.reifyContext context = context := by
  intro context shell
  induction shell with
  | hole => rfl
  | quoteDrop inner inductionHypothesis =>
      simp [CostStaticAtomEnvironment.reifyContext, inductionHypothesis]
  | parallelSingleton inner inductionHypothesis =>
      simp [CostStaticAtomEnvironment.reifyContext, inductionHypothesis]

end RhoCanonicalAtomShell

/-- A reified finite nesting of rho collapsing shells canonicalizes to its
selected semantic atom. -/
theorem CostStaticRegionNode.canonicalizeReifiedTargetFrame_atomShell
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    (slot : Fin environment.atomCount)
    {context : OneHoleContext}
    (shell : RhoCanonicalAtomShell context)
    (reifiedFrame : (node.reifiedSourceFrame environment).1 =
      context.fill (.fvar (environment.atomName slot))) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      .fvar (environment.atomName slot) := by
  rw [CostStaticRegionNode.canonicalizeReifiedTargetFrame_eq_map_sourceCanonicalize
    node environment, reifiedFrame]
  rw [RhoCanonicalAtomShell.canonicalizeByDepths_fill_fvar _ _ shell]
  simp [mapPattern, CostStaticBinderThinning.thickenAmbientBVars]

/-- An exact stopped occurrence beneath an arbitrary atom shell determines
the complete canonical-frame equation for its semantic slot. -/
theorem CostStaticRegionNode.stopped_atomShell_canonicalFrame
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    {values : TypedCostRegionBoundaryTable.Values rhoCIGSLT color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory rhoCIGSLT color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment rhoCIGSLT color targetFree
      inventory)
    {payload : Pattern}
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (shell : RhoCanonicalAtomShell state.skeletonContext)
    (slot : Fin environment.atomCount)
    (selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot) :
    node.canonicalizeReifiedTargetFrame environment
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation) =
      .fvar (environment.atomName slot) := by
  have reifiedFrame : (node.reifiedSourceFrame environment).1 =
      state.skeletonContext.fill (.fvar (environment.atomName slot)) := by
    rw [node.reifiedSourceFrame_pattern]
    calc
      environment.reify node.skeleton.1 =
          environment.reify
            (state.skeletonContext.fill
              (.fvar (costRegionBoundaryVariableName
                state.certified.typed.boundary))) :=
        congrArg environment.reify state.abstract_eq
      _ = (environment.reifyContext state.skeletonContext).fill
          (environment.reify
            (.fvar (costRegionBoundaryVariableName
              state.certified.typed.boundary))) :=
        (environment.reifyContext_fill state.skeletonContext _).symm
      _ = state.skeletonContext.fill
          (.fvar (environment.atomName slot)) := by
        rw [RhoCanonicalAtomShell.reifyContext_eq_self environment shell]
        simp only [CostStaticAtomEnvironment.reify]
        change state.skeletonContext.fill
            (.fvar (environment.reifyName state.boundaryOccurrence.name)) = _
        unfold CostStaticAtomEnvironment.reifyName
        rw [selected]
  exact CostStaticRegionNode.canonicalizeReifiedTargetFrame_atomShell
    node environment slot shell reifiedFrame

namespace RhoCollapsingLeafExposure

/-- Close a stopped boundary beneath any finite nesting of rho atom shells.

The new shell certificate supplies only the canonical-frame equation.  Child
normalization, endpoint comparison, and same-support restoration are delegated
unchanged to the existing occurrence-indexed boundary terminal. -/
noncomputable def stoppedAtomShellBoundaryElaborationAlignedSameSupport
    {color : CostStaticColor} {targetFree : WellSorted.FreeTypeContext}
    {payload : Pattern}
    {alignedAvailable alignedOuter rightAvailable rightOuter : List TypeExpr}
    (node : CostStaticRegionNode rhoCIGSLT color targetFree)
    (children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable)
    (state : CostStaticPlanStopped rhoCIGSLT color targetFree payload
      node.skeleton.1)
    (entryEmbedding : CostStaticPlanEntryEmbedding rhoCIGSLT color targetFree
      [state.certified.typed] node.finiteBoundaryTable.entries)
    (shell : RhoCanonicalAtomShell state.skeletonContext)
    {alignedPattern rightPattern : Pattern}
    {alignedType rightType : TypeExpr}
    (leftElaboration : CostRegionTree rhoCIGSLT targetFree
      state.certified.typed.boundary.targetSupport []
      state.certified.typed.boundary.content
      state.certified.typed.boundary.targetType)
    (alignedRight : CostRegionTree rhoCIGSLT targetFree alignedAvailable
      alignedOuter alignedPattern alignedType)
    (right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType)
    (childAlignment : CostRegionTreeNormalizationAlignment rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree leftElaboration alignedRight)
    (alignedToRight :
      (alignedRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern)
    (sameSupport : state.certified.typed.boundary.targetSupport.length =
      node.targetBound.length) :
    RhoCollapsingLeafExposure node children right := by
  let environment := node.normalizationEnvironment
    rhoHereditaryStaticNormalizer children
  have slotExists := environment.slotOfName?_isSome_of_occurrence
    state.boundaryOccurrence
  let slot := (environment.slotOfName? state.boundaryOccurrence.name).get
    slotExists
  have selected : environment.slotOfName? state.boundaryOccurrence.name =
      some slot := (Option.some_get slotExists).symm
  have staticFrame :
      node.canonicalizeReifiedTargetFrame environment
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation) =
        .fvar (environment.atomName slot) :=
    CostStaticRegionNode.stopped_atomShell_canonicalFrame node environment
      state shell slot selected
  exact stoppedBoundaryElaborationAlignedSameSupport node children state
    entryEmbedding leftElaboration alignedRight right
    (fun candidate candidateSelected => by
      have candidateEq : candidate = slot :=
        Option.some.inj (candidateSelected.symm.trans selected)
      subst candidate
      exact staticFrame)
    childAlignment alignedToRight sameSupport

/-- Recursive provider closure at a stopped boundary beneath an arbitrary
finite atom shell.  The recursive call is made only for the certified
boundary content, whose size is strictly below the static root. -/
noncomputable def stoppedAtomShellOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
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
    RhoCollapsingLeafExposure leftView.node leftView.children right := by
  have boundaryWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType
      state.certified.typed.boundary.content :=
    ⟨⟨state.certified.typed.contentTyped,
        state.certified.typed.contentCanonicalBinderMetadata,
        state.certified.typed.contentObjectPattern,
        state.certified.typed.contentTyped.isWellScopedAt⟩,
      state.certified.typed.contentReflectiveScopeSafe⟩
  have boundaryRightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType rightPattern := by
    simpa only [boundarySupport, boundaryType] using rightWellSorted
  have boundaryMember : state.certified.typed ∈
      leftView.node.plan.boundaryTable.entries :=
    entryEmbedding.subset (by simp)
  have boundarySmaller :
      sizeOf state.certified.typed.boundary.content + sizeOf rightPattern <
        sizeOf leftPattern + sizeOf rightPattern := by
    have contentLt :=
      leftView.node.plan.boundary_content_size_lt_of_isStaticRoot
        leftView.node.rootStatic state.certified.typed boundaryMember
    have nodePatternEq : leftView.node.term.1 = leftPattern :=
      leftView.patternEq
    have contentLt' :
        sizeOf state.certified.typed.boundary.content < sizeOf leftPattern := by
      calc
        sizeOf state.certified.typed.boundary.content <
            sizeOf leftView.node.term.1 := contentLt
        _ = sizeOf leftPattern := congrArg sizeOf nodePatternEq
    omega
  have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      state.certified.typed.boundary.targetType := by
    exact (leftView.typeEq.trans boundaryType.symm) ▸
      rhoCanonicalRecursiveTypeDomain.base _
  let childPair := Classical.choice
    (closeSmaller (childOuter := []) boundaryWellSorted
      boundaryRightWellSorted boundaryCanonical boundarySmaller
        childAdmissible)
  let ambientRight : CostRegionTree rhoCIGSLT targetFree available outer
      rightPattern type :=
    ((childPair.rightTree.extendOuter outer).reindexAvailable boundarySupport
      ).reindexType boundaryType
  have childToAmbient :
      (childPair.rightTree.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
    have typeReindex := CostRegionTree.reindexType_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundaryType
      ((childPair.rightTree.extendOuter outer).reindexAvailable
        boundarySupport)
    have supportReindex := CostRegionTree.reindexAvailable_normalize
      (normalizeStatic := rhoHereditaryStaticNormalizer) boundarySupport
      (childPair.rightTree.extendOuter outer)
    have weakened := childPair.rightTree.extendOuter_normalize_pattern outer
      rhoHereditaryStaticNormalizer
    exact (typeReindex.trans (supportReindex.trans weakened)).symm
  have ambientToRight :
      (ambientRight.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern :=
    CostRegionTree.normalize_pattern_eq_of_unambiguous
      CostCanonicalLaws.rho_unambiguousStaticDecomposition
      rhoHereditaryNormalizationKernel ambientRight right
      rightWellSorted.1.2.2.1
  exact stoppedAtomShellBoundaryElaborationAlignedSameSupport
    leftView.node leftView.children state entryEmbedding shell
      childPair.leftTree childPair.rightTree right childPair.alignment
      (childToAmbient.trans ambientToRight)
      (congrArg List.length (boundarySupport.trans leftView.availableEq.symm))

/-- Support-independent recursive closure when a deep atom shell exposes a
source variable.

The structural free variable can be typed at the certified boundary support
without identifying that support with the caller's ambient context.  This is
the quote-reset branch: only the result type is shared, while the exact
stopped occurrence continues to select the semantic atom. -/
noncomputable def stoppedAtomShellSourceVariableOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern : Pattern} {type : TypeExpr} {name : String}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer (.fvar name)
      type)
    (leftView : left.StaticRootView color)
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
    RhoCollapsingLeafExposure leftView.node leftView.children right := by
  have boundaryWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType
      state.certified.typed.boundary.content :=
    ⟨⟨state.certified.typed.contentTyped,
        state.certified.typed.contentCanonicalBinderMetadata,
        state.certified.typed.contentObjectPattern,
        state.certified.typed.contentTyped.isWellScopedAt⟩,
      state.certified.typed.contentReflectiveScopeSafe⟩
  have nameLookup : targetFree name = some type := by
    cases rightWellSorted.1.1 with
    | fvar lookup => exact lookup
  have boundaryRightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree state.certified.typed.boundary.targetSupport
      state.certified.typed.boundary.targetType (Pattern.fvar name) := by
    refine ⟨⟨WellSorted.HasType.fvar ?_, rfl, rfl, rfl⟩, ?_⟩
    · simpa only [boundaryType] using nameLookup
    · intro declaration _declarationMembership
      rfl
  have boundaryMember : state.certified.typed ∈
      leftView.node.plan.boundaryTable.entries :=
    entryEmbedding.subset (by simp)
  have boundarySmaller :
      sizeOf state.certified.typed.boundary.content +
          sizeOf (Pattern.fvar name) <
        sizeOf leftPattern + sizeOf (Pattern.fvar name) := by
    have contentLt :=
      leftView.node.plan.boundary_content_size_lt_of_isStaticRoot
        leftView.node.rootStatic state.certified.typed boundaryMember
    have nodePatternEq : leftView.node.term.1 = leftPattern :=
      leftView.patternEq
    have contentLt' :
        sizeOf state.certified.typed.boundary.content < sizeOf leftPattern := by
      calc
        sizeOf state.certified.typed.boundary.content <
            sizeOf leftView.node.term.1 := contentLt
        _ = sizeOf leftPattern := congrArg sizeOf nodePatternEq
    omega
  have childAdmissible : rhoCanonicalRecursiveTypeDomain.Admissible
      state.certified.typed.boundary.targetType := by
    exact (leftView.typeEq.trans boundaryType.symm) ▸
      rhoCanonicalRecursiveTypeDomain.base _
  let childPair := Classical.choice
    (closeSmaller (childOuter := []) boundaryWellSorted
      boundaryRightWellSorted boundaryCanonical boundarySmaller
        childAdmissible)
  exact stoppedBoundaryElaborationSourceVariable leftView.node
    leftView.children state entryEmbedding name childPair.leftTree
      childPair.rightTree right
      (fun slot selected =>
        CostStaticRegionNode.stopped_atomShell_canonicalFrame leftView.node
          (leftView.node.normalizationEnvironment
            rhoHereditaryStaticNormalizer leftView.children)
          state shell slot selected)
      childPair.alignment

/-- Pair-elaboration projection of the occurrence-retaining deep-shell
provider. -/
noncomputable def stoppedAtomShellPairElaborationOfCloseSmaller
    {declarationColor color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    (left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type)
    (right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type)
    (leftView : left.StaticRootView color)
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
    CostCanonicalPairElaboration rhoCIGSLT
      rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type := by
  let exposure := stoppedAtomShellOfCloseSmaller left right leftView
    rightWellSorted state entryEmbedding shell boundaryCanonical
      boundarySupport boundaryType closeSmaller
  exact
    { leftTree := left
      rightTree := right
      alignment :=
        (leftView.rootBridge_reindex_left
          exposure.toRootBridge).toTreeAlignment }

end RhoCollapsingLeafExposure

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
