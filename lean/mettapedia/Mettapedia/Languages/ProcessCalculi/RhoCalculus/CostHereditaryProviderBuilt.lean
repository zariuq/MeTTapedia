import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderObligations
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryObjectReduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCanonicalOccurrencePathSupport
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesRestorationApex
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCrossColorFlat
import Mettapedia.GSLT.LanguageDef.CostRestorationFvarPairLeaf

/-!
# The provider over built trees

`RhoCanonicalStaticPairSemanticCutsInDomain.of_provider` consumes the cut
provider at exactly one kind of tree: the outputs of `CostRegionTree.build?`
on the two well-sorted patterns.  The general provider interface nonetheless
quantifies over arbitrary trees, and that generality is not free — over
arbitrary trees the boundary *values* are constrained only by their types,
while over built trees every environment component is computed from the
pattern and its typing context.

This module states the provider at its point of use.  The `Built` interface
carries the two origin facts; `of_provider_built` shows it suffices for the
whole downstream chain, because at the only invocation site the origin facts
hold by definition.  The general provider trivially specializes.

Obligations discharged against the `Built` interface may therefore use the
functional origin of both trees — in particular, that equal boundary
contents yield equal normalized values, which is false for arbitrary value
vectors.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **Two preimages of one declared constructor share a source label.**

The preimage's `labelMap` pins the coloured spelling of its source label to
the materialized declared constructor, which both sides share; the colouring's
constructor renaming is injective
(`CostStaticColor.symbols_constructor_injective`), so the source labels agree.

This is what makes the two endpoints' source frames share a head: root
alignment gives one wire name, `application_dispatch_of_isStaticRoot` plus
`Option.some.inj` gives one declared constructor, and this gives one label. -/
theorem CostStaticConstructorPreimage.sourceLabel_eq {source : CIGSLT}
    {color : CostStaticColor} {constructor : source.DeclaredCostConstructor}
    (first second : CostStaticConstructorPreimage source color constructor) :
    first.sourceConstructor.1.label = second.sourceConstructor.1.label :=
  CostStaticColor.symbols_constructor_injective source color
    (first.labelMap.symm.trans second.labelMap)

/-- **The canonicalized source frame keeps an application head.**

Chains the structural facts: the reified source frame is `reify skeleton`
(`reifiedSourceFrame_pattern`, definitional), the skeleton is the plan's
abstract pattern (the node's own field), that abstract is an application when
the term is (`abstractPattern_apply`), `reify` is structural on applications,
and keyed canonicalization preserves a non-quote head
(`canonicalizeByDepths_apply_of_ne_quote`).

The skeleton equation is applied through `congrArg environment.reify` rather
than `rw`: the inventory is indexed by `node.skeleton.1`, so rewriting that
term directly makes the motive ill-typed, while `reify`'s own type does not
depend on its argument. -/
theorem CostStaticRegionNode.sourceFrame_apply
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {values : TypedCostRegionBoundaryTable.Values source color targetFree
      node.boundaryTable}
    {inventory : CostStaticParameterInventory source color targetFree
      node.boundaryTable values node.skeleton.1}
    (environment : CostStaticAtomEnvironment source color targetFree inventory)
    {Key : Type} [LinearOrder Key] (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl)
    {label : String} {abstracts : List Pattern}
    (abstractEq : node.plan.abstractPattern = .apply label abstracts)
    (notQuote : label ≠ declaration.quoteConstructor) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths key
        declaration node.targetBound.length 0
        (node.reifiedSourceFrame environment).1 =
      .apply label
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByDepths key
          declaration node.targetBound.length 0
          (abstracts.map environment.reify)) := by
  have skeletonEq : node.skeleton.1 = .apply label abstracts :=
    node.skeleton_pattern.trans abstractEq
  rw [node.reifiedSourceFrame_pattern, congrArg environment.reify skeletonEq]
  simp only [CostStaticAtomEnvironment.reify]
  exact Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByDepths_apply_of_ne_quote
    key declaration node.targetBound.length 0 label
    (abstracts.map environment.reify) notQuote

/-- **A static node whose term is an application abstracts to an
application.**

The plan is indexed by both the pattern and the source sort, so a direct
`cases` fails dependent elimination while those indices are projections
(`node.term.1`, `node.sourceSort.1`).  Destructuring the node, its term and
its sort turns them into variables, after which `subst` applies and the
elimination goes through: every non-application plan is killed by the pattern
index, and `boundaryApplication` — which is application-shaped but abstracts
to a bare boundary variable — is killed by `isStaticRoot`.

This is the structural step of source-frame alignment: it exposes the shared
head that `canonicalizeByDepths_apply_of_ne_quote` then preserves. -/
theorem CostStaticRegionNode.abstractPattern_apply
    {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (node : CostStaticRegionNode source color targetFree)
    {wireName : String} {arguments : List Pattern}
    (shape : node.term.1 = .apply wireName arguments) :
    ∃ label abstracts, node.plan.abstractPattern = .apply label abstracts := by
  obtain ⟨targetBound, sourceSort, term, plan, rootStatic, skeleton,
    skeletonPattern, supported, supportSafe⟩ := node
  obtain ⟨termPattern, termTyped⟩ := term
  obtain ⟨sortName, sortMember⟩ := sourceSort
  simp only at shape
  subst shape
  cases plan <;>
    first
      | exact ⟨_, _, rfl⟩
      | simp [CostStaticRegionPlan.isStaticRoot] at rootStatic

/-- **A static root view observes a static root.**

The three reindexings are matches on equality proofs, so they block reduction
until substituted; afterwards the tree is literally `.static node children`
and the boolean is `rfl`.

With `CostRegionTree.pattern_shape_of_rootIsStatic` this excludes every
non-static root shape: a viewed pattern is an application or a collection,
never a bound or free variable, a binder, or a substitution.  That is what
discharges the unreachable arms of a root-alignment case split. -/
theorem CostRegionTree.StaticRootView.rootIsStatic
    {source : CIGSLT} {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {tree : CostRegionTree source targetFree available outer pattern type}
    {color : CostStaticColor}
    (view : tree.StaticRootView color) : tree.rootIsStatic = true := by
  obtain ⟨node, children, patternEq, availableEq, typeEq, treeEq⟩ := view
  subst patternEq
  subst availableEq
  subst typeEq
  subst treeEq
  rfl

end Mettapedia.GSLT.LanguageDef

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- The semantic-cut provider stated at its sole point of use: both trees
are the `build?` outputs of the two patterns.  Everything else matches
`RhoCanonicalStaticPair.HasSemanticCut`. -/
def RhoCanonicalStaticPair.HasBuiltSemanticCut
    (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr},
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type leftPattern) →
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type rightPattern) →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern →
    (CostStaticRootShape rhoCIGSLT leftPattern type ∨
      CostStaticRootShape rhoCIGSLT rightPattern type) →
    (∀ {childAvailable childOuter : List TypeExpr}
      {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree childAvailable childType leftChild →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree childAvailable childType rightChild →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftChild =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightChild →
      sizeOf leftChild + sizeOf rightChild <
        sizeOf leftPattern + sizeOf rightPattern →
      rhoCanonicalRecursiveTypeDomain.Admissible childType →
      Nonempty (CostCanonicalPairElaboration rhoCIGSLT
        rhoHereditaryNormalizationKernel targetFree childAvailable childOuter
        leftChild rightChild childType)) →
    ∀ (rootCase : RhoCanonicalStaticPairBridgeCase declarationColor
        ((CostRegionTree.build? (source := rhoCIGSLT)
            (targetFree := targetFree) available outer leftPattern type).get
          (CostRegionTree.build?_isSome_of_wellSorted leftWellSorted))
        ((CostRegionTree.build? (source := rhoCIGSLT)
            (targetFree := targetFree) available outer rightPattern type).get
          (CostRegionTree.build?_isSome_of_wellSorted rightWellSorted))),
      Nonempty (RhoCanonicalStaticPairSemanticCut declarationColor _ _
        rootCase)

/-- The general provider specializes to the built interface. -/
theorem RhoCanonicalStaticPair.HasSemanticCut.toBuilt
    {declarationColor : CostStaticColor}
    (provider :
      RhoCanonicalStaticPair.HasSemanticCut declarationColor) :
    RhoCanonicalStaticPair.HasBuiltSemanticCut declarationColor :=
  fun admissible leftWellSorted rightWellSorted canonical staticShape
      closeSmaller rootCase =>
    provider admissible leftWellSorted rightWellSorted canonical staticShape
      closeSmaller _ _ rootCase

/-- **The built provider suffices for the downstream chain.**  At the sole
invocation site both trees are the `build?` outputs, so the origin facts the
built interface carries hold definitionally. -/
theorem RhoCanonicalStaticPairSemanticCutsInDomain.of_provider_built
    {declarationColor : CostStaticColor}
    (provider :
      RhoCanonicalStaticPair.HasBuiltSemanticCut
        declarationColor) :
    RhoCanonicalStaticPairSemanticCutsInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical staticShape closeSmaller
  obtain ⟨rootCase⟩ := nonempty_rhoCanonicalStaticPairBridgeCase
    declarationColor
    ((CostRegionTree.build? (source := rhoCIGSLT)
        (targetFree := targetFree) available outer leftPattern type).get
      (CostRegionTree.build?_isSome_of_wellSorted leftWellSorted))
    ((CostRegionTree.build? (source := rhoCIGSLT)
        (targetFree := targetFree) available outer rightPattern type).get
      (CostRegionTree.build?_isSome_of_wellSorted rightWellSorted))
    canonical staticShape
  obtain ⟨cut⟩ := provider admissible leftWellSorted rightWellSorted canonical
    staticShape closeSmaller rootCase
  exact ⟨⟨_, _, rootCase, cut⟩⟩

/-- **The seal from the built provider alone.**

The route check for the built interface: generator-tree alignability comes
from the per-colour static closure, whose step is the built provider through
`of_provider_built`; reflective-support preservation is already a closed
term.  So the whole remaining content of the rho cost layer domain object is the
built provider. -/
noncomputable def rhoHereditaryCostLayer_ofBuiltProvider
    (built : ∀ color,
      RhoCanonicalStaticPair.HasBuiltSemanticCut color) :
    Cost.Layer :=
  rhoHereditaryCostLayer_of
    (rhoCostOpenGeneratorTreeAlignable_of_staticClosures (fun color =>
      CostCanonicalStaticPair.IsClosedIn.of_step
        (by exact List.mem_cons_self)
        (RhoCanonicalStaticPairSemanticCutsInDomain.toStaticPairStepInDomain
          (RhoCanonicalStaticPairSemanticCutsInDomain.of_provider_built
            (built color)))))
    (rhoHereditaryReflectiveSupportPreserving_of
      rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path)

/-- The cost layer object laws from the built provider alone. -/
noncomputable def rhoHereditaryCompactOpenNormalizerLaws_ofBuiltProvider
    (built : ∀ color,
      RhoCanonicalStaticPair.HasBuiltSemanticCut color) :
    Cost.CompactOpenNormalizer.Laws rhoCIGSLT
      rhoCostNormalizeOpenHereditarySupported :=
  rhoHereditaryCompactOpenNormalizerLaws_of
    (rhoCostOpenGeneratorTreeAlignable_of_staticClosures (fun color =>
      CostCanonicalStaticPair.IsClosedIn.of_step
        (by exact List.mem_cons_self)
        (RhoCanonicalStaticPairSemanticCutsInDomain.toStaticPairStepInDomain
          (RhoCanonicalStaticPairSemanticCutsInDomain.of_provider_built
            (built color)))))
    (rhoHereditaryReflectiveSupportPreserving_of
      rhoHereditaryStaticNormalizer_preservesReflectiveSupport_path)

/-- **Equal source frames plus leg agreement on their own names give
restoration alignment.**

Frame equality alone does *not* suffice: the two endpoints reify through
different environments and different cospan slots, so identical frames still
produce different reifications.  Leg agreement is the missing side condition.

It is demanded only at the names the frame actually mentions — reification
renames nothing else, and both `mapPattern` and `thickenAmbientBVars` leave
the name set alone.  A formulation quantified over every string would instead
force the two environments to resolve identical name sets, since `lookupAtom?`
resolves exactly the atom-namespace names below `atomCount`.

Ambient-binder agreement is free: two static root views over one available
context share a `targetBound`.  `reifyNameWith_eq_of_keys` discharges the
hypothesis from key agreement, which `matchedFvarKeyAgreement_of_sourceVariable`
supplies automatically on the source namespace. -/
theorem restorationAligned_of_framesEq_of_frameNames
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (framesEq :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt leftView.node
            leftEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          leftView.node.targetBound.length 0
          (leftView.node.reifiedSourceFrame leftEnvironment).1 =
        canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
            rightEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          rightView.node.targetBound.length 0
          (rightView.node.reifiedSourceFrame rightEnvironment).1)
    (names :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ∀ name ∈ (canonicalizeByDepths
          (CostStaticRegionNode.sourceSemanticPatternKeyAt rightView.node
            rightEnvironment)
          rhoReflectivePresentation.toReflectivePresentationDecl
          rightView.node.targetBound.length 0
          (rightView.node.reifiedSourceFrame rightEnvironment).1).freeFvarNames,
        cospan.reifyNameWith leftEnvironment.lookupAtom? cospan.leftSlot name =
          cospan.reifyNameWith rightEnvironment.lookupAtom? cospan.rightSlot
            name) :
    RhoStaticFramesRestorationAligned leftView rightView := by
  have thickenEq (depth : Nat) (pattern : Pattern) :
      leftView.node.thinning.thickenAmbientBVars depth pattern =
        rightView.node.thinning.thickenAmbientBVars depth pattern := by
    simpa only [CostStaticRegionNode.thinning] using congrArg
      (fun targetBound =>
        (CostStaticBinderThinning.ofTargetThinning rhoCIGSLT color targetBound)
          |>.thickenAmbientBVars depth pattern)
      (leftView.targetBound_eq_targetBound rightView)
  apply RhoStaticFramesRestorationAligned.ofSourceCanonicalAlignment
  simp only at framesEq names
  refine .leaf ?_
  intro depth
  rw [framesEq, thickenEq depth,
    CostStaticAtomKeyCospan.reifyWith_eq_of_free _ _ _ _
      (fun name inThickened => names name (by
        rwa [CostStaticBinderThinning.thickenAmbientBVars_freeFvarNames,
          StructuralMorphism.mapPattern_freeFvarNames] at inThickened))]
  exact fun _ => rfl

/-! ### The provider from two root-level facts

The seven semantic-cut constructors are not seven independent obligations.
Five of them — both cross-colour enclosing arms, both same-colour static
enclosing arms, and the root-aligned `matched` arm — consume one and the same
object: endpoint restoration alignment of two static root views, which is
stated at *independent* colours and is therefore blind to the same/different
colour distinction the constructors draw.  The remaining two arms are the ones
whose partner carries no static root at all.

So a bridge case needs exactly two things: restoration alignment whenever both
roots are static, and leaf exposure when the partner root is structural.  The
partner trichotomy is decided by `rootIsStatic`, and in the static branch the
partner's colour is recovered from its own root shape. -/

/-- **Leaf exposure against any partner.**

`RhoCollapsingLeaf.HasExposure` carries `other.rootIsStatic = false`, but
that premise is not used by any exposure producer — none of
`CostHereditaryStaticCollapseExposure`, `CostHereditaryStaticDeepAtomExposure`
or `CostStaticProcessBoundary` mentions it.  It scoped the lane rather than
enabling it.

Dropping it lets the two enclosing arms absorb the foreign-colour static
partner as well as the structural one, which is what makes the cross-colour
restoration lane unnecessary: `.leftEnclosing` imposes no staticness condition
on the partner, so any collapsing root with an exposure cuts, whatever the
partner's root is. -/
abbrev RhoCollapsingLeafExposureAnyPartner
    (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {collapsedPattern otherPattern : Pattern} {type : TypeExpr}
    {collapsed : CostRegionTree rhoCIGSLT targetFree available outer
      collapsedPattern type}
    {other : CostRegionTree rhoCIGSLT targetFree available outer otherPattern
      type}
    {color : CostStaticColor}
    (view : collapsed.StaticRootView color),
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type collapsedPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type otherPattern →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf collapsedPattern + sizeOf otherPattern) →
    CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        collapsedPattern →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        collapsedPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        otherPattern →
    Nonempty (RhoCollapsingLeafExposure view.node view.children other)

/-! ### When the cross-colour lane is inhabitable

The cross-colour lane is not merely harder than the same-colour one; it is
outright empty on a whole quadrant.  The two theorems below pin that down, so
an attempt on the lane knows which configurations it must show unreachable
rather than prove. -/

/-- Two applications with different constructors can only be leaf-aligned:
the congruence arm of `PatternLeafAligned` demands one shared constructor. -/
theorem relation_of_patternLeafAligned_apply_apply_of_ne
    {relation : Pattern → Pattern → Prop}
    {leftConstructor rightConstructor : String}
    {leftArguments rightArguments : List Pattern}
    (different : leftConstructor ≠ rightConstructor)
    (aligned : PatternLeafAligned relation
      (.apply leftConstructor leftArguments)
      (.apply rightConstructor rightArguments)) :
    relation (.apply leftConstructor leftArguments)
      (.apply rightConstructor rightArguments) := by
  cases aligned with
  | leaf related => exact related
  | apply constructor arguments => exact absurd rfl different

/-- **Cross-colour restoration alignment is impossible between two
application frames.**

Leaf alignment is the only available arm, and it asks the two reified frames
to restore together — which two colour-decodable application heads never do.
So `.leftCrossColorEnclosing` and `.rightCrossColorEnclosing` are inhabitable
only where the collapsing endpoint's canonical frame degenerates below an
application. -/
theorem not_restorationAligned_of_crossColor_applicationFrames
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {leftColor rightColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (different : leftColor ≠ rightColor)
    {leftWire rightWire leftSource rightSource : String}
    {leftArguments rightArguments : List Pattern}
    (leftFrame :
      leftView.node.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory
          (leftView.node.semanticAtomEnvironment
            (leftView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
        (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
          rhoReflectivePresentation.toReflectivePresentationDecl) =
        .apply leftWire leftArguments)
    (rightFrame :
      rightView.node.canonicalizeReifiedTargetFrame
        (CostStaticAtomEnvironment.ofInventory
          (rightView.node.semanticAtomEnvironment
            (rightView.children.normalizeValues
              (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
        (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
          rhoReflectivePresentation.toReflectivePresentationDecl) =
        .apply rightWire rightArguments)
    (leftDecoded :
      decodeCostStaticConstructor leftColor leftWire = some leftSource)
    (rightDecoded :
      decodeCostStaticConstructor rightColor rightWire = some rightSource) :
    ¬ RhoStaticFramesRestorationAligned leftView rightView := by
  intro aligned
  simp only [RhoStaticFramesRestorationAligned] at aligned
  rw [leftFrame, rightFrame] at aligned
  have headNe : leftWire ≠ rightWire := by
    intro equality
    exact decodeCostStaticConstructor_color_disjoint different leftDecoded
      (equality ▸ rightDecoded)
  exact not_restoresTogether_reifyWith_apply_apply different leftDecoded
    rightDecoded _ _ _ _ _ _ _ _ leftArguments rightArguments
    (relation_of_patternLeafAligned_apply_apply_of_ne headNe aligned)

/-- **Every bridge case cuts, given restoration alignment and the standing
exposure obligation.**  The partner trichotomy — structural, static at the
same colour, static at the other colour — selects the enclosing,
static-enclosing, or cross-colour constructor, and the aligned case is the
restoration cut.

The enclosing arms use `RhoCollapsingLeaf.HasExposure`, which carries the
recursion the exposure producers actually consume; restoration alignment is
root-level and does not.

OFF THE LIVE PATH — this dispatcher and the two builders below duplicate, by
hand, the route already implemented in `CostHereditaryProviderObligations`, which
consumes the four restoration obligations and seals through
`rhoHereditaryCostLayer_ofRestorationObligations`.  The inhabitation
ledger records `RhoAlignedViewsRestorationAlignedInDomain` as strictly stronger
than its consumer requires, with no route back; and
`RhoCollapsingLeafExposureAnyPartner` below drops the partner's
`rootIsStatic = false` premise, which is the same weakening that leaves the
three-classification route vacuous against the empty-parallel witness.  Prefer
the restoration route; these declarations have no dependents. -/
theorem nonempty_rhoCanonicalStaticPairSemanticCut_of_restorationAligned
    {declarationColor : CostStaticColor}
    (sameColorRestoration :
      RhoAlignedViewsRestorationAlignedInDomain declarationColor)
    (exposure : RhoCollapsingLeafExposureAnyPartner declarationColor)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern))
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern)
    (rootCase : RhoCanonicalStaticPairBridgeCase declarationColor left right) :
    Nonempty (RhoCanonicalStaticPairSemanticCut declarationColor left right
      rootCase) := by
  cases rootCase with
  | aligned color leftView rightView roots =>
      exact ⟨.matched leftView rightView roots
        (RhoMatchedStaticFramesCut.ofRestorationAligned leftView rightView
          (sameColorRestoration leftView rightView admissible leftWellSorted
            rightWellSorted closeSmaller roots))⟩
  | leftCollapsing leftColor leftView collapsing =>
      obtain ⟨exposed⟩ := exposure leftView admissible leftWellSorted
        rightWellSorted closeSmaller collapsing canonical
      exact ⟨.leftEnclosing leftView collapsing exposed⟩
  | rightCollapsing rightColor rightView collapsing =>
      obtain ⟨exposed⟩ := exposure rightView admissible rightWellSorted
        leftWellSorted
        (fun childLeft childRight childCanonical smaller childAdmissible =>
          closeSmaller childLeft childRight childCanonical (by omega)
            childAdmissible)
        collapsing canonical.symm
      exact ⟨.rightEnclosing rightView collapsing exposed⟩

/-- The built provider at every declaration colour. -/
theorem rhoCanonicalStaticPair_hasBuiltSemanticCut_of_restorationAligned
    (sameColorRestoration : ∀ color,
      RhoAlignedViewsRestorationAlignedInDomain color)
    (exposure : ∀ color, RhoCollapsingLeafExposureAnyPartner color)
    (declarationColor : CostStaticColor) :
    RhoCanonicalStaticPair.HasBuiltSemanticCut declarationColor := by
  intro targetFree available outer leftPattern rightPattern type admissible
    leftWellSorted rightWellSorted canonical staticShape closeSmaller rootCase
  exact nonempty_rhoCanonicalStaticPairSemanticCut_of_restorationAligned
    (sameColorRestoration declarationColor) (exposure declarationColor)
    admissible leftWellSorted
    rightWellSorted closeSmaller canonical rootCase

/-- **The rho cost layer domain object from restoration alignment and the standing
exposure obligation.** -/
noncomputable def rhoHereditaryCostLayer_ofRestorationAligned
    (sameColorRestoration : ∀ color,
      RhoAlignedViewsRestorationAlignedInDomain color)
    (exposure : ∀ color, RhoCollapsingLeafExposureAnyPartner color) :
    Cost.Layer :=
  rhoHereditaryCostLayer_ofBuiltProvider
    (rhoCanonicalStaticPair_hasBuiltSemanticCut_of_restorationAligned
      sameColorRestoration exposure)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
