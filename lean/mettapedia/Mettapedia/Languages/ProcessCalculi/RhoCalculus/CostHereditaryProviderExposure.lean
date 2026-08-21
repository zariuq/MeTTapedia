import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderLeftCollapsing

/-!
# Partner-shape reduction for the collapsing-leaf exposure obligation

`RhoCollapsingLeafExposureInDomain` quantifies over an arbitrary non-static
partner endpoint.  `CostRegionTree` has eight constructors, so a direct attack
faces eight configurations.  Four of them are impossible and are refuted here
outright, leaving the obligation supported on exactly the three leaf-shaped
partner patterns.

* `lambda`, `multiLambda` and `collection` partners carry an arrow or
  collection result type, whereas a static root view certifies a base sort.
  Each is refuted by `CostRegionTree.StaticRootView.typeEq` alone.
* A `subst` partner is refuted semantically rather than by its type index.
  The collapsed endpoint is an authored object term, canonicalization
  preserves the object/schema boundary, and a pending substitution is not an
  object pattern; so no canonicalization of an authored term is a `subst`.
  The supporting preservation law for the unkeyed canonicalizer is proved
  below from the keyed one.

What remains is `rho_collapsingLeafExposureInDomain_of_leafRoutes`: the
obligation follows from three routes whose partner pattern is a bound
variable, a free variable, or a constructor application.  This is the exact
case list a proof of the obligation has to cover, and it is closed under the
premises the provider actually supplies.

## What the exposure asserts

`RhoCollapsingLeafExposure.normalize_eq` reads the content off the two
constructors: each one pins the partner's hereditary normal form to the
collapsed node's static normal form, either through the restored semantic
atom or through the rigid bound variable.  So an exposure is exactly a
certified agreement of the two hereditary normal forms, carrying in addition
a shape certificate for the collapsed side.

Projecting that through the obligation gives
`rho_normalize_eq_of_collapsingLeafExposureInDomain`: assuming
`RhoCollapsingLeafExposureInDomain` for one colour, any two endpoints in one
fibre with equal canonicalizations, one static with a collapsing root and one
with a non-static root, already have equal hereditary normal forms.  That is
the normalization-soundness statement itself, restricted to a mixed pair, and
the obligation states it with no recursion parameter — neither a
strictly-decreasing callback nor an induction principle on the endpoint pair.
`RhoCollapsingLeafExposure.isEmpty_of_normalize_ne` is the matching
falsification handle: a single mixed pair whose hereditary normal forms
differ refutes the obligation.
-/

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The unkeyed reflective canonicalizer preserves the object/schema
boundary.  The keyed canonicalizer already has this law; the unkeyed one is
its `patternCode` instance at any ambient depth. -/
theorem canonicalize_isObjectPattern
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (object : isObjectPattern pattern = true) :
    isObjectPattern (canonicalize declaration pattern) = true := by
  rw [← canonicalizeBy_patternCode declaration pattern,
    ← canonicalizeByAt_const PatternCode.patternCode declaration 0 pattern]
  exact canonicalizeByAt_isObjectPattern _ declaration 0 pattern object

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- A canonicalized authored object term never exposes a pending
substitution at its root.

This is the semantic exclusion that removes the `subst` partner from the
collapsing-leaf obligation: the type index of `CostRegionTree.subst` is an
arbitrary codomain, so it survives the static root view's base-sort
certificate and has to be refuted by content. -/
theorem canonicalize_ne_subst_of_isObjectPattern
    (declaration : ReflectivePresentationDecl) {pattern : Pattern}
    (object : isObjectPattern pattern = true) (body replacement : Pattern) :
    canonicalize declaration pattern ≠ .subst body replacement := by
  intro collapse
  have := canonicalize_isObjectPattern declaration object
  rw [collapse] at this
  simp [isObjectPattern] at this

namespace RhoCollapsingLeafExposure

/-- **The exposure is an agreement of hereditary normal forms.**

The atom constructor pins the partner to the restored selected atom, and its
frame equation says that same atom is the collapsed node's canonical reified
target frame, whose restoration is the node's static normal form.  The rigid
constructor pins both sides to one bound variable.  Neither constructor
carries any further content about the partner. -/
theorem normalize_eq
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    {node : CostStaticRegionNode rhoCIGSLT color targetFree}
    {children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable}
    {rightPattern : Pattern} {rightType : TypeExpr}
    {right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType}
    (exposure : RhoCollapsingLeafExposure node children right) :
    (right.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (rhoHereditaryStaticNormalizer node
        (children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1 := by
  cases exposure with
  | atom slot staticFrame structuralNormal =>
      rw [structuralNormal, ← staticFrame]
      unfold rhoHereditaryStaticNormalizer
        CostStaticRegionNode.normalizeHereditary
      rw [CostStaticRegionNode.normalizeHereditaryWithInventory_pattern]
      rfl
  | rigidBVar index staticNormal structuralNormal =>
      rw [structuralNormal, staticNormal]

/-- Falsification handle for the collapsing-leaf obligation.  Any endpoint
whose hereditary normal form differs from the collapsed node's static normal
form admits no exposure at all, whatever its pattern and whatever the
canonical relation between the two endpoints. -/
theorem isEmpty_of_normalize_ne
    {color : CostStaticColor} {targetFree : FreeTypeContext}
    {rightAvailable rightOuter : List TypeExpr}
    {node : CostStaticRegionNode rhoCIGSLT color targetFree}
    {children : CostRegionBoundaryTrees rhoCIGSLT targetFree color
      node.finiteBoundaryTable}
    {rightPattern : Pattern} {rightType : TypeExpr}
    {right : CostRegionTree rhoCIGSLT targetFree rightAvailable rightOuter
      rightPattern rightType}
    (differs :
      (right.normalize
          (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern ≠
        (rhoHereditaryStaticNormalizer node
          (children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1) :
    IsEmpty (RhoCollapsingLeafExposure node children right) :=
  ⟨fun exposure => differs exposure.normalize_eq⟩

end RhoCollapsingLeafExposure

/-- **The obligation is a normalization-soundness statement.**

Discharging `RhoCollapsingLeafExposureInDomain` for one colour already
decides every mixed endpoint pair in the domain: equal canonicalizations,
one collapsing static root, one non-static root, hence equal hereditary
normal forms.  The obligation offers no recursion parameter with which to
establish that on the partner's own subterms — the provider's
strictly-decreasing callback is discarded before the obligation is stated. -/
theorem rho_normalize_eq_of_collapsingLeafExposureInDomain
    {declarationColor : CostStaticColor}
    (exposure : RhoCollapsingLeafExposureInDomain declarationColor)
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {collapsedPattern otherPattern : Pattern} {type : TypeExpr}
    {collapsed : CostRegionTree rhoCIGSLT targetFree available outer
      collapsedPattern type}
    {other : CostRegionTree rhoCIGSLT targetFree available outer otherPattern
      type}
    {color : CostStaticColor}
    (view : collapsed.StaticRootView color)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (collapsedWellSorted :
      ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type collapsedPattern)
    (otherWellSorted :
      ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type otherPattern)
    (close : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf collapsedPattern + sizeOf otherPattern))
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      collapsedPattern)
    (structural : other.rootIsStatic = false)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          collapsedPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          otherPattern) :
    (other.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern =
      (collapsed.normalize
        (normalizeStatic := rhoHereditaryStaticNormalizer)).pattern := by
  obtain ⟨leaf⟩ := exposure view admissible collapsedWellSorted
    otherWellSorted close collapsing structural canonical
  rw [leaf.normalize_eq, view.normalize_pattern rhoHereditaryStaticNormalizer]

/-- **Route for a bound-variable partner.**  Canonical equality is already
reduced: canonicalization fixes a bound variable, so the collapsed endpoint
canonicalizes to that exact variable. -/
def RhoCollapsingLeafExposureBVarRoute (declarationColor : CostStaticColor) :
    Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {collapsedPattern : Pattern} {index : Nat} {type : TypeExpr}
    {collapsed : CostRegionTree rhoCIGSLT targetFree available outer
      collapsedPattern type}
    {color : CostStaticColor}
    (view : collapsed.StaticRootView color)
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.bvar index) type),
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type (Pattern.bvar index) →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf collapsedPattern + sizeOf (Pattern.bvar index)) →
    CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        collapsedPattern →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        collapsedPattern =
      .bvar index →
    Nonempty (RhoCollapsingLeafExposure view.node view.children other)

/-- **Route for a free-variable partner.**  Canonical equality is again
already reduced to the exact collapsed normal form. -/
def RhoCollapsingLeafExposureFVarRoute (declarationColor : CostStaticColor) :
    Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {collapsedPattern : Pattern} {name : String} {type : TypeExpr}
    {collapsed : CostRegionTree rhoCIGSLT targetFree available outer
      collapsedPattern type}
    {color : CostStaticColor}
    (view : collapsed.StaticRootView color)
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.fvar name) type),
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type (Pattern.fvar name) →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf collapsedPattern + sizeOf (Pattern.fvar name)) →
    CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        collapsedPattern →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        collapsedPattern =
      .fvar name →
    Nonempty (RhoCollapsingLeafExposure view.node view.children other)

/-- **Route for a constructor-application partner.**  Both neutral
application constructors of `CostRegionTree` land here; the retained root
observation is kept, since it is the only datum separating this route from a
second static endpoint. -/
def RhoCollapsingLeafExposureApplyRoute (declarationColor : CostStaticColor) :
    Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {collapsedPattern : Pattern} {label : String}
    {arguments : List Pattern} {type : TypeExpr}
    {collapsed : CostRegionTree rhoCIGSLT targetFree available outer
      collapsedPattern type}
    {color : CostStaticColor}
    (view : collapsed.StaticRootView color)
    (other : CostRegionTree rhoCIGSLT targetFree available outer
      (.apply label arguments) type),
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type (Pattern.apply label arguments) →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf collapsedPattern + sizeOf (Pattern.apply label arguments)) →
    CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        collapsedPattern →
    other.rootIsStatic = false →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        collapsedPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply label arguments) →
    Nonempty (RhoCollapsingLeafExposure view.node view.children other)

/-- **The collapsing-leaf obligation reduced to three partner shapes.**

Binders, collections and pending substitutions are refuted outright, so the
whole content of `RhoCollapsingLeafExposureInDomain` is carried by partners
whose pattern is a bound variable, a free variable, or an application.  In
the two variable routes the canonical premise is delivered already solved,
because canonicalization fixes variables. -/
theorem rho_collapsingLeafExposureInDomain_of_leafRoutes
    {declarationColor : CostStaticColor}
    (bvarRoute : RhoCollapsingLeafExposureBVarRoute declarationColor)
    (fvarRoute : RhoCollapsingLeafExposureFVarRoute declarationColor)
    (applyRoute : RhoCollapsingLeafExposureApplyRoute declarationColor) :
    RhoCollapsingLeafExposureInDomain declarationColor := by
  intro targetFree available outer collapsedPattern otherPattern type
    collapsed other color view admissible _collapsedWellSorted
    otherWellSorted close collapsing structural canonical
  have collapsedObject : isObjectPattern collapsedPattern = true := by
    rw [← view.patternEq]
    exact view.node.term.2.2.2.1
  cases other.structuralRootView structural with
  | bvar lookup =>
      refine bvarRoute view _ admissible otherWellSorted close collapsing ?_
      rw [canonical]
      simp [canonicalize]
  | fvar lookup =>
      refine fvarRoute view _ admissible otherWellSorted close collapsing ?_
      rw [canonical]
      simp [canonicalize]
  | neutralApplicationOrdinary membership notBare constructor materializes
      neutral ordinary children =>
      exact applyRoute view _ admissible otherWellSorted close collapsing rfl canonical
  | neutralApplicationQuote membership notBare constructor materializes
      neutral quoted children =>
      exact applyRoute view _ admissible otherWellSorted close collapsing rfl canonical
  | lambda bodyTree => exact absurd view.typeEq (by simp)
  | multiLambda bodyTree => exact absurd view.typeEq (by simp)
  | subst bodyTree replacementTree =>
      exact absurd canonical
        (canonicalize_ne_subst_of_isObjectPattern _ collapsedObject _ _)
  | collection children => exact absurd view.typeEq (by simp)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
