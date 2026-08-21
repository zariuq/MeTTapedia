import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryAlignedRestoration

/-!
# The collapsing arms of the rho static-pair provider

`RhoCollapsingViewsRestorationAlignedInDomain` asks two static root views of a
canonically equal pair, one endpoint of which has a collapsing root, to be
restoration-aligned.  This module reduces that obligation, records the exact
measure at which its raw descent can be stated, and separates the two colour
configurations its call sites actually produce.

## The measure of the raw descent

The aligned obligation routes through `canonicalStopAligned_of_root_aligned`,
whose retained stop relation is measured at `sizeOf left + sizeOf right`: a
root alignment delegates only *proper* subpairs.  A collapsing root does not.
`CanonicalStopAligned.given_of_collapsingRoot_left` shows why: every rigid
descent constructor of `CanonicalStopAligned` excludes the quote constructor
and the parallel collection type, which are exactly the two collapsing root
shapes, so at a collapsing root only `.leaf` remains and the retained stop
relation must already contain the endpoint pair itself.

Combined with `not_rhoCanonicalRawStop_endpoints_at_endpointMeasure` this is a
theorem, not a preference: `not_canonicalStopAligned_endpoints_of_collapsing`
shows there is *no* descent for a collapsing pair at the endpoint measure, at
either endpoint, whatever the canonical data.  The collapsing arm's raw stop
is therefore stated one above the endpoint pair, and
`rhoCanonicalStopAligned_succ_of_collapsing` produces it.

The strictly-smaller recursion callback is unaffected.  Everything the
certified-boundary quadrant consumes is measured against the *node's own*
boundary table (`boundary_content_size_lt_of_isStaticRoot`), not against the
reached payload, so the quadrant closes at the raised measure by the same
producer the aligned arm uses.

## The two colour configurations

`RhoStaticFramesRestorationAligned` is indexed by two independent colours, and
both collapsing arms consume it at either colour: the same-colour branch feeds
`leftStaticEnclosing` through `RhoMatchedStaticFramesApex.ofRestorationAligned`,
the different-colour branch feeds `leftCrossColorEnclosing` directly.  The two
configurations do not share machinery.  Every producer of the source-form
alignment — `RhoStaticFramesRestorationAligned.ofSourceCanonicalAlignment`,
`reifiedSourceAlignment_of_rawAlignment`, and the whole boundary-restoration
chain below them — is stated for two nodes of one and the same colour, because
a single semantic-key cospan is built from two environments over that colour.
So the split here is not a convenience: the same-colour half is reduced to the
plan-stop residual the aligned arm already carries, and the cross-colour half
is named separately.

The cross-colour half is not empty, but it is confined.  The two views share
one result type, and the two static colour actions on sorts differ exactly at
the authored interacting sort, so
`CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne` shows a
different-colour pair necessarily carries one and the same source sort, and
that sort is never the interacting one.  Both facts are supplied to the
cross-colour residual below, which is therefore an obligation about the shared
non-interacting fibre alone.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open WellSorted

/-- **Two different-colour static root views of one type share a source sort
outside the interacting sort.**

The base colour sends every authored sort into the base namespace; the
wrapped colour agrees with it except at the authored interacting sort, which
it sends to the single reserved wrapped name.  A common result type therefore
forces the two source sorts to be equal and to avoid that sort — the
different-colour configuration lives entirely in the colour-agnostic
fibre. -/
theorem CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne
    {source : CIGSLT} {targetFree : FreeTypeContext}
    {available leftOuter rightOuter : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {leftTree : CostRegionTree source targetFree available leftOuter
      leftPattern type}
    {rightTree : CostRegionTree source targetFree available rightOuter
      rightPattern type}
    {leftColor rightColor : CostStaticColor}
    (leftView : leftTree.StaticRootView leftColor)
    (rightView : rightTree.StaticRootView rightColor)
    (different : leftColor ≠ rightColor) :
    leftView.node.sourceSort.1 = rightView.node.sourceSort.1 ∧
      leftView.node.sourceSort.1 ≠
        source.theory.presentation.interactingSort.1.name := by
  have nameEq :
      (leftColor.symbols source).sort leftView.node.sourceSort.1 =
        (rightColor.symbols source).sort rightView.node.sourceSort.1 :=
    TypeExpr.base.inj (leftView.typeEq.trans rightView.typeEq.symm)
  cases leftColor <;> cases rightColor
  · exact absurd rfl different
  · simp only [CostStaticColor.symbols, costBaseStaticSymbols,
      costBasePresentationSymbols, costWrappedStaticSymbols] at nameEq
    split_ifs at nameEq with interacting
    · exact absurd nameEq (costBaseSortName_ne_wrapped _)
    · have sortEq := costBaseSortName_injective nameEq
      exact ⟨sortEq, by rw [sortEq]; exact interacting⟩
  · simp only [CostStaticColor.symbols, costBaseStaticSymbols,
      costBasePresentationSymbols, costWrappedStaticSymbols] at nameEq
    split_ifs at nameEq with interacting
    · exact absurd nameEq.symm (costBaseSortName_ne_wrapped _)
    · have sortEq := costBaseSortName_injective nameEq
      exact ⟨sortEq, interacting⟩
  · exact absurd rfl different

end Mettapedia.GSLT.LanguageDef

namespace Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **A collapsing root admits no rigid descent step.**

Every constructor of `CanonicalStopAligned` other than `.leaf` either fixes a
root shape that is not collapsing, or carries a side condition excluding
exactly the collapsing shape: `.apply` excludes the quote constructor and
`.collection` excludes the parallel collection type.  A stopped alignment
whose left root collapses therefore hands its whole endpoint pair to the stop
relation. -/
theorem CanonicalStopAligned.given_of_collapsingRoot_left
    {declaration : ReflectivePresentationDecl}
    {stop : Pattern → Pattern → Prop} {left right : Pattern}
    (aligned : CanonicalStopAligned declaration stop left right)
    (collapsing : CollapsingRoot declaration left) :
    stop left right := by
  cases aligned with
  | leaf given => exact given
  | bvar index =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | fvar name =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | apply ne arguments =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩
      · injection shape with headEq _
        exact absurd headEq ne
      · simp at shape
  | lambda binder body =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | multiLambda arity binders body =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | subst body replacement =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | collection ne elements =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩
      · simp at shape
      · injection shape with typeEq _ _
        exact absurd typeEq ne
  | collectionRest collectionType rest elements =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape

/-- The mirror of `given_of_collapsingRoot_left` on the right endpoint.  The
descent constructors are symmetric in the two roots, so a collapsing right
root stops the descent just as a collapsing left root does. -/
theorem CanonicalStopAligned.given_of_collapsingRoot_right
    {declaration : ReflectivePresentationDecl}
    {stop : Pattern → Pattern → Prop} {left right : Pattern}
    (aligned : CanonicalStopAligned declaration stop left right)
    (collapsing : CollapsingRoot declaration right) :
    stop left right := by
  cases aligned with
  | leaf given => exact given
  | bvar index =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | fvar name =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | apply ne arguments =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩
      · injection shape with headEq _
        exact absurd headEq ne
      · simp at shape
  | lambda binder body =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | multiLambda arity binders body =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | subst body replacement =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape
  | collection ne elements =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩
      · simp at shape
      · injection shape with typeEq _ _
        exact absurd typeEq ne
  | collectionRest collectionType rest elements =>
      rcases collapsing with ⟨_, shape⟩ | ⟨_, shape⟩ <;> simp at shape

/-- Either collapsing endpoint stops the descent. -/
theorem CanonicalStopAligned.given_of_collapsingRoot
    {declaration : ReflectivePresentationDecl}
    {stop : Pattern → Pattern → Prop} {left right : Pattern}
    (aligned : CanonicalStopAligned declaration stop left right)
    (collapsing : CollapsingRoot declaration left ∨
      CollapsingRoot declaration right) :
    stop left right :=
  collapsing.elim aligned.given_of_collapsingRoot_left
    aligned.given_of_collapsingRoot_right

end Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open CostStaticRegionNode

/-! ## The measure gate -/

/-- **The collapsing arm has no descent at the endpoint measure.**

`rhoCanonicalRawStop_endpoints_of_leftCollapsing` records that the endpoint
pair of a collapsing arm belongs to the raw stop relation one above itself,
and `not_rhoCanonicalRawStop_endpoints_at_endpointMeasure` records that it
belongs to no raw stop relation measured at itself.  This closes the gap
between those two facts: because a collapsing root forces `.leaf`, a descent
at the endpoint measure would have to place the endpoint pair in a relation
that provably excludes it.

Consequently the aligned arm's route — `canonicalStopAligned_of_root_aligned`,
whose stop relation is measured at `sizeOf leftPattern + sizeOf rightPattern`
— is not merely inconvenient in a collapsing arm; it is uninhabited there. -/
theorem not_canonicalStopAligned_endpoints_of_collapsing
    {declarationColor : CostStaticColor} {leftPattern rightPattern : Pattern}
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern ∨
      CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) :
    ¬ CanonicalStopAligned
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern))
        leftPattern rightPattern :=
  fun aligned =>
    not_rhoCanonicalRawStop_endpoints_at_endpointMeasure
      (aligned.given_of_collapsingRoot collapsing)

/-- The raw descent available to a collapsing arm: canonical equality alone,
at the least measure that can retain the endpoint pair. -/
theorem rhoCanonicalStopAligned_succ_of_collapsing
    {declarationColor : CostStaticColor} {leftPattern rightPattern : Pattern}
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) :
    CanonicalStopAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftPattern + sizeOf rightPattern + 1))
      leftPattern rightPattern :=
  canonicalStopAligned_of_canonicalize_eq_below _ canonical
    (Nat.lt_succ_self _)

/-! ## The same-colour half -/

/-- **Obligation A2s — the same-colour collapsing branch in plan-stop form.**

The exact analogue of the aligned arm's `RhoStaticPlanStopSourceAligned`
obligation, with the root alignment replaced by canonical equality plus a
collapsing endpoint, and the raw stop measured one above the endpoint pair as
the gate above forces. -/
def RhoCollapsingViewsPlanStopSourceAlignedInDomain
    (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color),
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type rightPattern →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) →
    (CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern ∨
      CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern →
    RhoStaticPlanStopSourceAligned leftView rightView declarationColor
      (RhoCanonicalRawStop declarationColor
        (sizeOf leftPattern + sizeOf rightPattern + 1))

/-- **The same-colour collapsing branch from its plan-stop obligation.**

The exact mirror of
`rhoAlignedViewsRestorationAligned_of_planStopSourceAligned`, with the raw
descent generated by canonical equality at the raised measure instead of by a
root alignment at the endpoint measure. -/
theorem rhoCollapsingSameColorViewsRestorationAligned_of_planStopSourceAligned
    {declarationColor : CostStaticColor}
    (planStops : RhoCollapsingViewsPlanStopSourceAlignedInDomain
      declarationColor)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {color : CostStaticColor}
    (leftView : left.StaticRootView color)
    (rightView : right.StaticRootView color)
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (closeSmaller : RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern))
    (collapsing : CollapsingRoot
      (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
        rhoReflectivePresentation.toReflectivePresentationDecl)
      leftPattern ∨
      CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern)
    (canonical :
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) :
    RhoStaticFramesRestorationAligned leftView rightView := by
  apply RhoStaticFramesRestorationAligned.ofSourceCanonicalAlignment leftView
    rightView
  have rawAligned := rhoCanonicalStopAligned_succ_of_collapsing
    (declarationColor := declarationColor) canonical
  have stops := planStops leftView rightView admissible leftWellSorted
    rightWellSorted closeSmaller collapsing canonical
  have result := reifiedSourceAlignment_of_rawAlignment leftView.node
    rightView.node leftView.children rightView.children
    (CostStaticAtomEnvironment.ofInventory
      (leftView.node.semanticAtomEnvironment
        (leftView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
    (CostStaticAtomEnvironment.ofInventory
      (rightView.node.semanticAtomEnvironment
        (rightView.children.normalizeValues
          (normalizeStatic := rhoHereditaryStaticNormalizer))).1)
    (leftView.targetBound_eq_targetBound rightView)
    (leftView.sourceSort_eq_sourceSort rightView)
    (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
      rhoReflectivePresentation)
    (rawStop := RhoCanonicalRawStop declarationColor
      (sizeOf leftPattern + sizeOf rightPattern + 1))
    (by
      rw [leftView.patternEq, rightView.patternEq]
      exact rawAligned)
    (sourceSemanticPatternKeyAt leftView.node
      (CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1))
    (sourceSemanticPatternKeyAt rightView.node
      (CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1))
    leftView.node.targetBound.length 0
    (fun callbackAvailable callbackScope {_leftAbstract _rightAbstract} stop =>
      stops callbackAvailable callbackScope stop)
  rw [leftView.targetBound_length_eq_targetBound_length rightView] at result ⊢
  exact result

/-- **Obligation A2s after the certified-boundary quadrant.**

The both-certified-boundary quadrant of the same-colour collapsing branch is
discharged by the same producer the aligned arm uses.  Nothing in that
producer is measured against the reached payload — its strict decrease comes
from `boundary_content_size_lt_of_isStaticRoot` on the node's own boundary
table — so raising the raw stop measure by one leaves it untouched, and the
strictly-smaller callback consumed is exactly the one the obligation already
carries. -/
theorem rhoCollapsingViewsPlanStopSourceAligned_of_nonBoundaryRemainder
    {declarationColor : CostStaticColor}
    (remaining : ∀ {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer
        rightPattern type}
      {color : CostStaticColor}
      (leftView : left.StaticRootView color)
      (rightView : right.StaticRootView color),
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type leftPattern →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type rightPattern →
      RhoPairCloseSmaller declarationColor targetFree
        (sizeOf leftPattern + sizeOf rightPattern) →
      (CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern ∨
        CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern →
      RhoStaticNonBoundaryPlanStopSourceAligned leftView rightView
        declarationColor
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern + 1))) :
    RhoCollapsingViewsPlanStopSourceAlignedInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    color leftView rightView admissible leftWellSorted rightWellSorted
    closeSmaller collapsing canonical
  refine RhoStaticPlanStopSourceAligned.of_nonBoundaryRemainder leftView
    rightView declarationColor
    (rightRootAdmissible_of_admissible rightView admissible)
    (fun stopped => stopped.1.2) ?_
    (remaining leftView rightView admissible leftWellSorted rightWellSorted
      closeSmaller collapsing canonical)
  intro childAvailable childOuter leftChild rightChild childType
    leftChildWellSorted rightChildWellSorted childCanonical smaller
    childAdmissible
  refine closeSmaller leftChildWellSorted rightChildWellSorted childCanonical
    ?_ childAdmissible
  rw [leftView.patternEq, rightView.patternEq] at smaller
  exact smaller

/-! ## The cross-colour half -/

/-- Whole-frame restoration is one sufficient way to align two frames: take
the alignment to be a single leaf.

This is offered as a route, not as an equivalent form.  It is strictly
sufficient and possibly strictly stronger, because `PatternLeafAligned` also
admits rigid steps at a cross-colour pair — collection types are not renamed
by colour (`costStaticReflectivePresentationDecl_parallelCollection`), so a
collection step is available even between two different-colour frames, as are
the binder and `subst` steps.  The residual named below is therefore stated
with the alignment itself as its conclusion, and this lemma is available to
whoever chooses to close it by a leaf. -/
theorem RhoStaticFramesRestorationAligned.ofFramesRestoreTogether
    {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {leftColor rightColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor)
    (restores :
      let leftEnvironment := CostStaticAtomEnvironment.ofInventory
        (leftView.node.semanticAtomEnvironment
          (leftView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let rightEnvironment := CostStaticAtomEnvironment.ofInventory
        (rightView.node.semanticAtomEnvironment
          (rightView.children.normalizeValues
            (normalizeStatic := rhoHereditaryStaticNormalizer))).1
      let cospan := leftEnvironment.semanticKeyCospan rightEnvironment
      ReflectiveContextSupport.RestoresTogether
        rhoCIGSLT.costWholeReflectionProfile cospan.commonSupport
          cospan.commonAssignment
          (cospan.reifyWith leftEnvironment.lookupAtom? cospan.leftSlot
            (leftView.node.canonicalizeReifiedTargetFrame leftEnvironment
              (costStaticReflectivePresentationDecl rhoCIGSLT leftColor
                rhoReflectivePresentation.toReflectivePresentationDecl)))
          (cospan.reifyWith rightEnvironment.lookupAtom? cospan.rightSlot
            (rightView.node.canonicalizeReifiedTargetFrame rightEnvironment
              (costStaticReflectivePresentationDecl rhoCIGSLT rightColor
                rhoReflectivePresentation.toReflectivePresentationDecl)))) :
    RhoStaticFramesRestorationAligned leftView rightView :=
  .leaf restores

/-- **Obligation A2x — the cross-colour collapsing branch.**

`RhoCollapsingViewsRestorationAlignedInDomain` restricted to two
different-colour views and handed two further premises, hence strictly weaker
than the cross-colour part of A2.  It is separated from the same-colour half
because every source-form producer in the lane — the semantic-key cospan, the
reified source frames, the boundary-restoration chain — is built from two
environments over one colour and does not apply here.

The two sort premises are not extra strength demanded of a prover: they are
derived from the shared result type by
`CostRegionTree.StaticRootView.sourceSort_eq_of_color_ne` and supplied at the
call site.  Stating them here confines the obligation to the shared
non-interacting fibre, which for rho is the `Name` fibre. -/
def RhoCollapsingCrossColorViewsRestorationAlignedInDomain
    (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : FreeTypeContext} {available outer : List TypeExpr}
    {leftPattern rightPattern : Pattern} {type : TypeExpr}
    {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
      type}
    {right : CostRegionTree rhoCIGSLT targetFree available outer rightPattern
      type}
    {leftColor rightColor : CostStaticColor}
    (leftView : left.StaticRootView leftColor)
    (rightView : right.StaticRootView rightColor),
    leftColor ≠ rightColor →
    leftView.node.sourceSort.1 = rightView.node.sourceSort.1 →
    leftView.node.sourceSort.1 ≠
      rhoCIGSLT.theory.presentation.interactingSort.1.name →
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree available type rightPattern →
    RhoPairCloseSmaller declarationColor targetFree
      (sizeOf leftPattern + sizeOf rightPattern) →
    (CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern ∨
      CollapsingRoot
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern) →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightPattern →
    RhoStaticFramesRestorationAligned leftView rightView

/-! ## Obligation A2 from the two halves -/

/-- **Obligation A2 from the same-colour plan-stop residual and the
cross-colour frame residual.**

The colour split is exhaustive by decidability of `CostStaticColor` equality,
and the same-colour branch substitutes the two colours before invoking the
one-colour chain. -/
theorem rho_collapsingViewsRestorationAlignedInDomain_of_halves
    {declarationColor : CostStaticColor}
    (sameColor : RhoCollapsingViewsPlanStopSourceAlignedInDomain
      declarationColor)
    (crossColor : RhoCollapsingCrossColorViewsRestorationAlignedInDomain
      declarationColor) :
    RhoCollapsingViewsRestorationAlignedInDomain declarationColor := by
  intro targetFree available outer leftPattern rightPattern type left right
    leftColor rightColor leftView rightView admissible leftWellSorted
    rightWellSorted closeSmaller collapsing canonical
  by_cases sameColour : leftColor = rightColor
  · subst sameColour
    exact rhoCollapsingSameColorViewsRestorationAligned_of_planStopSourceAligned
      sameColor leftView rightView admissible leftWellSorted rightWellSorted
      closeSmaller collapsing canonical
  · obtain ⟨sourceSortEq, notInteracting⟩ :=
      leftView.sourceSort_eq_of_color_ne rightView sameColour
    exact crossColor leftView rightView sameColour sourceSortEq notInteracting
      admissible leftWellSorted rightWellSorted closeSmaller collapsing
      canonical

/-- **Obligation A2 from the non-boundary plan-stop residual and the
cross-colour frame residual.**

This is the operative reduction: the same-colour half is carried by exactly
the residual the aligned arm carries, differing only in the measure the gate
above forces, and the cross-colour half is a single whole-frame restoration
statement. -/
theorem rho_collapsingViewsRestorationAlignedInDomain_of_residuals
    {declarationColor : CostStaticColor}
    (remaining : ∀ {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr}
      {leftPattern rightPattern : Pattern} {type : TypeExpr}
      {left : CostRegionTree rhoCIGSLT targetFree available outer leftPattern
        type}
      {right : CostRegionTree rhoCIGSLT targetFree available outer
        rightPattern type}
      {color : CostStaticColor}
      (leftView : left.StaticRootView color)
      (rightView : right.StaticRootView color),
      rhoCanonicalRecursiveTypeDomain.Admissible type →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type leftPattern →
      ReflectiveWellSorted.OpenPatternWellSorted
          rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
          targetFree available type rightPattern →
      RhoPairCloseSmaller declarationColor targetFree
        (sizeOf leftPattern + sizeOf rightPattern) →
      (CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern ∨
        CollapsingRoot
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern) →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          leftPattern =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation.toReflectivePresentationDecl)
          rightPattern →
      RhoStaticNonBoundaryPlanStopSourceAligned leftView rightView
        declarationColor
        (RhoCanonicalRawStop declarationColor
          (sizeOf leftPattern + sizeOf rightPattern + 1)))
    (crossColor : RhoCollapsingCrossColorViewsRestorationAlignedInDomain
      declarationColor) :
    RhoCollapsingViewsRestorationAlignedInDomain declarationColor :=
  rho_collapsingViewsRestorationAlignedInDomain_of_halves
    (rhoCollapsingViewsPlanStopSourceAligned_of_nonBoundaryRemainder remaining)
    crossColor

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
