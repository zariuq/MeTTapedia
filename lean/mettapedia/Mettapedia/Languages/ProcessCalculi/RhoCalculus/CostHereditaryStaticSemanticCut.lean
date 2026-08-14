import Mettapedia.GSLT.LanguageDef.CostRestorationCut
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticPairApex

/-!
# Semantic cuts for hereditary rho Cost pairs

A canonical child-pair elaboration remembers the two selected region trees and
their final normalization alignment.  A reached static-plan branch needs more:
it must retain the exact contexts in which the recursive result is used and
the common-restoration evidence for every fixed sibling of those contexts.

`CommonRestorationCut` is that stronger recursive certificate.  It is a
Kripke-style family indexed by the current context depth and endpoints.  Every
descent keeps the parent semantic cospan fixed while recording the aligned
one-hole contexts through which the recursive certificate is used.  Its
eliminator composes the evidence; it does not assume equality of the enclosing
normal forms.  This module supplies the rho-specific closure theorems for that
generic carrier.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace RhoCommonRestorationCut

/-! ## Fixed-cospan recursive closure -/

/-- Hereditarily typed canonical rho endpoints yield a semantic cut in their
already selected common namespace.

All restoration evidence is constructed by rho's well-founded common-apex
recursion.  The cut merely retains that proof in the fixed cospan; it does not
reconstruct a parent namespace from a compact child elaboration. -/
theorem nonempty_of_canonicalWithin
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {left right : Pattern}
    {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat}
    (leftHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound left type)
    (rightHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound right type)
    (leftObject : isObjectPattern left = true)
    (rightObject : isObjectPattern right = true)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        left =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        right)
    (admissible : rhoReachableType type = true)
    (compatible : RhoCommonRestorationApex.RhoApexDepthCompatible
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      type leftDepth rightDepth rootDepth) :
    Nonempty (CommonRestorationCut rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth left)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth right)) :=
  ⟨.terminal
    (RhoCommonRestorationApex.rhoCommonRestorationApex_of_canonicalWithin
      cospan color leftHereditary rightHereditary leftObject rightObject
      canonical admissible compatible)⟩

/-- The fixed-cospan closure in the exact well-founded callback shape.

The strict raw-size premise names the enclosing pair whose recursion opened
this child obligation.  Construction remains in the selected parent cospan,
so eliminating the result never needs to recover semantic keys from a child
tree alignment. -/
theorem nonempty_of_canonicalWithin_smaller
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {enclosingLeft enclosingRight : Pattern}
    {bound : List TypeExpr} {left right : Pattern}
    {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat}
    (leftHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound left type)
    (rightHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound right type)
    (leftObject : isObjectPattern left = true)
    (rightObject : isObjectPattern right = true)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        left =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        right)
    (_smaller : sizeOf left + sizeOf right <
      sizeOf enclosingLeft + sizeOf enclosingRight)
    (admissible : rhoReachableType type = true)
    (compatible : RhoCommonRestorationApex.RhoApexDepthCompatible
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      type leftDepth rightDepth rootDepth) :
    Nonempty (CommonRestorationCut rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth left)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth right)) :=
  nonempty_of_canonicalWithin cospan color leftHereditary rightHereditary
    leftObject rightObject canonical admissible compatible

/-- Positive recursion canary: removing a selected rho Quote/Drop shell from
the left endpoint strictly decreases the symmetric raw endpoint measure. -/
theorem quoteDropLeft_payload_smaller
    (color : CostStaticColor) (inner right : Pattern) :
    sizeOf inner + sizeOf right <
      sizeOf
          (Pattern.apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).quoteConstructor
            [Pattern.apply
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl
                ).dropConstructor [inner]]) +
        sizeOf right := by
  simp_wf
  omega

/-- Negative recursion canary: the fixed-cospan callback cannot discharge its
own enclosing pair through the strict raw endpoint measure. -/
theorem not_pair_smaller_than_itself (left right : Pattern) :
    ¬ (sizeOf left + sizeOf right < sizeOf left + sizeOf right) :=
  Nat.lt_irrefl _

/-- Actual Quote/Drop-shaped endpoints inhabit the fixed-cospan cut family.
This is a specialization of the constructed rho recursion, not a new terminal
assumption. -/
theorem nonempty_quoteDropLeft
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {inner right : Pattern}
    {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat}
    (leftHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]]) type)
    (rightHereditary : HasTypeWithConstructors
      rhoCIGSLT.costWholeLanguage
      (CostStaticColor.hereditaryConstructorImage rhoCIGSLT color)
      cospan.commonTargetFreeContext bound right type)
    (leftObject : isObjectPattern
      (.apply
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl
          ).quoteConstructor
        [.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).dropConstructor [inner]]) = true)
    (rightObject : isObjectPattern right = true)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor
          [.apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).dropConstructor [inner]]) =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        right)
    (admissible : rhoReachableType type = true)
    (compatible : RhoCommonRestorationApex.RhoApexDepthCompatible
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      type leftDepth rightDepth rootDepth) :
    Nonempty (CommonRestorationCut rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth
        (.apply
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl
            ).quoteConstructor
          [.apply
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl
              ).dropConstructor [inner]]))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth right)) :=
  nonempty_of_canonicalWithin cospan color leftHereditary rightHereditary
    leftObject rightObject canonical admissible compatible

end RhoCommonRestorationCut

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
