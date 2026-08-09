import Mettapedia.GSLT.LanguageDef.CostRestorationRelationQuoteArm
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalReachableDomain
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryStaticStructuralClosure
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnostic

/-!
# Typed common-restoration apex for rho Cost

The generic reflective root dichotomy deliberately admits untyped collapsing
pairs.  Rho's generated typing rules remove the bad cases: Quote/Drop exposes
the exact generated name fibre, while the only base-typed bare collection is
the generated parallel constructor.  This module combines those typed facts
with the common-restoration relation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.GSLT.LanguageDef.CostStaticAtomKeyCospan

namespace RhoCommonRestorationApex

/-- Lift a typed rho constructor spine through a caller-supplied apex for
strictly smaller canonical pairs.  Parameter reachability is supplied from
the one generated rule, so the recursion never invents a second typing table. -/
theorem rhoArguments
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (parentLeft parentRight : Pattern)
    (close : ∀ {bound : List TypeExpr} {left right : Pattern}
      {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat},
      HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound left type →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound right type →
        isObjectPattern left = true →
        isObjectPattern right = true →
        canonicalize declaration left = canonicalize declaration right →
        sizeOf left + sizeOf right <
          sizeOf parentLeft + sizeOf parentRight →
        rhoReachableType type = true →
        CommonRestorationApex rhoCIGSLT cospan declaration rootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            declaration leftDepth left)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
            declaration rightDepth right)) :
    ∀ {bound : List TypeExpr} {leftArguments rightArguments : List Pattern}
      {parameters : List TermParam} {leftDepth rightDepth rootDepth : Nat},
      ArgumentsHaveTypes rhoCIGSLT.costWholeLanguage
          cospan.commonTargetFreeContext bound leftArguments parameters →
      ArgumentsHaveTypes rhoCIGSLT.costWholeLanguage
          cospan.commonTargetFreeContext bound rightArguments parameters →
      isObjectPatternList leftArguments = true →
      isObjectPatternList rightArguments = true →
      (∀ argument ∈ leftArguments, sizeOf argument < sizeOf parentLeft) →
      (∀ argument ∈ rightArguments, sizeOf argument < sizeOf parentRight) →
      (∀ {parameter : TermParam}, parameter ∈ parameters →
        ∀ {expected : TypeExpr}, parameterType? parameter = some expected →
          rhoReachableType expected = true) →
      List.Forall₂
        (fun left right =>
          canonicalize declaration left = canonicalize declaration right)
        leftArguments rightArguments →
      CommonRestorationApexList rhoCIGSLT cospan declaration rootDepth
        (canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration leftDepth
          leftArguments)
        (canonicalizeListByAt
          (cospan.commonSemanticPatternKeyAt rhoCIGSLT) declaration rightDepth
          rightArguments) := by
  intro bound leftArguments rightArguments parameters leftDepth rightDepth
    rootDepth leftTyped rightTyped leftObjects rightObjects leftSmaller
    rightSmaller parametersReachable canonical
  rw [canonicalizeListByAt_eq_map, canonicalizeListByAt_eq_map]
  induction canonical generalizing parameters with
  | nil =>
      cases leftTyped
      cases rightTyped
      exact .nil rootDepth
  | @cons leftHead rightHead leftTail rightTail headCanonical tailCanonical ih =>
      cases leftTyped with
      | @cons _ _ _ leftParameter leftParameters leftExpected
          leftRepresentation leftParameterType leftHeadTyped leftTailTyped =>
          cases rightTyped with
          | @cons _ _ _ rightParameter rightParameters rightExpected
              rightRepresentation rightParameterType rightHeadTyped
              rightTailTyped =>
              have expectedEq : rightExpected = leftExpected :=
                Option.some.inj
                  (rightParameterType.symm.trans leftParameterType)
              subst rightExpected
              have leftObjectParts : isObjectPattern leftHead = true ∧
                  isObjectPatternList leftTail = true := by
                simpa [isObjectPatternList] using leftObjects
              have rightObjectParts : isObjectPattern rightHead = true ∧
                  isObjectPatternList rightTail = true := by
                simpa [isObjectPatternList] using rightObjects
              have headMeasure : sizeOf leftHead + sizeOf rightHead <
                  sizeOf parentLeft + sizeOf parentRight := by
                have leftLt := leftSmaller leftHead (by simp)
                have rightLt := rightSmaller rightHead (by simp)
                omega
              have headReachable : rhoReachableType leftExpected = true :=
                parametersReachable (by simp) leftParameterType
              have head := close (leftDepth := leftDepth)
                (rightDepth := rightDepth) (rootDepth := rootDepth)
                leftHeadTyped rightHeadTyped
                leftObjectParts.1 rightObjectParts.1 headCanonical headMeasure
                headReachable
              have tail := ih leftTailTyped rightTailTyped leftObjectParts.2
                rightObjectParts.2
                (fun argument membership =>
                  leftSmaller argument (by simp [membership]))
                (fun argument membership =>
                  rightSmaller argument (by simp [membership]))
                (fun {parameter} membership {expected} parameterType =>
                  parametersReachable (by simp [membership]) parameterType)
              exact .cons head tail

/-- One non-collapsing typed rho layer lifts to the common restoration apex.
The recursive callback is used only on proper children.  Structural
collection fibres are excluded by `rhoReachableType`; the only base-typed
bare collection rule is PPar, which cannot occur in the nonparallel aligned
arm. -/
theorem rhoCanonicalRootAligned
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (color : CostStaticColor)
    {bound : List TypeExpr} {parentLeft parentRight : Pattern}
    {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat}
    (close : ∀ {bound : List TypeExpr} {left right : Pattern}
      {type : TypeExpr} {leftDepth rightDepth rootDepth : Nat},
      HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound left type →
        HasType rhoCIGSLT.costWholeLanguage cospan.commonTargetFreeContext
          bound right type →
        isObjectPattern left = true →
        isObjectPattern right = true →
        canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            left =
          canonicalize
            (costStaticReflectivePresentationDecl rhoCIGSLT color
              rhoReflectivePresentation.toReflectivePresentationDecl)
            right →
        sizeOf left + sizeOf right < sizeOf parentLeft + sizeOf parentRight →
        rhoReachableType type = true →
        CommonRestorationApex rhoCIGSLT cospan
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
            rightDepth right))
    (leftTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext bound parentLeft type)
    (rightTyped : HasType rhoCIGSLT.costWholeLanguage
      cospan.commonTargetFreeContext bound parentRight type)
    (leftObject : isObjectPattern parentLeft = true)
    (rightObject : isObjectPattern parentRight = true)
    (admissible : rhoReachableType type = true)
    (aligned : CanonicalRootAligned
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      parentLeft parentRight) :
    CommonRestorationApex rhoCIGSLT cospan
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl)
      rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        leftDepth parentLeft)
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
        (costStaticReflectivePresentationDecl rhoCIGSLT color
          rhoReflectivePresentation.toReflectivePresentationDecl)
        rightDepth parentRight) := by
  let declaration := costStaticReflectivePresentationDecl rhoCIGSLT color
    rhoReflectivePresentation.toReflectivePresentationDecl
  cases aligned with
  | bvar index =>
      simpa [declaration, canonicalizeByAt] using
        (CommonRestorationApex.refl (source := rhoCIGSLT) cospan declaration rootDepth
          (.bvar index))
  | fvar name =>
      simpa [declaration, canonicalizeByAt] using
        (CommonRestorationApex.refl (source := rhoCIGSLT) cospan declaration rootDepth
          (.fvar name))
  | @apply constructor ne leftArguments rightArguments childrenCanonical =>
      obtain ⟨rule, membership, labelEq, notBare, typeEq, leftArgumentsTyped,
          rightArgumentsTyped⟩ :=
        hasType_apply_pair rho_costWholeLanguage_labelDeterministic leftTyped
          rightTyped
      subst constructor
      subst type
      have leftObjects : isObjectPatternList leftArguments = true := by
        simpa [isObjectPattern] using leftObject
      have rightObjects : isObjectPatternList rightArguments = true := by
        simpa [isObjectPattern] using rightObject
      let childRootDepth :=
        if ReflectiveContextSupport.isQuoteConstructor
            rhoCIGSLT.costWholeReflectionProfile rule.label then 0 else rootDepth
      have ordinaryDeclarationHead : rule.label ≠
          (costStaticReflectivePresentationDecl rhoCIGSLT color
            rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor := by
        simpa [declaration] using ne
      have ordinaryMappedHead : rule.label ≠
          (ReflectionExtension.mapReflectivePresentation
            (CostStaticColor.reflectiveSymbols rhoCIGSLT color)
            rhoReflectivePresentation.toReflectivePresentationDecl).quoteConstructor := by
        simpa only [costStaticReflectivePresentationDecl_eq_map] using
          ordinaryDeclarationHead
      have arguments := rhoArguments cospan declaration
        (.apply rule.label leftArguments) (.apply rule.label rightArguments)
        close leftArgumentsTyped rightArgumentsTyped leftObjects rightObjects
        (by
          intro argument argumentMembership
          have argumentBound := List.sizeOf_lt_of_mem argumentMembership
          simp_wf
          omega)
        (by
          intro argument argumentMembership
          have argumentBound := List.sizeOf_lt_of_mem argumentMembership
          simp_wf
          omega)
        (by
          intro parameter parameterMembership expected parameterType
          exact rho_generatedParameter_reachable membership notBare
            parameterMembership parameterType)
        childrenCanonical (leftDepth := leftDepth) (rightDepth := rightDepth)
        (rootDepth := childRootDepth)
      have leftCanonical :
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              leftDepth (.apply rule.label leftArguments) =
            .apply rule.label
              (canonicalizeListByAt
                (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl)
                leftDepth leftArguments) := by
        simp [canonicalizeByAt, ordinaryMappedHead]
      have rightCanonical :
          canonicalizeByAt (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
              (costStaticReflectivePresentationDecl rhoCIGSLT color
                rhoReflectivePresentation.toReflectivePresentationDecl)
              rightDepth (.apply rule.label rightArguments) =
            .apply rule.label
              (canonicalizeListByAt
                (cospan.commonSemanticPatternKeyAt rhoCIGSLT)
                (costStaticReflectivePresentationDecl rhoCIGSLT color
                  rhoReflectivePresentation.toReflectivePresentationDecl)
                rightDepth rightArguments) := by
        simp [canonicalizeByAt, ordinaryMappedHead]
      rw [leftCanonical, rightCanonical]
      exact CommonRestorationApex.apply rule.label arguments
  | @lambda binder leftBody rightBody bodyCanonical =>
      cases leftTyped with
      | lambda leftBodyTyped =>
          cases rightTyped with
          | lambda rightBodyTyped =>
              have body := close (leftDepth := leftDepth + 1)
                (rightDepth := rightDepth + 1)
                (rootDepth := rootDepth + 1) leftBodyTyped rightBodyTyped
                (by simpa [isObjectPattern] using leftObject)
                (by simpa [isObjectPattern] using rightObject)
                bodyCanonical (by
                  have leftBound : sizeOf leftBody <
                      sizeOf (Pattern.lambda binder leftBody) := by simp_wf
                  have rightBound : sizeOf rightBody <
                      sizeOf (Pattern.lambda binder rightBody) := by simp_wf
                  exact Nat.add_lt_add leftBound rightBound)
                (by simpa [rhoReachableType] using admissible)
              exact .lambda binder body
  | @multiLambda arity binders leftBody rightBody bodyCanonical =>
      cases leftTyped with
      | multiLambda leftBodyTyped =>
          cases rightTyped with
          | multiLambda rightBodyTyped =>
              have body := close (leftDepth := leftDepth + arity)
                (rightDepth := rightDepth + arity)
                (rootDepth := rootDepth + arity) leftBodyTyped rightBodyTyped
                (by simpa [isObjectPattern] using leftObject)
                (by simpa [isObjectPattern] using rightObject)
                bodyCanonical (by
                  have leftBound : sizeOf leftBody <
                      sizeOf (Pattern.multiLambda arity binders leftBody) := by
                    simp_wf
                  have rightBound : sizeOf rightBody <
                      sizeOf (Pattern.multiLambda arity binders rightBody) := by
                    simp_wf
                  exact Nat.add_lt_add leftBound rightBound)
                (by simpa [rhoReachableType] using admissible)
              exact .multiLambda binders body
  | subst bodyCanonical replacementCanonical =>
      simp [isObjectPattern] at leftObject
  | @collection collectionType ne leftElements rightElements
      childrenCanonical =>
      rcases hasType_collection_inversion leftTyped with
        ⟨elementType, typeEq, elementsTyped⟩ |
          ⟨rule, parameterName, elementType, membership, parameterShape,
            typeEq, elementsTyped⟩
      · rw [typeEq] at admissible
        exact (rhoCanonicalRecursiveTypeDomain.noCollection admissible).elim
      · rcases rho_collectionRule_cases membership parameterShape with
          ⟨parallelType, category, element⟩ |
          ⟨parallelType, category, element⟩
        all_goals
          have declarationParallel : declaration.parallelCollection =
              rhoReflectivePresentation.parallelCollection := by
            cases color <;> rfl
          exact (ne (parallelType.trans declarationParallel.symm)).elim
  | collectionRest collectionType rest childrenCanonical =>
      simp [isObjectPattern] at leftObject

end RhoCommonRestorationApex

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
