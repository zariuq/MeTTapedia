import Mettapedia.GSLT.LanguageDef.CostSemanticAtomAlignment

/-!
# Reify congruence over aligned free-variable spellings

Two static skeletons produced for the two endpoints of one generated edge
differ only in free-variable spellings: a changed boundary child changes its
content-keyed boundary name, while every constructor, binder, and bound
index is preserved.  Reification into a common semantic apex forgets exactly
those spellings whenever the related names resolve to slots with one common
leg index.  This module records that congruence once, structurally, so
neither closure ever compares boundary spellings again.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

mutual
  /-- Structural identity up to a relation on free-variable spellings. -/
  inductive FvarAligned (relation : String → String → Prop) :
      Pattern → Pattern → Prop where
    | bvar (index : Nat) : FvarAligned relation (.bvar index) (.bvar index)
    | fvar {left right : String} (related : relation left right) :
        FvarAligned relation (.fvar left) (.fvar right)
    | apply (constructor : String)
        {leftArguments rightArguments : List Pattern}
        (arguments : FvarAlignedList relation leftArguments rightArguments) :
        FvarAligned relation (.apply constructor leftArguments)
          (.apply constructor rightArguments)
    | lambda (binder : Option String) {leftBody rightBody : Pattern}
        (body : FvarAligned relation leftBody rightBody) :
        FvarAligned relation (.lambda binder leftBody)
          (.lambda binder rightBody)
    | multiLambda (arity : Nat) (binders : List String)
        {leftBody rightBody : Pattern}
        (body : FvarAligned relation leftBody rightBody) :
        FvarAligned relation (.multiLambda arity binders leftBody)
          (.multiLambda arity binders rightBody)
    | subst {leftBody rightBody leftReplacement rightReplacement : Pattern}
        (body : FvarAligned relation leftBody rightBody)
        (replacement : FvarAligned relation leftReplacement
          rightReplacement) :
        FvarAligned relation (.subst leftBody leftReplacement)
          (.subst rightBody rightReplacement)
    | collection (collectionType : CollType) (rest : Option String)
        {leftElements rightElements : List Pattern}
        (elements : FvarAlignedList relation leftElements rightElements) :
        FvarAligned relation (.collection collectionType leftElements rest)
          (.collection collectionType rightElements rest)

  /-- Pointwise spelling alignment for pattern lists. -/
  inductive FvarAlignedList (relation : String → String → Prop) :
      List Pattern → List Pattern → Prop where
    | nil : FvarAlignedList relation [] []
    | cons {leftHead rightHead : Pattern}
        {leftTail rightTail : List Pattern}
        (head : FvarAligned relation leftHead rightHead)
        (tail : FvarAlignedList relation leftTail rightTail) :
        FvarAlignedList relation (leftHead :: leftTail)
          (rightHead :: rightTail)
end

mutual
  /-- Reflexivity along a reflexive spelling relation. -/
  theorem FvarAligned.refl {relation : String → String → Prop}
      (reflexive : ∀ name, relation name name) :
      ∀ pattern, FvarAligned relation pattern pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar (reflexive name)
    | .apply constructor arguments =>
        .apply constructor (FvarAlignedList.refl reflexive arguments)
    | .lambda binder body => .lambda binder (FvarAligned.refl reflexive body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (FvarAligned.refl reflexive body)
    | .subst body replacement =>
        .subst (FvarAligned.refl reflexive body)
          (FvarAligned.refl reflexive replacement)
    | .collection collectionType elements rest =>
        .collection collectionType rest
          (FvarAlignedList.refl reflexive elements)

  /-- Listwise reflexivity along a reflexive spelling relation. -/
  theorem FvarAlignedList.refl {relation : String → String → Prop}
      (reflexive : ∀ name, relation name name) :
      ∀ patterns, FvarAlignedList relation patterns patterns
    | [] => .nil
    | pattern :: patterns =>
        .cons (FvarAligned.refl reflexive pattern)
          (FvarAlignedList.refl reflexive patterns)
end

namespace CostStaticAtomKeyCospan

mutual
  /-- Reification through a common semantic apex is invariant across aligned
  free-variable spellings whenever every related pair of names resolves on
  both sides to one common leg index. -/
  theorem reifyWith_eq_of_fvarAligned
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      {relation : String → String → Prop}
      (matched : ∀ {leftName rightName : String},
        relation leftName rightName →
        ∃ leftSlot rightSlot,
          leftResolve leftName = some leftSlot ∧
            rightResolve rightName = some rightSlot ∧
            leftLeg leftSlot = rightLeg rightSlot)
      {leftPattern rightPattern : Pattern}
      (aligned : FvarAligned relation leftPattern rightPattern) :
      cospan.reifyWith leftResolve leftLeg leftPattern =
        cospan.reifyWith rightResolve rightLeg rightPattern :=
    match aligned with
    | .bvar index => by simp [reifyWith]
    | .fvar related => by
        obtain ⟨leftSlot, rightSlot, leftResolved, rightResolved, legsEq⟩ :=
          matched related
        simp [reifyWith, leftResolved, rightResolved, legsEq]
    | .apply constructor arguments => by
        simp only [reifyWith, Pattern.apply.injEq, true_and]
        exact reifyWithList_eq_of_fvarAlignedList cospan leftResolve
          rightResolve leftLeg rightLeg matched arguments
    | .lambda binder body => by
        simp only [reifyWith, Pattern.lambda.injEq, true_and]
        exact reifyWith_eq_of_fvarAligned cospan leftResolve rightResolve
          leftLeg rightLeg matched body
    | .multiLambda arity binders body => by
        simp only [reifyWith, Pattern.multiLambda.injEq, true_and]
        exact reifyWith_eq_of_fvarAligned cospan leftResolve
          rightResolve leftLeg rightLeg matched body
    | .subst body replacement => by
        simp only [reifyWith, Pattern.subst.injEq]
        exact ⟨reifyWith_eq_of_fvarAligned cospan leftResolve rightResolve
            leftLeg rightLeg matched body,
          reifyWith_eq_of_fvarAligned cospan leftResolve rightResolve
            leftLeg rightLeg matched replacement⟩
    | .collection collectionType rest elements => by
        simp only [reifyWith, Pattern.collection.injEq, true_and, and_true]
        exact reifyWithList_eq_of_fvarAlignedList cospan leftResolve
          rightResolve leftLeg rightLeg matched elements

  /-- Listwise companion of the reification congruence. -/
  theorem reifyWithList_eq_of_fvarAlignedList
      {leftCount rightCount leftEndpoint rightEndpoint : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftEndpoint))
      (rightResolve : String → Option (Fin rightEndpoint))
      (leftLeg : Fin leftEndpoint → Fin cospan.commonKeys.length)
      (rightLeg : Fin rightEndpoint → Fin cospan.commonKeys.length)
      {relation : String → String → Prop}
      (matched : ∀ {leftName rightName : String},
        relation leftName rightName →
        ∃ leftSlot rightSlot,
          leftResolve leftName = some leftSlot ∧
            rightResolve rightName = some rightSlot ∧
            leftLeg leftSlot = rightLeg rightSlot)
      {leftPatterns rightPatterns : List Pattern}
      (aligned : FvarAlignedList relation leftPatterns rightPatterns) :
      leftPatterns.map (cospan.reifyWith leftResolve leftLeg) =
        rightPatterns.map (cospan.reifyWith rightResolve rightLeg) :=
    match aligned with
    | .nil => rfl
    | .cons head tail => by
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨reifyWith_eq_of_fvarAligned cospan leftResolve rightResolve
            leftLeg rightLeg matched head,
          reifyWithList_eq_of_fvarAlignedList cospan leftResolve rightResolve
            leftLeg rightLeg matched tail⟩
end

end CostStaticAtomKeyCospan

end Mettapedia.GSLT.LanguageDef
