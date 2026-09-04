import Mettapedia.GSLT.LanguageDef.CostRestorationFvarPairLeaf

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PROBE: reification agrees on fvar-aligned patterns whose related names
reify alike — covering both resolvable and unresolvable leaves. -/
theorem CostStaticAtomKeyCospan.reifyWith_eq_of_fvarAligned_of_names
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftCount))
    (rightResolve : String → Option (Fin rightCount))
    {relation : String → String → Prop}
    (names : ∀ leftName rightName, relation leftName rightName →
      cospan.reifyNameWith leftResolve cospan.leftSlot leftName =
        cospan.reifyNameWith rightResolve cospan.rightSlot rightName) :
    ∀ {leftPattern rightPattern : Pattern},
      FvarAligned relation leftPattern rightPattern →
      cospan.reifyWith leftResolve cospan.leftSlot leftPattern =
        cospan.reifyWith rightResolve cospan.rightSlot rightPattern
  | _, _, .bvar index => by simp [reifyWith]
  | _, _, .fvar related => by
      have nameEq := names _ _ related
      unfold CostStaticAtomKeyCospan.reifyNameWith at nameEq
      simp only [reifyWith]
      split <;> split <;> simp_all
  | _, _, .apply constructor arguments => by
      simp only [reifyWith, Pattern.apply.injEq, true_and]
      exact reifyWithList_eq cospan leftResolve rightResolve names arguments
  | _, _, .lambda binder body => by
      simp only [reifyWith, Pattern.lambda.injEq, true_and]
      exact reifyWith_eq_of_fvarAligned_of_names cospan leftResolve
        rightResolve names body
  | _, _, .multiLambda arity binders body => by
      simp only [reifyWith, Pattern.multiLambda.injEq, true_and]
      exact reifyWith_eq_of_fvarAligned_of_names cospan leftResolve
        rightResolve names body
  | _, _, .subst body replacement => by
      simp only [reifyWith, Pattern.subst.injEq]
      exact ⟨reifyWith_eq_of_fvarAligned_of_names cospan leftResolve
        rightResolve names body,
        reifyWith_eq_of_fvarAligned_of_names cospan leftResolve rightResolve
          names replacement⟩
  | _, _, .collection collectionType rest elements => by
      simp only [reifyWith, Pattern.collection.injEq, true_and, and_true]
      exact reifyWithList_eq cospan leftResolve rightResolve names elements
where
  reifyWithList_eq
      {leftCount rightCount : Nat}
      {leftKey : Fin leftCount → CostStaticAtomKey}
      {rightKey : Fin rightCount → CostStaticAtomKey}
      (cospan : CostStaticAtomKeyCospan leftKey rightKey)
      (leftResolve : String → Option (Fin leftCount))
      (rightResolve : String → Option (Fin rightCount))
      {relation : String → String → Prop}
      (names : ∀ leftName rightName, relation leftName rightName →
        cospan.reifyNameWith leftResolve cospan.leftSlot leftName =
          cospan.reifyNameWith rightResolve cospan.rightSlot rightName)
      {leftPatterns rightPatterns : List Pattern}
      (aligned : FvarAlignedList relation leftPatterns rightPatterns) :
      leftPatterns.map (cospan.reifyWith leftResolve cospan.leftSlot) =
        rightPatterns.map (cospan.reifyWith rightResolve cospan.rightSlot) :=
    match aligned with
    | .nil => rfl
    | .cons head tail => by
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨reifyWith_eq_of_fvarAligned_of_names cospan leftResolve
          rightResolve names head,
          reifyWithList_eq cospan leftResolve rightResolve names tail⟩

end Mettapedia.GSLT.LanguageDef
