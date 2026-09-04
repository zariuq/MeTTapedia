import Mettapedia.GSLT.LanguageDef.CostRestorationFvarPairLeaf

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PROBE: name-level leg agreement lifts to whole patterns. -/
theorem CostStaticAtomKeyCospan.reifyWith_eq_of_reifyNameWith_eq
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftCount))
    (rightResolve : String → Option (Fin rightCount))
    (names : ∀ name,
      cospan.reifyNameWith leftResolve cospan.leftSlot name =
        cospan.reifyNameWith rightResolve cospan.rightSlot name) :
    ∀ pattern,
      cospan.reifyWith leftResolve cospan.leftSlot pattern =
        cospan.reifyWith rightResolve cospan.rightSlot pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [reifyWith]
  | hfvar name =>
      have nameEq := names name
      unfold CostStaticAtomKeyCospan.reifyNameWith at nameEq
      simp only [reifyWith]
      cases leftSelected : leftResolve name <;>
        cases rightSelected : rightResolve name <;> simp_all
  | happly constructor arguments inductionHypothesis =>
      simp only [reifyWith, Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership
  | hlambda binder body inductionHypothesis =>
      simp only [reifyWith, Pattern.lambda.injEq, true_and]
      exact inductionHypothesis
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [reifyWith, Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [reifyWith, Pattern.subst.injEq]
      exact ⟨bodyHypothesis, replacementHypothesis⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [reifyWith, Pattern.collection.injEq, true_and, and_true]
      apply List.map_congr_left
      intro element membership
      exact inductionHypothesis element membership

end Mettapedia.GSLT.LanguageDef
