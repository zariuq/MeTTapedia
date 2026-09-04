import Mettapedia.GSLT.LanguageDef.CostRestorationFvarPairLeaf

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PROBE: agreement only on the names the pattern actually mentions. -/
theorem CostStaticAtomKeyCospan.reifyWith_eq_of_free
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (leftResolve : String → Option (Fin leftCount))
    (rightResolve : String → Option (Fin rightCount)) :
    ∀ pattern, (∀ name ∈ pattern.freeFvarNames,
        cospan.reifyNameWith leftResolve cospan.leftSlot name =
          cospan.reifyNameWith rightResolve cospan.rightSlot name) →
      cospan.reifyWith leftResolve cospan.leftSlot pattern =
        cospan.reifyWith rightResolve cospan.rightSlot pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; simp [reifyWith]
  | hfvar name =>
      intro names
      have nameEq := names name (by simp [Pattern.freeFvarNames])
      unfold CostStaticAtomKeyCospan.reifyNameWith at nameEq
      simp only [reifyWith]
      cases leftSelected : leftResolve name <;>
        cases rightSelected : rightResolve name <;> simp_all
  | happly constructor arguments inductionHypothesis =>
      intro names
      simp only [reifyWith, Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      refine inductionHypothesis argument membership (fun name inArgument => ?_)
      exact names name (by
        simp only [Pattern.freeFvarNames, List.mem_flatMap]
        exact ⟨argument, membership, inArgument⟩)
  | hlambda binder body inductionHypothesis =>
      intro names
      simp only [reifyWith, Pattern.lambda.injEq, true_and]
      exact inductionHypothesis (fun name inBody =>
        names name (by simpa [Pattern.freeFvarNames] using inBody))
  | hmultiLambda arity binders body inductionHypothesis =>
      intro names
      simp only [reifyWith, Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis (fun name inBody =>
        names name (by simpa [Pattern.freeFvarNames] using inBody))
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro names
      simp only [reifyWith, Pattern.subst.injEq]
      refine ⟨bodyHypothesis (fun name inBody => names name ?_),
        replacementHypothesis (fun name inReplacement => names name ?_)⟩
      · simp only [Pattern.freeFvarNames, List.mem_append]
        exact .inl inBody
      · simp only [Pattern.freeFvarNames, List.mem_append]
        exact .inr inReplacement
  | hcollection collectionType elements rest inductionHypothesis =>
      intro names
      simp only [reifyWith, Pattern.collection.injEq, true_and, and_true]
      apply List.map_congr_left
      intro element membership
      refine inductionHypothesis element membership (fun name inElement => ?_)
      exact names name (by
        simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
        exact .inl ⟨element, membership, inElement⟩)

end Mettapedia.GSLT.LanguageDef
