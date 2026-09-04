import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

namespace Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.RestoresTogether

/-- Supported substitution is independent of the ambient depth when every
free name occurring in the pattern is assigned a binder-closed value. -/
theorem substituteAt_eq_of_freeFvarNames_scopedAtZero
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support) (assignment : ContextSupport.Assignment)
    {pattern : Pattern}
    (closed : ∀ name, name ∈ pattern.freeFvarNames →
      (assignment name).isWellScopedAt 0 = true)
    (first second : Nat) :
    substituteAt profile support assignment first pattern =
      substituteAt profile support assignment second pattern := by
  induction pattern using Pattern.inductionOn generalizing first second with
  | hbvar index => simp only [substituteAt]
  | hfvar name =>
      simp only [substituteAt]
      have assignedClosed := closed name (by
        simp only [Pattern.freeFvarNames, List.mem_singleton])
      rw [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
          assignedClosed,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
          assignedClosed]
  | happly constructor arguments inductionHypothesis =>
      simp only [substituteAt, Pattern.apply.injEq, true_and]
      apply List.map_congr_left
      intro argument membership
      apply inductionHypothesis argument membership
      intro name nameMembership
      exact closed name (by
        simp only [Pattern.freeFvarNames] at nameMembership ⊢
        exact List.mem_flatMap.mpr ⟨argument, membership, nameMembership⟩)
  | hlambda binder body inductionHypothesis =>
      simp only [substituteAt, Pattern.lambda.injEq, true_and]
      apply inductionHypothesis
      intro name nameMembership
      exact closed name (by simpa [Pattern.freeFvarNames] using nameMembership)
  | hmultiLambda arity binders body inductionHypothesis =>
      simp only [substituteAt, Pattern.multiLambda.injEq, true_and]
      apply inductionHypothesis
      intro name nameMembership
      exact closed name (by simpa [Pattern.freeFvarNames] using nameMembership)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [substituteAt, Pattern.subst.injEq]
      constructor
      · apply bodyHypothesis
        intro name nameMembership
        exact closed name (by simp [Pattern.freeFvarNames, nameMembership])
      · apply replacementHypothesis
        intro name nameMembership
        exact closed name (by simp [Pattern.freeFvarNames, nameMembership])
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [substituteAt, Pattern.collection.injEq, true_and, and_true]
      apply List.map_congr_left
      intro element membership
      apply inductionHypothesis element membership
      intro name nameMembership
      exact closed name (by
        simp only [Pattern.freeFvarNames] at nameMembership ⊢
        exact List.mem_append_left _
          (List.mem_flatMap.mpr ⟨element, membership, nameMembership⟩))

/-- Equality at one depth extends to depth-uniform restoration when all
assigned values consulted by both endpoints are binder-closed. -/
theorem of_eq_at_of_freeFvarNames_scopedAtZero
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support) (assignment : ContextSupport.Assignment)
    {left right : Pattern} {keyDepth : Nat}
    (leftClosed : ∀ name, name ∈ left.freeFvarNames →
      (assignment name).isWellScopedAt 0 = true)
    (rightClosed : ∀ name, name ∈ right.freeFvarNames →
      (assignment name).isWellScopedAt 0 = true)
    (equalAt : substituteAt profile support assignment keyDepth left =
      substituteAt profile support assignment keyDepth right) :
    RestoresTogether profile support assignment left right := by
  intro depth
  rw [substituteAt_eq_of_freeFvarNames_scopedAtZero profile support assignment
      leftClosed depth keyDepth,
    substituteAt_eq_of_freeFvarNames_scopedAtZero profile support assignment
      rightClosed depth keyDepth]
  exact equalAt

end Mettapedia.GSLT.LanguageDef.ReflectiveContextSupport.RestoresTogether
