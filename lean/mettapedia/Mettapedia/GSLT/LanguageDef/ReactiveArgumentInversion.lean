import Mettapedia.GSLT.LanguageDef.ReactiveContexts

/-! Inverting an authored argument-congruence firing retains the exact
child derivation and both untouched sibling vectors. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec Engine ContextualStep
open ReflectiveCanonical ReflectiveSubstitution

theorem ArgumentCongruence.invert {base : BasePremiseEvaluator} {language : LanguageDef}
    {rule : RewriteRule} {label : String} {before after : List String} {source target : String}
    (congruence : ArgumentCongruence rule label before after source target)
    {fuel : Nat} {state next : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPatternForRule language rule state)
    (premises : PremisesAt base language fuel initial rule.premises final)
    (targetEq : applyBindingsForRule language rule final = next) :
    ∃ beforeTerms afterTerms redex reduct,
      beforeTerms.length = before.length ∧ afterTerms.length = after.length ∧
      state = .apply label (beforeTerms ++ redex :: afterTerms) ∧
      next = .apply label (beforeTerms ++ reduct :: afterTerms) ∧
      StepAt base language fuel redex reduct := by
  have leftExact : isMatchCorrectAux rule.left = true := by
    rw [congruence.left]
    exact isMatchCorrectAux_apply_variables label _
  have rightExact : isMatchCorrectAux rule.right = true := by
    rw [congruence.right]
    exact isMatchCorrectAux_apply_variables label _
  have matched' : initial ∈ matchPattern rule.left state := by simpa using matched
  rw [congruence.premises] at premises
  cases premises with
  | cons firstPremise restPremises =>
      cases restPremises
      cases firstPremise with
      | @congruence _ _ premiseBindings _ _ _ candidate innerStep premiseMatched merged =>
          have premiseShape : premiseBindings = [(target, candidate)] := by
            have relation := matchPattern_sound premiseMatched
            cases relation
            rfl
          subst premiseShape
          have initialLeft : applyBindings initial rule.left = state := matchPattern_correct matched' leftExact
          have finalLeft : applyBindings final rule.left = state :=
            matchRel_correct_of_extends (matchPattern_sound matched') leftExact
              (fun _ _ found => mergeBindings_subsumed_left merged found)
          have finalTarget : applyBindings final (.fvar target) = candidate := by
            have found : final.find? (·.1 == target) = some (target, candidate) :=
              mergeBindings_subsumed_right merged (by simp)
            simp [applyBindings, found]
          have nextEq : applyBindings final rule.right = next := by
            rw [← targetEq, applyBindingsForRule_eq_applyBindings _ _ _
              (ruleDepthAligned_of_binderFree rule
                (binderFree_of_isMatchCorrectAux _ leftExact)
                (binderFree_of_isMatchCorrectAux _ rightExact))]
          rw [congruence.left, applyBindings_apply_variables] at initialLeft finalLeft
          rw [congruence.right, applyBindings_apply_variables] at nextEq
          simp only [List.map_append, List.map_cons] at initialLeft finalLeft nextEq
          have same : (before.map fun name => applyBindings final (.fvar name)) ++
              applyBindings final (.fvar source) :: (after.map fun name => applyBindings final (.fvar name)) =
              (before.map fun name => applyBindings initial (.fvar name)) ++
                applyBindings initial (.fvar source) :: (after.map fun name => applyBindings initial (.fvar name)) := by
            have equal := finalLeft.trans initialLeft.symm
            injection equal
          obtain ⟨sameBefore, sameRest⟩ := List.append_inj same (by simp)
          obtain ⟨_, sameAfter⟩ := List.cons.inj sameRest
          rw [sameBefore, sameAfter, finalTarget] at nextEq
          exact ⟨before.map (fun name => applyBindings initial (.fvar name)),
            after.map (fun name => applyBindings initial (.fvar name)),
            applyBindings initial (.fvar source), candidate, by simp, by simp,
            initialLeft.symm, nextEq.symm, innerStep⟩

end Mettapedia.GSLT.LanguageDef
