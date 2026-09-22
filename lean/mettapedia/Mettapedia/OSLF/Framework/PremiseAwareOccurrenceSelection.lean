import Mettapedia.OSLF.Framework.PremiseAwareOccurrence

/-!
# Exact indexed selection for premise-aware engine occurrences

The existing selection theorem recovers an authored rule and local alternative
from an admitted occurrence. Here the converse constructs precisely that
numbered occurrence from an indexed rule and a selected executable result.
Together they characterize operational admission without forgetting rule or
alternative positions. No equation-modulo or cross-presentation claim is
made by this local theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.PremiseAwareOccurrenceSelection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence

/-- An exact alternative index produces its numbered occurrence for one
authored rule; this is the converse of `ruleOccurrencesAt_selected`. -/
theorem ruleOccurrencesAt_mem_of_selected
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveFuel ruleIndex : Nat) (rule : RewriteRule)
    (source target : Pattern) (alternativeIndex : Nat)
    (selected :
      (applyRuleUsing base language (rewriteAt base language recursiveFuel)
        rule source)[alternativeIndex]? = some target) :
    (⟨ruleIndex, rule.name, alternativeIndex, target⟩ : RewriteOccurrence) ∈
      ruleOccurrencesAt base language recursiveFuel ruleIndex rule source := by
  unfold ruleOccurrencesAt
  apply List.mem_map.mpr
  exact ⟨(target, alternativeIndex),
    List.mk_mem_zipIdx_iff_getElem?.mpr selected, rfl⟩

/-- Selecting a rule by its actual list position and a result by its actual
alternative position reconstructs the occurrence in the ordered traversal. -/
theorem rewriteOccurrencesFromAt_mem_of_selected
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveFuel startingIndex : Nat) (rules : List RewriteRule)
    (source target : Pattern) (ruleOffset alternativeIndex : Nat)
    (rule : RewriteRule)
    (ruleAt : rules[ruleOffset]? = some rule)
    (selected :
      (applyRuleUsing base language (rewriteAt base language recursiveFuel)
        rule source)[alternativeIndex]? = some target) :
    (⟨startingIndex + ruleOffset, rule.name, alternativeIndex, target⟩ :
      RewriteOccurrence) ∈
        rewriteOccurrencesFromAt base language recursiveFuel startingIndex
          rules source := by
  induction rules generalizing startingIndex ruleOffset with
  | nil => cases ruleOffset <;> simp at ruleAt
  | cons head rest inductionHypothesis =>
      cases ruleOffset with
      | zero =>
          have sameRule : head = rule := by
            simpa using ruleAt
          subst head
          apply List.mem_append.mpr
          left
          simpa [rewriteOccurrencesFromAt] using
            ruleOccurrencesAt_mem_of_selected base language recursiveFuel
              startingIndex rule source target alternativeIndex selected
      | succ laterOffset =>
          have tailRule : rest[laterOffset]? = some rule := by
            simpa using ruleAt
          have later := inductionHypothesis (startingIndex + 1) laterOffset
            tailRule
          apply List.mem_append.mpr
          right
          simpa [rewriteOccurrencesFromAt, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using later

/-- Exact admission of the occurrence named by a rule position and an
alternative position in the finite-fuel premise-aware engine. -/
theorem rewriteAtOccurrences_mem_of_selected
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveFuel : Nat) (source target : Pattern)
    (ruleIndex alternativeIndex : Nat) (rule : RewriteRule)
    (ruleAt : language.rewrites[ruleIndex]? = some rule)
    (selected :
      (applyRuleUsing base language (rewriteAt base language recursiveFuel)
        rule source)[alternativeIndex]? = some target) :
    (⟨ruleIndex, rule.name, alternativeIndex, target⟩ : RewriteOccurrence) ∈
      rewriteAtOccurrences base language (recursiveFuel + 1) source := by
  simpa only [rewriteAtOccurrences, Nat.zero_add] using
    (rewriteOccurrencesFromAt_mem_of_selected base language recursiveFuel
      0 language.rewrites source target ruleIndex alternativeIndex rule ruleAt
      selected)

/-- Membership is characterized by the exact authored rule and exact
runtime alternative, not merely by endpoint support or an authored name. -/
theorem rewriteAtOccurrences_mem_iff_selected
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveFuel : Nat) (source : Pattern)
    (occurrence : RewriteOccurrence) :
    occurrence ∈ rewriteAtOccurrences base language
        (recursiveFuel + 1) source ↔
      ∃ rule,
        language.rewrites[occurrence.ruleIndex]? = some rule ∧
        occurrence.ruleName = rule.name ∧
        (applyRuleUsing base language
          (rewriteAt base language recursiveFuel) rule source)[occurrence.alternativeIndex]? =
            some occurrence.target := by
  constructor
  · exact rewriteAtOccurrences_selected base language recursiveFuel
      source occurrence
  · rintro ⟨rule, ruleAt, nameEq, selected⟩
    have admitted := rewriteAtOccurrences_mem_of_selected base language
      recursiveFuel source occurrence.target occurrence.ruleIndex
      occurrence.alternativeIndex rule ruleAt selected
    obtain ⟨index, name, alternative, target⟩ := occurrence
    change name = rule.name at nameEq
    subst name
    exact admitted

#print axioms ruleOccurrencesAt_mem_of_selected
#print axioms rewriteAtOccurrences_mem_of_selected
#print axioms rewriteAtOccurrences_mem_iff_selected

end Mettapedia.OSLF.Framework.PremiseAwareOccurrenceSelection
