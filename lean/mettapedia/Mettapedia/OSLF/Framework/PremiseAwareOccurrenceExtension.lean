import Mettapedia.OSLF.Framework.PremiseAwareOccurrence

/-!
# Occurrence transport under an execution-preserving rule prefix

A rule's local index is a position in the current authored rule list, not a
stable identifier across presentations. When an added first rule is inert at
one request and every old rule has the same ordered executable alternatives
at that request, the actual finite-fuel occurrence list transports by
incrementing each old rule position. The hypotheses are stated at the
premise-aware engine boundary; they must be proved for each proposed theory
change, and cannot be inferred from rule-list inclusion alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.PremiseAwareOccurrenceExtension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence

/-- Preserve an occurrence's authored rule name, selected alternative, and
target while accounting for one newly inserted rule position. -/
def shiftRuleIndex (occurrence : RewriteOccurrence) : RewriteOccurrence :=
  { occurrence with ruleIndex := occurrence.ruleIndex + 1 }

@[simp] theorem shiftRuleIndex_target (occurrence : RewriteOccurrence) :
    (shiftRuleIndex occurrence).target = occurrence.target := rfl

@[simp] theorem shiftRuleIndex_ruleName (occurrence : RewriteOccurrence) :
    (shiftRuleIndex occurrence).ruleName = occurrence.ruleName := rfl

@[simp] theorem shiftRuleIndex_alternativeIndex
    (occurrence : RewriteOccurrence) :
    (shiftRuleIndex occurrence).alternativeIndex =
      occurrence.alternativeIndex := rfl

/-- Renumbering does not merge two previously distinct occurrences. -/
theorem shiftRuleIndex_injective : Function.Injective shiftRuleIndex := by
  intro first second equal
  rcases first with ⟨firstIndex, firstName, firstAlternative, firstTarget⟩
  rcases second with ⟨secondIndex, secondName, secondAlternative, secondTarget⟩
  have indexEqual : firstIndex = secondIndex := by
    have shifted := congrArg RewriteOccurrence.ruleIndex equal
    dsimp [shiftRuleIndex] at shifted
    omega
  have nameEqual := congrArg RewriteOccurrence.ruleName equal
  have alternativeEqual := congrArg RewriteOccurrence.alternativeIndex equal
  have targetEqual := congrArg RewriteOccurrence.target equal
  dsimp [shiftRuleIndex] at nameEqual alternativeEqual targetEqual
  simp [indexEqual, nameEqual, alternativeEqual, targetEqual]

/-- A rule's occurrence list shifts exactly when its ordered executable
alternatives agree in the two presentations at this recursive fuel. -/
theorem ruleOccurrencesAt_shift
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (recursiveFuel ruleIndex : Nat) (rule : RewriteRule) (source : Pattern)
    (sameAlternatives :
      applyRuleUsing secondBase secondLanguage
          (rewriteAt secondBase secondLanguage recursiveFuel) rule source =
        applyRuleUsing firstBase firstLanguage
          (rewriteAt firstBase firstLanguage recursiveFuel) rule source) :
    ruleOccurrencesAt secondBase secondLanguage recursiveFuel
        (ruleIndex + 1) rule source =
      (ruleOccurrencesAt firstBase firstLanguage recursiveFuel
        ruleIndex rule source).map shiftRuleIndex := by
  simp [ruleOccurrencesAt, sameAlternatives, shiftRuleIndex,
    List.map_map, Function.comp_def]

/-- Ordered rule-list traversal commutes with shifting all retained local
indices. This preserves duplicate alternatives and their exact positions. -/
theorem rewriteOccurrencesFromAt_shift
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (recursiveFuel : Nat) (rules : List RewriteRule) (source : Pattern)
    (sameAlternatives : ∀ rule ∈ rules,
      applyRuleUsing secondBase secondLanguage
          (rewriteAt secondBase secondLanguage recursiveFuel) rule source =
        applyRuleUsing firstBase firstLanguage
          (rewriteAt firstBase firstLanguage recursiveFuel) rule source) :
    ∀ ruleIndex,
      rewriteOccurrencesFromAt secondBase secondLanguage recursiveFuel
          (ruleIndex + 1) rules source =
        (rewriteOccurrencesFromAt firstBase firstLanguage recursiveFuel
          ruleIndex rules source).map shiftRuleIndex := by
  intro ruleIndex
  induction rules generalizing ruleIndex with
  | nil => rfl
  | cons rule rest inductionHypothesis =>
      have headAgreement := sameAlternatives rule (by simp)
      have tailAgreement : ∀ later ∈ rest,
          applyRuleUsing secondBase secondLanguage
              (rewriteAt secondBase secondLanguage recursiveFuel) later source =
            applyRuleUsing firstBase firstLanguage
              (rewriteAt firstBase firstLanguage recursiveFuel) later source := by
        intro later member
        exact sameAlternatives later (List.mem_cons_of_mem rule member)
      have head := ruleOccurrencesAt_shift firstBase secondBase
        firstLanguage secondLanguage recursiveFuel ruleIndex rule source
        headAgreement
      have tail := inductionHypothesis tailAgreement (ruleIndex + 1)
      simp only [rewriteOccurrencesFromAt, List.map_append]
      rw [head, tail]

/-- An inert first rule induces a source-faithful transport of every old
finite-fuel occurrence when each old rule's ordered alternatives agree.
Rule-list inclusion by itself is intentionally insufficient. -/
theorem rewriteAtOccurrences_prefix_shift
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (recursiveFuel : Nat) (addedRule : RewriteRule) (source : Pattern)
    (ruleList : secondLanguage.rewrites = addedRule :: firstLanguage.rewrites)
    (prefixInert :
      applyRuleUsing secondBase secondLanguage
        (rewriteAt secondBase secondLanguage recursiveFuel) addedRule source = [])
    (oldAlternatives : ∀ rule ∈ firstLanguage.rewrites,
      applyRuleUsing secondBase secondLanguage
          (rewriteAt secondBase secondLanguage recursiveFuel) rule source =
        applyRuleUsing firstBase firstLanguage
          (rewriteAt firstBase firstLanguage recursiveFuel) rule source) :
    rewriteAtOccurrences secondBase secondLanguage
        (recursiveFuel + 1) source =
      (rewriteAtOccurrences firstBase firstLanguage
        (recursiveFuel + 1) source).map shiftRuleIndex := by
  change rewriteOccurrencesFromAt secondBase secondLanguage recursiveFuel 0
      secondLanguage.rewrites source =
    (rewriteOccurrencesFromAt firstBase firstLanguage recursiveFuel 0
      firstLanguage.rewrites source).map shiftRuleIndex
  rw [ruleList]
  have firstEmpty : ruleOccurrencesAt secondBase secondLanguage recursiveFuel
      0 addedRule source = [] := by
    simp [ruleOccurrencesAt, prefixInert]
  rw [rewriteOccurrencesFromAt, firstEmpty, List.nil_append]
  exact rewriteOccurrencesFromAt_shift firstBase secondBase
    firstLanguage secondLanguage recursiveFuel firstLanguage.rewrites source
    oldAlternatives 0

#print axioms rewriteOccurrencesFromAt_shift
#print axioms rewriteAtOccurrences_prefix_shift
#print axioms shiftRuleIndex_injective

end Mettapedia.OSLF.Framework.PremiseAwareOccurrenceExtension
