import Mettapedia.OSLF.Framework.PremiseAwareOccurrenceSelection
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Forward transport of exact engine occurrences across a presentation map

A structural map retains authored declarations but does not by itself retain
their list positions or executable alternatives. The theorem below makes
those two missing operational laws explicit: an index map selects each
translated rule in the target list, and the premise-aware engine returns the
mapped ordered alternatives for that rule at the selected source and fuel.
Under those laws every admitted source occurrence maps to an admitted target
occurrence, with its local alternative index retained. Target-only rules may
fire, so no surjectivity or whole-GSLT exactness is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.EngineOccurrenceStructuralTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrenceSelection
open Mettapedia.GSLT.LanguageDef

/-- Translate the parts of an engine occurrence that have an authored
structural action, and translate its local rule position using an explicitly
supplied positional map. Alternative position is preserved only when the
ordered-alternatives law below is proved. -/
def mapOccurrence (symbols : LanguageDefSymbolMap)
    (mapRuleIndex : Nat → Nat) (occurrence : RewriteOccurrence) :
    RewriteOccurrence :=
  { ruleIndex := mapRuleIndex occurrence.ruleIndex
    ruleName := symbols.rewrite occurrence.ruleName
    alternativeIndex := occurrence.alternativeIndex
    target := mapPattern symbols occurrence.target }

@[simp] theorem mapOccurrence_alternativeIndex
    (symbols : LanguageDefSymbolMap) (mapRuleIndex : Nat → Nat)
    (occurrence : RewriteOccurrence) :
    (mapOccurrence symbols mapRuleIndex occurrence).alternativeIndex =
      occurrence.alternativeIndex := rfl

@[simp] theorem mapOccurrence_target
    (symbols : LanguageDefSymbolMap) (mapRuleIndex : Nat → Nat)
    (occurrence : RewriteOccurrence) :
    (mapOccurrence symbols mapRuleIndex occurrence).target =
      mapPattern symbols occurrence.target := rfl

/-- A selected source event survives a presentation change when its actual
rule position and the complete ordered alternative list are transported.
This is a one-way comparison: extra target rules may introduce new events. -/
theorem mapOccurrence_admitted
    (firstBase secondBase : BasePremiseEvaluator)
    (firstLanguage secondLanguage : LanguageDef)
    (symbols : LanguageDefSymbolMap) (mapRuleIndex : Nat → Nat)
    (recursiveFuel : Nat) (source : Pattern)
    (rulesAligned : ∀ (index : Nat) (rule : RewriteRule),
      firstLanguage.rewrites[index]? = some rule →
        secondLanguage.rewrites[mapRuleIndex index]? =
          some (mapRewriteRule symbols rule))
    (alternativesAligned : ∀ (index : Nat) (rule : RewriteRule),
      firstLanguage.rewrites[index]? = some rule →
        applyRuleUsing secondBase secondLanguage
            (rewriteAt secondBase secondLanguage recursiveFuel)
            (mapRewriteRule symbols rule) (mapPattern symbols source) =
          (applyRuleUsing firstBase firstLanguage
            (rewriteAt firstBase firstLanguage recursiveFuel) rule source).map
              (mapPattern symbols))
    (occurrence : RewriteOccurrence)
    (admitted : occurrence ∈ rewriteAtOccurrences firstBase firstLanguage
      (recursiveFuel + 1) source) :
    mapOccurrence symbols mapRuleIndex occurrence ∈
      rewriteAtOccurrences secondBase secondLanguage (recursiveFuel + 1)
        (mapPattern symbols source) := by
  obtain ⟨rule, ruleAt, nameEq, selected⟩ :=
    (rewriteAtOccurrences_mem_iff_selected firstBase firstLanguage
      recursiveFuel source occurrence).mp admitted
  have mappedRuleAt := rulesAligned occurrence.ruleIndex rule ruleAt
  have mappedSelected :
      (applyRuleUsing secondBase secondLanguage
        (rewriteAt secondBase secondLanguage recursiveFuel)
        (mapRewriteRule symbols rule) (mapPattern symbols source))[occurrence.alternativeIndex]? =
        some (mapPattern symbols occurrence.target) := by
    rw [alternativesAligned occurrence.ruleIndex rule ruleAt]
    simpa using congrArg (Option.map (mapPattern symbols)) selected
  have targetAdmitted := rewriteAtOccurrences_mem_of_selected secondBase
    secondLanguage recursiveFuel (mapPattern symbols source)
    (mapPattern symbols occurrence.target) (mapRuleIndex occurrence.ruleIndex)
    occurrence.alternativeIndex (mapRewriteRule symbols rule) mappedRuleAt
    mappedSelected
  simpa [mapOccurrence, mapRewriteRule, nameEq] using targetAdmitted

#print axioms mapOccurrence_admitted

end Mettapedia.OSLF.Framework.EngineOccurrenceStructuralTransport
