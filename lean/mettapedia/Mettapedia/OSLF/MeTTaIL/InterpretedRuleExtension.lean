import Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep

/-!
# Rule extension for interpreted conditional rewriting

An interpreted reduction may inspect the whole language when matching,
instantiating, or evaluating non-recursive premises. Inclusion of rule lists
alone therefore does not preserve derivations. Under explicit stability of
those operations, rule inclusion transports every finite conditional
derivation, including recursively used congruence premises.
-/

namespace Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)

set_option autoImplicit false

/-- A bounded interpreted derivation survives rule-list extension when its
matching, instantiation, and base-premise semantics remain stable. -/
theorem StepAt.mono_language
    {interpretation : RuleInterpretation}
    {base : BasePremiseEvaluator}
    {lang₁ lang₂ : LanguageDef}
    (rulesMono : ∀ rule, rule ∈ lang₁.rewrites → rule ∈ lang₂.rewrites)
    (matchStable : ∀ rule source,
      interpretation.matchRule lang₁ rule source =
        interpretation.matchRule lang₂ rule source)
    (instantiateStable : ∀ rule bindings,
      interpretation.instantiateRule lang₁ rule bindings =
        interpretation.instantiateRule lang₂ rule bindings)
    (baseMono : ∀ bindings premise result,
      result ∈ base lang₁ bindings premise →
        result ∈ base lang₂ bindings premise)
    {fuel : Nat} {source target : Pattern}
    (evidence : StepAt interpretation base lang₁ fuel source target) :
    StepAt interpretation base lang₂ fuel source target := by
  induction fuel generalizing source target with
  | zero => cases evidence
  | succ fuel inductionHypothesis =>
      have premiseMono :
          ∀ {initial final : Bindings} {premise : Premise},
            PremiseAt interpretation base lang₁ fuel
                initial premise final →
              PremiseAt interpretation base lang₂ fuel
                initial premise final := by
        intro initial final premise premiseEvidence
        cases premiseEvidence with
        | freshness member => exact .freshness (baseMono _ _ _ member)
        | relationQuery member => exact .relationQuery (baseMono _ _ _ member)
        | forAll member => exact .forAll (baseMono _ _ _ member)
        | congruence recursive matched merged =>
            exact .congruence (inductionHypothesis recursive) matched merged
        | scopedRoot empty recursive matched merged =>
            exact .scopedRoot empty (inductionHypothesis recursive) matched merged
      have premisesMono :
          ∀ {initial final : Bindings} {premises : List Premise},
            PremisesAt interpretation base lang₁ fuel
                initial premises final →
              PremisesAt interpretation base lang₂ fuel
                initial premises final := by
        intro initial final premises premiseEvidence
        induction premises generalizing initial final with
        | nil =>
            cases premiseEvidence
            exact .nil initial
        | cons premise premises inductionHypothesis =>
            cases premiseEvidence with
            | cons first rest =>
                exact .cons (premiseMono first) (inductionHypothesis rest)
      cases evidence with
      | @rule stepFuel stepSource stepTarget authoredRule initialBindings
          finalBindings ruleMember matched premises targetEq =>
          have matched₂ : initialBindings ∈
              interpretation.matchRule lang₂ authoredRule source := by
            simpa only [← matchStable authoredRule source] using matched
          have targetEq₂ :
              interpretation.instantiateRule lang₂ authoredRule finalBindings =
                target := by
            simpa only [← instantiateStable authoredRule finalBindings] using targetEq
          exact .rule (rulesMono _ ruleMember) matched₂
            (premisesMono premises) targetEq₂

/-- Rule extension preserves the least finite interpreted relation under the
same explicit semantic-stability hypotheses. -/
theorem Step.mono_language
    {interpretation : RuleInterpretation}
    {base : BasePremiseEvaluator}
    {lang₁ lang₂ : LanguageDef}
    (rulesMono : ∀ rule, rule ∈ lang₁.rewrites → rule ∈ lang₂.rewrites)
    (matchStable : ∀ rule source,
      interpretation.matchRule lang₁ rule source =
        interpretation.matchRule lang₂ rule source)
    (instantiateStable : ∀ rule bindings,
      interpretation.instantiateRule lang₁ rule bindings =
        interpretation.instantiateRule lang₂ rule bindings)
    (baseMono : ∀ bindings premise result,
      result ∈ base lang₁ bindings premise →
        result ∈ base lang₂ bindings premise)
    {source target : Pattern}
    (evidence : Step interpretation base lang₁ source target) :
    Step interpretation base lang₂ source target := by
  obtain ⟨fuel, bounded⟩ := evidence
  exact ⟨fuel, bounded.mono_language rulesMono matchStable
    instantiateStable baseMono⟩

end Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
