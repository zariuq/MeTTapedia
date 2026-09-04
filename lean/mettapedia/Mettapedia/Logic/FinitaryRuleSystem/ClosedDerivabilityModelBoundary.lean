import Mettapedia.Logic.FinitaryRuleSystem.RuleHomomorphism

/-!
# Closed derivability does not determine local model transport

A conservative translation of closed derivability records agreement about
theorems.  It need not expose how primitive rules act on assumptions that are
not themselves closed theorems.  Consequently it is too weak, by itself, to
pull semantic models back.

Strict rule homomorphisms do support contravariant model transport via
`FiniteModel.reduct`.  The positive control below exercises that construction.
The adversarial control adds one latent rule with an underivable premise.  The
source and target still have exactly the same closed theorems (none), while a
target model fails to validate the latent source rule.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem.ClosedDerivabilityModelBoundary

open Mettapedia.Logic

/-- Two judgments separate an unavailable premise from its latent
consequence. -/
inductive Judgment where
  | premise
  | conclusion
deriving DecidableEq

/-- The source has one rule, but no closed way to obtain its premise. -/
inductive LatentRules : List Judgment → Judgment → Prop where
  | latent : LatentRules [.premise] .conclusion

/-- The target has no primitive rules. -/
def NoRules (_premises : List Judgment) (_conclusion : Judgment) : Prop :=
  False

/-- No judgment is derivable from the empty target rule system. -/
theorem noRules_underivable (judgment : Judgment) :
    ¬ Derives NoRules judgment := by
  intro derivation
  exact Derives.least (fun _ => False)
    (by
      intro rulePremises ruleConclusion rule _premiseResults
      exact rule)
    derivation

/-- The latent source rule also generates no closed derivations: every use of
the only rule would require a strictly smaller derivation of `premise`, but no
rule concludes it. -/
theorem latentRules_underivable (judgment : Judgment) :
    ¬ Derives LatentRules judgment := by
  intro derivation
  exact Derives.least (fun _ => False)
    (by
      intro rulePremises ruleConclusion rule premiseResults
      cases rule with
      | latent => exact premiseResults .premise (by simp))
    derivation

/-- Identity on judgments preserves closed derivability because both least
closures are empty. -/
def closedTranslation : DerivabilityTranslation LatentRules NoRules where
  mapJudgment := fun judgment => judgment
  map_derives := fun {judgment} derivation =>
    (latentRules_underivable judgment derivation).elim

/-- The same identity translation is conservative on closed derivability. -/
theorem closedTranslation_conservative : closedTranslation.Conservative :=
  fun judgment derivation => (noRules_underivable judgment derivation).elim

/-- Source and target therefore agree on every closed theorem. -/
theorem closed_derivability_agreement (judgment : Judgment) :
    Derives NoRules (closedTranslation.mapJudgment judgment) ↔
      Derives LatentRules judgment :=
  closedTranslation.derives_iff_of_conservative
    closedTranslation_conservative judgment

/-! ## Positive control: strict maps really do transport models -/

/-- A nonconstant finite model of the rule-free target. -/
def noRulesModel : FiniteModel NoRules where
  World := Unit
  worldFintype := inferInstance
  satisfies := fun _world judgment =>
    match judgment with
    | .premise => true
    | .conclusion => false
  rulesSound := by
    intro rulePremises ruleConclusion rule _world _premiseResults
    exact rule.elim

/-- Pulling back along the strict identity homomorphism produces a genuine
finite model. -/
def identityReduct : FiniteModel NoRules :=
  noRulesModel.reduct (RuleHomomorphism.id NoRules)

/-- The positive model transport preserves executable global validity
exactly. -/
theorem identityReduct_checkValid (judgment : Judgment) :
    identityReduct.checkValid judgment = noRulesModel.checkValid judgment :=
  FiniteModel.reduct_checkValid (RuleHomomorphism.id NoRules)
    noRulesModel judgment

theorem premise_is_valid_in_positive_model :
    identityReduct.checkValid .premise = true := by
  rfl

theorem conclusion_is_refuted_in_positive_model :
    identityReduct.checkValid .conclusion = false := by
  rfl

/-! ## Negative control: closed theorem agreement is insufficient -/

/-- The exact local obligation that a naive pullback along the identity
closed-derivability translation would have to discharge. -/
def TargetSatisfactionSoundForLatent : Prop :=
  ∀ rulePremises ruleConclusion,
    LatentRules rulePremises ruleConclusion →
    ∀ world : noRulesModel.World,
      (∀ rulePremise ∈ rulePremises,
        noRulesModel.satisfies world rulePremise = true) →
      noRulesModel.satisfies world ruleConclusion = true

/-- The target satisfaction relation is not sound for the latent source rule:
its premise holds while its conclusion fails. -/
theorem target_satisfaction_not_sound_for_latent :
    ¬ TargetSatisfactionSoundForLatent := by
  intro sound
  have conclusionTrue := sound [.premise] .conclusion .latent () (by
    intro rulePremise member
    simp only [List.mem_singleton] at member
    subst rulePremise
    rfl)
  change false = true at conclusionTrue
  exact Bool.noConfusion conclusionTrue

/-- There cannot be a strict rule homomorphism into a rule-free target. -/
theorem no_strict_rule_homomorphism :
    ¬ Nonempty (RuleHomomorphism LatentRules NoRules) := by
  rintro ⟨homomorphism⟩
  exact homomorphism.map_rule LatentRules.latent

/-- Main separation: exact agreement on every closed theorem does not imply
that a target model validates, or can be pulled back along, the source's
primitive rules. -/
theorem closed_theorem_agreement_does_not_imply_model_transport :
    (∀ judgment,
      Derives NoRules (closedTranslation.mapJudgment judgment) ↔
        Derives LatentRules judgment) ∧
      ¬ TargetSatisfactionSoundForLatent :=
  ⟨closed_derivability_agreement,
    target_satisfaction_not_sound_for_latent⟩

#print axioms closed_derivability_agreement
#print axioms identityReduct_checkValid
#print axioms premise_is_valid_in_positive_model
#print axioms conclusion_is_refuted_in_positive_model
#print axioms target_satisfaction_not_sound_for_latent
#print axioms no_strict_rule_homomorphism
#print axioms closed_theorem_agreement_does_not_imply_model_transport

end Mettapedia.Logic.FinitaryRuleSystem.ClosedDerivabilityModelBoundary
