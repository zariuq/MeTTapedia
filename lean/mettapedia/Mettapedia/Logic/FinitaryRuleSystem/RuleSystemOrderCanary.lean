import Mettapedia.Logic.FinitaryRuleSystem.RuleSystemOrder

/-!
# The rule-system comparison orders are genuinely different

The source has one nullary theorem rule and one redundant unary identity rule.
The target has only the nullary theorem rule.  Their single closed theorem is
the same, so a conservative closed-derivability translation exists.  No strict
rule homomorphism exists because the redundant unary primitive has no target
primitive of the same ordered premise shape.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem.RuleSystemOrderCanary

open Mettapedia.Logic

inductive SourceRules : List Unit → Unit → Prop where
  | axiom : SourceRules [] ()
  | redundant : SourceRules [()] ()

def TargetRules (premises : List Unit) (conclusion : Unit) : Prop :=
  premises = [] ∧ conclusion = ()

def sourceSystem : System where
  Judgment := Unit
  rules := SourceRules

def targetSystem : System where
  Judgment := Unit
  rules := TargetRules

theorem source_derives_unit : Derives SourceRules () := by
  exact Derives.node [] () .axiom (by simp)

theorem target_derives_unit : Derives TargetRules () := by
  exact Derives.node [] () ⟨rfl, rfl⟩ (by simp)

/-- Both systems have the same only possible closed theorem. -/
def closedTranslation :
    DerivabilityTranslation SourceRules TargetRules where
  mapJudgment := fun _ => ()
  map_derives := fun _derivation => target_derives_unit

theorem closedTranslation_conservative : closedTranslation.Conservative :=
  fun _judgment _targetDerivation => source_derives_unit

/-- Positive control: the target conservatively simulates source closed
derivability. -/
theorem target_conservatively_simulates_source :
    ConservativelyDerivabilitySimulates targetSystem sourceSystem :=
  ⟨closedTranslation, closedTranslation_conservative⟩

/-- The source's redundant unary primitive cannot map to the target's only
nullary primitive. -/
theorem no_strict_rule_homomorphism :
    ¬ Nonempty (RuleHomomorphism SourceRules TargetRules) := by
  rintro ⟨homomorphism⟩
  have translated := homomorphism.map_rule SourceRules.redundant
  change [homomorphism.mapJudgment ()] = [] ∧
    homomorphism.mapJudgment () = () at translated
  cases translated.1

/-- Negative control: conservative agreement on all closed theorems does not
imply strict agreement of primitive rule structure. -/
theorem target_not_strictly_simulates_source :
    ¬ StrictRuleSimulates targetSystem sourceSystem :=
  no_strict_rule_homomorphism

end Mettapedia.Logic.FinitaryRuleSystem.RuleSystemOrderCanary
