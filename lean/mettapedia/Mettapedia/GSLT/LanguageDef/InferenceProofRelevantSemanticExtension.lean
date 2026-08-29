import Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension

/-!
# Proof-relevant semantics of calculus-language extensions

The proposition-valued semantic extension proves that every checked goal is
true in an independent semantics.  Relational hypotheses, proof programs, and
execution receipts need the stronger result: a checked derivation constructs
an inhabitant of a `Type`-valued semantic fibre, with the ordered evidence for
every premise retained.

This module supplies that interpretation without changing the generic checker.
A calculus-language semantics interprets one rule application from an indexed list
of premise meanings.  A semantic extension separately interprets retained base
rules and genuinely added rules.  The target definition then receives one
compositional proof-relevant semantics.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
open Mettapedia.GSLT.LanguageDef.InferenceSemanticExtension

universe uMeaning uFirstMeaning uSecondMeaning

/-! ## Ordered dependent premise evidence -/

/-- Evidence for an ordered list of semantic fibres.  Unlike a proposition
indexed by list membership, this retains each occurrence and its exact slot. -/
inductive EvidenceList (Meaning : Pattern → Type uMeaning) :
    List Pattern → Type uMeaning where
  | nil : EvidenceList Meaning []
  | cons {premise : Pattern} {premises : List Pattern}
      (head : Meaning premise) (tail : EvidenceList Meaning premises) :
      EvidenceList Meaning (premise :: premises)

namespace EvidenceList

/-- Pointwise transport of an ordered evidence list.  Source and target
fibres may live in different universes; extending a hosted calculus by a
proof-relevant judgment commonly raises the semantic universe. -/
def map {First : Pattern → Type uFirstMeaning}
    {Second : Pattern → Type uSecondMeaning}
    (transform : ∀ pattern, First pattern → Second pattern) :
    {patterns : List Pattern} → EvidenceList First patterns →
      EvidenceList Second patterns
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons (transform _ head) (map transform tail)

@[simp] theorem map_nil {First : Pattern → Type uFirstMeaning}
    {Second : Pattern → Type uSecondMeaning}
    (transform : ∀ pattern, First pattern → Second pattern) :
    map transform (.nil : EvidenceList First []) = .nil :=
  rfl

@[simp] theorem map_cons {First : Pattern → Type uFirstMeaning}
    {Second : Pattern → Type uSecondMeaning}
    (transform : ∀ pattern, First pattern → Second pattern)
    {premise : Pattern} {premises : List Pattern}
    (head : First premise) (tail : EvidenceList First premises) :
    map transform (.cons head tail) =
      .cons (transform premise head) (map transform tail) :=
  rfl

end EvidenceList

/-! ## Proof-relevant interpretation -/

/-- A compositional proof-relevant interpretation of one validated calculus
language. -/
structure CalculusLanguageSemantics (definition : ValidatedCalculusLanguageDef)
    (Meaning : Pattern → Type uMeaning) where
  ruleMeaning : ∀ {ruleInstance premises conclusion},
    RuleApplication definition ruleInstance premises conclusion →
      EvidenceList Meaning premises → Meaning conclusion

namespace CalculusLanguageSemantics

mutual

/-- Interpret a checked derivation into its exact semantic fibre. -/
def interpret {definition : ValidatedCalculusLanguageDef}
    {Meaning : Pattern → Type uMeaning}
    (semantics : CalculusLanguageSemantics definition Meaning) :
    {goal : Pattern} → Derivation definition goal → Meaning goal
  | _, .byRule _ application children =>
      semantics.ruleMeaning application (interpretList semantics children)

/-- Interpret ordered child derivations without quotienting occurrences. -/
def interpretList {definition : ValidatedCalculusLanguageDef}
    {Meaning : Pattern → Type uMeaning}
    (semantics : CalculusLanguageSemantics definition Meaning) :
    {premises : List Pattern} → DerivationList definition premises →
      EvidenceList Meaning premises
  | [], .nil => .nil
  | _ :: _, .cons head tail =>
      .cons (interpret semantics head) (interpretList semantics tail)

end

end CalculusLanguageSemantics

/-! ## Semantic extension -/

/-- Independent proof-relevant semantics for a validated calculus-language
extension.  Added rules receive meanings only after structural validation has
identified the exact stored schema and its instantiated ordered premises. -/
structure SemanticExtension (base : ValidatedCalculusLanguageDef)
    (extension : ValidatedCalculusLanguageExtension base)
    (Meaning : Pattern → Type uMeaning) where
  baseSemantics : CalculusLanguageSemantics base Meaning
  addedRuleMeaning : ∀ (rule : RuleSchema),
    rule ∈ extension.extension.newRules →
      ∀ (ruleInstance : RuleInstance) (premises : List Pattern)
        (conclusion : Pattern),
        extension.target.1.lookupRule? ruleInstance.ruleId = some rule →
        RuleApplication extension.target ruleInstance premises conclusion →
        EvidenceList Meaning premises → Meaning conclusion

namespace SemanticExtension

variable {base : ValidatedCalculusLanguageDef}
variable {extension : ValidatedCalculusLanguageExtension base}
variable {Meaning : Pattern → Type uMeaning}

/-- Interpret every target rule by classifying it as a retained base rule or
an exact member of the extension delta. -/
noncomputable def targetRuleMeaning
    (self : SemanticExtension base extension Meaning) :
    ∀ {ruleInstance premises conclusion},
      RuleApplication extension.target ruleInstance premises conclusion →
        EvidenceList Meaning premises → Meaning conclusion := by
  intro ruleInstance premises conclusion application premiseEvidence
  classical
  by_cases baseApplication :
      RuleApplication base ruleInstance premises conclusion
  · exact self.baseSemantics.ruleMeaning baseApplication premiseEvidence
  · have addedApplication :
        ∃ rule,
          rule ∈ extension.extension.newRules ∧
            extension.target.1.lookupRule? ruleInstance.ruleId = some rule := by
      rcases
          InferenceSemanticExtension.SemanticExtension.target_application_classifies
            application with retained | added
      · exact False.elim (baseApplication retained)
      · exact added
    cases targetLookup : extension.target.1.lookupRule? ruleInstance.ruleId with
    | none =>
        have impossible : False := by
          rcases addedApplication with ⟨rule, _, lookup⟩
          rw [targetLookup] at lookup
          contradiction
        exact False.elim impossible
    | some rule =>
        have memberAdded : rule ∈ extension.extension.newRules := by
          rcases addedApplication with ⟨addedRule, member, lookup⟩
          rw [targetLookup] at lookup
          cases Option.some.inj lookup
          exact member
        exact self.addedRuleMeaning rule memberAdded ruleInstance premises
          conclusion targetLookup application premiseEvidence

/-- The composite calculus language inherits one proof-relevant semantics. -/
noncomputable def targetSemantics
    (self : SemanticExtension base extension Meaning) :
    CalculusLanguageSemantics extension.target Meaning where
  ruleMeaning := self.targetRuleMeaning

/-- A checked target derivation constructs semantic evidence; checking alone
does not supply the interpretation of newly learned rules. -/
noncomputable def interpret
    (self : SemanticExtension base extension Meaning)
    {goal : Pattern} (derivation : Derivation extension.target goal) :
    Meaning goal :=
  self.targetSemantics.interpret derivation

/-- Old derivations retain their exact raw artifact while acquiring target
semantic evidence through the validated extension. -/
noncomputable def interpretTransported
    (self : SemanticExtension base extension Meaning)
    {goal : Pattern} (derivation : Derivation base goal) :
    Meaning goal :=
  self.interpret (extension.transport derivation)

@[simp] theorem transported_erasure
    (_self : SemanticExtension base extension Meaning)
    {goal : Pattern} (derivation : Derivation base goal) :
    (extension.transport derivation).erase = derivation.erase :=
  Derivation.erase_transport extension.refines derivation

/-- Negative control: if one checked target derivation lands in an empty
semantic fibre, no proof-relevant semantic extension can exist.  Structural
validation cannot manufacture an inhabitant of that fibre. -/
theorem no_semantic_extension_of_empty_fibre
    {goal : Pattern} (derivation : Derivation extension.target goal)
    (empty : Meaning goal → False) :
    ¬ Nonempty (SemanticExtension base extension Meaning) := by
  rintro ⟨semanticExtension⟩
  exact empty (semanticExtension.interpret derivation)

end SemanticExtension

#print axioms CalculusLanguageSemantics.interpret
#print axioms CalculusLanguageSemantics.interpretList
#print axioms SemanticExtension.targetSemantics
#print axioms SemanticExtension.interpretTransported
#print axioms SemanticExtension.transported_erasure
#print axioms SemanticExtension.no_semantic_extension_of_empty_fibre

end Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
