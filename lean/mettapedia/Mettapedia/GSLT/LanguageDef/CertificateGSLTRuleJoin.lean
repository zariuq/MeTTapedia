import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-!
# Joins of rule theories over one language

Two rule tables over one syntax-and-judgment core amalgamate: under
disjoint rule identifiers, the appended table is the **join** of the two
theories in the rule-retaining preorder — both inject, and it refines
anything both refine.  The same universal property is packaged below as a
genuine binary coproduct (`IsColimit` of a `BinaryCofan`) in the strict
rule-retaining category.

Once the two inputs and their append are validated, the universal-property
proof is pure lookup algebra.  This fixed-core coproduct is not a colimit of
different syntax GSLTs, a universal simulator, or a formalization of the
Ruliad; those require syntax-translating interpretations and a specified
diagram.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open CategoryTheory Limits

/-- One rule table over a fixed syntax-and-judgment core. -/
def rulesDefinition (core : LanguageDef) (calculus : ProofCalculus)
    (rules : List RuleSchema) :
    CalculusLanguageDef :=
  CalculusLanguageDef.extend core { calculus with rules }

@[simp] theorem rulesDefinition_rules (core : LanguageDef)
    (calculus : ProofCalculus) (rules : List RuleSchema) :
    (rulesDefinition core calculus rules).rules = rules := rfl

/-- Rule tables with disjoint identifiers. -/
def RulesDisjoint (leftRules rightRules : List RuleSchema) : Prop :=
  ∀ leftRule ∈ leftRules, ∀ rightRule ∈ rightRules,
    leftRule.id ≠ rightRule.id

section Join

variable {core : LanguageDef} {calculus : ProofCalculus}
variable {leftRules rightRules : List RuleSchema}
variable {leftValid : (rulesDefinition core calculus leftRules).isValid = true}
variable {rightValid : (rulesDefinition core calculus rightRules).isValid = true}
variable {joinValid :
  (rulesDefinition core calculus (leftRules ++ rightRules)).isValid = true}

/-- The left theory injects into the join. -/
theorem join_refines_left :
    RuleLookupRefines
      ⟨rulesDefinition core calculus leftRules, leftValid⟩
      ⟨rulesDefinition core calculus (leftRules ++ rightRules), joinValid⟩ := by
  apply RuleLookupRefines.of_rules_eq_append rightRules
  rfl

/-- The right theory injects into the join, provided the identifiers are
disjoint: right lookups skip the whole left table. -/
theorem join_refines_right
    (disjoint : RulesDisjoint leftRules rightRules) :
    RuleLookupRefines
      ⟨rulesDefinition core calculus rightRules, rightValid⟩
      ⟨rulesDefinition core calculus (leftRules ++ rightRules), joinValid⟩ := by
  intro ruleId rule lookup
  unfold CalculusLanguageDef.lookupRule? at lookup ⊢
  simp only [rulesDefinition_rules] at lookup ⊢
  rw [List.find?_append]
  have ruleMem : rule ∈ rightRules := List.mem_of_find?_eq_some lookup
  have ruleId_eq : rule.id = ruleId := by
    have := List.find?_some lookup
    simpa using this
  have leftMiss : leftRules.find?
      (fun candidate => decide (candidate.id = ruleId)) = none := by
    apply List.find?_eq_none.mpr
    intro leftRule leftMem
    simp only [decide_eq_true_eq]
    intro collide
    exact disjoint leftRule leftMem rule ruleMem (by rw [collide, ruleId_eq])
  rw [leftMiss, Option.none_or]
  exact lookup

/-- The join is a least upper bound: any theory refined by both components
is refined by the join.  With the two injections, appended disjoint rule
tables are binary joins in the rule-retaining preorder. -/
theorem join_refines_of_both {other : ValidatedCalculusLanguageDef}
    (fromLeft : RuleLookupRefines
      ⟨rulesDefinition core calculus leftRules, leftValid⟩ other)
    (fromRight : RuleLookupRefines
      ⟨rulesDefinition core calculus rightRules, rightValid⟩ other) :
    RuleLookupRefines
      ⟨rulesDefinition core calculus (leftRules ++ rightRules), joinValid⟩ other := by
  intro ruleId rule lookup
  unfold CalculusLanguageDef.lookupRule? at lookup
  simp only [rulesDefinition_rules, List.find?_append] at lookup
  cases leftLookup : leftRules.find?
      (fun candidate => decide (candidate.id = ruleId)) with
  | some found =>
      rw [leftLookup] at lookup
      simp only [Option.some_or, Option.some.injEq] at lookup
      subst lookup
      exact fromLeft ruleId found leftLookup
  | none =>
      rw [leftLookup, Option.none_or] at lookup
      exact fromRight ruleId rule lookup

/-! ## The join as arrows of the strict category -/

/-- Left injection as a strict certificate-GSLT arrow. -/
def joinLeftArrow :
    RuleRetaining.ofDefinition
        ⟨rulesDefinition core calculus leftRules, leftValid⟩ ⟶
      RuleRetaining.ofDefinition
        ⟨rulesDefinition core calculus (leftRules ++ rightRules), joinValid⟩ :=
  ⟨join_refines_left⟩

/-- Right injection as a strict certificate-GSLT arrow. -/
def joinRightArrow (disjoint : RulesDisjoint leftRules rightRules) :
    RuleRetaining.ofDefinition
        ⟨rulesDefinition core calculus rightRules, rightValid⟩ ⟶
      RuleRetaining.ofDefinition
        ⟨rulesDefinition core calculus (leftRules ++ rightRules), joinValid⟩ :=
  ⟨join_refines_right disjoint⟩

/-- The universal arrow out of the join. -/
def joinDescendArrow {other : ValidatedCalculusLanguageDef}
    (fromLeft : RuleLookupRefines
      ⟨rulesDefinition core calculus leftRules, leftValid⟩ other)
    (fromRight : RuleLookupRefines
      ⟨rulesDefinition core calculus rightRules, rightValid⟩ other) :
    RuleRetaining.ofDefinition
        ⟨rulesDefinition core calculus (leftRules ++ rightRules), joinValid⟩ ⟶
      RuleRetaining.ofDefinition other :=
  ⟨join_refines_of_both fromLeft fromRight⟩

/-! ## Exact categorical universal property -/

/-- The two strict injections as a binary cofan. -/
def joinCofan (disjoint : RulesDisjoint leftRules rightRules) :
    BinaryCofan
      (RuleRetaining.ofDefinition
        ⟨rulesDefinition core calculus leftRules, leftValid⟩)
      (RuleRetaining.ofDefinition
        ⟨rulesDefinition core calculus rightRules, rightValid⟩) :=
  BinaryCofan.mk
    (joinLeftArrow (core := core) (leftRules := leftRules)
      (rightRules := rightRules) (leftValid := leftValid)
      (joinValid := joinValid))
    (joinRightArrow (core := core) (leftRules := leftRules)
      (rightRules := rightRules) (rightValid := rightValid)
      (joinValid := joinValid) disjoint)

/-- Appending validated identifier-disjoint rule tables over one core is a
binary coproduct in the strict rule-retaining category. -/
def joinCofanIsColimit (disjoint : RulesDisjoint leftRules rightRules) :
    IsColimit (joinCofan (leftValid := leftValid)
      (rightValid := rightValid) (joinValid := joinValid) disjoint) :=
  BinaryCofan.IsColimit.mk
    (joinCofan (leftValid := leftValid) (rightValid := rightValid)
      (joinValid := joinValid) disjoint)
    (fun fromLeft fromRight =>
      joinDescendArrow (leftValid := leftValid) (rightValid := rightValid)
        (joinValid := joinValid) fromLeft.refines fromRight.refines)
    (fun _ _ => RuleRetaining.hom_ext _ _)
    (fun _ _ => RuleRetaining.hom_ext _ _)
    (fun _ _ _ _ _ => RuleRetaining.hom_ext _ _)

end Join

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
