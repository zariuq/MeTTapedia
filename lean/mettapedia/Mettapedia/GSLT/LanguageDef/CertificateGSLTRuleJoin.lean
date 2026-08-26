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
def rulesPresentation (core : LanguageDef) (calculus : ProofCalculus)
    (rules : List RuleSchema) :
    Presentation :=
  { language := core, calculus := { calculus with rules } }

@[simp] theorem rulesPresentation_rules (core : LanguageDef)
    (calculus : ProofCalculus) (rules : List RuleSchema) :
    (rulesPresentation core calculus rules).rules = rules := rfl

/-- Rule tables with disjoint identifiers. -/
def RulesDisjoint (leftRules rightRules : List RuleSchema) : Prop :=
  ∀ leftRule ∈ leftRules, ∀ rightRule ∈ rightRules,
    leftRule.id ≠ rightRule.id

section Join

variable {core : LanguageDef} {calculus : ProofCalculus}
variable {leftRules rightRules : List RuleSchema}
variable {leftValid : (rulesPresentation core calculus leftRules).isValidV2 = true}
variable {rightValid : (rulesPresentation core calculus rightRules).isValidV2 = true}
variable {joinValid :
  (rulesPresentation core calculus (leftRules ++ rightRules)).isValidV2 = true}

/-- The left theory injects into the join. -/
theorem join_refines_left :
    RuleLookupRefines
      ⟨rulesPresentation core calculus leftRules, leftValid⟩
      ⟨rulesPresentation core calculus (leftRules ++ rightRules), joinValid⟩ := by
  apply RuleLookupRefines.of_rules_eq_append rightRules
  rfl

/-- The right theory injects into the join, provided the identifiers are
disjoint: right lookups skip the whole left table. -/
theorem join_refines_right
    (disjoint : RulesDisjoint leftRules rightRules) :
    RuleLookupRefines
      ⟨rulesPresentation core calculus rightRules, rightValid⟩
      ⟨rulesPresentation core calculus (leftRules ++ rightRules), joinValid⟩ := by
  intro ruleId rule lookup
  unfold Presentation.lookupRule? at lookup ⊢
  simp only [rulesPresentation_rules] at lookup ⊢
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
theorem join_refines_of_both {other : ValidatedPresentation}
    (fromLeft : RuleLookupRefines
      ⟨rulesPresentation core calculus leftRules, leftValid⟩ other)
    (fromRight : RuleLookupRefines
      ⟨rulesPresentation core calculus rightRules, rightValid⟩ other) :
    RuleLookupRefines
      ⟨rulesPresentation core calculus (leftRules ++ rightRules), joinValid⟩ other := by
  intro ruleId rule lookup
  unfold Presentation.lookupRule? at lookup
  simp only [rulesPresentation_rules, List.find?_append] at lookup
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
    RuleRetaining.ofPresentation
        ⟨rulesPresentation core calculus leftRules, leftValid⟩ ⟶
      RuleRetaining.ofPresentation
        ⟨rulesPresentation core calculus (leftRules ++ rightRules), joinValid⟩ :=
  ⟨join_refines_left⟩

/-- Right injection as a strict certificate-GSLT arrow. -/
def joinRightArrow (disjoint : RulesDisjoint leftRules rightRules) :
    RuleRetaining.ofPresentation
        ⟨rulesPresentation core calculus rightRules, rightValid⟩ ⟶
      RuleRetaining.ofPresentation
        ⟨rulesPresentation core calculus (leftRules ++ rightRules), joinValid⟩ :=
  ⟨join_refines_right disjoint⟩

/-- The universal arrow out of the join. -/
def joinDescendArrow {other : ValidatedPresentation}
    (fromLeft : RuleLookupRefines
      ⟨rulesPresentation core calculus leftRules, leftValid⟩ other)
    (fromRight : RuleLookupRefines
      ⟨rulesPresentation core calculus rightRules, rightValid⟩ other) :
    RuleRetaining.ofPresentation
        ⟨rulesPresentation core calculus (leftRules ++ rightRules), joinValid⟩ ⟶
      RuleRetaining.ofPresentation other :=
  ⟨join_refines_of_both fromLeft fromRight⟩

/-! ## Exact categorical universal property -/

/-- The two strict injections as a binary cofan. -/
def joinCofan (disjoint : RulesDisjoint leftRules rightRules) :
    BinaryCofan
      (RuleRetaining.ofPresentation
        ⟨rulesPresentation core calculus leftRules, leftValid⟩)
      (RuleRetaining.ofPresentation
        ⟨rulesPresentation core calculus rightRules, rightValid⟩) :=
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
