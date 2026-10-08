import Mettapedia.GSLT.Dedukti.Typing

/-!
# Conversion under substitution, and uniqueness of types

The existing lifting and substitution of λΠ terms had no commutation laws.
This module proves the ones that a calculus with declared rules needs
(`lift_lift`, `lift_subst`, `subst_subst`, and the two laws for the
instantiation of pattern variables), and draws two consequences.

* **Steps and conversion are stable under substitution** (`Step.subst`,
  `Conv.subst`), for every theory whose definitions are closed.  A beta redex
  stays a beta redex by `subst_subst`; an instance of a declared rule stays an
  instance by `subst_instantiate`, with no condition on the rule.
* **Uniqueness of types** (`HasType.unique`): in a functional system, two
  types of one term in one context are convertible.

## Where the hypotheses of uniqueness are used

* **Confluence**, with rules headed by constants: to compare the sorts of the
  two formations of a product (`Conv.srt_injective`), and to pass from the
  two types of a function to its two codomains (`Conv.pi_injective`).
* **Functionality** of the product rules: two rules with the same premises
  have the same conclusion.  The axioms are functional by construction.
* **Closed definitions**: for conversion to be stable under substitution.

Negative: without functionality a product has two sorts
(`Example.nonFunctional_two_sorts`), which under confluence are not
convertible.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## Commutation of lifting and substitution -/

/-- Two lifts at one cutoff are one lift. -/
theorem lift_lift_same (term : Term) :
    ∀ (first second cutoff : Nat),
      lift first cutoff (lift second cutoff term) = lift (first + second) cutoff term := by
  induction term with
  | var index =>
      intro first second cutoff
      by_cases below : index < cutoff
      · simp [lift, below]
      · have notBelow : ¬ index + second < cutoff := by omega
        simp only [lift, below, notBelow, if_false]
        congr 1
        omega
  | srt sort => intro first second cutoff; rfl
  | con name => intro first second cutoff; rfl
  | pi domain body ihDomain ihBody =>
      intro first second cutoff; simp [lift, ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      intro first second cutoff; simp [lift, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro first second cutoff; simp [lift, ihFunction, ihArgument]

/-- A lift below commutes with a lift above. -/
theorem lift_lift (term : Term) :
    ∀ (outer inner low high : Nat), low ≤ high →
      lift outer low (lift inner high term) = lift inner (high + outer) (lift outer low term) := by
  induction term with
  | var index =>
      intro outer inner low high ordered
      by_cases belowLow : index < low
      · have belowHigh : index < high := by omega
        have belowShifted : index < high + outer := by omega
        simp [lift, belowLow, belowHigh, belowShifted]
      · by_cases belowHigh : index < high
        · have belowShifted : index + outer < high + outer := by omega
          simp [lift, belowLow, belowHigh, belowShifted]
        · have notLow : ¬ index + inner < low := by omega
          have notShifted : ¬ index + outer < high + outer := by omega
          simp only [lift, belowLow, belowHigh, notLow, notShifted, if_false]
          congr 1
          omega
  | srt sort => intro outer inner low high _; rfl
  | con name => intro outer inner low high _; rfl
  | pi domain body ihDomain ihBody =>
      intro outer inner low high ordered
      have under := ihBody outer inner (low + 1) (high + 1) (Nat.succ_le_succ ordered)
      have shifted : high + 1 + outer = high + outer + 1 := by omega
      rw [shifted] at under
      simp [lift, ihDomain outer inner low high ordered, under]
  | lam domain body ihDomain ihBody =>
      intro outer inner low high ordered
      have under := ihBody outer inner (low + 1) (high + 1) (Nat.succ_le_succ ordered)
      have shifted : high + 1 + outer = high + outer + 1 := by omega
      rw [shifted] at under
      simp [lift, ihDomain outer inner low high ordered, under]
  | app function argument ihFunction ihArgument =>
      intro outer inner low high ordered
      simp [lift, ihFunction outer inner low high ordered, ihArgument outer inner low high ordered]

/-- A lift below a substituted variable commutes with the substitution. -/
theorem lift_subst (term : Term) :
    ∀ (amount cutoff target : Nat) (replacement : Term), cutoff ≤ target →
      lift amount cutoff (subst target replacement term) =
        subst (target + amount) (lift amount cutoff replacement) (lift amount cutoff term) := by
  induction term with
  | var index =>
      intro amount cutoff target replacement ordered
      by_cases same : index = target
      · have notBelow : ¬ target < cutoff := by omega
        simp [lift, subst, same, notBelow]
      · by_cases above : target < index
        · have notBelow : ¬ index < cutoff := by omega
          have notBelowPred : ¬ index - 1 < cutoff := by omega
          have notSame : index + amount ≠ target + amount := by omega
          have aboveShifted : target + amount < index + amount := by omega
          simp only [lift, subst, same, above, notBelow, notBelowPred, notSame, aboveShifted,
            if_true, if_false]
          congr 1
          omega
        · by_cases below : index < cutoff
          · have notSame : index ≠ target + amount := by omega
            have notAbove : ¬ target + amount < index := by omega
            simp [lift, subst, same, above, below, notSame, notAbove]
          · have notAbove : ¬ target + amount < index + amount := by omega
            simp [lift, subst, same, above, below, notAbove]
  | srt sort => intro amount cutoff target replacement _; rfl
  | con name => intro amount cutoff target replacement _; rfl
  | pi domain body ihDomain ihBody =>
      intro amount cutoff target replacement ordered
      have under := ihBody amount (cutoff + 1) (target + 1) (lift 1 0 replacement)
        (Nat.succ_le_succ ordered)
      have commute : lift amount (cutoff + 1) (lift 1 0 replacement) =
          lift 1 0 (lift amount cutoff replacement) :=
        (lift_lift replacement 1 amount 0 cutoff (Nat.zero_le _)).symm
      have shifted : target + 1 + amount = target + amount + 1 := by omega
      rw [commute, shifted] at under
      simp [lift, subst, ihDomain amount cutoff target replacement ordered, under]
  | lam domain body ihDomain ihBody =>
      intro amount cutoff target replacement ordered
      have under := ihBody amount (cutoff + 1) (target + 1) (lift 1 0 replacement)
        (Nat.succ_le_succ ordered)
      have commute : lift amount (cutoff + 1) (lift 1 0 replacement) =
          lift 1 0 (lift amount cutoff replacement) :=
        (lift_lift replacement 1 amount 0 cutoff (Nat.zero_le _)).symm
      have shifted : target + 1 + amount = target + amount + 1 := by omega
      rw [commute, shifted] at under
      simp [lift, subst, ihDomain amount cutoff target replacement ordered, under]
  | app function argument ihFunction ihArgument =>
      intro amount cutoff target replacement ordered
      simp [lift, subst, ihFunction amount cutoff target replacement ordered,
        ihArgument amount cutoff target replacement ordered]

/-- **Two substitutions commute**: the substitution lemma for terms. -/
theorem subst_subst (term : Term) :
    ∀ (inner outer : Nat) (argument replacement : Term), inner ≤ outer →
      subst outer replacement (subst inner argument term) =
        subst inner (subst outer replacement argument)
          (subst (outer + 1) (lift 1 inner replacement) term) := by
  induction term with
  | var index =>
      intro inner outer argument replacement ordered
      by_cases isInner : index = inner
      · subst isInner
        have notOuter : index ≠ outer + 1 := by omega
        have notAbove : ¬ outer + 1 < index := by omega
        simp [subst, notOuter, notAbove]
      · by_cases isOuter : index = outer + 1
        · have aboveInner : inner < index := by omega
          have notInner' : outer + 1 ≠ inner := by omega
          have aboveInner' : inner < outer + 1 := by omega
          simp [subst, isOuter, notInner', aboveInner', subst_lift_cancel]
        · by_cases belowInner : index < inner
          · have notAboveInner : ¬ inner < index := by omega
            have notOuter' : index ≠ outer := by omega
            have notAboveOuter : ¬ outer < index := by omega
            have notAboveOuter' : ¬ outer + 1 < index := by omega
            simp [subst, isInner, isOuter, notAboveInner, notOuter', notAboveOuter, notAboveOuter']
          · have aboveInner : inner < index := by omega
            by_cases belowOuter : index < outer + 1
            · have notOuter' : index - 1 ≠ outer := by omega
              have notAboveOuter : ¬ outer < index - 1 := by omega
              have notAboveOuter' : ¬ outer + 1 < index := by omega
              simp [subst, isInner, isOuter, aboveInner, notOuter', notAboveOuter, notAboveOuter']
            · have aboveOuter : outer + 1 < index := by omega
              have notOuter' : index - 1 ≠ outer := by omega
              have aboveOuter' : outer < index - 1 := by omega
              have notInner' : index - 1 ≠ inner := by omega
              have aboveInner' : inner < index - 1 := by omega
              simp [subst, isInner, isOuter, aboveInner, aboveOuter, notOuter', aboveOuter',
                notInner', aboveInner']
  | srt sort => intro inner outer argument replacement _; rfl
  | con name => intro inner outer argument replacement _; rfl
  | pi domain body ihDomain ihBody =>
      intro inner outer argument replacement ordered
      have under := ihBody (inner + 1) (outer + 1) (lift 1 0 argument) (lift 1 0 replacement)
        (Nat.succ_le_succ ordered)
      have first : subst (outer + 1) (lift 1 0 replacement) (lift 1 0 argument) =
          lift 1 0 (subst outer replacement argument) :=
        (lift_subst argument 1 0 outer replacement (Nat.zero_le _)).symm
      have second : lift 1 (inner + 1) (lift 1 0 replacement) = lift 1 0 (lift 1 inner replacement) :=
        (lift_lift replacement 1 1 0 inner (Nat.zero_le _)).symm
      rw [first, second] at under
      simp [subst, ihDomain inner outer argument replacement ordered, under]
  | lam domain body ihDomain ihBody =>
      intro inner outer argument replacement ordered
      have under := ihBody (inner + 1) (outer + 1) (lift 1 0 argument) (lift 1 0 replacement)
        (Nat.succ_le_succ ordered)
      have first : subst (outer + 1) (lift 1 0 replacement) (lift 1 0 argument) =
          lift 1 0 (subst outer replacement argument) :=
        (lift_subst argument 1 0 outer replacement (Nat.zero_le _)).symm
      have second : lift 1 (inner + 1) (lift 1 0 replacement) = lift 1 0 (lift 1 inner replacement) :=
        (lift_lift replacement 1 1 0 inner (Nat.zero_le _)).symm
      rw [first, second] at under
      simp [subst, ihDomain inner outer argument replacement ordered, under]
  | app function argument' ihFunction ihArgument =>
      intro inner outer argument replacement ordered
      simp [subst, ihFunction inner outer argument replacement ordered,
        ihArgument inner outer argument replacement ordered]

/-- Substitution commutes with a beta contraction. -/
theorem subst_subst0 (target : Nat) (replacement argument body : Term) :
    subst target replacement (subst0 argument body) =
      subst0 (subst target replacement argument) (subst (target + 1) (lift 1 0 replacement) body) :=
  subst_subst body 0 target argument replacement (Nat.zero_le _)

/-- Substitution commutes with the instantiation of pattern variables. -/
theorem subst_instantiate (assignment : Nat → Term) (pattern : Term) :
    ∀ (depth target : Nat) (replacement : Term),
      subst (target + depth) (lift depth 0 replacement) (instantiate assignment depth pattern) =
        instantiate (fun index => subst target replacement (assignment index)) depth pattern := by
  induction pattern with
  | var index =>
      intro depth target replacement
      by_cases below : index < depth
      · have notSame : index ≠ target + depth := by omega
        have notAbove : ¬ target + depth < index := by omega
        simp [instantiate, subst, below, notSame, notAbove]
      · simp only [instantiate, below, if_false]
        exact (lift_subst (assignment (index - depth)) depth 0 target replacement
          (Nat.zero_le _)).symm
  | srt sort => intro depth target replacement; rfl
  | con name => intro depth target replacement; rfl
  | pi domain body ihDomain ihBody =>
      intro depth target replacement
      have under := ihBody (depth + 1) target replacement
      have merged : lift 1 0 (lift depth 0 replacement) = lift (depth + 1) 0 replacement := by
        rw [lift_lift_same, Nat.add_comm]
      have shifted : target + (depth + 1) = target + depth + 1 := by omega
      rw [shifted, ← merged] at under
      simp [instantiate, subst, ihDomain depth target replacement, under]
  | lam domain body ihDomain ihBody =>
      intro depth target replacement
      have under := ihBody (depth + 1) target replacement
      have merged : lift 1 0 (lift depth 0 replacement) = lift (depth + 1) 0 replacement := by
        rw [lift_lift_same, Nat.add_comm]
      have shifted : target + (depth + 1) = target + depth + 1 := by omega
      rw [shifted, ← merged] at under
      simp [instantiate, subst, ihDomain depth target replacement, under]
  | app function argument ihFunction ihArgument =>
      intro depth target replacement
      simp [instantiate, subst, ihFunction depth target replacement,
        ihArgument depth target replacement]

/-- The instance of the previous law under no binder. -/
theorem subst_inst (assignment : Nat → Term) (pattern : Term) (target : Nat) (replacement : Term) :
    subst target replacement (inst assignment pattern) =
      inst (fun index => subst target replacement (assignment index)) pattern := by
  have general := subst_instantiate assignment pattern 0 target replacement
  rwa [lift_zero] at general

/-! ## Steps and conversion under substitution -/

/-- The definitions of a theory are closed terms. -/
def Theory.ClosedBodies (theory : Theory) : Prop :=
  ∀ name term, theory.body name = some term → Closed term

variable {theory : Theory}

theorem RootStep.subst (closed : theory.ClosedBodies) {source target : Term}
    (step : RootStep theory source target) (index : Nat) (replacement : Term) :
    RootStep theory (LFTyping.subst index replacement source)
      (LFTyping.subst index replacement target) := by
  cases step with
  | beta domain body argument =>
      rw [subst_subst0]
      exact .beta _ _ _
  | delta defined =>
      rw [(closed _ _ defined).subst]
      exact .delta defined
  | rule assignment member =>
      rw [subst_inst, subst_inst]
      exact .rule _ member

/-- **A step is stable under substitution.** -/
theorem Step.subst (closed : theory.ClosedBodies) {source target : Term}
    (step : Step theory source target) :
    ∀ (index : Nat) (replacement : Term),
      Step theory (LFTyping.subst index replacement source)
        (LFTyping.subst index replacement target) := by
  cases step with
  | @inContext context redex contractum root =>
      induction context with
      | hole => intro index replacement; exact Step.root (root.subst closed index replacement)
      | piDomain rest body ih =>
          intro index replacement
          exact (ih index replacement).plug (.piDomain .hole _)
      | piBody domain rest ih =>
          intro index replacement
          exact (ih (index + 1) (lift 1 0 replacement)).plug (.piBody _ .hole)
      | lamDomain rest body ih =>
          intro index replacement
          exact (ih index replacement).plug (.lamDomain .hole _)
      | lamBody domain rest ih =>
          intro index replacement
          exact (ih (index + 1) (lift 1 0 replacement)).plug (.lamBody _ .hole)
      | appFunction rest argument ih =>
          intro index replacement
          exact (ih index replacement).plug (.appFunction .hole _)
      | appArgument function rest ih =>
          intro index replacement
          exact (ih index replacement).plug (.appArgument _ .hole)

/-- **Conversion is stable under substitution.** -/
theorem Conv.subst (closed : theory.ClosedBodies) {source target : Term}
    (convertible : Conv theory source target) (index : Nat) (replacement : Term) :
    Conv theory (LFTyping.subst index replacement source)
      (LFTyping.subst index replacement target) := by
  induction convertible with
  | rel _ _ step => exact .rel _ _ (step.subst closed index replacement)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-! ## Uniqueness of types -/

/-- A system is functional when two product rules with the same premises
have the same conclusion.  Its axioms are functional by construction. -/
def Functional (profile : Profile) : Prop :=
  ∀ first ∈ profile.products, ∀ second ∈ profile.products,
    first.domain = second.domain → first.codomain = second.codomain → first.result = second.result

/-- **Uniqueness of types**: in a functional system, under confluence, two
types of one term in one context are convertible. -/
theorem HasType.unique {profile : Profile} (functional : Functional profile)
    (confluent : Confluent (Step theory)) (headed : theory.Headed) (closed : theory.ClosedBodies)
    (term : Term) :
    ∀ {context : Ctx} {first second : Term},
      HasType profile theory context term first → HasType profile theory context term second →
        Conv theory first second := by
  induction term with
  | srt sort =>
      intro context first second firstTyped secondTyped
      obtain ⟨firstSort, firstAxiom, firstConv⟩ := firstTyped.sort_inv
      obtain ⟨secondSort, secondAxiom, secondConv⟩ := secondTyped.sort_inv
      have same : firstSort = secondSort := Option.some.inj (firstAxiom.symm.trans secondAxiom)
      subst same
      exact .trans _ _ _ (.symm _ _ firstConv) secondConv
  | var index =>
      intro context first second firstTyped secondTyped
      obtain ⟨firstDeclared, firstFound, firstConv⟩ := firstTyped.var_inv
      obtain ⟨secondDeclared, secondFound, secondConv⟩ := secondTyped.var_inv
      have same : firstDeclared = secondDeclared := Option.some.inj (firstFound.symm.trans secondFound)
      subst same
      exact .trans _ _ _ (.symm _ _ firstConv) secondConv
  | con name =>
      intro context first second firstTyped secondTyped
      obtain ⟨firstDeclared, firstFound, firstConv⟩ := firstTyped.con_inv
      obtain ⟨secondDeclared, secondFound, secondConv⟩ := secondTyped.con_inv
      have same : firstDeclared = secondDeclared := Option.some.inj (firstFound.symm.trans secondFound)
      subst same
      exact .trans _ _ _ (.symm _ _ firstConv) secondConv
  | pi domain body ihDomain ihBody =>
      intro context first second firstTyped secondTyped
      obtain ⟨d1, c1, r1, domainFirst, bodyFirst, ruleFirst, firstConv⟩ := firstTyped.pi_inv
      obtain ⟨d2, c2, r2, domainSecond, bodySecond, ruleSecond, secondConv⟩ := secondTyped.pi_inv
      have domains : d1 = d2 := Conv.srt_injective confluent headed (ihDomain domainFirst domainSecond)
      have codomains : c1 = c2 := Conv.srt_injective confluent headed (ihBody bodyFirst bodySecond)
      have results : r1 = r2 := functional _ ruleFirst _ ruleSecond domains codomains
      subst results
      exact .trans _ _ _ (.symm _ _ firstConv) secondConv
  | lam domain body _ ihBody =>
      intro context first second firstTyped secondTyped
      obtain ⟨firstBody, _, _, _, _, _, _, bodyFirst, firstConv⟩ := firstTyped.lam_inv
      obtain ⟨secondBody, _, _, _, _, _, _, bodySecond, secondConv⟩ := secondTyped.lam_inv
      exact .trans _ _ _ (.symm _ _ firstConv)
        (.trans _ _ _ (Conv.pi (.refl _) (ihBody bodyFirst bodySecond)) secondConv)
  | app function argument ihFunction _ =>
      intro context first second firstTyped secondTyped
      obtain ⟨_, firstBody, functionFirst, _, firstConv⟩ := firstTyped.app_inv
      obtain ⟨_, secondBody, functionSecond, _, secondConv⟩ := secondTyped.app_inv
      have bodies := (Conv.pi_injective confluent headed (ihFunction functionFirst functionSecond)).2
      exact .trans _ _ _ (.symm _ _ firstConv)
        (.trans _ _ _ (bodies.subst closed 0 argument) secondConv)

namespace Example

/-- A system with two rules for one pair of sorts. -/
def twoResults : Profile where
  sortAxiom := LFProfile.typeAxiom
  products := [LFProfile.typeTypeType, ⟨.type, .type, .kind⟩]

/-- **Negative**: the system is not functional. -/
theorem twoResults_not_functional : ¬ Functional twoResults := by
  intro functional
  have same := functional LFProfile.typeTypeType (by decide) ⟨.type, .type, .kind⟩ (by decide)
    rfl rfl
  cases same

/-- A type constant. -/
def base : Theory := Theory.ofSig [.const "A" (.srt .type)] []

/-- **Without functionality a product has two sorts.** -/
theorem nonFunctional_two_sorts :
    HasType twoResults base [] (.pi (.con "A") (.con "A")) (.srt .type) ∧
      HasType twoResults base [] (.pi (.con "A") (.con "A")) (.srt .kind) :=
  ⟨.pi (.con rfl) (.con rfl) (by decide), .pi (.con rfl) (.con rfl) (by decide)⟩

/-- **Positive**: the existing profile of λΠ is functional. -/
theorem basic_functional : Functional LFProfile.basic := by
  intro first firstMember second secondMember domains codomains
  have firstCases : first = LFProfile.typeTypeType ∨ first = LFProfile.typeKindKind := by
    simpa [LFProfile.basic] using firstMember
  have secondCases : second = LFProfile.typeTypeType ∨ second = LFProfile.typeKindKind := by
    simpa [LFProfile.basic] using secondMember
  rcases firstCases with rfl | rfl <;> rcases secondCases with rfl | rfl <;>
    first | rfl | (cases codomains)

end Example

#print axioms lift_lift
#print axioms lift_subst
#print axioms subst_subst
#print axioms subst_instantiate
#print axioms Step.subst
#print axioms Conv.subst
#print axioms HasType.unique
#print axioms Example.nonFunctional_two_sorts

end Mettapedia.GSLT.Dedukti
