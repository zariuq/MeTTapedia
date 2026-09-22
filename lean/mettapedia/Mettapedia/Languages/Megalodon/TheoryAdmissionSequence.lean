import Mettapedia.Languages.Megalodon.TheoryAdmissionKernel

/-!
# Retained articles for ordered theory admission

The sequence compiler connects untrusted single-declaration articles using
the existing theory-admission rules. For closed, canonically scoped source
data, its checker equation is exact: the
compiled article is accepted iff every retained step checks in the preceding
step's output environment. Concatenation uses that exact environment, including
its assumptions and definitions; it is not weakening or replay under a revised
theory. No truth assertion is made about admitted axioms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.TheoryAdmissionSequence

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Megalodon.TheoryAdmissionKernel
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- One untrusted declaration, claimed output environment and retained article.
The input environment comes from the sequence, never from a trusted side field. -/
structure Step where
  item : Pattern
  next : Pattern
  evidence : RawProof

def finalEnvironment : Pattern → List Step → Pattern
  | initial, [] => initial
  | _, step :: rest => finalEnvironment step.next rest

def items : List Step → Pattern
  | [] => a "MTheoryItemsNil"
  | step :: rest => a "MTheoryItemsCons" [step.item, items rest]

/-- Compute the complete article, retaining every supplied admission proof. -/
def article : Pattern → List Step → RawProof
  | initial, [] =>
      .node ⟨ruleId "megalodon-theory-checks-nil", [initial]⟩ []
  | initial, step :: rest =>
      .node ⟨ruleId "megalodon-theory-checks-cons",
        [initial, step.item, items rest, step.next,
          finalEnvironment step.next rest]⟩
        [step.evidence, article step.next rest]

/-- The same authority checks each step at its actual sequence position. -/
def checkSteps : Pattern → List Step → Bool
  | _, [] => true
  | initial, step :: rest =>
      checkRaw validated (admits initial step.item step.next) step.evidence &&
        checkSteps step.next rest

/-- Source data are closed patterns with canonical binder metadata. These
structural conditions do not assert that any admission evidence is accepted. -/
def WellScoped : List Step → Prop
  | [] => True
  | step :: rest => argumentValidAt 0 step.item = true ∧
      argumentValidAt 0 step.next = true ∧ WellScoped rest

theorem wellScoped_append (first second : List Step) :
    WellScoped (first ++ second) ↔ WellScoped first ∧ WellScoped second := by
  induction first with
  | nil => simp [WellScoped]
  | cons step rest ih => simp [WellScoped, ih, and_assoc]

theorem finalEnvironment_valid (initial : Pattern) (steps : List Step)
    (initialValid : argumentValidAt 0 initial = true) (scopeValid : WellScoped steps) :
    argumentValidAt 0 (finalEnvironment initial steps) = true := by
  induction steps generalizing initial with
  | nil => exact initialValid
  | cons step rest ih => exact ih step.next scopeValid.2.1 scopeValid.2.2

theorem items_valid (steps : List Step) (scopeValid : WellScoped steps) :
    argumentValidAt 0 (items steps) = true := by
  induction steps with
  | nil => decide
  | cons step rest ih =>
      have hv := scopeValid.1
      have hr := ih scopeValid.2.2
      simp only [argumentValidAt, Bool.and_eq_true] at hv hr
      simp [items, a, argumentValidAt, Pattern.isGroundAt, Pattern.isGroundListAt,
        Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
        hv, hr]

private theorem check_nil (initial : Pattern)
    (initialValid : argumentValidAt 0 initial = true) :
    checkRaw validated (checks initial (items []) initial) (article initial []) = true := by
  simp [article, items, checkRaw, instantiateRule?, validated, lookup_checksNilRule,
    checksNilRule, rule, ruleId, checks, a, m, checkRawChildren,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, lookupArgumentAt?, argumentsValidAt, initialValid]

private theorem check_cons (initial : Pattern) (step : Step) (rest : List Step)
    (initialValid : argumentValidAt 0 initial = true) (scopeValid : WellScoped (step :: rest)) :
    checkRaw validated
        (checks initial (items (step :: rest)) (finalEnvironment initial (step :: rest)))
        (article initial (step :: rest)) =
      (checkRaw validated (admits initial step.item step.next) step.evidence &&
        checkRaw validated (checks step.next (items rest) (finalEnvironment step.next rest))
          (article step.next rest)) := by
  simp only [article, items, finalEnvironment, checkRaw, instantiateRule?, validated]
  simp [lookup_checksConsRule, checksConsRule, rule, ruleId, checks, admits, a, m,
    instantiateSchemas?, instantiateSchema?, instantiateSchemasAt?,
    instantiateSchemaAt?, lookupArgumentAt?, checkRawChildren, argumentsValidAt,
    initialValid, scopeValid.1, scopeValid.2.1, items_valid rest scopeValid.2.2,
    finalEnvironment_valid step.next rest scopeValid.2.1 scopeValid.2.2]

/-- The computed whole article accepts exactly the connected, checked steps.
Neither source ordering alone nor an unordered collection of valid proofs suffices. -/
theorem check_article (initial : Pattern) (steps : List Step)
    (initialValid : argumentValidAt 0 initial = true) (scopeValid : WellScoped steps) :
    checkRaw validated (checks initial (items steps) (finalEnvironment initial steps))
      (article initial steps) = checkSteps initial steps := by
  induction steps generalizing initial with
  | nil => exact check_nil initial initialValid
  | cons step rest ih =>
      rw [check_cons initial step rest initialValid scopeValid,
        ih step.next scopeValid.2.1 scopeValid.2.2]
      rfl

@[simp] theorem finalEnvironment_append (initial : Pattern) (first second : List Step) :
    finalEnvironment initial (first ++ second) =
      finalEnvironment (finalEnvironment initial first) second := by
  induction first generalizing initial with
  | nil => rfl
  | cons step rest ih => exact ih step.next

theorem checkSteps_append (initial : Pattern) (first second : List Step) :
    checkSteps initial (first ++ second) =
      (checkSteps initial first && checkSteps (finalEnvironment initial first) second) := by
  induction first generalizing initial with
  | nil => simp [checkSteps, finalEnvironment]
  | cons step rest ih => simp only [List.cons_append, checkSteps, finalEnvironment, ih,
      Bool.and_assoc]

/-- Accepted library prefixes compose with later checked declarations exactly
when those declarations check at the prefix's output. The article is computed
from the retained evidence, not supplied as an additional conclusion premise. -/
theorem check_article_append_iff (initial : Pattern) (first second : List Step)
    (initialValid : argumentValidAt 0 initial = true)
    (firstScoped : WellScoped first) (secondScoped : WellScoped second) :
    checkRaw validated
        (checks initial (items (first ++ second)) (finalEnvironment initial (first ++ second)))
        (article initial (first ++ second)) = true ↔
      checkRaw validated (checks initial (items first) (finalEnvironment initial first))
        (article initial first) = true ∧
      checkRaw validated
        (checks (finalEnvironment initial first) (items second)
          (finalEnvironment (finalEnvironment initial first) second))
        (article (finalEnvironment initial first) second) = true := by
  rw [check_article _ _ initialValid ((wellScoped_append first second).mpr
      ⟨firstScoped, secondScoped⟩),
    checkSteps_append, check_article _ _ initialValid firstScoped,
    check_article _ _ (finalEnvironment_valid initial first initialValid firstScoped) secondScoped,
    Bool.and_eq_true]

/-- An accepted fixed article cannot be reused at a different input environment,
even if its item and claimed output have not changed. Revisions require replay
or newly established transport, not relabelling a retained certificate. -/
theorem changed_input_rejected (initial changed : Pattern) (step : Step)
    (accepted : checkRaw validated (admits initial step.item step.next) step.evidence = true)
    (different : initial ≠ changed) :
    checkRaw validated (admits changed step.item step.next) step.evidence = false := by
  cases h : checkRaw validated (admits changed step.item step.next) step.evidence with
  | false => rfl
  | true =>
      have unique := checkRaw_goal_unique accepted h
      simp only [admits, a, Pattern.apply.injEq, List.cons.injEq] at unique
      exact False.elim (different unique.2.1)

namespace Controls

def primitive : Step :=
  ⟨canaryPrimitiveItem, canaryPrimitiveEnvironment, canaryPrimitiveAdmissionArticle⟩
def assumed : Step :=
  ⟨canaryAxiomItem, canaryAxiomEnvironment, canaryAxiomAdmissionArticle⟩
def proved : Step :=
  ⟨canaryTheoremItem, canaryFinalEnvironment, canaryTheoremAdmissionArticle⟩

theorem primitive_axiom_theorem_checked :
    checkSteps canaryInitialEnvironment [primitive, assumed, proved] = true := by
  rw [← check_article _ _ (by decide) (by simp only [WellScoped]; decide)]
  exact ordered_primitive_axiom_theorem_accepted

theorem assumed_step_checked :
    checkRaw validated (admits canaryPrimitiveEnvironment assumed.item assumed.next)
      assumed.evidence = true := by
  have h := primitive_axiom_theorem_checked
  simp only [checkSteps, Bool.and_eq_true] at h
  exact h.2.1

/-- The axiom's formation proof needs the earlier primitive declaration. -/
theorem skipping_primitive_rejected :
    checkSteps canaryInitialEnvironment [assumed, proved] = false := by
  rw [checkSteps, changed_input_rejected canaryPrimitiveEnvironment
    canaryInitialEnvironment assumed assumed_step_checked (by decide)]
  rfl

theorem unresolved_environment_rejected :
    checkRaw validated
      (checks (.fvar "unresolved") (items []) (.fvar "unresolved"))
      (article (.fvar "unresolved") []) = false := by
  simp [article, items, checkRaw, instantiateRule?, validated,
    checksNilRule, rule, ruleId, argumentsValidAt, argumentValidAt,
    Pattern.isGroundAt]

end Controls

#print axioms check_article
#print axioms check_article_append_iff
#print axioms changed_input_rejected
#print axioms Controls.primitive_axiom_theorem_checked
#print axioms Controls.skipping_primitive_rejected
#print axioms Controls.unresolved_environment_rejected

end Mettapedia.Languages.Megalodon.TheoryAdmissionSequence
