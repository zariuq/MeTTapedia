import Mettapedia.OSLF.Syntax.ScopedPremiseElaborationExecution

/-!
# Executing checked canonical scoped premises

An authored rule is elaborated before its premise list is executed. The
elaborated list has one explicit local context and endpoint sort for every
step premise. Successful elaboration preserves the complete ordered firing
list of the existing executor, including assignments and selected evidence.
Compilation failure is retained as `none`, rather than treated as an empty
set of firings.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution

open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.Binding.ScopedPremiseElaborationExecution

/-- Elaborate a rule at a declared ambient context. At the root this agrees
exactly with the existing authored rule compiler. -/
def compileRulePremisesAt? (language : LanguageDef) (rule : RewriteRule)
    (ambient : List TypeExpr) : Option (List CanonicalPremise) :=
  if (rule.typeContext.map Prod.fst).Nodup then
    compileList? language (freeFromRuleContext rule.typeContext)
      ambient rule.premises
  else none

theorem compileRulePremisesAt?_root (language : LanguageDef)
    (rule : RewriteRule) :
    compileRulePremisesAt? language rule [] =
      compileRulePremises? language rule := rfl

/-- Successful elaboration at any ambient context retains every authored
premise position, including ordered collection and query positions. -/
theorem compileRulePremisesAt?_length
    {language : LanguageDef} {rule : RewriteRule}
    {ambient : List TypeExpr} {premises : List CanonicalPremise}
    (compiled : compileRulePremisesAt? language rule ambient =
      some premises) :
    premises.length = rule.premises.length := by
  unfold compileRulePremisesAt? at compiled
  split at compiled
  · exact compileList?_length compiled
  · contradiction

/-- Run the canonical premise list in its declared ambient context. -/
def applyWithCanonicalPremisesAt {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (ambient : List TypeExpr) (term : Pattern)
    (premises : List CanonicalPremise) : List (RuleFiring Evidence) :=
  match rule.bindings with
  | none => []
  | some spec =>
      if admittedFor rule spec then
        (matchRuleAt rule spec ambient.length term).flatMap fun captured =>
          (runPremises oracle relEnv language rule spec ambient.length 0
            (premises.map CanonicalPremise.toAuthored) captured).filterMap
              fun (completed, history) =>
                finish? rule spec ambient.length captured completed history
      else []

/-- Keep compilation failure distinct from an empty firing list at any
declared ambient context. -/
def applyCompiledRuleAt? {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (ambient : List TypeExpr) (term : Pattern) :
    Option (List (RuleFiring Evidence)) := do
  let premises ← compileRulePremisesAt? language rule ambient
  pure (applyWithCanonicalPremisesAt oracle relEnv language rule
    ambient term premises)

/-- Successful contextual elaboration preserves the complete proof-relevant
list of old rule firings, at precisely the declared ambient depth. -/
theorem applyWithCanonicalPremisesAt_eq
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (ambient : List TypeExpr) (term : Pattern)
    (premises : List CanonicalPremise)
    (compiled : compileRulePremisesAt? language rule ambient =
      some premises) :
    applyWithCanonicalPremisesAt oracle relEnv language rule ambient term
        premises =
      applyRuleWithOracle oracle relEnv language ambient.length rule term := by
  have compiledList :
      compileList? language (freeFromRuleContext rule.typeContext)
        ambient rule.premises = some premises := by
    unfold compileRulePremisesAt? at compiled
    split at compiled
    · exact compiled
    · contradiction
  unfold applyWithCanonicalPremisesAt applyRuleWithOracle
  cases rule.bindings with
  | none => rfl
  | some spec =>
      by_cases admitted : admittedFor rule spec = true
      · simp only [admitted, if_true]
        congr 1
        funext captured
        rw [runPremises_compileList oracle relEnv language
          (freeFromRuleContext rule.typeContext) ambient rule spec 0
          rule.premises premises captured compiledList]
      · have rejected : admittedFor rule spec = false :=
          Bool.eq_false_iff.mpr admitted
        simp [rejected]

theorem applyCompiledRuleAt?_eq
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (ambient : List TypeExpr) (term : Pattern)
    (premises : List CanonicalPremise)
    (compiled : compileRulePremisesAt? language rule ambient =
      some premises) :
    applyCompiledRuleAt? oracle relEnv language rule ambient term =
      some (applyRuleWithOracle oracle relEnv language
        ambient.length rule term) := by
  simp [applyCompiledRuleAt?, compiled,
    applyWithCanonicalPremisesAt_eq oracle relEnv language rule ambient
      term premises compiled]

/-- Elaborate the complete authored rule list in declaration order, retaining
each rule position. A failure in any declaration rejects the list. -/
def compileRuleListAt? (language : LanguageDef)
    (ambient : List TypeExpr) :
    List (RewriteRule × Nat) →
      Option (List (RewriteRule × Nat × List CanonicalPremise))
  | [] => some []
  | (rule, index) :: rest => do
      let premises ← compileRulePremisesAt? language rule ambient
      let later ← compileRuleListAt? language ambient rest
      pure ((rule, index, premises) :: later)

/-- All firings of the checked canonical declarations, with their authored
rule positions. This is an optional list so rejection is not confused with
a language that has no possible step at the input. -/
def applyCompiledLanguageAt? {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (ambient : List TypeExpr)
    (term : Pattern) : Option (List (Nat × RuleFiring Evidence)) := do
  let rules ← compileRuleListAt? language ambient language.rewrites.zipIdx
  pure (rules.flatMap fun (rule, index, premises) =>
    (applyWithCanonicalPremisesAt oracle relEnv language rule ambient term
      premises).map fun firing => (index, firing))

/-- Every successfully compiled rule list has exactly the old one-layer
result list, with rule indices and all firing witnesses in the same order. -/
theorem compileRuleListAt?_results
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (ambient : List TypeExpr) (term : Pattern)
    (entries : List (RewriteRule × Nat))
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (h : compileRuleListAt? language ambient entries = some compiled) :
    (compiled.flatMap fun (rule, index, premises) =>
      (applyWithCanonicalPremisesAt oracle relEnv language rule ambient
        term premises).map fun firing => (index, firing)) =
      (entries.flatMap fun (rule, index) =>
        (applyRuleWithOracle oracle relEnv language ambient.length
          rule term).map fun firing => (index, firing)) := by
  induction entries generalizing compiled with
  | nil =>
      simp [compileRuleListAt?] at h
      cases h
      rfl
  | cons entry rest ih =>
      rcases entry with ⟨rule, index⟩
      cases hfirst : compileRulePremisesAt? language rule ambient with
      | none => simp [compileRuleListAt?, hfirst] at h
      | some premises =>
          cases hlater : compileRuleListAt? language ambient rest with
          | none => simp [compileRuleListAt?, hfirst, hlater] at h
          | some later =>
              simp [compileRuleListAt?, hfirst, hlater] at h
              cases h
              simp only [List.flatMap_cons]
              rw [applyWithCanonicalPremisesAt_eq oracle relEnv language
                rule ambient term premises hfirst]
              exact congrArg₂ List.append rfl (ih later hlater)

/-- For every supplied oracle, checking the whole language and then running
its canonical scoped premises gives the same complete one-layer behavior as
the current executor, provided every declaration compiled. -/
theorem applyCompiledLanguageAt?_eq
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (ambient : List TypeExpr) (term : Pattern)
    (compiled : List (RewriteRule × Nat × List CanonicalPremise))
    (h : compileRuleListAt? language ambient
      language.rewrites.zipIdx = some compiled) :
    applyCompiledLanguageAt? oracle relEnv language ambient term =
      some (language.rewrites.zipIdx.flatMap fun (rule, index) =>
        (applyRuleWithOracle oracle relEnv language ambient.length
          rule term).map fun firing => (index, firing)) := by
  simp [applyCompiledLanguageAt?, h,
    compileRuleListAt?_results oracle relEnv language ambient term
      language.rewrites.zipIdx compiled h]

/-- Execute a rule with a checked canonical premise list. Its original rule
declaration still supplies the occurrence sites and binding specification. -/
def applyWithCanonicalPremises {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (term : Pattern) (premises : List CanonicalPremise) :
    List (RuleFiring Evidence) :=
  applyWithCanonicalPremisesAt oracle relEnv language rule [] term premises

/-- The checked rule compiler and the canonical executor form one partial
operation. `none` reports a rejected or ambiguous source declaration. -/
def applyCompiledRule? {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (term : Pattern) : Option (List (RuleFiring Evidence)) :=
  applyCompiledRuleAt? oracle relEnv language rule [] term

/-- At the rule root, successful checked elaboration preserves the exact
ordered list of complete firings, rather than only endpoint membership. -/
theorem applyWithCanonicalPremises_eq
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (term : Pattern)
    (premises : List CanonicalPremise)
    (compiled : compileRulePremises? language rule = some premises) :
    applyWithCanonicalPremises oracle relEnv language rule term premises =
      applyRuleWithOracle oracle relEnv language 0 rule term := by
  exact applyWithCanonicalPremisesAt_eq oracle relEnv language rule []
    term premises (by simpa only [compileRulePremisesAt?_root] using compiled)

/-- A successfully compiled rule has precisely its old firing behavior.
All premise and oracle positions survive because the two lists are equal. -/
theorem applyCompiledRule?_eq
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (term : Pattern)
    (premises : List CanonicalPremise)
    (compiled : compileRulePremises? language rule = some premises) :
    applyCompiledRule? oracle relEnv language rule term =
      some (applyRuleWithOracle oracle relEnv language 0 rule term) := by
  exact applyCompiledRuleAt?_eq oracle relEnv language rule [] term
    premises (by simpa only [compileRulePremisesAt?_root] using compiled)

/-- Compilation failure remains observable; it cannot be confused with a
well-formed rule that simply has no firing for this input. -/
theorem applyCompiledRule?_rejected
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (term : Pattern)
    (rejected : compileRulePremises? language rule = none) :
    applyCompiledRule? oracle relEnv language rule term = none := by
  simp [applyCompiledRule?, applyCompiledRuleAt?,
    compileRulePremisesAt?_root, rejected]

#print axioms applyWithCanonicalPremises_eq
#print axioms applyCompiledRule?_eq
#print axioms applyCompiledRule?_rejected
#print axioms applyCompiledRuleAt?_eq
#print axioms applyCompiledLanguageAt?_eq

end Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution
