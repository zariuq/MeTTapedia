import Mettapedia.OSLF.Syntax.LambdaPatternRendering
import Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-!
# The authored beta reduct at arbitrary intrinsic lambda contexts

The authored Beta declaration uses an explicit substitution node. This
module compares that node's executable reduct with intrinsic beta after the
body and argument have been supplied as contextual values. Matching those
values against every possible left-hand side is a separate completeness
obligation; this theorem concerns the exact reduct interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaAuthoredBetaExecutionComparison

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
open Mettapedia.OSLF.Binding.LambdaPatternRendering
open Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.Examples.ScopedLamCongExecution

private def termType : TypeExpr := .base "Term"

private def betaSpec : RuleBindingSpec :=
  { dependencies := [("B", [termType]), ("A", [])],
    occurrences :=
      [{ «name» := "B", site := .left, path := [0, 0, 0],
         arguments := [.bvar 0] },
       { «name» := "B", site := .right, path := [0],
         arguments := [.bvar 0] }] }

theorem beta_rule_uses_spec : betaRule.bindings = some betaSpec := rfl

/-- A value produced in the body context retains its one local dependency,
while the argument lives only in the caller's ambient context. -/
def supplied {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) : Assignment :=
  [("B", { dependencies := [termType], ambient := Γ.length,
            body := encodeTerm body }),
   ("A", { dependencies := [], ambient := Γ.length,
            body := encodeTerm argument })]

/-- The matcher prepends captures, so its ordered list is argument then body;
lookup semantics are independent of that list order. -/
def matched {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) : Assignment :=
  [("A", { dependencies := [], ambient := Γ.length,
            body := encodeTerm argument }),
   ("B", { dependencies := [termType], ambient := Γ.length,
            body := encodeTerm body })]

private theorem body_occurrence_identity :
    occurrenceAssignment 1 1 [.bvar 0] = Pattern.bvar := by
  funext index
  cases index with
  | zero => rfl
  | succ n => simp [occurrenceAssignment, Nat.add_comm]

private theorem argument_occurrence_identity :
    occurrenceAssignment 0 0 [] = Pattern.bvar := by
  funext index
  simp [occurrenceAssignment]

private theorem body_recovery_identity (ambient : Nat) :
    recoveryAssignment 1 1 ambient [0] = Pattern.bvar := by
  funext index
  cases index with
  | zero => simp [recoveryAssignment]
  | succ n => simp [recoveryAssignment, Nat.add_comm]

private theorem argument_recovery_identity (ambient : Nat) :
    recoveryAssignment 0 0 ambient [] = Pattern.bvar := by
  funext index
  simp [recoveryAssignment]

/-- At the authored right-hand occurrence, the body is read in precisely its
dependency context and no binder is captured. -/
theorem supplied_body_at_rhs {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) :
    instantiateValue?
      { dependencies := [termType], ambient := Γ.length,
        body := encodeTerm body }
      Γ.length 1 [.bvar 0] = some (encodeTerm body) := by
  have hscoped : (encodeTerm body).isWellScopedAt (1 + Γ.length) = true := by
    have hs := encodeTerm_scoped body
    change (encodeTerm body).isWellScopedAt (Γ.length + 1) = true at hs
    simpa [Nat.add_comm] using hs
  have hvar : (Pattern.bvar 0).isWellScopedAt (1 + Γ.length) = true := by
    simp [Pattern.isWellScopedAt]
  simp [instantiateValue?, hscoped, hvar,
    body_occurrence_identity,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id]

/-- The ambient argument is read unchanged at the rule root. -/
theorem supplied_argument_at_rhs {Γ : Ctx sig}
    (argument : Term sig Γ .term) :
    instantiateValue?
      { dependencies := [], ambient := Γ.length,
        body := encodeTerm argument }
      Γ.length 0 [] = some (encodeTerm argument) := by
  have hscoped := encodeTerm_scoped argument
  simp [instantiateValue?, hscoped,
    argument_occurrence_identity,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id]

/-- Matching the body occurrence recovers the same one-dependency contextual
value later used at the authored right-hand side. -/
theorem recover_body {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term) :
    recoverValue? [termType] Γ.length 1 [.bvar 0] (encodeTerm body) =
      some { dependencies := [termType], ambient := Γ.length,
             body := encodeTerm body } := by
  have hs := encodeTerm_scoped body
  have hscope : (encodeTerm body).isWellScopedAt (1 + Γ.length) = true := by
    change (encodeTerm body).isWellScopedAt (Γ.length + 1) = true at hs
    simpa [Nat.add_comm] using hs
  simp [recoverValue?, hscope, variableSpine?,
    body_recovery_identity,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id,
    supplied_body_at_rhs]

/-- The zero-dependency argument likewise recovers in the ambient context. -/
theorem recover_argument {Γ : Ctx sig}
    (argument : Term sig Γ .term) :
    recoverValue? [] Γ.length 0 [] (encodeTerm argument) =
      some { dependencies := [], ambient := Γ.length,
             body := encodeTerm argument } := by
  have hscope := encodeTerm_scoped argument
  simp [recoverValue?, hscope, variableSpine?,
    argument_recovery_identity,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id,
    supplied_argument_at_rhs]

/-- The actual authored left-hand matcher recovers both contextual values
from every intrinsic beta source, at every ambient context. -/
theorem beta_match_recovers_intrinsic {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    matchRuleAt betaRule betaSpec Γ.length
      (encodeTerm (appT (lamT body) argument)) =
        [matched body argument] := by
  rw [(encode_beta_endpoints body argument).1]
  simp [matchRuleAt, matchAt, matchArgsAt, capture?, assign, lookup,
    betaRule, betaSpec, matched, arguments?, dependencies?,
    occurrenceDeclared, sitePattern?, occurrenceAt?,
    recover_body, recover_argument]

/-- The actual RHS depends on the two named contextual values, independent
of their storage order or any other captured metavariables. -/
theorem beta_reduct_from_values {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) (assignment : Assignment)
    (hbody : lookup assignment "B" = some
      { dependencies := [termType], ambient := Γ.length,
        body := encodeTerm body })
    (hargument : lookup assignment "A" = some
      { dependencies := [], ambient := Γ.length,
        body := encodeTerm argument }) :
    reduct? betaRule betaSpec Γ.length assignment =
      some (encodeTerm (inst body argument)) := by
  have bodyEq := supplied_body_at_rhs body
  have argumentEq := supplied_argument_at_rhs argument
  simp [reduct?, instantiateAt?, betaRule, betaSpec,
    arguments?, dependencies?, occurrenceDeclared,
    sitePattern?, occurrenceAt?, bodyEq, argumentEq,
    hbody, hargument, encode_inst]

/-- The actual authored RHS interpreter computes intrinsic beta for every
well-sorted intrinsic body and argument, in every ambient context. -/
theorem beta_reduct_matches_intrinsic {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    reduct? betaRule betaSpec Γ.length (supplied body argument) =
      some (encodeTerm (inst body argument)) :=
  beta_reduct_from_values body argument _ rfl rfl

/-- The values actually returned by the authored matcher have the same beta
reduct, despite their reversed capture order. -/
theorem beta_reduct_after_match {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    reduct? betaRule betaSpec Γ.length (matched body argument) =
      some (encodeTerm (inst body argument)) :=
  beta_reduct_from_values body argument _ rfl rfl

private theorem beta_admitted : admittedFor betaRule betaSpec = true := by
  decide +kernel

/-- The complete executable authored Beta rule produces one located firing
with the intrinsic contractum and an empty ordered-premise history, in any
intrinsic ambient context. -/
theorem authored_beta_executes_intrinsic {Evidence : Type}
    (oracle : StepOracle Evidence) {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    applyRuleWithOracle oracle
      RelationEnv.empty language Γ.length betaRule
      (encodeTerm (appT (lamT body) argument)) =
        [{ captured := matched body argument,
           completed := matched body argument,
           history := [], target := encodeTerm (inst body argument) }] := by
  have hmatch := beta_match_recovers_intrinsic body argument
  have hreduct := beta_reduct_after_match body argument
  have hscope := encodeTerm_scoped (inst body argument)
  have hno : betaRule.premises = [] := rfl
  simp [applyRuleWithOracle, beta_rule_uses_spec, beta_admitted,
    hmatch, hno, runPremises, finish?, hreduct, hscope]

/-- The actual authored language emits the same beta firing at one layer,
with its selected rule index and empty premise history retained. -/
theorem authored_beta_in_rewriteAt {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term) :
    (RuleHistory.fire 0 [], encodeTerm (inst body argument)) ∈
      rewriteAt RelationEnv.empty language 1 Γ.length
        (encodeTerm (appT (lamT body) argument)) := by
  apply (mem_rewriteAt_succ_iff RelationEnv.empty language 0 Γ.length
    (encodeTerm (appT (lamT body) argument))
    (encodeTerm (inst body argument)) (.fire 0 [])).2
  let firing : RuleFiring RuleHistory :=
    { captured := matched body argument,
      completed := matched body argument,
      history := [], target := encodeTerm (inst body argument) }
  refine ⟨betaRule, 0, ?_, firing, ?_, rfl, rfl⟩
  · simp [language]
  · rw [authored_beta_executes_intrinsic
      (rewriteAt RelationEnv.empty language 0) body argument]
    exact List.mem_singleton.mpr rfl

/-- Every executable Beta firing on an encoded intrinsic redex corresponds
to the beta constructor of the proof-relevant intrinsic rule polynomial. -/
theorem authored_beta_firing_has_tree {Evidence : Type}
    (oracle : StepOracle Evidence) {Γ : Ctx sig}
    (body : Term sig (.term :: Γ) .term)
    (argument : Term sig Γ .term)
    (firing : RuleFiring Evidence)
    (h : firing ∈ applyRuleWithOracle oracle RelationEnv.empty language
      Γ.length betaRule (encodeTerm (appT (lamT body) argument))) :
    ∃ target : Term sig Γ .term,
      firing.target = encodeTerm target ∧
        Nonempty (Derivation (appT (lamT body) argument) target) ∧
        firing.history = [] := by
  rw [authored_beta_executes_intrinsic oracle body argument] at h
  have heq := List.mem_singleton.mp h
  cases heq
  refine ⟨inst body argument, rfl, ?_, rfl⟩
  exact ⟨.roll (.beta body argument)
    (fun impossible => impossible.elim)⟩

/-- A variable is not a Beta redex in the actual authored matcher. -/
theorem authored_beta_rejects_variable :
    applyRuleWithOracle (Evidence := Unit) (fun _ _ => [])
      RelationEnv.empty language 1 betaRule (.bvar 0) = [] := by
  simp [applyRuleWithOracle, matchRuleAt, matchAt, betaRule]

#print axioms beta_reduct_matches_intrinsic
#print axioms beta_match_recovers_intrinsic
#print axioms beta_reduct_after_match
#print axioms authored_beta_executes_intrinsic
#print axioms authored_beta_in_rewriteAt
#print axioms authored_beta_firing_has_tree
#print axioms authored_beta_rejects_variable

end Mettapedia.OSLF.Binding.LambdaAuthoredBetaExecutionComparison
