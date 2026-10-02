import Mettapedia.Languages.Agda.Intrinsic.Lowering
import Mettapedia.Languages.Agda.Intrinsic.Semantics

/-!
# Execution of the generated structural rules

The generic contextual executor consumes the rules compiled from the same
intrinsic table used by the presheaf semantics. Its bounded result retains
rule and premise positions. The language value below is an execution
environment; it does not supply an Agda concrete-syntax parser.

The quantified beta theorem checks the real matcher and reduct interpreter
on every scoped body and argument. General soundness and completeness of the
whole lowered executor remain a distinct obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic.Execution

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.Engine
open Rendering (encode encode_scoped encode_inst encode_beta_endpoints)

/-- Only the generated operational table is consumed by the scoped executor.
Concrete source syntax and static Agda judgments have separate interfaces. -/
def language : LanguageDef :=
  { name := "agda-intrinsic-operations"
    types := [.plain "Term"]
    terms := []
    equations := []
    rewrites := Lowering.compiled }

def run {Γ : Ctx sig} (fuel : Nat) (source : Tm Γ) :
    List (RuleHistory × Pattern) :=
  rewriteAt RelationEnv.empty language fuel Γ.length (encode source)

def betaRule : RewriteRule := Lowering.compiled[0]'(by decide +kernel)

private def termType : TypeExpr := .base "Term"

private def betaSpec : RuleBindingSpec :=
  { dependencies := [("m0", [termType]), ("m1", [termType]),
      ("m2", []), ("m3", []), ("m4", []), ("m5", []), ("m6", []), ("m7", [])]
    occurrences :=
      [⟨"m0", .left, [0, 0, 0], [.bvar 0]⟩,
       ⟨"m0", .right, [0], [.bvar 0]⟩] }

/-- This equality evaluates the compiler on the actual intrinsic beta schema.
The executable rule is not authored a second time. -/
private theorem beta_view : betaRule =
    { name := "agda-step-0"
      typeContext := [("m0", termType), ("m1", termType), ("m2", termType),
        ("m3", termType), ("m4", termType), ("m5", termType),
        ("m6", termType), ("m7", termType)]
      premises := []
      left := .apply "App" [.apply "Lam" [.lambda none (.fvar "m0")], .fvar "m2"]
      right := .subst (.fvar "m0") (.fvar "m2")
      bindings := some betaSpec } := rfl

def matched {Γ : Ctx sig} (body : Tm (.term :: Γ)) (argument : Tm Γ) : Assignment :=
  [("m2", ⟨[], Γ.length, encode argument⟩),
   ("m0", ⟨[termType], Γ.length, encode body⟩)]

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

private theorem instantiate_body {Γ : Ctx sig} (body : Tm (.term :: Γ)) :
    instantiateValue? ⟨[termType], Γ.length, encode body⟩
      Γ.length 1 [.bvar 0] = some (encode body) := by
  have hscoped : (encode body).isWellScopedAt (1 + Γ.length) = true := by
    have h := encode_scoped body
    change (encode body).isWellScopedAt (Γ.length + 1) = true at h
    simpa only [Nat.add_comm] using h
  have varScoped : (Pattern.bvar 0).isWellScopedAt (1 + Γ.length) = true := by
    simp [Pattern.isWellScopedAt]
  simp [instantiateValue?, hscoped, varScoped, body_occurrence_identity,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id]

private theorem instantiate_argument {Γ : Ctx sig} (argument : Tm Γ) :
    instantiateValue? ⟨[], Γ.length, encode argument⟩
      Γ.length 0 [] = some (encode argument) := by
  simp [instantiateValue?, encode_scoped argument, argument_occurrence_identity,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id]

private theorem recover_body {Γ : Ctx sig} (body : Tm (.term :: Γ)) :
    recoverValue? [termType] Γ.length 1 [.bvar 0] (encode body) =
      some ⟨[termType], Γ.length, encode body⟩ := by
  have hscoped : (encode body).isWellScopedAt (1 + Γ.length) = true := by
    have h := encode_scoped body
    change (encode body).isWellScopedAt (Γ.length + 1) = true at h
    simpa only [Nat.add_comm] using h
  simp [recoverValue?, hscoped, variableSpine?, body_recovery_identity,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id, instantiate_body]

private theorem recover_argument {Γ : Ctx sig} (argument : Tm Γ) :
    recoverValue? [] Γ.length 0 [] (encode argument) =
      some ⟨[], Γ.length, encode argument⟩ := by
  simp [recoverValue?, encode_scoped argument, variableSpine?, argument_recovery_identity,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute_id, instantiate_argument]

theorem beta_match_recovers {Γ : Ctx sig}
    (body : Tm (.term :: Γ)) (argument : Tm Γ) :
    matchRuleAt betaRule betaSpec Γ.length (encode (app (lam body) argument)) =
      [matched body argument] := by
  rw [(encode_beta_endpoints body argument).1, beta_view]
  simp [matchRuleAt, matchRuleWithAt, matchAtWith, matchArgsAtWith, capture?, assign, lookup,
    betaSpec, matched, arguments?, dependencies?, occurrenceDeclared,
    sitePattern?, occurrenceAt?, recover_body, recover_argument]

theorem beta_reduct_correct {Γ : Ctx sig}
    (body : Tm (.term :: Γ)) (argument : Tm Γ) :
    reduct? betaRule betaSpec Γ.length (matched body argument) =
      some (encode (inst body argument)) := by
  rw [beta_view]
  simp [reduct?, instantiateAt?, instantiateWith?, betaSpec, matched, lookup, arguments?, dependencies?,
    occurrenceDeclared, sitePattern?, occurrenceAt?, instantiate_body,
    instantiate_argument, encode_inst]

private theorem beta_admitted : admittedFor betaRule betaSpec = true := by decide +kernel

/-- The actual generic rule executor computes structural beta in every open
context. Its premise oracle is unused because beta is unconditional. -/
theorem beta_executes {Evidence : Type} (oracle : StepOracle Evidence)
    {Γ : Ctx sig} (body : Tm (.term :: Γ)) (argument : Tm Γ) :
    applyRuleWithOracle oracle RelationEnv.empty language Γ.length betaRule
      (encode (app (lam body) argument)) =
        [⟨matched body argument, matched body argument, [], encode (inst body argument)⟩] := by
  have bindings : betaRule.bindings = some betaSpec := rfl
  have noPremises : betaRule.premises = [] := rfl
  simp [applyRuleWithOracle, bindings, beta_admitted, beta_match_recovers,
    noPremises, runPremises, finish?, beta_reduct_correct, encode_scoped]

/-- Executable beta and term-level OSLF have the same intrinsic endpoints. -/
theorem beta_execution_and_modality {Γ : Ctx sig}
    (body : Tm (.term :: Γ)) (argument : Tm Γ) :
    reduct? betaRule betaSpec Γ.length (matched body argument) =
      some (encode (inst body argument)) ∧
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
      (Semantics.theory Γ) (Semantics.predicate (fun t => t = inst body argument))
      (Semantics.state (app (lam body) argument)) :=
  ⟨beta_reduct_correct body argument, Semantics.beta_observable body argument⟩

end Mettapedia.Languages.Agda.Intrinsic.Execution
