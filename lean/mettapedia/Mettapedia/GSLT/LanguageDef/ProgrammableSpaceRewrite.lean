import Mettapedia.GSLT.Core.ProgrammableSpace
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceSyntax
import Mettapedia.OSLF.Syntax.LambdaAuthoredBetaExecutionComparison

/-!
# Authored scoped rewriting as a programmable-space language

The adapter executes the existing scoped authored-rule interpreter. Its
receipts keep the declaration position, contextual captures, completed
assignment and ordered premise history. Finite premise depth belongs to the
receipt; it is not a claim that a bounded search has exhausted the calculus.

This language reads the shared store without modifying it. Its declared
outcome is the current term, which need not be a normal form. Publishing a
result as a fact is a separate transaction. The lambda instance below uses
the existing authored Beta schema at every intrinsic ambient context.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceRewrite

open Mettapedia.GSLT.Core.ProgrammableSpace
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

structure Scope where
  ambient : Nat
  relations : RelationEnv

structure Receipt where
  premiseDepth : Nat
  ruleIndex : Nat
  firing : RuleFiring RuleHistory

def Receipt.history (receipt : Receipt) : RuleHistory :=
  .fire receipt.ruleIndex receipt.firing.history

def SourceEvent (calculus : LanguageDef) (scope : Scope)
    (source : Pattern) (receipt : Receipt) (target : Pattern) : Prop :=
  ∃ rule, (rule, receipt.ruleIndex) ∈ calculus.rewrites.zipIdx ∧
    receipt.firing ∈ applyRuleWithOracle
      (rewriteAt scope.relations calculus receipt.premiseDepth)
      scope.relations calculus scope.ambient rule source ∧
    receipt.firing.target = target

/-- Forgetting the capture record yields an actual source history and reduct. -/
theorem source_event_executes (calculus : LanguageDef) (scope : Scope)
    (source : Pattern) (receipt : Receipt) (target : Pattern)
    (event : SourceEvent calculus scope source receipt target) :
    (receipt.history, target) ∈ rewriteAt scope.relations calculus
      (receipt.premiseDepth + 1) scope.ambient source := by
  obtain ⟨rule, located, generated, targetEq⟩ := event
  exact (mem_rewriteAt_succ_iff scope.relations calculus receipt.premiseDepth
    scope.ambient source target receipt.history).mpr
      ⟨rule, receipt.ruleIndex, located, receipt.firing, generated, rfl, targetEq.symm⟩

/-- Every source result supplies a retained receipt, including the original
captured and completed contextual assignments. -/
theorem executed_has_receipt (calculus : LanguageDef) (scope : Scope)
    (depth : Nat) (source target : Pattern) (history : RuleHistory)
    (executed : (history, target) ∈ rewriteAt scope.relations calculus
      (depth + 1) scope.ambient source) :
    ∃ receipt : Receipt, SourceEvent calculus scope source receipt target ∧
      receipt.premiseDepth = depth ∧ receipt.history = history := by
  obtain ⟨rule, index, located, firing, generated, historyEq, targetEq⟩ :=
    (mem_rewriteAt_succ_iff scope.relations calculus depth scope.ambient source target history).mp executed
  exact ⟨⟨depth, index, firing⟩, ⟨rule, located, generated, targetEq.symm⟩,
    rfl, historyEq.symm⟩

theorem receipt_exists_iff_source_reduct (calculus : LanguageDef) (scope : Scope)
    (source target : Pattern) :
    (∃ receipt, SourceEvent calculus scope source receipt target) ↔
      ∃ depth history, (history, target) ∈
        rewriteAt scope.relations calculus depth scope.ambient source := by
  constructor
  · rintro ⟨receipt, event⟩
    exact ⟨receipt.premiseDepth + 1, receipt.history,
      source_event_executes calculus scope source receipt target event⟩
  · rintro ⟨depth, history, executed⟩
    cases depth with
    | zero => cases executed
    | succ depth =>
        obtain ⟨receipt, event, _, _⟩ :=
          executed_has_receipt calculus scope depth source target history executed
        exact ⟨receipt, event⟩

theorem source_event_scoped (calculus : LanguageDef) (scope : Scope)
    (source : Pattern) (receipt : Receipt) (target : Pattern)
    (event : SourceEvent calculus scope source receipt target) :
    target.isWellScopedAt scope.ambient = true :=
  rewriteAt_scoped scope.relations calculus (receipt.premiseDepth + 1)
    scope.ambient source target receipt.history
    (source_event_executes calculus scope source receipt target event)

def language (calculus : LanguageDef) : Language Atom where
  Scope := Scope
  Request := Pattern
  Residual := Pattern
  Outcome := Pattern
  Receipt := Receipt
  admit atom request := ProgrammableSpaceSyntax.decode atom = some request
  initial _ request _ := request
  advance scope before source receipt after target :=
    after = before ∧ SourceEvent calculus scope source receipt target
  observes residual current := residual = current

theorem adapter_exact (calculus : LanguageDef) (scope : Scope)
    (atoms : List Atom) (source target : Pattern) :
    (∃ receipt, (language calculus).advance scope atoms source receipt atoms target) ↔
      ∃ depth history, (history, target) ∈
        rewriteAt scope.relations calculus depth scope.ambient source := by
  rw [← receipt_exists_iff_source_reduct]
  exact ⟨fun ⟨receipt, _, event⟩ => ⟨receipt, event⟩,
    fun ⟨receipt, event⟩ => ⟨receipt, rfl, event⟩⟩

theorem request_admitted (calculus : LanguageDef) (request : Pattern) :
    (language calculus).admit (ProgrammableSpaceSyntax.encode request) request :=
  ProgrammableSpaceSyntax.decode_encode request

theorem foreign_exec_inert (calculus : LanguageDef) (priority inputs outputs : Atom) :
    ¬ ∃ request, (language calculus).admit
      (.expression [.symbol "exec", priority, inputs, outputs]) request := by
  rintro ⟨request, admitted⟩
  change (none : Option Pattern) = some request at admitted
  cases admitted

theorem store_preserved (calculus : LanguageDef) (scope : Scope)
    (before after : List Atom) (source target : Pattern) (receipt : Receipt)
    (event : (language calculus).advance scope before source receipt after target) :
    after = before := event.1

/-- Policy bounds source proof height and accounts for each admitted event.
The counter records work; it does not decide which source terms are equal. -/
def depthPolicy (calculus : LanguageDef) (bound : Nat) : Policy (language calculus) where
  State := Nat
  permits spent _ _ _ receipt _ _ next :=
    receipt.premiseDepth < bound ∧ next = spent + 1

theorem depth_policy_accounts (calculus : LanguageDef) (bound spent next : Nat)
    (scope : Scope) (before after : List Atom) (source target : Pattern) (receipt : Receipt)
    (permitted : (depthPolicy calculus bound).permits spent scope before source receipt after target next) :
    next = spent + 1 := permitted.2

namespace Lambda

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaPatternRendering
open Mettapedia.OSLF.Binding.LambdaAuthoredBetaExecutionComparison
open Mettapedia.OSLF.Binding.LambdaScopedAuthoringComparison
open Mettapedia.GSLT.Examples.ScopedLamCongExecution

abbrev calculus := Mettapedia.GSLT.Examples.ScopedLamCongExecution.language

def scope (context : Ctx sig) : Scope := ⟨context.length, RelationEnv.empty⟩

def betaReceipt {context : Ctx sig} (body : Term sig (.term :: context) .term)
    (argument : Term sig context .term) : Receipt where
  premiseDepth := 0
  ruleIndex := 0
  firing := {
    captured := matched body argument
    completed := matched body argument
    history := []
    target := encodeTerm (inst body argument) }

theorem beta_event {context : Ctx sig} (body : Term sig (.term :: context) .term)
    (argument : Term sig context .term) :
    SourceEvent calculus (scope context) (encodeTerm (appT (lamT body) argument))
      (betaReceipt body argument) (encodeTerm (inst body argument)) := by
  refine ⟨betaRule, ?_, ?_, rfl⟩
  · simp [calculus, Mettapedia.GSLT.Examples.ScopedLamCongExecution.language, betaReceipt]
  · change _ ∈ applyRuleWithOracle _ RelationEnv.empty calculus context.length betaRule _
    rw [authored_beta_executes_intrinsic]
    exact List.mem_singleton_self _

theorem beta_adapter {context : Ctx sig} (body : Term sig (.term :: context) .term)
    (argument : Term sig context .term) (atoms : List Atom) :
    (ProgrammableSpaceRewrite.language calculus).advance (scope context) atoms
      (encodeTerm (appT (lamT body) argument)) (betaReceipt body argument) atoms
      (encodeTerm (inst body argument)) :=
  ⟨rfl, beta_event body argument⟩

end Lambda

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceRewrite
