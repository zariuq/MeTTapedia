import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Framework.RuleRestriction
import Mettapedia.GSLT.LanguageDef.SchemaTyping
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mathlib.Computability.TuringMachine.Config

/-!
# The partial-recursive machine as a language definition

Mathlib's `Turing.ToPartrec` machine evaluates codes for partial recursive
functions on lists of naturals by a continuation-passing small-step semantics:
`stepNormal` descends into a code, building a continuation, and `stepRet` hands a
value to a continuation.  This module authors that machine as a `LanguageDef`,
so that computation over it is reduction in an authored language rather than
evaluation of a Lean function.

Sorts and constructors mirror Mathlib's types one for one:

* `Nat` — unary naturals `Zero`, `Succ`;
* `Nats` — lists `Nil`, `Cons`;
* `Code` — the seven codes `zero'`, `succ`, `tail`, `cons`, `comp`, `case`, `fix`;
* `Cont` — the five continuations `halt`, `cons₁`, `cons₂`, `comp`, `fix`;
* `Cfg` — `Halt` and `Ret` as in Mathlib, and `Normal c k v`, the pending
  `stepNormal c k v` that Mathlib evaluates eagerly and this language reduces.

Every rewrite is premise-free and first order, one per case of `stepNormal` and
`stepRet`.  Where Mathlib inspects `List.headI` or `List.tail`, the empty-list and
cons cases are separate rules, since `headI [] = 0`.

What this module establishes is structural: the definition validates, needs no
relation modes, and every rule is sorted at `Cfg` in its declared variable
context.  The reference controls pin one case's behaviour against the engine.
That reduction agrees with Mathlib's machine on every configuration is the
subject of the adequacy module, not of this one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Constructors: one per constructor of Mathlib's `Nat`, `List ℕ`, `Code`, `Cont`
and `Cfg`, plus `Normal` for a pending `stepNormal`.  Arguments are written
positionally; concrete notation is not part of this definition. -/
def terms : List GrammarRule := [
    { label := "Zero", category := "Nat",
      params := [],
      syntaxPattern := [] },
    { label := "Succ", category := "Nat",
      params := [.simple "n" (.base "Nat")],
      syntaxPattern := [.nonTerminal "n"] },
    { label := "Nil", category := "Nats",
      params := [],
      syntaxPattern := [] },
    { label := "Cons", category := "Nats",
      params := [.simple "head" (.base "Nat"), .simple "tail" (.base "Nats")],
      syntaxPattern := [.nonTerminal "head", .nonTerminal "tail"] },
    { label := "ZeroCode", category := "Code",
      params := [],
      syntaxPattern := [] },
    { label := "SuccCode", category := "Code",
      params := [],
      syntaxPattern := [] },
    { label := "TailCode", category := "Code",
      params := [],
      syntaxPattern := [] },
    { label := "ConsCode", category := "Code",
      params := [.simple "f" (.base "Code"), .simple "fs" (.base "Code")],
      syntaxPattern := [.nonTerminal "f", .nonTerminal "fs"] },
    { label := "CompCode", category := "Code",
      params := [.simple "f" (.base "Code"), .simple "g" (.base "Code")],
      syntaxPattern := [.nonTerminal "f", .nonTerminal "g"] },
    { label := "CaseCode", category := "Code",
      params := [.simple "f" (.base "Code"), .simple "g" (.base "Code")],
      syntaxPattern := [.nonTerminal "f", .nonTerminal "g"] },
    { label := "FixCode", category := "Code",
      params := [.simple "f" (.base "Code")],
      syntaxPattern := [.nonTerminal "f"] },
    { label := "HaltCont", category := "Cont",
      params := [],
      syntaxPattern := [] },
    { label := "Cons1Cont", category := "Cont",
      params := [.simple "fs" (.base "Code"), .simple "as" (.base "Nats"), .simple "k" (.base "Cont")],
      syntaxPattern := [.nonTerminal "fs", .nonTerminal "as", .nonTerminal "k"] },
    { label := "Cons2Cont", category := "Cont",
      params := [.simple "ns" (.base "Nats"), .simple "k" (.base "Cont")],
      syntaxPattern := [.nonTerminal "ns", .nonTerminal "k"] },
    { label := "CompCont", category := "Cont",
      params := [.simple "f" (.base "Code"), .simple "k" (.base "Cont")],
      syntaxPattern := [.nonTerminal "f", .nonTerminal "k"] },
    { label := "FixCont", category := "Cont",
      params := [.simple "f" (.base "Code"), .simple "k" (.base "Cont")],
      syntaxPattern := [.nonTerminal "f", .nonTerminal "k"] },
    { label := "Halt", category := "Cfg",
      params := [.simple "v" (.base "Nats")],
      syntaxPattern := [.nonTerminal "v"] },
    { label := "Ret", category := "Cfg",
      params := [.simple "k" (.base "Cont"), .simple "v" (.base "Nats")],
      syntaxPattern := [.nonTerminal "k", .nonTerminal "v"] },
    { label := "Normal", category := "Cfg",
      params := [.simple "c" (.base "Code"), .simple "k" (.base "Cont"), .simple "v" (.base "Nats")],
      syntaxPattern := [.nonTerminal "c", .nonTerminal "k", .nonTerminal "v"] }
]

/-- Rewrites: one per case of `stepNormal` and `stepRet`, with the empty-list and
cons cases of `List.headI` and `List.tail` as separate rules. -/
def rewrites : List RewriteRule := [
    { name := "ZeroCode"
      typeContext := [("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Normal" [.apply "ZeroCode" [], .fvar "k", .fvar "v"]
      right := .apply "Ret" [.fvar "k", .apply "Cons" [.apply "Zero" [], .fvar "v"]] },
    { name := "SuccOnEmpty"
      typeContext := [("k", .base "Cont")]
      premises := []
      left := .apply "Normal" [.apply "SuccCode" [], .fvar "k", .apply "Nil" []]
      right := .apply "Ret" [.fvar "k", .apply "Cons" [.apply "Succ" [.apply "Zero" []], .apply "Nil" []]] },
    { name := "SuccOnCons"
      typeContext := [("k", .base "Cont"), ("n", .base "Nat"), ("v", .base "Nats")]
      premises := []
      left := .apply "Normal" [.apply "SuccCode" [], .fvar "k", .apply "Cons" [.fvar "n", .fvar "v"]]
      right := .apply "Ret" [.fvar "k", .apply "Cons" [.apply "Succ" [.fvar "n"], .apply "Nil" []]] },
    { name := "TailOnEmpty"
      typeContext := [("k", .base "Cont")]
      premises := []
      left := .apply "Normal" [.apply "TailCode" [], .fvar "k", .apply "Nil" []]
      right := .apply "Ret" [.fvar "k", .apply "Nil" []] },
    { name := "TailOnCons"
      typeContext := [("k", .base "Cont"), ("n", .base "Nat"), ("v", .base "Nats")]
      premises := []
      left := .apply "Normal" [.apply "TailCode" [], .fvar "k", .apply "Cons" [.fvar "n", .fvar "v"]]
      right := .apply "Ret" [.fvar "k", .fvar "v"] },
    { name := "ConsCode"
      typeContext := [("f", .base "Code"), ("fs", .base "Code"), ("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Normal" [.apply "ConsCode" [.fvar "f", .fvar "fs"], .fvar "k", .fvar "v"]
      right := .apply "Normal" [.fvar "f", .apply "Cons1Cont" [.fvar "fs", .fvar "v", .fvar "k"], .fvar "v"] },
    { name := "CompCode"
      typeContext := [("f", .base "Code"), ("g", .base "Code"), ("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Normal" [.apply "CompCode" [.fvar "f", .fvar "g"], .fvar "k", .fvar "v"]
      right := .apply "Normal" [.fvar "g", .apply "CompCont" [.fvar "f", .fvar "k"], .fvar "v"] },
    { name := "CaseOnEmpty"
      typeContext := [("f", .base "Code"), ("g", .base "Code"), ("k", .base "Cont")]
      premises := []
      left := .apply "Normal" [.apply "CaseCode" [.fvar "f", .fvar "g"], .fvar "k", .apply "Nil" []]
      right := .apply "Normal" [.fvar "f", .fvar "k", .apply "Nil" []] },
    { name := "CaseOnZero"
      typeContext := [("f", .base "Code"), ("g", .base "Code"), ("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Normal" [.apply "CaseCode" [.fvar "f", .fvar "g"], .fvar "k", .apply "Cons" [.apply "Zero" [], .fvar "v"]]
      right := .apply "Normal" [.fvar "f", .fvar "k", .fvar "v"] },
    { name := "CaseOnSucc"
      typeContext := [("f", .base "Code"), ("g", .base "Code"), ("k", .base "Cont"), ("y", .base "Nat"), ("v", .base "Nats")]
      premises := []
      left := .apply "Normal" [.apply "CaseCode" [.fvar "f", .fvar "g"], .fvar "k", .apply "Cons" [.apply "Succ" [.fvar "y"], .fvar "v"]]
      right := .apply "Normal" [.fvar "g", .fvar "k", .apply "Cons" [.fvar "y", .fvar "v"]] },
    { name := "FixCode"
      typeContext := [("f", .base "Code"), ("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Normal" [.apply "FixCode" [.fvar "f"], .fvar "k", .fvar "v"]
      right := .apply "Normal" [.fvar "f", .apply "FixCont" [.fvar "f", .fvar "k"], .fvar "v"] },
    { name := "ReturnHalt"
      typeContext := [("v", .base "Nats")]
      premises := []
      left := .apply "Ret" [.apply "HaltCont" [], .fvar "v"]
      right := .apply "Halt" [.fvar "v"] },
    { name := "ReturnCons1"
      typeContext := [("fs", .base "Code"), ("as", .base "Nats"), ("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Ret" [.apply "Cons1Cont" [.fvar "fs", .fvar "as", .fvar "k"], .fvar "v"]
      right := .apply "Normal" [.fvar "fs", .apply "Cons2Cont" [.fvar "v", .fvar "k"], .fvar "as"] },
    { name := "ReturnCons2OnEmpty"
      typeContext := [("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Ret" [.apply "Cons2Cont" [.apply "Nil" [], .fvar "k"], .fvar "v"]
      right := .apply "Ret" [.fvar "k", .apply "Cons" [.apply "Zero" [], .fvar "v"]] },
    { name := "ReturnCons2OnCons"
      typeContext := [("n", .base "Nat"), ("ns", .base "Nats"), ("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Ret" [.apply "Cons2Cont" [.apply "Cons" [.fvar "n", .fvar "ns"], .fvar "k"], .fvar "v"]
      right := .apply "Ret" [.fvar "k", .apply "Cons" [.fvar "n", .fvar "v"]] },
    { name := "ReturnComp"
      typeContext := [("f", .base "Code"), ("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Ret" [.apply "CompCont" [.fvar "f", .fvar "k"], .fvar "v"]
      right := .apply "Normal" [.fvar "f", .fvar "k", .fvar "v"] },
    { name := "ReturnFixOnEmpty"
      typeContext := [("f", .base "Code"), ("k", .base "Cont")]
      premises := []
      left := .apply "Ret" [.apply "FixCont" [.fvar "f", .fvar "k"], .apply "Nil" []]
      right := .apply "Ret" [.fvar "k", .apply "Nil" []] },
    { name := "ReturnFixOnZero"
      typeContext := [("f", .base "Code"), ("k", .base "Cont"), ("v", .base "Nats")]
      premises := []
      left := .apply "Ret" [.apply "FixCont" [.fvar "f", .fvar "k"], .apply "Cons" [.apply "Zero" [], .fvar "v"]]
      right := .apply "Ret" [.fvar "k", .fvar "v"] },
    { name := "ReturnFixOnSucc"
      typeContext := [("f", .base "Code"), ("k", .base "Cont"), ("n", .base "Nat"), ("v", .base "Nats")]
      premises := []
      left := .apply "Ret" [.apply "FixCont" [.fvar "f", .fvar "k"], .apply "Cons" [.apply "Succ" [.fvar "n"], .fvar "v"]]
      right := .apply "Normal" [.fvar "f", .apply "FixCont" [.fvar "f", .fvar "k"], .fvar "v"] }
]

/-- Mathlib's partial-recursive machine, authored. -/
def partrecMachine : LanguageDef :=
  LanguageDef.ofCore "PartrecMachine" ["Nat", "Nats", "Code", "Cont", "Cfg"] terms [] rewrites

theorem partrecMachine_rewrites : partrecMachine.rewrites = rewrites := rfl

/-! ## Structural admission -/

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
private theorem rewrites_validate :
    ∀ rule ∈ partrecMachine.rewrites,
      LanguageDef.validateRewrite partrecMachine rule = [] := by
  intro rule membership
  simp only [partrecMachine_rewrites, rewrites, List.mem_cons, List.mem_nil_iff,
    or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp +decide [LanguageDef.validateRewrite, partrecMachine, LanguageDef.ofCore, terms,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      LanguageDef.typeNames]

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
/-- The definition passes the structural declaration gate. -/
theorem partrecMachine_validate_eq_nil : partrecMachine.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  exact rewrites_validate

/-- No rule needs an external relation mode. -/
theorem partrecMachine_executionFlowErrors_eq_nil :
    partrecMachine.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule membership
    simp only [partrecMachine_rewrites, rewrites, List.mem_cons, List.mem_nil_iff, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro rule membership name nameMembership
    simp only [partrecMachine_rewrites, rewrites, List.mem_cons, List.mem_nil_iff,
      or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [Pattern.freeFvarNames] at nameMembership ⊢
      try tauto

/-- Both sides of every rule are configurations in the rule's declared variable
context. -/
theorem partrecMachine_rules_sorted_at_cfg :
    partrecMachine.rewrites.all (fun rule =>
      checkHasType partrecMachine (FreeTypeContext.ofList rule.typeContext) []
          rule.left (.base "Cfg")
        && checkHasType partrecMachine (FreeTypeContext.ofList rule.typeContext) []
          rule.right (.base "Cfg")) = true := by
  decide +kernel

theorem partrecMachine_rules_wellSorted :
    ∀ rule ∈ partrecMachine.rewrites, RewriteWellSorted partrecMachine rule := by
  intro rule member
  have checked := List.all_eq_true.mp partrecMachine_rules_sorted_at_cfg rule member
  simp only [Bool.and_eq_true] at checked
  exact ⟨.base "Cfg", checkHasType_sound checked.1, checkHasType_sound checked.2⟩

/-! ## Reference controls

`stepNormal succ halt [] = ret halt [1]` in Mathlib, because `headI [] = 0`.  The
authored language performs that step; a variant without the empty-list case
for `succ` is stuck on the same configuration, so the case is load-bearing. -/

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

theorem mathlib_stepNormal_succ_empty :
    Turing.ToPartrec.stepNormal .succ .halt [] = .ret .halt [1] := rfl

def succOnEmptySource : Pattern :=
  .apply "Normal" [.apply "SuccCode" [], .apply "HaltCont" [], .apply "Nil" []]

def succOnEmptyTarget : Pattern :=
  .apply "Ret" [.apply "HaltCont" [],
    .apply "Cons" [.apply "Succ" [.apply "Zero" []], .apply "Nil" []]]

theorem succ_on_empty_steps : Step base partrecMachine succOnEmptySource succOnEmptyTarget :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- The machine with the empty-list case for `succ` removed. -/
def withoutSuccOnEmpty : LanguageDef :=
  partrecMachine.restrictRewrites fun rule => rule.name != "SuccOnEmpty"

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 100000 in
theorem withoutSuccOnEmpty_validate_eq_nil : withoutSuccOnEmpty.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  intro rule membership
  have inMachine : rule ∈ partrecMachine.rewrites := (List.mem_filter.mp membership).1
  exact rewrites_validate rule inMachine

theorem withoutSuccOnEmpty_stuck (target : Pattern) :
    ¬ Step base withoutSuccOnEmpty succOnEmptySource target := by
  apply not_step_of_matchPatternForRule_eq_nil
  have none : withoutSuccOnEmpty.rewrites.all (fun rule =>
      matchPatternForRule withoutSuccOnEmpty rule succOnEmptySource == []) = true := by
    decide +kernel
  intro rule member
  exact beq_iff_eq.mp (List.all_eq_true.mp none rule member)

/-! ## Axiom audit -/

#print axioms partrecMachine_validate_eq_nil
#print axioms partrecMachine_executionFlowErrors_eq_nil
#print axioms partrecMachine_rules_wellSorted
#print axioms succ_on_empty_steps
#print axioms withoutSuccOnEmpty_stuck

end Mettapedia.Languages.PartrecMachine
