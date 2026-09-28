import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution
import Mettapedia.OSLF.MeTTaIL.ScopedStepPremise

/-!
# Contextual execution of authored step premises

Step premises execute in their declared local binder context. The supplied
step oracle returns individual firing witnesses; its list positions are kept
even when two firings have the same witness and endpoints. Ordinary root
premises continue through the existing premise machine, with an explicit
restriction on occurrence substitutions that machine cannot interpret.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.Engine

/-- A step oracle is indexed by the full context size of its source and
returns individual evidence, rather than only a set of possible endpoints. -/
abbrev StepOracle (Evidence : Type) := Nat → Pattern → List (Evidence × Pattern)

/-- The source of each event remains visible in a conditional rule history.
The ordinal distinguishes repeated equal entries in an oracle result list. -/
inductive PremiseEvent (Evidence : Type) where
  | step (premiseIndex resultIndex : Nat) (evidence : Evidence)
  | root (premiseIndex resultIndex : Nat)
deriving Repr, DecidableEq

/-- A root premise may use the old machine only if none of its endpoint sites
has an explicit occurrence substitution. -/
def hasOccurrenceAt (spec : RuleBindingSpec) (index : Nat) : Bool :=
  spec.occurrences.any fun row =>
    match row.site with
    | .premise actual _ _ => actual == index
    | _ => false

/-- Execute one step premise in its own binder prefix. Source instantiation
uses the authored occurrence substitutions; target matching recovers values in
their declared dependency contexts. Ill-scoped oracle results are rejected. -/
def stepResults {Evidence : Type} (oracle : StepOracle Evidence)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient index localDepth : Nat)
    (source target : Pattern) (assignment : Assignment) :
    List (PremiseEvent Evidence × Assignment) :=
  match instantiateAt? rule spec ambient (.premise index 0 0) [] localDepth
      assignment source with
  | none => []
  | some instantiated =>
      if instantiated.isWellScopedAt (localDepth + ambient) then
        (oracle (localDepth + ambient) instantiated).zipIdx.flatMap fun
            ((evidence, candidate), resultIndex) =>
          if candidate.isWellScopedAt (localDepth + ambient) then
            (matchAt rule spec ambient (.premise index 0 1) [] localDepth
              assignment target candidate).map fun completed =>
                (.step index resultIndex evidence, completed)
          else []
      else []

/-- Existing freshness and relation-table behavior at the root, with each
returned occurrence located. Collection quantification remains unsupported by
the base evaluator and supplies no result here. -/
def rootResults {Evidence : Type} (relEnv : RelationEnv)
    (lang : LanguageDef) (spec : RuleBindingSpec) (ambient index : Nat)
    (premise : Premise) (assignment : Assignment) :
    List (PremiseEvent Evidence × Assignment) :=
  if hasOccurrenceAt spec index then [] else
  match projectRoot? ambient assignment with
  | none => []
  | some root =>
      (premiseStepWithEnv relEnv lang root premise).zipIdx.filterMap fun
          (result, resultIndex) => do
        let completed ← extendRoot? spec ambient assignment result
        some (.root index resultIndex, completed)

/-- The new step case uses contextual matching. Other cases retain the
restricted root adapter until their own contextual interpretation is proved. -/
def premiseResults {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (lang : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index : Nat)
    (premise : Premise) (assignment : Assignment) :
    List (PremiseEvent Evidence × Assignment) :=
  match premise with
  | .scopedStep step =>
      if step.isWellScopedAt ambient then
        stepResults oracle rule spec ambient index step.binders.length
          step.source step.target assignment
      else []
  | .congruence source target =>
      stepResults oracle rule spec ambient index 0 source target assignment
  | premise => rootResults relEnv lang spec ambient index premise assignment

/-- Ordered premise execution retains the evidence for each selected firing
in source order. -/
def runPremises {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (lang : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : Nat) :
    Nat → List Premise → Assignment →
      List (Assignment × List (PremiseEvent Evidence))
  | _, [], assignment => [(assignment, [])]
  | index, premise :: rest, assignment =>
      (premiseResults oracle relEnv lang rule spec ambient index premise
        assignment).flatMap fun (event, completed) =>
          (runPremises oracle relEnv lang rule spec ambient
            (index + 1) rest completed).map fun (final, history) =>
              (final, event :: history)

/-- Every successful ordered run records exactly one selected event per
authored premise, including root checks and binder-local reductions. -/
theorem runPremises_history_length {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (lang : LanguageDef) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index : Nat) (premises : List Premise)
    (initial final : Assignment) (history : List (PremiseEvent Evidence))
    (h : (final, history) ∈ runPremises oracle relEnv lang rule spec
      ambient index premises initial) :
    history.length = premises.length := by
  induction premises generalizing index initial final history with
  | nil =>
      simp only [runPremises, List.mem_singleton, Prod.mk.injEq] at h
      exact h.2.symm ▸ rfl
  | cons premise rest inductionHypothesis =>
      simp only [runPremises, List.mem_flatMap, List.mem_map] at h
      obtain ⟨⟨event, completed⟩, _, ⟨next, tail⟩, htail, hresult⟩ := h
      cases hresult
      simp [inductionHypothesis (index := index + 1)
        (initial := completed) (final := next) (history := tail) htail]

/-- A located rule firing remembers the initial and final contextual values
as well as each ordered premise witness. -/
structure RuleFiring (Evidence : Type) where
  captured : Assignment
  completed : Assignment
  history : List (PremiseEvent Evidence)
  target : Pattern
deriving Repr, DecidableEq

/-- Admit a reduct only when it is still scoped in the caller's context. -/
def finish? {Evidence : Type} (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : Nat)
    (captured completed : Assignment)
    (history : List (PremiseEvent Evidence)) : Option (RuleFiring Evidence) := do
  let target ← reduct? rule spec ambient completed
  if target.isWellScopedAt ambient then
    some { captured, completed, history, target }
  else none

theorem finish?_scoped {Evidence : Type} (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : Nat)
    (captured completed : Assignment)
    (history : List (PremiseEvent Evidence)) (firing : RuleFiring Evidence)
    (h : finish? rule spec ambient captured completed history = some firing) :
    firing.target.isWellScopedAt ambient = true := by
  unfold finish? at h
  cases hred : reduct? rule spec ambient completed with
  | none => simp [hred] at h
  | some target =>
      by_cases hscope : target.isWellScopedAt ambient = true
      · simp [hred, hscope] at h
        cases h
        exact hscope
      · simp [hred, hscope] at h

/-- Apply one authored rule with the contextual premise interpreter. -/
def applyRuleWithOracle {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (lang : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (term : Pattern) : List (RuleFiring Evidence) :=
  match rule.bindings with
  | none => []
  | some spec =>
      if admittedFor rule spec then
        (matchRuleAt rule spec ambient term).flatMap fun captured =>
          (runPremises oracle relEnv lang rule spec ambient 0
            rule.premises captured).filterMap fun (completed, history) =>
              finish? rule spec ambient captured completed history
      else []

/-- Every returned firing is generated by an admitted declaration, one
matching capture, the ordered premise run, and an in-scope reduct. -/
theorem mem_applyRuleWithOracle_iff {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (lang : LanguageDef) (ambient : Nat) (rule : RewriteRule)
    (term : Pattern) (firing : RuleFiring Evidence) :
    firing ∈ applyRuleWithOracle oracle relEnv lang ambient rule term ↔
      ∃ spec captured completed history,
        rule.bindings = some spec ∧ admittedFor rule spec = true ∧
        captured ∈ matchRuleAt rule spec ambient term ∧
        (completed, history) ∈
          runPremises oracle relEnv lang rule spec ambient 0
            rule.premises captured ∧
        finish? rule spec ambient captured completed history = some firing := by
  cases hspec : rule.bindings with
  | none => simp [applyRuleWithOracle, hspec]
  | some spec =>
      by_cases hvalid : admittedFor rule spec = true
      · simp only [applyRuleWithOracle, hspec, hvalid, if_true,
          List.mem_flatMap, List.mem_filterMap]
        constructor
        · rintro ⟨captured, hcaptured, pair, hpair, hresult⟩
          rcases pair with ⟨completed, history⟩
          exact ⟨spec, captured, completed, history, rfl,
            hvalid, hcaptured, hpair, hresult⟩
        · rintro ⟨chosen, captured, completed, history, hchosen,
            hvalid', hcaptured, hpair, hresult⟩
          cases Option.some.inj hchosen
          exact ⟨captured, hcaptured, (completed, history), hpair, hresult⟩
      · have hfalse : admittedFor rule spec = false :=
          Bool.eq_false_iff.mpr hvalid
        simp [applyRuleWithOracle, hspec, hfalse]

theorem applyRuleWithOracle_scoped {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (lang : LanguageDef) (ambient : Nat) (rule : RewriteRule)
    (term : Pattern) (firing : RuleFiring Evidence)
    (h : firing ∈ applyRuleWithOracle oracle relEnv lang ambient rule term) :
    firing.target.isWellScopedAt ambient = true := by
  obtain ⟨spec, captured, completed, history, _, _, _, _, hfinish⟩ :=
    (mem_applyRuleWithOracle_iff oracle relEnv lang ambient rule term firing).mp h
  exact finish?_scoped rule spec ambient captured completed history firing hfinish

/-- A free firing tree records the selected authored rule position and all
ordered premise events. Recursive events carry their own trees. -/
inductive RuleHistory where
  | fire (ruleIndex : Nat) (premises : List (PremiseEvent RuleHistory))
deriving Repr

/-- Fuel bounds the height of nested authored step premises. Rule and oracle
list positions remain in the returned history rather than being quotiented by
equal endpoints. -/
def rewriteAt (relEnv : RelationEnv) (lang : LanguageDef) :
    Nat → StepOracle RuleHistory
  | 0, _, _ => []
  | fuel + 1, ambient, source =>
      lang.rewrites.zipIdx.flatMap fun (rule, ruleIndex) =>
        (applyRuleWithOracle (rewriteAt relEnv lang fuel) relEnv lang
          ambient rule source).map fun firing =>
            (.fire ruleIndex firing.history, firing.target)

/-- Every bounded result comes from a located authored rule and one complete
contextual premise run at the preceding depth. -/
theorem mem_rewriteAt_succ_iff (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern) (history : RuleHistory) :
    (history, target) ∈ rewriteAt relEnv lang (fuel + 1) ambient source ↔
      ∃ rule ruleIndex, (rule, ruleIndex) ∈ lang.rewrites.zipIdx ∧
        ∃ firing ∈ applyRuleWithOracle (rewriteAt relEnv lang fuel)
          relEnv lang ambient rule source,
          history = .fire ruleIndex firing.history ∧ target = firing.target := by
  simp only [rewriteAt, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨rule, ruleIndex⟩, hrule, firing, hfiring, heq⟩
    exact ⟨rule, ruleIndex, hrule, firing, hfiring,
      (Prod.mk.inj heq).1.symm, (Prod.mk.inj heq).2.symm⟩
  · rintro ⟨rule, ruleIndex, hrule, firing, hfiring, hhistory, htarget⟩
    exact ⟨(rule, ruleIndex), hrule, firing, hfiring,
      by cases hhistory; cases htarget; rfl⟩

/-- No recursive premise can fire at depth zero. -/
theorem rewriteAt_zero (relEnv : RelationEnv) (lang : LanguageDef)
    (ambient : Nat) (source : Pattern) :
    rewriteAt relEnv lang 0 ambient source = [] := rfl

/-- The fuel-indexed evaluator always returns a reduct in the context it was
asked to rewrite, regardless of how many premise binders were traversed. -/
theorem rewriteAt_scoped (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern) (history : RuleHistory)
    (h : (history, target) ∈ rewriteAt relEnv lang fuel ambient source) :
    target.isWellScopedAt ambient = true := by
  cases fuel with
  | zero => simp [rewriteAt] at h
  | succ fuel =>
      obtain ⟨rule, ruleIndex, _, firing, hfiring, _, htarget⟩ :=
        (mem_rewriteAt_succ_iff relEnv lang fuel ambient
          source target history).mp h
      subst target
      exact applyRuleWithOracle_scoped
        (rewriteAt relEnv lang fuel) relEnv lang ambient rule source firing hfiring

end Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
