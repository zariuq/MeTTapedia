import Mettapedia.OSLF.Syntax.CanonicalScopedRuleExecution

/-!
# Context-indexed step evidence for canonical scoped premises

A depth-only oracle cannot distinguish two sorted binder contexts of equal
length. The canonical executor below supplies the entire local binder prefix
followed by the ambient context to every recursive step query. Forgetting the
sort list to its length recovers the existing scoped executor exactly,
including the order and multiplicity of firing evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalContextOracle

open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.Binding.CanonicalScopedRuleExecution

/-- A recursive reduction provider receives the full ordered sort context
of the term it is asked to step, not just that context's length. -/
abbrev ContextOracle (Evidence : Type) :=
  List TypeExpr → Pattern → List (Evidence × Pattern)

/-- Any current depth-indexed oracle defines a context-indexed one by
forgetting the sorts but retaining the exact context length. -/
def fromDepth {Evidence : Type} (oracle : StepOracle Evidence) :
    ContextOracle Evidence :=
  fun context source => oracle context.length source

/-- A depth-indexed provider cannot distinguish equal-length contexts. -/
theorem fromDepth_eq_of_length_eq {Evidence : Type}
    (oracle : StepOracle Evidence) {first second : List TypeExpr}
    (sameLength : first.length = second.length) (source : Pattern) :
    fromDepth oracle first source = fromDepth oracle second source := by
  simp [fromDepth, sameLength]

/-- Exactly the invariance needed to forget the sorts of a recursive query
without changing any evidence or outcome order. -/
def DepthInvariant {Evidence : Type} (oracle : ContextOracle Evidence) : Prop :=
  ∀ first second source,
    first.length = second.length →
      oracle first source = oracle second source

/-- A context oracle factors through depth precisely when it is invariant
under every change of sort list that preserves the context length. -/
theorem depthInvariant_iff_fromDepth {Evidence : Type}
    (oracle : ContextOracle Evidence) :
    DepthInvariant oracle ↔
      ∃ depthOracle : StepOracle Evidence,
        fromDepth depthOracle = oracle := by
  constructor
  · intro invariant
    refine ⟨fun depth source =>
      oracle (List.replicate depth (.base "Term")) source, ?_⟩
    funext context source
    exact invariant (List.replicate context.length (.base "Term"))
      context source (by simp)
  · rintro ⟨depthOracle, rfl⟩
    intro first second source sameLength
    exact fromDepth_eq_of_length_eq depthOracle sameLength source

/-- This context-indexed provider deliberately accepts a term-context query
and rejects an equally long query in a different sort. -/
def separatingOracle : ContextOracle Unit :=
  fun context _ =>
    if context = [.base "Term"] then [((), .fvar "answer")] else []

theorem separatingOracle_distinguishes_sorts :
    separatingOracle [.base "Term"] (.fvar "query") ≠
      separatingOracle [.base "Other"] (.fvar "query") := by
  decide +kernel

/-- No oracle indexed only by depth can implement that sorted behavior. -/
theorem separatingOracle_not_fromDepth :
    ¬ ∃ oracle : StepOracle Unit, fromDepth oracle = separatingOracle := by
  rintro ⟨oracle, equality⟩
  have same := fromDepth_eq_of_length_eq oracle
    (first := [.base "Term"]) (second := [.base "Other"]) rfl
    (.fvar "query")
  rw [equality] at same
  exact separatingOracle_distinguishes_sorts same

/-- The recursive query runs in `binders ++ ambient`. Explicit occurrence
substitutions still use the existing binding-aware matcher, and the selected
list position remains part of each emitted premise event. -/
def stepResults {Evidence : Type} (oracle : ContextOracle Evidence)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) (index : Nat)
    (step : ScopedStepPremise) (assignment : Assignment) :
    List (PremiseEvent Evidence × Assignment) :=
  match instantiateAt? rule spec ambient.length (.premise index 0 0) []
      step.binders.length assignment step.source with
  | none => []
  | some instantiated =>
      if instantiated.isWellScopedAt (step.binders ++ ambient).length then
        (oracle (step.binders ++ ambient) instantiated).zipIdx.flatMap fun
            ((evidence, candidate), resultIndex) =>
          if candidate.isWellScopedAt (step.binders ++ ambient).length then
            (matchAt rule spec ambient.length (.premise index 0 1) []
              step.binders.length assignment step.target candidate).map
                fun completed => (.step index resultIndex evidence, completed)
          else []
      else []

/-- Erasing the context sort list makes the new step executor exactly the
old one for every binding assignment and every oracle outcome list. -/
theorem stepResults_fromDepth {Evidence : Type}
    (oracle : StepOracle Evidence) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (index : Nat) (step : ScopedStepPremise) (assignment : Assignment) :
    stepResults (fromDepth oracle) rule spec ambient index step assignment =
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.stepResults oracle rule spec ambient.length
        index step.binders.length step.source step.target assignment := by
  simp only [stepResults, Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.stepResults,
    fromDepth, List.length_append]
  rfl

/-- All executable canonical forms use the same context-indexed step
interface. Non-step premises keep the existing ordered base evaluator. -/
def premiseResults {Evidence : Type} (oracle : ContextOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) (index : Nat)
    (premise : CanonicalPremise) (assignment : Assignment) :
    List (PremiseEvent Evidence × Assignment) :=
  match premise with
  | .step step =>
      if step.isWellScopedAt ambient.length then
        stepResults oracle rule spec ambient index step assignment
      else []
  | .freshness condition =>
      rootResults relEnv language spec ambient.length index
        (.freshness condition) assignment
  | .relationQuery relation arguments =>
      rootResults relEnv language spec ambient.length index
        (.relationQuery relation arguments) assignment
  | .forAll collection parameter body =>
      rootResults relEnv language spec ambient.length index
        (.forAll collection parameter body.toAuthored) assignment

/-- The canonical premise semantics agrees with the old executable meaning
after depth erasure; even equal oracle values retain their list positions. -/
theorem premiseResults_fromDepth {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (index : Nat) (premise : CanonicalPremise)
    (assignment : Assignment) :
    premiseResults (fromDepth oracle) relEnv language rule spec ambient
        index premise assignment =
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.premiseResults oracle relEnv language rule
        spec ambient.length index premise.toAuthored assignment := by
  cases premise with
  | freshness _ => rfl
  | step step =>
      simp only [premiseResults, CanonicalPremise.toAuthored,
        Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.premiseResults]
      split
      · exact stepResults_fromDepth oracle rule spec ambient index step
          assignment
      · rfl
  | relationQuery _ _ => rfl
  | forAll _ _ _ => rfl

/-- Canonical ordered execution propagates the full ambient sort context to
each step premise and retains one event per authored premise position. -/
def runPremises {Evidence : Type} (oracle : ContextOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : List TypeExpr) :
    Nat → List CanonicalPremise → Assignment →
      List (Assignment × List (PremiseEvent Evidence))
  | _, [], assignment => [(assignment, [])]
  | index, premise :: rest, assignment =>
      (premiseResults oracle relEnv language rule spec ambient index
        premise assignment).flatMap fun (event, completed) =>
          (runPremises oracle relEnv language rule spec ambient
            (index + 1) rest completed).map fun (final, history) =>
              (final, event :: history)

/-- Forgetting contextual sorts commutes with the whole ordered premise
machine, including its intermediate assignments and event histories. -/
theorem runPremises_fromDepth {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : List TypeExpr)
    (index : Nat) (premises : List CanonicalPremise)
    (assignment : Assignment) :
    runPremises (fromDepth oracle) relEnv language rule spec ambient
        index premises assignment =
      Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.runPremises oracle relEnv language rule spec
        ambient.length index (premises.map CanonicalPremise.toAuthored)
        assignment := by
  induction premises generalizing index assignment with
  | nil => rfl
  | cons head tail ih =>
      simp only [runPremises, Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.runPremises,
        List.map_cons]
      rw [premiseResults_fromDepth]
      apply List.flatMap_congr
      intro result _
      rcases result with ⟨event, completed⟩
      rw [ih]

/-- One checked canonical rule consumes a context-indexed recursive oracle.
The runtime's existing matching and reduct construction are unchanged. -/
def applyRule {Evidence : Type} (oracle : ContextOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (ambient : List TypeExpr)
    (term : Pattern) (premises : List CanonicalPremise) :
    List (RuleFiring Evidence) :=
  match rule.bindings with
  | none => []
  | some spec =>
      if admittedFor rule spec then
        (matchRuleAt rule spec ambient.length term).flatMap fun captured =>
          (runPremises oracle relEnv language rule spec ambient 0
            premises captured).filterMap fun (completed, history) =>
              finish? rule spec ambient.length captured completed history
      else []

/-- The context-indexed and depth-indexed canonical rule interpreters agree
on full firing records after sort erasure. -/
theorem applyRule_fromDepth {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (ambient : List TypeExpr) (term : Pattern)
    (premises : List CanonicalPremise) :
    applyRule (fromDepth oracle) relEnv language rule ambient term premises =
      applyWithCanonicalPremisesAt oracle relEnv language rule ambient
        term premises := by
  unfold applyRule applyWithCanonicalPremisesAt
  cases rule.bindings with
  | none => rfl
  | some spec =>
      by_cases admitted : admittedFor rule spec = true
      · simp only [admitted, if_true]
        congr 1
        funext captured
        rw [runPremises_fromDepth oracle relEnv language rule spec
          ambient 0 premises captured]
      · have rejected : admittedFor rule spec = false :=
          Bool.eq_false_iff.mpr admitted
        simp [rejected]

/-- Elaboration and contextual execution form one partial operation; a
rejected authored declaration is distinct from a rule with no firings. -/
def applyCompiledRuleAt? {Evidence : Type}
    (oracle : ContextOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (ambient : List TypeExpr) (term : Pattern) :
    Option (List (RuleFiring Evidence)) := do
  let premises ← compileRulePremisesAt? language rule ambient
  pure (applyRule oracle relEnv language rule ambient term premises)

/-- Every compiled contextual rule specializes to the exact current result
under the depth-erasing embedding, including all firing histories. -/
theorem applyCompiledRuleAt?_fromDepth {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (rule : RewriteRule)
    (ambient : List TypeExpr) (term : Pattern) :
    applyCompiledRuleAt? (fromDepth oracle) relEnv language rule ambient term =
      CanonicalScopedRuleExecution.applyCompiledRuleAt? oracle relEnv
        language rule ambient term := by
  unfold applyCompiledRuleAt?
    CanonicalScopedRuleExecution.applyCompiledRuleAt?
  cases compiled : compileRulePremisesAt? language rule ambient with
  | none => simp
  | some premises =>
      simp [applyRule_fromDepth]

/-- A complete authored language is compiled in declaration order before
its context-indexed one-layer firings are interpreted. -/
def applyCompiledLanguageAt? {Evidence : Type}
    (oracle : ContextOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (ambient : List TypeExpr)
    (term : Pattern) : Option (List (Nat × RuleFiring Evidence)) := do
  let rules ← compileRuleListAt? language ambient language.rewrites.zipIdx
  pure (rules.flatMap fun (rule, index, premises) =>
    (applyRule oracle relEnv language rule ambient term premises).map
      fun firing => (index, firing))

/-- Forgetting the context sorts recovers the prior canonical executor for
the whole rule list, not merely one selected rule. Rule indices, oracle
result indices, assignments, and premise histories all remain equal. -/
theorem applyCompiledLanguageAt?_fromDepth {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (language : LanguageDef) (ambient : List TypeExpr)
    (term : Pattern) :
    applyCompiledLanguageAt? (fromDepth oracle) relEnv language ambient term =
      CanonicalScopedRuleExecution.applyCompiledLanguageAt? oracle relEnv
        language ambient term := by
  unfold applyCompiledLanguageAt?
    CanonicalScopedRuleExecution.applyCompiledLanguageAt?
  cases compiled : compileRuleListAt? language ambient
      language.rewrites.zipIdx with
  | none => simp
  | some rules =>
      change some (rules.flatMap fun (rule, index, premises) =>
          (applyRule (fromDepth oracle) relEnv language rule ambient term
            premises).map fun firing => (index, firing)) =
        some (rules.flatMap fun (rule, index, premises) =>
          (applyWithCanonicalPremisesAt oracle relEnv language rule ambient
            term premises).map fun firing => (index, firing))
      congr 1
      apply List.flatMap_congr
      intro entry _
      rcases entry with ⟨rule, index, premises⟩
      change (applyRule (fromDepth oracle) relEnv language rule ambient term
          premises).map (fun firing => (index, firing)) =
        (applyWithCanonicalPremisesAt oracle relEnv language rule ambient
          term premises).map (fun firing => (index, firing))
      rw [applyRule_fromDepth]

#print axioms stepResults_fromDepth
#print axioms premiseResults_fromDepth
#print axioms runPremises_fromDepth
#print axioms applyRule_fromDepth
#print axioms separatingOracle_not_fromDepth
#print axioms depthInvariant_iff_fromDepth
#print axioms applyCompiledRuleAt?_fromDepth
#print axioms applyCompiledLanguageAt?_fromDepth

end Mettapedia.OSLF.Binding.CanonicalContextOracle
