import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

/-!
# Source-derived match plans for the PeTTa call guard

The cold call-guard backend needs both halves of each authored rewrite row.
Right-hand sides and relation premises already compile to narrow StructuredC
actions.  This module compiles the left-hand side to an independent typed
match plan instead of assigning behavior by row number.

The decoder accepts the complete first-order shapes represented by the native
call-guard state: running, argument, and result controls; empty and nonempty
declaration/input cursors; variables; and literal term patterns.  Successful
decoding is translation-validated by reconstructing the complete source
pattern.  Complete branch compilation traverses the source occurrence space
in authored order and fails on any unsupported matcher, premise, or target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceMatchPlan

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPatternMatrixCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardRulePlanCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

namespace FirstOrder

export Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
  (PatternPlan RulePlan)

end FirstOrder

private def app (constructor : String)
    (arguments : List FirstOrder.PatternPlan := []) : FirstOrder.PatternPlan :=
  .application constructor arguments

private def planVar (name : String) : FirstOrder.PatternPlan :=
  .metavariable name

private def variableName? : FirstOrder.PatternPlan → Option String
  | .metavariable name => some name
  | _ => none

/-! ## Typed left-hand-side plans -/

/-- The declaration skeleton exposed by the native call-guard ABI. -/
structure DeclarationMatchPlan where
  occurrence : String
  head : String
  inputs : String
  output : ValuePlan
deriving Repr

def DeclarationMatchPlan.encode
    (plan : DeclarationMatchPlan) : FirstOrder.PatternPlan :=
  app "petta-call-guard:declaration"
    [ planVar plan.occurrence, planVar plan.head, planVar plan.inputs
    , plan.output.encode ]

/-- Running-state declaration-list shapes admitted by the backend. -/
inductive DeclarationsMatchPlan where
  | nil
  | cons (head : DeclarationMatchPlan) (tail : String)
deriving Repr

def DeclarationsMatchPlan.encode :
    DeclarationsMatchPlan → FirstOrder.PatternPlan
  | .nil => app "petta-call-guard:declarations-nil"
  | .cons head tail =>
      app "petta-call-guard:declarations-cons"
        [head.encode, planVar tail]

/-- Argument-cursor shapes admitted by the backend. -/
inductive InputCursorMatchPlan where
  | nil
  | cons (head : ValuePlan) (tail : String)
deriving Repr

def InputCursorMatchPlan.encode :
    InputCursorMatchPlan → FirstOrder.PatternPlan
  | .nil => app "petta-call-guard:terms-nil"
  | .cons head tail =>
      app "petta-call-guard:terms-cons" [head.encode, planVar tail]

/-- Complete supported state matcher.  Repeated source names remain repeated
in this data, so a later matcher backend must preserve equality constraints. -/
inductive StateMatchPlan where
  | running
      (owner revision head arity : String)
      (remaining : DeclarationsMatchPlan) (accepted : String)
  | arguments
      (owner revision head arity : String)
      (declaration : DeclarationMatchPlan) (remaining : String)
      (inputCursor : InputCursorMatchPlan) (modes accepted : String)
  | result
      (owner revision head arity : String)
      (declaration : DeclarationMatchPlan) (remaining modes accepted : String)
deriving Repr

def StateMatchPlan.encode : StateMatchPlan → FirstOrder.PatternPlan
  | .running owner revision head arity remaining accepted =>
      app "petta-call-guard:compile-running"
        [ planVar owner, planVar revision, planVar head, planVar arity
        , remaining.encode, planVar accepted ]
  | .arguments owner revision head arity declaration remaining inputCursor
      modes accepted =>
      app "petta-call-guard:compile-arguments"
        [ planVar owner, planVar revision, planVar head, planVar arity
        , declaration.encode, planVar remaining, inputCursor.encode
        , planVar modes, planVar accepted ]
  | .result owner revision head arity declaration remaining modes accepted =>
      app "petta-call-guard:compile-result"
        [ planVar owner, planVar revision, planVar head, planVar arity
        , declaration.encode, planVar remaining, planVar modes
        , planVar accepted ]

/-! ## Structural decoding and translation validation -/

private def decodeDeclarationCore? : FirstOrder.PatternPlan →
    Option DeclarationMatchPlan
  | .application "petta-call-guard:declaration"
      [occurrence, head, inputs, output] => do
      let occurrenceName ← variableName? occurrence
      let headName ← variableName? head
      let inputsName ← variableName? inputs
      pure
        { occurrence := occurrenceName
          head := headName
          inputs := inputsName
          output := ValuePlan.ofPattern output }
  | _ => none

private def decodeDeclarationsCore? : FirstOrder.PatternPlan →
    Option DeclarationsMatchPlan
  | .application "petta-call-guard:declarations-nil" [] => some .nil
  | .application "petta-call-guard:declarations-cons" [head, tail] => do
      let headPlan ← decodeDeclarationCore? head
      let tailName ← variableName? tail
      pure (.cons headPlan tailName)
  | _ => none

private def decodeInputCursorCore? : FirstOrder.PatternPlan →
    Option InputCursorMatchPlan
  | .application "petta-call-guard:terms-nil" [] => some .nil
  | .application "petta-call-guard:terms-cons" [head, tail] => do
      let tailName ← variableName? tail
      pure (.cons (ValuePlan.ofPattern head) tailName)
  | _ => none

private def decodeStateMatchCore? : FirstOrder.PatternPlan →
    Option StateMatchPlan
  | .application "petta-call-guard:compile-running"
      [owner, revision, head, arity, remaining, accepted] => do
      let ownerName ← variableName? owner
      let revisionName ← variableName? revision
      let headName ← variableName? head
      let arityName ← variableName? arity
      let remainingPlan ← decodeDeclarationsCore? remaining
      let acceptedName ← variableName? accepted
      pure (.running ownerName revisionName headName arityName remainingPlan
        acceptedName)
  | .application "petta-call-guard:compile-arguments"
      [owner, revision, head, arity, declaration, remaining, inputCursor,
        modes, accepted] => do
      let ownerName ← variableName? owner
      let revisionName ← variableName? revision
      let headName ← variableName? head
      let arityName ← variableName? arity
      let declarationPlan ← decodeDeclarationCore? declaration
      let remainingName ← variableName? remaining
      let inputCursorPlan ← decodeInputCursorCore? inputCursor
      let modesName ← variableName? modes
      let acceptedName ← variableName? accepted
      pure (.arguments ownerName revisionName headName arityName
        declarationPlan remainingName inputCursorPlan modesName acceptedName)
  | .application "petta-call-guard:compile-result"
      [owner, revision, head, arity, declaration, remaining, modes,
        accepted] => do
      let ownerName ← variableName? owner
      let revisionName ← variableName? revision
      let headName ← variableName? head
      let arityName ← variableName? arity
      let declarationPlan ← decodeDeclarationCore? declaration
      let remainingName ← variableName? remaining
      let modesName ← variableName? modes
      let acceptedName ← variableName? accepted
      pure (.result ownerName revisionName headName arityName declarationPlan
        remainingName modesName acceptedName)
  | _ => none

/-- Decode and validate a native state matcher.  The equality check is over
the reconstructed complete first-order source pattern, not a family tag. -/
def compileStateMatch? (source : FirstOrder.PatternPlan) :
    Option StateMatchPlan :=
  match decodeStateMatchCore? source with
  | none => none
  | some plan =>
      if _ : plan.encode.erase = source.erase then some plan else none

/-- Successful matcher compilation preserves the complete source pattern. -/
theorem encode_of_compileStateMatch?
    {source : FirstOrder.PatternPlan} {plan : StateMatchPlan}
    (compiled : compileStateMatch? source = some plan) :
    plan.encode.erase = source.erase := by
  unfold compileStateMatch? at compiled
  cases decoded : decodeStateMatchCore? source with
  | none => simp [decoded] at compiled
  | some decodedPlan =>
      simp only [decoded] at compiled
      split at compiled
      next exact =>
        have samePlan : decodedPlan = plan := Option.some.inj compiled
        simpa [samePlan] using exact
      next notExact => simp at compiled

/-! ## Whole-branch compilation -/

/-- A successful state-match decode carries its exact source-pattern
certificate as data consumed by later lowering passes. -/
structure CertifiedStateMatch (source : FirstOrder.PatternPlan) where
  matcher : StateMatchPlan
  exact : matcher.encode.erase = source.erase

/-- Package the structural decoder together with its translation-validation
equation. -/
def certifyStateMatch? (source : FirstOrder.PatternPlan) :
    Option (CertifiedStateMatch source) :=
  match accepted : compileStateMatch? source with
  | none => none
  | some matcher =>
      some
        { matcher
          exact := encode_of_compileStateMatch? accepted }

/-- One residual branch retains its exact occurrence, first-order rule plan,
validated matcher, and source-derived target body. -/
structure CompiledBranch where
  occurrence : SourceOccurrence
  rule : FirstOrder.RulePlan
  matcher : StateMatchPlan
  matcherExact : matcher.encode.erase = rule.left.erase
  body : Pattern
deriving Repr

/-- Compile one already selected source occurrence and rule plan.  This is the
leaf compiler consumed by structural decision-program lowering; it does not
look the rule up again or inspect an occurrence number to choose behavior. -/
def compileSelectedRule? (occurrence : SourceOccurrence)
    (rule : FirstOrder.RulePlan) : Option CompiledBranch := do
  let certified ← certifyStateMatch? rule.left
  let body ← lowerMatchedRule? rule
  pure
    { occurrence
      rule
      matcher := certified.matcher
      matcherExact := certified.exact
      body }

/-- Compile one exact source occurrence without consulting a row-family
inventory. -/
def compileBranch? (occurrence : SourceOccurrence) : Option CompiledBranch := do
  let rule ← planOptionAt occurrence
  compileSelectedRule? occurrence rule

/-- A successfully compiled selected leaf retains its exact occurrence and
complete first-order rule plan. -/
theorem compileSelectedRule?_exact
    {occurrence : SourceOccurrence} {rule : FirstOrder.RulePlan}
    {branch : CompiledBranch}
    (compiled : compileSelectedRule? occurrence rule = some branch) :
    branch.occurrence = occurrence ∧ branch.rule = rule := by
  unfold compileSelectedRule? at compiled
  cases matcherCompiled : certifyStateMatch? rule.left with
  | none => simp [matcherCompiled] at compiled
  | some certified =>
      cases bodyCompiled : lowerMatchedRule? rule with
      | none => simp [matcherCompiled, bodyCompiled] at compiled
      | some body =>
          simp [matcherCompiled, bodyCompiled] at compiled
          subst branch
          simp

/-- A successfully compiled selected leaf retains the complete source
left-hand side through its typed matcher. -/
theorem compileSelectedRule?_matcher_exact
    {occurrence : SourceOccurrence} {rule : FirstOrder.RulePlan}
    {branch : CompiledBranch}
    (compiled : compileSelectedRule? occurrence rule = some branch) :
    branch.matcher.encode.erase = rule.left.erase := by
  have ruleExact := (compileSelectedRule?_exact compiled).2
  rw [← ruleExact]
  exact branch.matcherExact

/-- Successful branch compilation retains the source-indexed rule plan. -/
theorem compileBranch?_rule_exact
    {occurrence : SourceOccurrence} {branch : CompiledBranch}
    (compiled : compileBranch? occurrence = some branch) :
    planOptionAt occurrence = some branch.rule := by
  unfold compileBranch? at compiled
  cases ruleCompiled : planOptionAt occurrence with
  | none => simp [ruleCompiled] at compiled
  | some rule =>
      simp only [ruleCompiled] at compiled
      have branchExact := compileSelectedRule?_exact compiled
      rw [branchExact.2]

/-- Successful branch compilation retains the selected source occurrence. -/
theorem compileBranch?_occurrence_exact
    {occurrence : SourceOccurrence} {branch : CompiledBranch}
    (compiled : compileBranch? occurrence = some branch) :
    branch.occurrence = occurrence := by
  unfold compileBranch? at compiled
  cases ruleCompiled : planOptionAt occurrence with
  | none => simp [ruleCompiled] at compiled
  | some rule =>
      simp only [ruleCompiled] at compiled
      exact (compileSelectedRule?_exact compiled).1

/-- Successful branch compilation retains the complete source left-hand side. -/
theorem compileBranch?_matcher_exact
    {occurrence : SourceOccurrence} {branch : CompiledBranch}
    (compiled : compileBranch? occurrence = some branch) :
    branch.matcher.encode.erase = branch.rule.left.erase := by
  unfold compileBranch? at compiled
  cases ruleCompiled : planOptionAt occurrence with
  | none => simp [ruleCompiled] at compiled
  | some rule =>
      simp only [ruleCompiled] at compiled
      have ruleExact := compileSelectedRule?_exact compiled
      rw [ruleExact.2]
      exact compileSelectedRule?_matcher_exact compiled

/-- Every authored call-guard occurrence belongs to the target leaf fragment.
The occurrence-indexed proof keeps reduction local to one source row. -/
theorem compileBranch?_isSome (occurrence : SourceOccurrence) :
    (compileBranch? occurrence).isSome = true := by
  fin_cases occurrence <;> decide +kernel

/-- The compiled target leaf for one exact authored occurrence. -/
def branchAt (occurrence : SourceOccurrence) : CompiledBranch :=
  (compileBranch? occurrence).get (compileBranch?_isSome occurrence)

/-- `branchAt` is the actual result of structural leaf compilation. -/
theorem branchAt_compilation_exact (occurrence : SourceOccurrence) :
    compileBranch? occurrence = some (branchAt occurrence) := by
  exact (Option.some_get (compileBranch?_isSome occurrence)).symm

/-- The total selected leaf retains its exact source occurrence. -/
theorem branchAt_occurrence (occurrence : SourceOccurrence) :
    (branchAt occurrence).occurrence = occurrence :=
  compileBranch?_occurrence_exact (branchAt_compilation_exact occurrence)

/-- The total selected leaf retains the independently compiled rule plan. -/
theorem branchAt_rule (occurrence : SourceOccurrence) :
    (branchAt occurrence).rule = planAt occurrence := by
  have compiled := compileBranch?_rule_exact
    (branchAt_compilation_exact occurrence)
  rw [show planOptionAt occurrence = some (planAt occurrence) by
    simpa [planOptionAt] using planAt_compilation_exact occurrence] at compiled
  exact Option.some.inj compiled.symm

/-- Complete branch compilation follows the authored source occurrence order. -/
def sourceDerivedBranches? : Option (List CompiledBranch) :=
  sourceOccurrences.mapM compileBranch?

/-! ## Discriminating controls -/

/-- The first ordinary source row is accepted through structural decoding. -/
example : (compileBranch? ⟨0, by decide⟩).isSome = true := by
  decide +kernel

/-- A foreign state constructor cannot be assigned call-guard behavior. -/
example :
    compileStateMatch? (app "petta-call-guard:foreign-state") = none := by
  rfl

/-- A malformed declaration spine fails rather than dropping its tail. -/
example :
    compileStateMatch?
      (app "petta-call-guard:compile-running"
        [ planVar "owner", planVar "revision", planVar "head"
        , planVar "arity"
        , app "petta-call-guard:declarations-cons" [planVar "head-only"]
        , planVar "accepted" ]) = none := by
  rfl

#print axioms encode_of_compileStateMatch?
#print axioms compileSelectedRule?_exact
#print axioms compileSelectedRule?_matcher_exact
#print axioms compileBranch?_rule_exact
#print axioms compileBranch?_occurrence_exact
#print axioms compileBranch?_matcher_exact
#print axioms compileBranch?_isSome
#print axioms branchAt_compilation_exact
#print axioms branchAt_occurrence
#print axioms branchAt_rule

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceMatchPlan
