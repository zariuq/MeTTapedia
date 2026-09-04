import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardRulePlanCompilation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

/-!
# Source-derived StructuredC bodies for the PeTTa call guard

This module replaces transition-family selection at the matched-row boundary
with structural compilation of the residual rule plans.  A target action is
decoded from the right-hand-side constructor tree, while every ordered source
relation premise is mapped through an explicit primitive ABI.  Compilation
fails if either structure is unsupported or if re-encoding the decoded action
does not recover the complete source template.

The resulting statement blocks use the existing narrow StructuredC
primitives.  Matching and variable extraction remain the next lowering stage;
this module assumes only that the variables bound by the compiled left-hand
side are present in the StructuredC environment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.StructuredC.Builder
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPatternMatrixCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardRulePlanCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFragments

namespace FirstOrder

export Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
  (PatternPlan PremisePlan RulePlan)

end FirstOrder

private def app (constructor : String)
    (arguments : List FirstOrder.PatternPlan := []) : FirstOrder.PatternPlan :=
  .application constructor arguments

private def planVariable (name : String) : FirstOrder.PatternPlan :=
  .metavariable name

/-! ## Typed target-delta plans -/

/-- Argument-mode structure retained from a source RHS. -/
inductive ArgumentModePlan where
  | raw
  | unchecked
  | checked (expected : String)
deriving DecidableEq, Repr

def ArgumentModePlan.encode : ArgumentModePlan -> FirstOrder.PatternPlan
  | .raw => app "petta-call-guard:arg-raw"
  | .unchecked => app "petta-call-guard:arg-unchecked"
  | .checked expected =>
      app "petta-call-guard:arg-checked" [planVariable expected]

/-- Result-mode structure retained from a source RHS. -/
inductive ResultModePlan where
  | unchecked
  | checked (expected : String)
deriving DecidableEq, Repr

def ResultModePlan.encode : ResultModePlan -> FirstOrder.PatternPlan
  | .unchecked => app "petta-call-guard:result-unchecked"
  | .checked expected =>
      app "petta-call-guard:result-checked" [planVariable expected]

/-- A result term is either supplied by an authored binding or retains a
structural source plan.  The structural case may still contain nested
metavariables; a concrete ABI lowerer must either implement those bindings or
reject the value. -/
inductive ValuePlan where
  | variable (name : String)
  | literal (value : FirstOrder.PatternPlan)
deriving Repr

def ValuePlan.encode : ValuePlan -> FirstOrder.PatternPlan
  | .variable name => planVariable name
  | .literal value => value

def ValuePlan.ofPattern : FirstOrder.PatternPlan -> ValuePlan
  | .metavariable name => .variable name
  | value => .literal value

/-- Semantic state updates supported by the call-guard ABI.  These are target
constructor forms, not source rule-family tags. -/
inductive DeltaPlan where
  | finish
      (owner revision head arity accepted : String)
  | setRunning
      (owner revision head arity remaining accepted : String)
  | startArguments
      (owner revision head arity occurrence declarationHead inputs output
        remaining inputCursor accepted : String)
  | appendArgumentMode
      (owner revision head arity occurrence declarationHead inputs output
        remaining inputCursor modes accepted : String)
      (mode : ArgumentModePlan)
  | setResult
      (owner revision head arity occurrence declarationHead inputs output
        remaining modes accepted : String)
  | appendCompiledPlan
      (owner revision head arity remaining accepted occurrence modes
        declarationHead inputs : String)
      (output : ValuePlan) (mode : ResultModePlan)
  | outsideFragment
deriving Repr

/-- Reconstruct the complete source RHS represented by a target delta. -/
def DeltaPlan.encode : DeltaPlan -> FirstOrder.PatternPlan
  | .finish owner revision head arity accepted =>
      app "petta-call-guard:compile-halted"
        [app "petta-call-guard:compiled"
          [app "petta-call-guard:family"
            [planVariable owner, planVariable revision, planVariable head,
              planVariable arity, planVariable accepted]]]
  | .setRunning owner revision head arity remaining accepted =>
      app "petta-call-guard:compile-running"
        [planVariable owner, planVariable revision, planVariable head,
          planVariable arity, planVariable remaining, planVariable accepted]
  | .startArguments owner revision head arity occurrence declarationHead
      inputs output remaining inputCursor accepted =>
      app "petta-call-guard:compile-arguments"
        [ planVariable owner, planVariable revision, planVariable head,
          planVariable arity
        , app "petta-call-guard:declaration"
            [planVariable occurrence, planVariable declarationHead,
              planVariable inputs, planVariable output]
        , planVariable remaining, planVariable inputCursor
        , app "petta-call-guard:arg-modes-nil", planVariable accepted ]
  | .appendArgumentMode owner revision head arity occurrence declarationHead
      inputs output remaining inputCursor modes accepted mode =>
      app "petta-call-guard:compile-arguments"
        [ planVariable owner, planVariable revision, planVariable head,
          planVariable arity
        , app "petta-call-guard:declaration"
            [planVariable occurrence, planVariable declarationHead,
              planVariable inputs, planVariable output]
        , planVariable remaining, planVariable inputCursor
        , app "petta-call-guard:arg-modes-snoc"
            [planVariable modes, mode.encode]
        , planVariable accepted ]
  | .setResult owner revision head arity occurrence declarationHead inputs
      output remaining modes accepted =>
      app "petta-call-guard:compile-result"
        [ planVariable owner, planVariable revision, planVariable head,
          planVariable arity
        , app "petta-call-guard:declaration"
            [planVariable occurrence, planVariable declarationHead,
              planVariable inputs, planVariable output]
        , planVariable remaining, planVariable modes, planVariable accepted ]
  | .appendCompiledPlan owner revision head arity remaining accepted occurrence
      modes declarationHead inputs output mode =>
      app "petta-call-guard:compile-running"
        [ planVariable owner, planVariable revision, planVariable head,
          planVariable arity
        , planVariable remaining
        , app "petta-call-guard:plans-snoc"
            [ planVariable accepted
            , app "petta-call-guard:plan"
                [ planVariable occurrence, planVariable modes, mode.encode
                , app "petta-call-guard:declaration"
                    [ planVariable occurrence, planVariable declarationHead
                    , planVariable inputs, output.encode ] ] ] ]
  | .outsideFragment =>
      app "petta-call-guard:compile-halted"
        [app "petta-call-guard:outside-fragment"]

private def decodeArgumentMode? : FirstOrder.PatternPlan ->
    Option ArgumentModePlan
  | .application "petta-call-guard:arg-raw" [] => some .raw
  | .application "petta-call-guard:arg-unchecked" [] => some .unchecked
  | .application "petta-call-guard:arg-checked"
      [.metavariable expected] => some (.checked expected)
  | _ => none

private def decodeResultMode? : FirstOrder.PatternPlan -> Option ResultModePlan
  | .application "petta-call-guard:result-unchecked" [] => some .unchecked
  | .application "petta-call-guard:result-checked"
      [.metavariable expected] => some (.checked expected)
  | _ => none

/-- Structural decoder for supported RHS constructors.  It does not inspect a
rule name or source occurrence. -/
def decodeDeltaCore? : FirstOrder.PatternPlan -> Option DeltaPlan
  | .application "petta-call-guard:compile-halted"
      [.application "petta-call-guard:compiled"
        [.application "petta-call-guard:family"
          [.metavariable owner, .metavariable revision, .metavariable head,
            .metavariable arity, .metavariable accepted]]] =>
      some (.finish owner revision head arity accepted)
  | .application "petta-call-guard:compile-halted"
      [.application "petta-call-guard:outside-fragment" []] =>
      some .outsideFragment
  | .application "petta-call-guard:compile-arguments"
      [ .metavariable owner, .metavariable revision, .metavariable head
      , .metavariable arity
      , .application "petta-call-guard:declaration"
          [.metavariable occurrence, .metavariable declarationHead,
            .metavariable inputs, .metavariable output]
      , .metavariable remaining, .metavariable inputCursor
      , .application "petta-call-guard:arg-modes-nil" []
      , .metavariable accepted ] =>
      some (.startArguments owner revision head arity occurrence
        declarationHead inputs output remaining inputCursor accepted)
  | .application "petta-call-guard:compile-arguments"
      [ .metavariable owner, .metavariable revision, .metavariable head
      , .metavariable arity
      , .application "petta-call-guard:declaration"
          [.metavariable occurrence, .metavariable declarationHead,
            .metavariable inputs, .metavariable output]
      , .metavariable remaining, .metavariable inputCursor
      , .application "petta-call-guard:arg-modes-snoc"
          [.metavariable modes, mode]
      , .metavariable accepted ] => do
      let mode <- decodeArgumentMode? mode
      pure (.appendArgumentMode owner revision head arity occurrence
        declarationHead inputs output remaining inputCursor modes accepted
        mode)
  | .application "petta-call-guard:compile-result"
      [ .metavariable owner, .metavariable revision, .metavariable head
      , .metavariable arity
      , .application "petta-call-guard:declaration"
          [.metavariable occurrence, .metavariable declarationHead,
            .metavariable inputs, .metavariable output]
      , .metavariable remaining, .metavariable modes
      , .metavariable accepted ] =>
      some (.setResult owner revision head arity occurrence declarationHead
        inputs output remaining modes accepted)
  | .application "petta-call-guard:compile-running"
      [ .metavariable owner, .metavariable revision, .metavariable head
      , .metavariable arity, .metavariable remaining
      , .application "petta-call-guard:plans-snoc"
          [ .metavariable accepted
          , .application "petta-call-guard:plan"
              [ .metavariable occurrence, .metavariable modes, resultMode
              , .application "petta-call-guard:declaration"
                  [ .metavariable planOccurrence
                  , .metavariable declarationHead, .metavariable inputs
                  , output ] ] ] ] => do
      if occurrence != planOccurrence then none
      let mode <- decodeResultMode? resultMode
      pure (.appendCompiledPlan owner revision head arity remaining accepted
        occurrence modes declarationHead inputs (ValuePlan.ofPattern output)
        mode)
  | .application "petta-call-guard:compile-running"
      [.metavariable owner, .metavariable revision, .metavariable head,
        .metavariable arity, .metavariable remaining,
        .metavariable accepted] =>
      some (.setRunning owner revision head arity remaining accepted)
  | _ => none

/-- Translation validation for the structural decoder.  A partial decoder is
never trusted merely because it returned an action. -/
def compileDelta? (source : FirstOrder.PatternPlan) :
    Option DeltaPlan :=
  match decodeDeltaCore? source with
  | none => none
  | some plan =>
      if _ : plan.encode.erase = source.erase then
        some plan
      else
        none

/-- Every successful target decode preserves the complete source RHS. -/
theorem encode_of_compileDelta?
    {source : FirstOrder.PatternPlan} {plan : DeltaPlan}
    (compiled : compileDelta? source = some plan) :
    plan.encode.erase = source.erase := by
  unfold compileDelta? at compiled
  cases decoded : decodeDeltaCore? source with
  | none => simp [decoded] at compiled
  | some decodedPlan =>
      simp only [decoded] at compiled
      split at compiled
      next exact =>
        have planExact : decodedPlan = plan := Option.some.inj compiled
        simpa [planExact] using exact
      next notExact => simp at compiled

/-! ## Source relation to target primitive ABI -/

/-- One explicit relation-query ABI entry. -/
structure QueryPrimitive where
  sourceRelation : String
  targetExternal : String
  arity : Nat
deriving DecidableEq, Repr

/-- The complete primitive map needed by the cold source rows. -/
def queryPrimitives : List QueryPrimitive :=
  [ { sourceRelation := notEqualRelation
      targetExternal := nameNotEqualQuery, arity := 2 }
  , { sourceRelation := arityDiffersRelation
      targetExternal := arityDiffersQuery, arity := 2 }
  , { sourceRelation := arityMatchesRelation
      targetExternal := arityMatchesQuery, arity := 2 }
  , { sourceRelation := checkedInputRelation
      targetExternal := inputIsCheckedQuery, arity := 1 }
  , { sourceRelation := openInputRelation
      targetExternal := inputIsOpenQuery, arity := 1 }
  , { sourceRelation := checkedResultRelation
      targetExternal := resultIsCheckedQuery, arity := 1 }
  , { sourceRelation := openResultRelation
      targetExternal := resultIsOpenQuery, arity := 1 } ]

/-- First-match primitive lookup. -/
def queryPrimitive? (relation : String) : Option QueryPrimitive :=
  queryPrimitives.find? fun primitive =>
    primitive.sourceRelation = relation

/-- C identifier spelling for one authored schema variable. -/
def targetVariable : String -> String
  | "declarationHead" => "declaration_head"
  | "inputCursor" => "input_cursor"
  | name => name

private def variableExpressions (names : List String) : List Pattern :=
  names.map fun name => variableExpression (targetVariable name)

/-- Compile one source relation premise to one visible StructuredC condition. -/
def lowerPremiseCondition? (plan : FirstOrder.PremisePlan) : Option Pattern := do
  let primitive <- queryPrimitive? plan.relation
  if plan.arguments.length = primitive.arity then
    pure (call primitive.targetExternal (variableExpressions plan.arguments))
  else
    none

/-- Wrap a successful action in every authored guard, retaining premise order
and duplicate occurrences. -/
def lowerPremises? : List FirstOrder.PremisePlan -> Pattern -> Option Pattern
  | [], success => some success
  | premise :: premises, success => do
      let condition <- lowerPremiseCondition? premise
      let guardedTail <- lowerPremises? premises success
      pure (statements [ifThenElse condition guardedTail (statements [])])

/-! ## Delta lowering -/

private def transitionBody (delta : String) (arguments : List Pattern)
    (outcome : String := advancedOutcome) : Pattern :=
  statements [effect (call delta arguments), returnSymbol outcome]

private def lowerArgumentMode
    (mode : ArgumentModePlan) : Pattern × Pattern :=
  match mode with
  | .raw => (symbol rawArgumentMode, symbol noModePayload)
  | .unchecked => (symbol uncheckedArgumentMode, symbol noModePayload)
  | .checked expected =>
      (symbol checkedArgumentMode,
        variableExpression (targetVariable expected))

private def lowerResultMode
    (mode : ResultModePlan) : Pattern × Pattern :=
  match mode with
  | .unchecked => (symbol uncheckedResultMode, symbol noModePayload)
  | .checked expected =>
      (symbol checkedResultMode,
        variableExpression (targetVariable expected))

private def lowerValue? : ValuePlan -> Option Pattern
  | .variable name => some (variableExpression (targetVariable name))
  | .literal value =>
      if value.erase = encodeTerm undefinedType then some (symbol undefinedTerm)
      else if value.erase = encodeTerm holeType then some (symbol holeTerm)
      else if value.erase = encodeTerm atomType then some (symbol atomTerm)
      else none

/-- Lower one structurally decoded target delta to the existing narrow ABI. -/
def lowerDelta? : DeltaPlan -> Option Pattern
  | .finish owner revision head arity accepted =>
      some (transitionBody setCompiledFamilyDelta
        (variableExpressions
          ["state", owner, revision, head, arity, accepted]) compiledOutcome)
  | .setRunning owner revision head arity remaining accepted =>
      some (transitionBody setCompileRunningDelta
        (variableExpressions
          ["state", owner, revision, head, arity, remaining, accepted]))
  | .startArguments owner revision head arity occurrence declarationHead
      inputs output remaining inputCursor accepted =>
      some (transitionBody startCompileArgumentsDelta
        (variableExpressions
          [ "state", owner, revision, head, arity, occurrence
          , declarationHead, inputs, output, remaining, inputCursor
          , accepted ]))
  | .appendArgumentMode owner revision head arity occurrence declarationHead
      inputs output remaining inputCursor modes accepted mode =>
      let encodedMode := lowerArgumentMode mode
      some (transitionBody appendArgumentModeDelta
        (variableExpressions
          [ "state", owner, revision, head, arity, occurrence
          , declarationHead, inputs, output, remaining, inputCursor
          , modes, accepted ] ++ [encodedMode.1, encodedMode.2]))
  | .setResult owner revision head arity occurrence declarationHead inputs
      output remaining modes accepted =>
      some (transitionBody setCompileResultDelta
        (variableExpressions
          [ "state", owner, revision, head, arity, occurrence
          , declarationHead, inputs, output, remaining, modes, accepted ]))
  | .appendCompiledPlan owner revision head arity remaining accepted occurrence
      modes declarationHead inputs output mode => do
      let encodedOutput <- lowerValue? output
      let encodedMode := lowerResultMode mode
      pure (transitionBody appendCompiledPlanDelta
        (variableExpressions
          [ "state", owner, revision, head, arity, remaining, accepted
          , occurrence, modes, declarationHead, inputs ] ++
          [encodedOutput, encodedMode.1, encodedMode.2]))
  | .outsideFragment =>
      some (transitionBody setOutsideFragmentDelta
        [variableExpression "state"] outsideFragmentOutcome)

/-- Compile one matched residual rule body entirely from its compiled premise
row and RHS constructor tree. -/
def lowerMatchedRule? (rule : FirstOrder.RulePlan) : Option Pattern := do
  let delta <- compileDelta? rule.right
  let success <- lowerDelta? delta
  lowerPremises? rule.premises success

/-! ## Complete cold-source instantiation -/

def bodyOptionAt (occurrence : SourceOccurrence) : Option Pattern :=
  planOptionAt occurrence >>= lowerMatchedRule?

/-- Exact authored occurrence order, obtained from the source length rather
than a backend-owned inventory. -/
def sourceOccurrences : List SourceOccurrence :=
  List.finRange sourceLanguage.rewrites.length

/-- Compile every authored occurrence by traversing the source index space in
order.  The result remains partial: any unsupported present or future row
makes the complete compilation fail. -/
def sourceDerivedBodies? : Option (List Pattern) :=
  sourceOccurrences.mapM bodyOptionAt

/-- A foreign relation cannot cross the target primitive boundary. -/
example :
    lowerPremiseCondition?
      { relation := "PeTTaCallGuardForeign", arguments := [] } = none := by
  rfl

/-- Unsupported target constructors fail instead of receiving a default
delta. -/
example :
    compileDelta? (app "petta-call-guard:invented-target") = none := by
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDerivedStructuredC
