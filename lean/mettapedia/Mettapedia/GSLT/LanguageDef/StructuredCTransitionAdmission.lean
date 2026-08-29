import Mettapedia.GSLT.LanguageDef.StructuredC

/-!
# Constructive transition admission for StructuredC

These lemmas isolate the generic matcher and premise plumbing of the authored
StructuredC rules.  A host supplies exact primitive-query fibres; the results
below turn those fibres into exact target-language transition fibres.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.StructuredC

def effectMatchBindings
    (expression rest environment receipt : Pattern) : Bindings := [
  ("environment", environment), ("receipt", receipt), ("rest", rest),
  ("expression", expression)]

def effectValueBindings
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern) : Bindings := [
  ("evaluatedEnvironment", evaluatedEnvironment),
  ("evaluatedReceipt", evaluatedReceipt), ("value", value)] ++
    effectMatchBindings expression rest environment receipt

theorem match_effectValueTransition
    (expression rest environment receipt : Pattern) :
    matchPatternForRule language effectValueTransition
        (run (consStatement (a "structured-c:effect" [expression]) rest)
          environment receipt) =
      [effectMatchBindings expression rest environment receipt] := by
  rw [matchPatternForRule_eq_syntactic]
  simp [effectValueTransition, run, consStatement, a, v, matchPattern,
    matchArgs, mergeBindings, effectMatchBindings]

theorem effectValueTransition_rewriteAt_exact
    (relationEnv : RelationEnv)
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern)
    (evaluationExact :
      premiseStepWithEnv relationEnv language
          (effectMatchBindings expression rest environment receipt)
          (query "StructuredCEvaluate"
            [v "expression", v "environment", v "receipt",
             evaluationValue (v "value"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) =
        [effectValueBindings expression rest environment receipt value
          evaluatedEnvironment evaluatedReceipt])
    (faultExact :
      premiseStepWithEnv relationEnv language
          (effectMatchBindings expression rest environment receipt)
          (query "StructuredCEvaluate"
            [v "expression", v "environment", v "receipt",
             evaluationFault (v "fault"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) = []) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement (a "structured-c:effect" [expression]) rest)
          environment receipt) =
      [run rest evaluatedEnvironment evaluatedReceipt] := by
  simp only [query, evaluationValue, evaluationFault, v, a,
    effectMatchBindings, effectValueBindings] at evaluationExact faultExact
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (run (consStatement (a "structured-c:effect" [expression]) rest)
          environment receipt)) = _
  simp [transitions, applyRuleUsing,
    matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, engineBasePremises,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]
  rw [evaluationExact, faultExact]
  simp

def ifMatchBindings
    (condition thenBranch elseBranch rest environment receipt : Pattern) :
    Bindings := [
  ("environment", environment), ("receipt", receipt), ("rest", rest),
  ("thenBranch", thenBranch), ("elseBranch", elseBranch),
  ("condition", condition)]

def ifValueBindings
    (condition thenBranch elseBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern) : Bindings := [
  ("evaluatedEnvironment", evaluatedEnvironment),
  ("evaluatedReceipt", evaluatedReceipt), ("value", value)] ++
    ifMatchBindings condition thenBranch elseBranch rest environment receipt

def ifSelectedBindings
    (condition thenBranch elseBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt selected : Pattern) : Bindings :=
  ("selected", selected) ::
    ifValueBindings condition thenBranch elseBranch rest environment receipt
      value evaluatedEnvironment evaluatedReceipt

theorem match_ifValueTransition
    (condition thenBranch elseBranch rest environment receipt : Pattern) :
    matchPatternForRule language ifValueTransition
        (run (consStatement
          (a "structured-c:if" [condition, thenBranch, elseBranch]) rest)
          environment receipt) =
      [ifMatchBindings condition thenBranch elseBranch rest environment receipt] := by
  rw [matchPatternForRule_eq_syntactic]
  simp [ifValueTransition, run, consStatement, a, v, matchPattern,
    matchArgs, mergeBindings, ifMatchBindings]

theorem ifValueTransition_rewriteAt_exact
    (relationEnv : RelationEnv)
    (condition thenBranch elseBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt selected : Pattern)
    (evaluationExact :
      premiseStepWithEnv relationEnv language
          (ifMatchBindings condition thenBranch elseBranch rest environment receipt)
          (query "StructuredCEvaluate"
            [v "condition", v "environment", v "receipt",
             evaluationValue (v "value"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) =
        [ifValueBindings condition thenBranch elseBranch rest environment receipt
          value evaluatedEnvironment evaluatedReceipt])
    (selectionExact :
      premiseStepWithEnv relationEnv language
          (ifValueBindings condition thenBranch elseBranch rest environment receipt
            value evaluatedEnvironment evaluatedReceipt)
          (query "StructuredCSelectBranch"
            [v "value", v "thenBranch", v "elseBranch", v "selected"]) =
        [ifSelectedBindings condition thenBranch elseBranch rest environment receipt
          value evaluatedEnvironment evaluatedReceipt selected])
    (faultExact :
      premiseStepWithEnv relationEnv language
          (ifMatchBindings condition thenBranch elseBranch rest environment receipt)
          (query "StructuredCEvaluate"
            [v "condition", v "environment", v "receipt",
             evaluationFault (v "fault"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) = []) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement
          (a "structured-c:if" [condition, thenBranch, elseBranch]) rest)
          environment receipt) =
      [run (appendStatements selected rest)
        evaluatedEnvironment evaluatedReceipt] := by
  simp only [query, evaluationValue, evaluationFault, v, a,
    ifMatchBindings, ifValueBindings, ifSelectedBindings]
    at evaluationExact selectionExact faultExact
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (run (consStatement
          (a "structured-c:if" [condition, thenBranch, elseBranch]) rest)
          environment receipt)) = _
  simp [transitions, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, engineBasePremises,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]
  rw [evaluationExact, faultExact]
  simp only [List.flatMap_singleton]
  rw [selectionExact]
  simp

theorem whileExpandTransition_rewriteAt_exact
    (relationEnv : RelationEnv)
    (condition body rest environment receipt : Pattern) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement
          (a "structured-c:while" [condition, body]) rest)
          environment receipt) =
      [run
        (consStatement
          (a "structured-c:if" [condition,
            appendStatements body
              (consStatement
                (a "structured-c:while" [condition, body]) nilStatements),
            nilStatements])
          rest)
        environment receipt] := by
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (run (consStatement
          (a "structured-c:while" [condition, body]) rest)
          environment receipt)) = _
  simp [transitions, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, engineBasePremises,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]

theorem appendEmptyTransition_rewriteAt_exact
    (relationEnv : RelationEnv)
    (continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (appendStatements nilStatements continuation)
          environment receipt) =
      [run continuation environment receipt] := by
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (run (appendStatements nilStatements continuation)
          environment receipt)) = _
  simp [transitions, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]

theorem appendConsTransition_rewriteAt_exact
    (relationEnv : RelationEnv)
    (statement tail continuation environment receipt : Pattern) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (appendStatements (consStatement statement tail) continuation)
          environment receipt) =
      [run (consStatement statement (appendStatements tail continuation))
        environment receipt] := by
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (run (appendStatements (consStatement statement tail) continuation)
          environment receipt)) = _
  simp [transitions, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]

theorem halted_rewriteAt_empty
    (relationEnv : RelationEnv) (outcome environment receipt : Pattern) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (halted outcome environment receipt) = [] := by
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (halted outcome environment receipt)) = []
  simp [transitions, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, applyBindingsForRule,
    applyBindings]

def returnMatchBindings
    (expression rest environment receipt : Pattern) : Bindings := [
  ("environment", environment), ("receipt", receipt), ("rest", rest),
  ("expression", expression)]

def returnValueBindings
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern) : Bindings := [
  ("evaluatedEnvironment", evaluatedEnvironment),
  ("evaluatedReceipt", evaluatedReceipt), ("value", value)] ++
    returnMatchBindings expression rest environment receipt

theorem returnValueTransition_rewriteAt_exact
    (relationEnv : RelationEnv)
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern)
    (evaluationExact :
      premiseStepWithEnv relationEnv language
          (returnMatchBindings expression rest environment receipt)
          (query "StructuredCEvaluate"
            [v "expression", v "environment", v "receipt",
             evaluationValue (v "value"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) =
        [returnValueBindings expression rest environment receipt value
          evaluatedEnvironment evaluatedReceipt])
    (faultExact :
      premiseStepWithEnv relationEnv language
          (returnMatchBindings expression rest environment receipt)
          (query "StructuredCEvaluate"
            [v "expression", v "environment", v "receipt",
             evaluationFault (v "fault"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) = []) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement (a "structured-c:return" [expression]) rest)
          environment receipt) =
      [halted (a "structured-c:outcome-return" [value])
        evaluatedEnvironment evaluatedReceipt] := by
  simp only [query, evaluationValue, evaluationFault, v, a,
    returnMatchBindings, returnValueBindings] at evaluationExact faultExact
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (run (consStatement (a "structured-c:return" [expression]) rest)
          environment receipt)) = _
  simp [transitions, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, engineBasePremises,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]
  rw [evaluationExact, faultExact]
  simp

def declareMatchBindings
    (variableName type expression rest environment receipt : Pattern) : Bindings := [
  ("environment", environment), ("receipt", receipt), ("rest", rest),
  ("type", type), ("expression", expression), ("variable", variableName)]

def declareValueBindings
    (variableName type expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern) : Bindings := [
  ("evaluatedEnvironment", evaluatedEnvironment),
  ("evaluatedReceipt", evaluatedReceipt), ("value", value)] ++
    declareMatchBindings variableName type expression rest environment receipt

def declareStoredBindings
    (variableName type expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt nextEnvironment : Pattern) :
    Bindings :=
  ("nextEnvironment", nextEnvironment) ::
    declareValueBindings variableName type expression rest environment receipt
      value evaluatedEnvironment evaluatedReceipt

theorem declareValueTransition_rewriteAt_exact
    (relationEnv : RelationEnv)
    (variableName type expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt nextEnvironment : Pattern)
    (evaluationExact :
      premiseStepWithEnv relationEnv language
          (declareMatchBindings variableName type expression rest environment receipt)
          (query "StructuredCEvaluate"
            [v "expression", v "environment", v "receipt",
             evaluationValue (v "value"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) =
        [declareValueBindings variableName type expression rest environment receipt
          value evaluatedEnvironment evaluatedReceipt])
    (storeExact :
      premiseStepWithEnv relationEnv language
          (declareValueBindings variableName type expression rest environment receipt
            value evaluatedEnvironment evaluatedReceipt)
          (query "StructuredCStore"
            [v "evaluatedEnvironment", v "variable", v "value",
             v "nextEnvironment"]) =
        [declareStoredBindings variableName type expression rest environment receipt
          value evaluatedEnvironment evaluatedReceipt nextEnvironment])
    (faultExact :
      premiseStepWithEnv relationEnv language
          (declareMatchBindings variableName type expression rest environment receipt)
          (query "StructuredCEvaluate"
            [v "expression", v "environment", v "receipt",
             evaluationFault (v "fault"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) = []) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement
          (a "structured-c:declare" [variableName, type, expression]) rest)
          environment receipt) =
      [run rest nextEnvironment evaluatedReceipt] := by
  simp only [query, evaluationValue, evaluationFault, v, a,
    declareMatchBindings, declareValueBindings, declareStoredBindings]
    at evaluationExact storeExact faultExact
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (run (consStatement
          (a "structured-c:declare" [variableName, type, expression]) rest)
          environment receipt)) = _
  simp [transitions, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, engineBasePremises,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]
  rw [evaluationExact, faultExact]
  simp only [List.flatMap_singleton]
  rw [storeExact]
  simp

def switchMatchBindings
    (scrutinee cases defaultBranch rest environment receipt : Pattern) :
    Bindings := [
  ("environment", environment), ("receipt", receipt), ("rest", rest),
  ("cases", cases), ("defaultBranch", defaultBranch),
  ("scrutinee", scrutinee)]

def switchValueBindings
    (scrutinee cases defaultBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern) : Bindings := [
  ("evaluatedEnvironment", evaluatedEnvironment),
  ("evaluatedReceipt", evaluatedReceipt), ("value", value)] ++
    switchMatchBindings scrutinee cases defaultBranch rest environment receipt

def switchSelectedBindings
    (scrutinee cases defaultBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt selected : Pattern) : Bindings :=
  ("selected", selected) ::
    switchValueBindings scrutinee cases defaultBranch rest environment receipt
      value evaluatedEnvironment evaluatedReceipt

theorem switchValueTransition_rewriteAt_exact
    (relationEnv : RelationEnv)
    (scrutinee cases defaultBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt selected : Pattern)
    (evaluationExact :
      premiseStepWithEnv relationEnv language
          (switchMatchBindings scrutinee cases defaultBranch rest environment receipt)
          (query "StructuredCEvaluate"
            [v "scrutinee", v "environment", v "receipt",
             evaluationValue (v "value"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) =
        [switchValueBindings scrutinee cases defaultBranch rest environment receipt
          value evaluatedEnvironment evaluatedReceipt])
    (selectionExact :
      premiseStepWithEnv relationEnv language
          (switchValueBindings scrutinee cases defaultBranch rest environment receipt
            value evaluatedEnvironment evaluatedReceipt)
          (query "StructuredCSelectCase"
            [v "cases", v "defaultBranch", v "value", v "selected"]) =
        [switchSelectedBindings scrutinee cases defaultBranch rest environment receipt
          value evaluatedEnvironment evaluatedReceipt selected])
    (faultExact :
      premiseStepWithEnv relationEnv language
          (switchMatchBindings scrutinee cases defaultBranch rest environment receipt)
          (query "StructuredCEvaluate"
            [v "scrutinee", v "environment", v "receipt",
             evaluationFault (v "fault"), v "evaluatedEnvironment",
             v "evaluatedReceipt"]) = []) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement
          (a "structured-c:switch" [scrutinee, cases, defaultBranch]) rest)
          environment receipt) =
      [run (appendStatements selected rest)
        evaluatedEnvironment evaluatedReceipt] := by
  simp only [query, evaluationValue, evaluationFault, v, a,
    switchMatchBindings, switchValueBindings, switchSelectedBindings]
    at evaluationExact selectionExact faultExact
  change transitions.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises relationEnv) language
        (rewriteAt (engineBasePremises relationEnv) language 0) rule
        (run (consStatement
          (a "structured-c:switch" [scrutinee, cases, defaultBranch]) rest)
          environment receipt)) = _
  simp [transitions, applyRuleUsing, matchPatternForRule_eq_syntactic,
    premisesUsing, premiseStepUsing, engineBasePremises,
    emptyTransition, appendEmptyTransition, appendConsTransition,
    assignValueTransition, assignFaultTransition,
    declareValueTransition, declareFaultTransition,
    effectValueTransition, effectFaultTransition,
    ifValueTransition, ifFaultTransition, whileExpandTransition,
    switchValueTransition, switchFaultTransition,
    returnValueTransition, returnFaultTransition,
    run, halted, nilStatements, consStatement, appendStatements,
    evaluationValue, evaluationFault, commonContext, query, typed, v, a,
    matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
    applyBindings]
  rw [evaluationExact, faultExact]
  simp only [List.flatMap_singleton]
  rw [selectionExact]
  simp

private def expressionBindings
    (expression rest environment receipt : Pattern) : Bindings := [
  ("environment", environment), ("receipt", receipt), ("rest", rest),
  ("expression", expression)]

private def expressionValueBindings
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern) : Bindings := [
  ("evaluatedEnvironment", evaluatedEnvironment),
  ("evaluatedReceipt", evaluatedReceipt), ("value", value)] ++
    expressionBindings expression rest environment receipt

theorem expressionEvaluationValue_exact_of_tuples
    (relationEnv : RelationEnv)
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern)
    (tuplesExact : ∀ result outputEnvironment outputReceipt,
      relationEnv.tuples "StructuredCEvaluate"
          [expression, environment, receipt, result,
           outputEnvironment, outputReceipt] =
        [[expression, environment, receipt, evaluationValue value,
          evaluatedEnvironment, evaluatedReceipt]]) :
    premiseStepWithEnv relationEnv language
        (expressionBindings expression rest environment receipt)
        (query "StructuredCEvaluate"
          [v "expression", v "environment", v "receipt",
           evaluationValue (v "value"), v "evaluatedEnvironment",
           v "evaluatedReceipt"]) =
      [expressionValueBindings expression rest environment receipt value
        evaluatedEnvironment evaluatedReceipt] := by
  change relationQueryStep relationEnv language
    (expressionBindings expression rest environment receipt)
    "StructuredCEvaluate"
      [v "expression", v "environment", v "receipt",
       evaluationValue (v "value"), v "evaluatedEnvironment",
       v "evaluatedReceipt"] = _
  simp [relationQueryStep, builtinRelationTuples, tuplesExact,
    expressionBindings, expressionValueBindings, evaluationValue, v, a,
    matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
    Bindings.lookup, applyBindings, mergeBindings]

theorem expressionEvaluationFault_empty_of_value_tuples
    (relationEnv : RelationEnv)
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern)
    (tuplesExact : ∀ result outputEnvironment outputReceipt,
      relationEnv.tuples "StructuredCEvaluate"
          [expression, environment, receipt, result,
           outputEnvironment, outputReceipt] =
        [[expression, environment, receipt, evaluationValue value,
          evaluatedEnvironment, evaluatedReceipt]]) :
    premiseStepWithEnv relationEnv language
        (expressionBindings expression rest environment receipt)
        (query "StructuredCEvaluate"
          [v "expression", v "environment", v "receipt",
           evaluationFault (v "fault"), v "evaluatedEnvironment",
           v "evaluatedReceipt"]) = [] := by
  change relationQueryStep relationEnv language
    (expressionBindings expression rest environment receipt)
    "StructuredCEvaluate"
      [v "expression", v "environment", v "receipt",
       evaluationFault (v "fault"), v "evaluatedEnvironment",
       v "evaluatedReceipt"] = []
  simp [relationQueryStep, builtinRelationTuples, tuplesExact,
    expressionBindings, evaluationValue, evaluationFault, v, a,
    matchRelationArgs, matchRelationArgument, matchPattern,
    Bindings.lookup, applyBindings, mergeBindings]

theorem effectValueTransition_rewriteAt_exact_of_tuples
    (relationEnv : RelationEnv)
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern)
    (tuplesExact : ∀ result outputEnvironment outputReceipt,
      relationEnv.tuples "StructuredCEvaluate"
          [expression, environment, receipt, result,
           outputEnvironment, outputReceipt] =
        [[expression, environment, receipt, evaluationValue value,
          evaluatedEnvironment, evaluatedReceipt]]) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement (a "structured-c:effect" [expression]) rest)
          environment receipt) =
      [run rest evaluatedEnvironment evaluatedReceipt] := by
  apply effectValueTransition_rewriteAt_exact
  · simpa [effectMatchBindings, effectValueBindings,
      expressionBindings, expressionValueBindings] using
      expressionEvaluationValue_exact_of_tuples relationEnv expression rest
        environment receipt value evaluatedEnvironment evaluatedReceipt
        tuplesExact
  · simpa [effectMatchBindings, expressionBindings] using
      expressionEvaluationFault_empty_of_value_tuples relationEnv expression rest
        environment receipt value evaluatedEnvironment evaluatedReceipt
        tuplesExact

theorem returnValueTransition_rewriteAt_exact_of_tuples
    (relationEnv : RelationEnv)
    (expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt : Pattern)
    (tuplesExact : ∀ result outputEnvironment outputReceipt,
      relationEnv.tuples "StructuredCEvaluate"
          [expression, environment, receipt, result,
           outputEnvironment, outputReceipt] =
        [[expression, environment, receipt, evaluationValue value,
          evaluatedEnvironment, evaluatedReceipt]]) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement (a "structured-c:return" [expression]) rest)
          environment receipt) =
      [halted (a "structured-c:outcome-return" [value])
        evaluatedEnvironment evaluatedReceipt] := by
  apply returnValueTransition_rewriteAt_exact
  · simpa [returnMatchBindings, returnValueBindings,
      expressionBindings, expressionValueBindings] using
      expressionEvaluationValue_exact_of_tuples relationEnv expression rest
        environment receipt value evaluatedEnvironment evaluatedReceipt
        tuplesExact
  · simpa [returnMatchBindings, expressionBindings] using
      expressionEvaluationFault_empty_of_value_tuples relationEnv expression rest
        environment receipt value evaluatedEnvironment evaluatedReceipt
        tuplesExact

theorem ifValueTransition_rewriteAt_exact_of_tuples
    (relationEnv : RelationEnv)
    (condition thenBranch elseBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt selected : Pattern)
    (evaluationTuples : ∀ result outputEnvironment outputReceipt,
      relationEnv.tuples "StructuredCEvaluate"
          [condition, environment, receipt, result,
           outputEnvironment, outputReceipt] =
        [[condition, environment, receipt, evaluationValue value,
          evaluatedEnvironment, evaluatedReceipt]])
    (selectionTuples : ∀ output,
      relationEnv.tuples "StructuredCSelectBranch"
          [value, thenBranch, elseBranch, output] =
        [[value, thenBranch, elseBranch, selected]]) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement
          (a "structured-c:if" [condition, thenBranch, elseBranch]) rest)
          environment receipt) =
      [run (appendStatements selected rest)
        evaluatedEnvironment evaluatedReceipt] := by
  refine ifValueTransition_rewriteAt_exact relationEnv condition thenBranch
    elseBranch rest environment receipt value evaluatedEnvironment
    evaluatedReceipt selected ?_ ?_ ?_
  · change relationQueryStep relationEnv language
      (ifMatchBindings condition thenBranch elseBranch rest environment receipt)
      "StructuredCEvaluate"
        [v "condition", v "environment", v "receipt",
         evaluationValue (v "value"), v "evaluatedEnvironment",
         v "evaluatedReceipt"] = _
    simp [relationQueryStep, builtinRelationTuples, evaluationTuples,
      ifMatchBindings, ifValueBindings, evaluationValue, v, a,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
      Bindings.lookup, applyBindings, mergeBindings]
  · change relationQueryStep relationEnv language
      (ifValueBindings condition thenBranch elseBranch rest environment receipt
        value evaluatedEnvironment evaluatedReceipt)
      "StructuredCSelectBranch"
        [v "value", v "thenBranch", v "elseBranch", v "selected"] = _
    simp [relationQueryStep, builtinRelationTuples, selectionTuples,
      ifMatchBindings, ifValueBindings, ifSelectedBindings, v,
      matchRelationArgs, matchRelationArgument,
      Bindings.lookup, applyBindings, mergeBindings]
  · change relationQueryStep relationEnv language
      (ifMatchBindings condition thenBranch elseBranch rest environment receipt)
      "StructuredCEvaluate"
        [v "condition", v "environment", v "receipt",
         evaluationFault (v "fault"), v "evaluatedEnvironment",
         v "evaluatedReceipt"] = []
    simp [relationQueryStep, builtinRelationTuples, evaluationTuples,
      ifMatchBindings, evaluationValue, evaluationFault, v, a,
      matchRelationArgs, matchRelationArgument, matchPattern,
      Bindings.lookup, applyBindings, mergeBindings]

theorem declareValueTransition_rewriteAt_exact_of_tuples
    (relationEnv : RelationEnv)
    (variableName type expression rest environment receipt value
      evaluatedEnvironment evaluatedReceipt nextEnvironment : Pattern)
    (evaluationTuples : ∀ result outputEnvironment outputReceipt,
      relationEnv.tuples "StructuredCEvaluate"
          [expression, environment, receipt, result,
           outputEnvironment, outputReceipt] =
        [[expression, environment, receipt, evaluationValue value,
          evaluatedEnvironment, evaluatedReceipt]])
    (storeTuples : ∀ output,
      relationEnv.tuples "StructuredCStore"
          [evaluatedEnvironment, variableName, value, output] =
        [[evaluatedEnvironment, variableName, value, nextEnvironment]]) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement
          (a "structured-c:declare" [variableName, type, expression]) rest)
          environment receipt) =
      [run rest nextEnvironment evaluatedReceipt] := by
  refine declareValueTransition_rewriteAt_exact relationEnv variableName type
    expression rest environment receipt value evaluatedEnvironment
    evaluatedReceipt nextEnvironment ?_ ?_ ?_
  · change relationQueryStep relationEnv language
      (declareMatchBindings variableName type expression rest environment receipt)
      "StructuredCEvaluate"
        [v "expression", v "environment", v "receipt",
         evaluationValue (v "value"), v "evaluatedEnvironment",
         v "evaluatedReceipt"] = _
    simp [relationQueryStep, builtinRelationTuples, evaluationTuples,
      declareMatchBindings, declareValueBindings, evaluationValue, v, a,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
      Bindings.lookup, applyBindings, mergeBindings]
  · change relationQueryStep relationEnv language
      (declareValueBindings variableName type expression rest environment receipt
        value evaluatedEnvironment evaluatedReceipt)
      "StructuredCStore"
        [v "evaluatedEnvironment", v "variable", v "value",
         v "nextEnvironment"] = _
    simp [relationQueryStep, builtinRelationTuples, storeTuples,
      declareMatchBindings, declareValueBindings, declareStoredBindings, v,
      matchRelationArgs, matchRelationArgument,
      Bindings.lookup, applyBindings, mergeBindings]
  · change relationQueryStep relationEnv language
      (declareMatchBindings variableName type expression rest environment receipt)
      "StructuredCEvaluate"
        [v "expression", v "environment", v "receipt",
         evaluationFault (v "fault"), v "evaluatedEnvironment",
         v "evaluatedReceipt"] = []
    simp [relationQueryStep, builtinRelationTuples, evaluationTuples,
      declareMatchBindings, evaluationValue, evaluationFault, v, a,
      matchRelationArgs, matchRelationArgument, matchPattern,
      Bindings.lookup, applyBindings, mergeBindings]

theorem switchValueTransition_rewriteAt_exact_of_tuples
    (relationEnv : RelationEnv)
    (scrutinee cases defaultBranch rest environment receipt value
      evaluatedEnvironment evaluatedReceipt selected : Pattern)
    (evaluationTuples : ∀ result outputEnvironment outputReceipt,
      relationEnv.tuples "StructuredCEvaluate"
          [scrutinee, environment, receipt, result,
           outputEnvironment, outputReceipt] =
        [[scrutinee, environment, receipt, evaluationValue value,
          evaluatedEnvironment, evaluatedReceipt]])
    (selectionTuples : ∀ output,
      relationEnv.tuples "StructuredCSelectCase"
          [cases, defaultBranch, value, output] =
        [[cases, defaultBranch, value, selected]]) :
    rewriteAt (engineBasePremises relationEnv) language 1
        (run (consStatement
          (a "structured-c:switch" [scrutinee, cases, defaultBranch]) rest)
          environment receipt) =
      [run (appendStatements selected rest)
        evaluatedEnvironment evaluatedReceipt] := by
  refine switchValueTransition_rewriteAt_exact relationEnv scrutinee cases
    defaultBranch rest environment receipt value evaluatedEnvironment
    evaluatedReceipt selected ?_ ?_ ?_
  · change relationQueryStep relationEnv language
      (switchMatchBindings scrutinee cases defaultBranch rest environment receipt)
      "StructuredCEvaluate"
        [v "scrutinee", v "environment", v "receipt",
         evaluationValue (v "value"), v "evaluatedEnvironment",
         v "evaluatedReceipt"] = _
    simp [relationQueryStep, builtinRelationTuples, evaluationTuples,
      switchMatchBindings, switchValueBindings, evaluationValue, v, a,
      matchRelationArgs, matchRelationArgument, matchPattern, matchArgs,
      Bindings.lookup, applyBindings, mergeBindings]
  · change relationQueryStep relationEnv language
      (switchValueBindings scrutinee cases defaultBranch rest environment receipt
        value evaluatedEnvironment evaluatedReceipt)
      "StructuredCSelectCase"
        [v "cases", v "defaultBranch", v "value", v "selected"] = _
    simp [relationQueryStep, builtinRelationTuples, selectionTuples,
      switchMatchBindings, switchValueBindings, switchSelectedBindings, v,
      matchRelationArgs, matchRelationArgument,
      Bindings.lookup, applyBindings, mergeBindings]
  · change relationQueryStep relationEnv language
      (switchMatchBindings scrutinee cases defaultBranch rest environment receipt)
      "StructuredCEvaluate"
        [v "scrutinee", v "environment", v "receipt",
         evaluationFault (v "fault"), v "evaluatedEnvironment",
         v "evaluatedReceipt"] = []
    simp [relationQueryStep, builtinRelationTuples, evaluationTuples,
      switchMatchBindings, evaluationValue, evaluationFault, v, a,
      matchRelationArgs, matchRelationArgument, matchPattern,
      Bindings.lookup, applyBindings, mergeBindings]

#print axioms effectValueTransition_rewriteAt_exact
#print axioms ifValueTransition_rewriteAt_exact
#print axioms whileExpandTransition_rewriteAt_exact
#print axioms appendEmptyTransition_rewriteAt_exact
#print axioms appendConsTransition_rewriteAt_exact
#print axioms halted_rewriteAt_empty
#print axioms returnValueTransition_rewriteAt_exact
#print axioms declareValueTransition_rewriteAt_exact
#print axioms switchValueTransition_rewriteAt_exact
#print axioms effectValueTransition_rewriteAt_exact_of_tuples
#print axioms returnValueTransition_rewriteAt_exact_of_tuples
#print axioms ifValueTransition_rewriteAt_exact_of_tuples
#print axioms declareValueTransition_rewriteAt_exact_of_tuples
#print axioms switchValueTransition_rewriteAt_exact_of_tuples

end Mettapedia.GSLT.LanguageDef.StructuredCTransitionAdmission
