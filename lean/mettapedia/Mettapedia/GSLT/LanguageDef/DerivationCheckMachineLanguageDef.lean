import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Std.Data.String.ToInt

/-!
# Authored presentation of the derivation-check machine

This is the reusable target presentation corresponding to the semantic
machine in `DerivationCheckMachine`.  Its control flow is fixed and visible.
Nine deliberately separate relations supply bounded index advancement,
local relevance-shape checking, input admission, parent resolution with
relevance-link discharge, calculus-rule checking, safe deletion, root
shape checking, final semantic checking, and final relevance checking.  A closed generated
instance must supply every relation from separately validated components;
there is no undifferentiated execute-instruction relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationCheckMachineLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

def ctor (label category : String)
    (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label := label
  category := category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy
}

def typed (entries : List (String × String)) :
    List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def v (name : String) : Pattern := .fvar name
def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments
def query (relation : String) (arguments : List Pattern) : Premise :=
  .relationQuery relation arguments

def run (instructions nodes nextId root serviceState : Pattern) : Pattern :=
  a "dcm:run" [instructions, nodes, nextId, root, serviceState]

def halted (outcome nodes : Pattern) : Pattern :=
  a "dcm:halted" [outcome, nodes]

def instructionsNil : Pattern := a "dcm:instructions-nil"
def instructionsCons (instruction rest : Pattern) : Pattern :=
  a "dcm:instructions-cons" [instruction, rest]
def nodesCons (node nodes : Pattern) : Pattern :=
  a "dcm:nodes-cons" [node, nodes]
def node (id formula relevance linked : Pattern) : Pattern :=
  a "dcm:node" [id, formula, relevance, linked]
def rootNone : Pattern := a "dcm:root-none"
def rootSome (id formula obligation : Pattern) : Pattern :=
  a "dcm:root-some" [id, formula, obligation]
def decisionFault (fault : Pattern) : Pattern :=
  a "dcm:decision-fault" [fault]
def decisionState (state : Pattern) : Pattern :=
  a "dcm:decision-state" [state]
def outcomeFault (fault : Pattern) : Pattern :=
  a "dcm:outcome-fault" [fault]

def commonContext : List (String × TypeExpr) := typed [
  ("rest", "Instructions"), ("nodes", "Nodes"),
  ("nextId", "Index"), ("root", "RootState"),
  ("serviceState", "ServiceState"), ("fault", "Fault")]

def missingFinishTransition : RewriteRule := {
  name := "dcm:missing-finish"
  typeContext := typed [
    ("nodes", "Nodes"), ("nextId", "Index"), ("root", "RootState"),
    ("serviceState", "ServiceState")]
  premises := []
  left := run instructionsNil (v "nodes") (v "nextId") (v "root")
    (v "serviceState")
  right := halted (outcomeFault (a "dcm:fault-missing-finish")) (v "nodes")
}

def inputIndexFaultTransition : RewriteRule := {
  name := "dcm:input-index-fault"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("formula", "Formula"),
    ("provenance", "Provenance"), ("relevance", "Relevance")]
  premises := [query "DCMIndexAdvance" [
    v "nextId", v "id", decisionFault (v "fault")]]
  left := run
    (instructionsCons
      (a "dcm:input" [v "id", v "formula", v "provenance", v "relevance"])
      (v "rest")) (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def inputDecisionFaultTransition : RewriteRule := {
  name := "dcm:input-decision-fault"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("formula", "Formula"),
    ("provenance", "Provenance"), ("relevance", "Relevance"),
    ("advanced", "Index")]
  premises := [
    query "DCMIndexAdvance" [v "nextId", v "id",
      a "dcm:decision-index" [v "advanced"]],
    query "DCMRelevanceShapeDecision" [v "id", v "relevance",
      a "dcm:decision-accept"],
    query "DCMInputDecision" [v "id", v "serviceState", v "provenance",
      v "formula", decisionFault (v "fault")]]
  left := run
    (instructionsCons
      (a "dcm:input" [v "id", v "formula", v "provenance", v "relevance"])
      (v "rest")) (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def inputRelevanceFaultTransition : RewriteRule := {
  name := "dcm:input-relevance-fault"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("formula", "Formula"),
    ("provenance", "Provenance"), ("relevance", "Relevance"),
    ("advanced", "Index")]
  premises := [
    query "DCMIndexAdvance" [v "nextId", v "id",
      a "dcm:decision-index" [v "advanced"]],
    query "DCMRelevanceShapeDecision" [v "id", v "relevance",
      decisionFault (v "fault")]]
  left := run
    (instructionsCons
      (a "dcm:input" [v "id", v "formula", v "provenance", v "relevance"])
      (v "rest")) (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def inputAcceptTransition : RewriteRule := {
  name := "dcm:input-accept"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("formula", "Formula"),
    ("provenance", "Provenance"), ("relevance", "Relevance"),
    ("advanced", "Index"), ("nextServiceState", "ServiceState")]
  premises := [
    query "DCMIndexAdvance" [v "nextId", v "id",
      a "dcm:decision-index" [v "advanced"]],
    query "DCMRelevanceShapeDecision" [v "id", v "relevance",
      a "dcm:decision-accept"],
    query "DCMInputDecision" [v "id", v "serviceState", v "provenance",
      v "formula", decisionState (v "nextServiceState")]]
  left := run
    (instructionsCons
      (a "dcm:input" [v "id", v "formula", v "provenance", v "relevance"])
      (v "rest")) (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := run (v "rest")
    (nodesCons (node (v "id") (v "formula") (v "relevance")
      (a "dcm:unlinked")) (v "nodes"))
    (v "advanced") (v "root") (v "nextServiceState")
}

def inferIndexFaultTransition : RewriteRule := {
  name := "dcm:infer-index-fault"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("rule", "Rule"), ("parents", "ParentIds"),
    ("evidence", "Evidence"), ("conclusion", "Formula"),
    ("relevance", "Relevance")]
  premises := [query "DCMIndexAdvance" [
    v "nextId", v "id", decisionFault (v "fault")]]
  left := run
    (instructionsCons (a "dcm:infer" [v "id", v "rule", v "parents",
      v "evidence", v "conclusion", v "relevance"]) (v "rest"))
    (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def inferParentFaultTransition : RewriteRule := {
  name := "dcm:infer-parent-fault"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("rule", "Rule"), ("parents", "ParentIds"),
    ("evidence", "Evidence"), ("conclusion", "Formula"),
    ("relevance", "Relevance"), ("advanced", "Index")]
  premises := [
    query "DCMIndexAdvance" [v "nextId", v "id",
      a "dcm:decision-index" [v "advanced"]],
    query "DCMRelevanceShapeDecision" [v "id", v "relevance",
      a "dcm:decision-accept"],
    query "DCMResolveParents" [v "nodes", v "id", v "relevance",
      v "parents", decisionFault (v "fault")]]
  left := run
    (instructionsCons (a "dcm:infer" [v "id", v "rule", v "parents",
      v "evidence", v "conclusion", v "relevance"]) (v "rest"))
    (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def inferRelevanceFaultTransition : RewriteRule := {
  name := "dcm:infer-relevance-fault"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("rule", "Rule"), ("parents", "ParentIds"),
    ("evidence", "Evidence"), ("conclusion", "Formula"),
    ("relevance", "Relevance"), ("advanced", "Index")]
  premises := [
    query "DCMIndexAdvance" [v "nextId", v "id",
      a "dcm:decision-index" [v "advanced"]],
    query "DCMRelevanceShapeDecision" [v "id", v "relevance",
      decisionFault (v "fault")]]
  left := run
    (instructionsCons (a "dcm:infer" [v "id", v "rule", v "parents",
      v "evidence", v "conclusion", v "relevance"]) (v "rest"))
    (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def inferRuleFaultTransition : RewriteRule := {
  name := "dcm:infer-rule-fault"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("rule", "Rule"), ("parents", "ParentIds"),
    ("evidence", "Evidence"), ("conclusion", "Formula"),
    ("relevance", "Relevance"), ("advanced", "Index"),
    ("parentFormulas", "Formulas"), ("nextNodes", "Nodes")]
  premises := [
    query "DCMIndexAdvance" [v "nextId", v "id",
      a "dcm:decision-index" [v "advanced"]],
    query "DCMRelevanceShapeDecision" [v "id", v "relevance",
      a "dcm:decision-accept"],
    query "DCMResolveParents" [v "nodes", v "id", v "relevance",
      v "parents", a "dcm:decision-parents" [v "parentFormulas", v "nextNodes"]],
    query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
      v "parentFormulas", v "evidence",
      v "conclusion", decisionFault (v "fault")]]
  left := run
    (instructionsCons (a "dcm:infer" [v "id", v "rule", v "parents",
      v "evidence", v "conclusion", v "relevance"]) (v "rest"))
    (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nextNodes")
}

def inferAcceptTransition : RewriteRule := {
  name := "dcm:infer-accept"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("rule", "Rule"), ("parents", "ParentIds"),
    ("evidence", "Evidence"), ("conclusion", "Formula"),
    ("relevance", "Relevance"), ("advanced", "Index"),
    ("parentFormulas", "Formulas"), ("nextNodes", "Nodes"),
    ("nextServiceState", "ServiceState")]
  premises := [
    query "DCMIndexAdvance" [v "nextId", v "id",
      a "dcm:decision-index" [v "advanced"]],
    query "DCMRelevanceShapeDecision" [v "id", v "relevance",
      a "dcm:decision-accept"],
    query "DCMResolveParents" [v "nodes", v "id", v "relevance",
      v "parents", a "dcm:decision-parents" [v "parentFormulas", v "nextNodes"]],
    query "DCMRuleDecision" [v "id", v "serviceState", v "rule",
      v "parentFormulas", v "evidence", v "conclusion",
      decisionState (v "nextServiceState")]]
  left := run
    (instructionsCons (a "dcm:infer" [v "id", v "rule", v "parents",
      v "evidence", v "conclusion", v "relevance"]) (v "rest"))
    (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := run (v "rest")
    (nodesCons (node (v "id") (v "conclusion") (v "relevance")
      (a "dcm:unlinked")) (v "nextNodes"))
    (v "advanced") (v "root") (v "nextServiceState")
}

def dropFaultTransition : RewriteRule := {
  name := "dcm:drop-fault"
  typeContext := commonContext ++ typed [("id", "Index")]
  premises := [query "DCMDropDecision"
    [v "nodes", v "id", decisionFault (v "fault")]]
  left := run (instructionsCons (a "dcm:drop" [v "id"]) (v "rest"))
    (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def dropAcceptTransition : RewriteRule := {
  name := "dcm:drop-accept"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("nextNodes", "Nodes")]
  premises := [query "DCMDropDecision" [v "nodes", v "id",
    a "dcm:decision-nodes" [v "nextNodes"]]]
  left := run (instructionsCons (a "dcm:drop" [v "id"]) (v "rest"))
    (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := run (v "rest") (v "nextNodes") (v "nextId") (v "root")
    (v "serviceState")
}

def duplicateRootTransition : RewriteRule := {
  name := "dcm:duplicate-root"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("obligation", "Obligation"),
    ("priorId", "Index"), ("priorFormula", "Formula"),
    ("priorObligation", "Obligation")]
  premises := []
  left := run (instructionsCons
    (a "dcm:root" [v "id", v "obligation"]) (v "rest"))
    (v "nodes") (v "nextId")
    (rootSome (v "priorId") (v "priorFormula") (v "priorObligation"))
    (v "serviceState")
  right := halted (outcomeFault (a "dcm:fault-duplicate-root")) (v "nodes")
}

def rootFaultTransition : RewriteRule := {
  name := "dcm:root-fault"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("obligation", "Obligation")]
  premises := [query "DCMRootShapeDecision" [v "nodes", v "id",
    decisionFault (v "fault")]]
  left := run (instructionsCons
    (a "dcm:root" [v "id", v "obligation"]) (v "rest"))
    (v "nodes") (v "nextId") rootNone (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def rootAcceptTransition : RewriteRule := {
  name := "dcm:root-accept"
  typeContext := commonContext ++ typed [
    ("id", "Index"), ("obligation", "Obligation"),
    ("formula", "Formula")]
  premises := [query "DCMRootShapeDecision" [v "nodes", v "id",
    a "dcm:decision-root" [v "formula"]]]
  left := run (instructionsCons
    (a "dcm:root" [v "id", v "obligation"]) (v "rest"))
    (v "nodes") (v "nextId") rootNone (v "serviceState")
  right := run (v "rest") (v "nodes") (v "nextId")
    (rootSome (v "id") (v "formula") (v "obligation")) (v "serviceState")
}

def finishTrailingTransition : RewriteRule := {
  name := "dcm:finish-trailing"
  typeContext := commonContext ++ typed [("next", "Instruction")]
  premises := []
  left := run (instructionsCons (a "dcm:finish")
    (instructionsCons (v "next") (v "rest")))
    (v "nodes") (v "nextId") (v "root") (v "serviceState")
  right := halted (outcomeFault (a "dcm:fault-trailing-after-finish"))
    (v "nodes")
}

def finishMissingRootTransition : RewriteRule := {
  name := "dcm:finish-missing-root"
  typeContext := typed [("nodes", "Nodes"), ("nextId", "Index"),
    ("serviceState", "ServiceState")]
  premises := []
  left := run (instructionsCons (a "dcm:finish") instructionsNil)
    (v "nodes") (v "nextId") rootNone (v "serviceState")
  right := halted (outcomeFault (a "dcm:fault-missing-root")) (v "nodes")
}

def finishRelevanceFaultTransition : RewriteRule := {
  name := "dcm:finish-relevance-fault"
  typeContext := typed [
    ("nodes", "Nodes"), ("nextId", "Index"), ("id", "Index"),
    ("formula", "Formula"), ("obligation", "Obligation"),
    ("serviceState", "ServiceState"), ("fault", "Fault")]
  premises := [query "DCMRelevanceDecision" [v "nodes", v "id",
    decisionFault (v "fault")]]
  left := run (instructionsCons (a "dcm:finish") instructionsNil)
    (v "nodes") (v "nextId")
    (rootSome (v "id") (v "formula") (v "obligation"))
    (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def finishRootFaultTransition : RewriteRule := {
  name := "dcm:finish-root-fault"
  typeContext := typed [
    ("nodes", "Nodes"), ("nextId", "Index"), ("id", "Index"),
    ("formula", "Formula"), ("obligation", "Obligation"),
    ("serviceState", "ServiceState"), ("fault", "Fault")]
  premises := [
    query "DCMRelevanceDecision" [v "nodes", v "id",
      a "dcm:decision-accept"],
    query "DCMFinalDecision" [v "id", v "serviceState", v "formula",
      v "obligation", decisionFault (v "fault")]]
  left := run (instructionsCons (a "dcm:finish") instructionsNil)
    (v "nodes") (v "nextId")
    (rootSome (v "id") (v "formula") (v "obligation"))
    (v "serviceState")
  right := halted (outcomeFault (v "fault")) (v "nodes")
}

def finishVerifiedTransition : RewriteRule := {
  name := "dcm:finish-verified"
  typeContext := typed [
    ("nodes", "Nodes"), ("nextId", "Index"), ("id", "Index"),
    ("formula", "Formula"), ("obligation", "Obligation"),
    ("serviceState", "ServiceState")]
  premises := [
    query "DCMRelevanceDecision" [v "nodes", v "id",
      a "dcm:decision-accept"],
    query "DCMFinalDecision" [v "id", v "serviceState", v "formula",
      v "obligation", a "dcm:decision-accept"]]
  left := run (instructionsCons (a "dcm:finish") instructionsNil)
    (v "nodes") (v "nextId")
    (rootSome (v "id") (v "formula") (v "obligation"))
    (v "serviceState")
  right := halted
    (a "dcm:outcome-verified" [v "id", v "formula", v "obligation"])
    (v "nodes")
}

def transitions : List RewriteRule := [
  missingFinishTransition,
  inputIndexFaultTransition,
  inputRelevanceFaultTransition,
  inputDecisionFaultTransition,
  inputAcceptTransition,
  inferIndexFaultTransition,
  inferRelevanceFaultTransition,
  inferParentFaultTransition,
  inferRuleFaultTransition,
  inferAcceptTransition,
  dropFaultTransition,
  dropAcceptTransition,
  duplicateRootTransition,
  rootFaultTransition,
  rootAcceptTransition,
  finishTrailingTransition,
  finishMissingRootTransition,
  finishRelevanceFaultTransition,
  finishRootFaultTransition,
  finishVerifiedTransition
]

def terms : List GrammarRule := [
  ctor "dcm:index" "Index" [("value", "Integer")],
  ctor "dcm:relevance" "Relevance" [
    ("distance", "Index"), ("towardRoot", "OptionalIndex")],
  ctor "dcm:index-none" "OptionalIndex" [],
  ctor "dcm:index-some" "OptionalIndex" [("value", "Index")],
  ctor "dcm:parent-ids-nil" "ParentIds" [],
  ctor "dcm:parent-ids-cons" "ParentIds" [
    ("id", "Index"), ("rest", "ParentIds")],
  ctor "dcm:formulas-nil" "Formulas" [],
  ctor "dcm:formulas-cons" "Formulas" [
    ("formula", "Formula"), ("rest", "Formulas")],
  ctor "dcm:unlinked" "LinkState" [],
  ctor "dcm:linked" "LinkState" [],
  ctor "dcm:node" "Node" [
    ("id", "Index"), ("formula", "Formula"),
    ("relevance", "Relevance"), ("linked", "LinkState")],
  ctor "dcm:nodes-nil" "Nodes" [],
  ctor "dcm:nodes-cons" "Nodes" [("node", "Node"), ("rest", "Nodes")],
  ctor "dcm:input" "Instruction" [
    ("id", "Index"), ("formula", "Formula"),
    ("provenance", "Provenance"), ("relevance", "Relevance")],
  ctor "dcm:infer" "Instruction" [
    ("id", "Index"), ("rule", "Rule"), ("parents", "ParentIds"),
    ("evidence", "Evidence"), ("conclusion", "Formula"),
    ("relevance", "Relevance")],
  ctor "dcm:drop" "Instruction" [("id", "Index")],
  ctor "dcm:root" "Instruction" [
    ("id", "Index"), ("obligation", "Obligation")],
  ctor "dcm:finish" "Instruction" [],
  ctor "dcm:instructions-nil" "Instructions" [],
  ctor "dcm:instructions-cons" "Instructions" [
    ("instruction", "Instruction"), ("rest", "Instructions")],
  ctor "dcm:root-none" "RootState" [],
  ctor "dcm:root-some" "RootState" [
    ("id", "Index"), ("formula", "Formula"),
    ("obligation", "Obligation")],
  ctor "dcm:decision-index" "Decision" [("next", "Index")],
  ctor "dcm:decision-parents" "Decision" [
    ("formulas", "Formulas"), ("nodes", "Nodes")],
  ctor "dcm:decision-nodes" "Decision" [("nodes", "Nodes")],
  ctor "dcm:decision-root" "Decision" [("formula", "Formula")],
  ctor "dcm:decision-state" "Decision" [("state", "ServiceState")],
  ctor "dcm:decision-accept" "Decision" [],
  ctor "dcm:decision-fault" "Decision" [("fault", "Fault")],
  ctor "dcm:fault-bad-node-id" "Fault" [
    ("expected", "Index"), ("actual", "Index")],
  ctor "dcm:fault-malformed-relevance" "Fault" [("id", "Index")],
  ctor "dcm:fault-input-rejected" "Fault" [("id", "Index")],
  ctor "dcm:fault-duplicate-parent" "Fault" [
    ("child", "Index"), ("parent", "Index")],
  ctor "dcm:fault-missing-parent" "Fault" [
    ("child", "Index"), ("parent", "Index")],
  ctor "dcm:fault-bad-relevance-edge" "Fault" [
    ("child", "Index"), ("parent", "Index")],
  ctor "dcm:fault-rule-rejected" "Fault" [("id", "Index")],
  ctor "dcm:fault-drop-rejected" "Fault" [("id", "Index")],
  ctor "dcm:fault-missing-root-node" "Fault" [("id", "Index")],
  ctor "dcm:fault-root-rejected" "Fault" [("id", "Index")],
  ctor "dcm:fault-irrelevant-node" "Fault" [("id", "Index")],
  ctor "dcm:fault-language" "Fault" [("message", "String")],
  ctor "dcm:fault-engine" "Fault" [("message", "String")],
  ctor "dcm:fault-resource" "Fault" [("message", "String")],
  ctor "dcm:fault-duplicate-root" "Fault" [],
  ctor "dcm:fault-malformed-record" "Fault" [],
  ctor "dcm:fault-missing-root" "Fault" [],
  ctor "dcm:fault-missing-finish" "Fault" [],
  ctor "dcm:fault-trailing-after-finish" "Fault" [],
  ctor "dcm:outcome-verified" "Outcome" [
    ("id", "Index"), ("formula", "Formula"),
    ("obligation", "Obligation")],
  ctor "dcm:outcome-fault" "Outcome" [("fault", "Fault")],
  ctor "dcm:service-state-initial" "ServiceState" [],
  ctor "dcm:run" "Config" [
    ("instructions", "Instructions"), ("nodes", "Nodes"),
    ("nextId", "Index"), ("root", "RootState"),
    ("serviceState", "ServiceState")] (some .rewrite),
  ctor "dcm:halted" "Config" [
    ("outcome", "Outcome"), ("nodes", "Nodes")]
]

/-- The open target schema.  `Formula`, `Rule`, `Evidence`, `Provenance`, and
`Obligation` are interface carriers populated by a generated closed instance. -/
def language : LanguageDef := {
  name := "DerivationCheckMachine"
  types := [
    { name := "Integer", carrier := .builtinInt },
    { name := "String", carrier := .builtinString },
    "Index", "OptionalIndex", "Formula", "Rule", "Evidence", "Provenance",
    "Obligation", "ServiceState", "Relevance", "ParentIds", "Formulas", "LinkState", "Node",
    "Nodes", "Instruction", "Instructions", "RootState", "Decision", "Fault",
    "Outcome", "Config"]
  terms := terms
  equations := []
  rewrites := transitions
}

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 100000 in
private theorem rewrites_validate :
    ∀ rewrite ∈ language.rewrites,
      LanguageDef.validateRewrite language rewrite = [] := by
  intro rewrite membership
  change rewrite ∈ transitions at membership
  simp only [transitions, List.mem_cons, List.mem_nil_iff, or_false]
    at membership
  rcases membership with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := { maxSteps := 2000000 })
      [LanguageDef.validateRewrite, language, terms, ctor, typed, v, a,
      query, run, halted, instructionsNil, instructionsCons, nodesCons,
      node, rootNone, rootSome, decisionFault, decisionState, outcomeFault,
      commonContext,
      missingFinishTransition, inputIndexFaultTransition,
      inputRelevanceFaultTransition, inputDecisionFaultTransition,
      inputAcceptTransition, inferIndexFaultTransition,
      inferRelevanceFaultTransition, inferParentFaultTransition,
      inferRuleFaultTransition, inferAcceptTransition,
      dropFaultTransition, dropAcceptTransition, duplicateRootTransition,
      rootFaultTransition, rootAcceptTransition, finishTrailingTransition,
      finishMissingRootTransition, finishRelevanceFaultTransition,
      finishRootFaultTransition,
      finishVerifiedTransition,
      LanguageDef.validatePatternConstructors,
      LanguageDef.validateRulePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, LanguageDef.premisePatterns,
      LanguageDef.premiseFvarNames,
      LanguageDef.premiseProducedFvarNames,
      LanguageDef.premiseForAllParams, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.typeNames, TypeDecl.plain,
      TypeExpr.baseNames]

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
  all_goals try decide
  exact rewrites_validate

def validated : ValidatedLanguageDef where
  language := language
  valid := language_validate

theorem transition_count : transitions.length = 20 := by decide

theorem wire_isSome :
    (CanonicalWire.renderLanguage? language).isSome := by
  decide +kernel

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

theorem wire_nonempty : wire != "" := by
  decide +kernel

def indexZero : Pattern := a "dcm:index" [a (toString (0 : Nat))]
def nodesNil : Pattern := a "dcm:nodes-nil"
def serviceStateInitial : Pattern := a "dcm:service-state-initial"
def missingFinishStart : Pattern :=
  run instructionsNil nodesNil indexZero rootNone serviceStateInitial
def missingFinishDone : Pattern :=
  halted (outcomeFault (a "dcm:fault-missing-finish")) nodesNil

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem missingFinishStart_has_type :
    CarrierWellSorted.checkHasType language
      WellSorted.FreeTypeContext.empty [] missingFinishStart
      (.base "Config") = true := by
  apply (CarrierWellSorted.checkHasType_eq_true_iff ?_).2
  · have instructionsTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          instructionsNil (.base "Instructions") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dcm:instructions-nil" "Instructions" [])
      · simp [language, terms]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .nil
    have nodesTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          nodesNil (.base "Nodes") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dcm:nodes-nil" "Nodes" [])
      · simp [language, terms]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .nil
    have integerTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          (a (toString (0 : Nat))) (.base "Integer") := by
      apply CarrierWellSorted.HasType.builtinAtom
      let declaration : TypeDecl :=
        { name := "Integer", carrier := .builtinInt }
      refine ⟨declaration, ?_, rfl, ?_⟩
      · change List.Mem declaration (declaration :: _)
        exact .head _
      · simp [declaration, CarrierWellSorted.carrierAcceptsAtom,
          Nat.toInt?_repr]
    have indexTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          indexZero (.base "Index") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dcm:index" "Index" [("value", "Integer")])
      · simp [language, terms]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .cons trivial rfl integerTyped .nil
    have rootTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          rootNone (.base "RootState") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dcm:root-none" "RootState" [])
      · simp [language, terms]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .nil
    have serviceStateTyped :
        CarrierWellSorted.HasType language WellSorted.FreeTypeContext.empty []
          serviceStateInitial (.base "ServiceState") := by
      apply CarrierWellSorted.HasType.constructor
        (rule := ctor "dcm:service-state-initial" "ServiceState" [])
      · simp [language, terms]
      · simp [WellSorted.UsesBareCollection, ctor]
      · exact .nil
    apply CarrierWellSorted.HasType.constructor
      (rule := ctor "dcm:run" "Config" [
        ("instructions", "Instructions"), ("nodes", "Nodes"),
        ("nextId", "Index"), ("root", "RootState"),
        ("serviceState", "ServiceState")] (some .rewrite))
    · simp [language, terms]
    · simp [WellSorted.UsesBareCollection, ctor]
    · exact .cons trivial rfl instructionsTyped
        (.cons trivial rfl nodesTyped
          (.cons trivial rfl indexTyped
            (.cons trivial rfl rootTyped
              (.cons trivial rfl serviceStateTyped .nil))))
  · rfl

#print axioms language_validate
#print axioms missingFinishStart_has_type

end Mettapedia.GSLT.LanguageDef.DerivationCheckMachineLanguageDef
