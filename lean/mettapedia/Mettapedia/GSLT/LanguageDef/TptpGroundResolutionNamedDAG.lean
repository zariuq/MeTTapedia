import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionEvidenceSynthesis

/-!
# Named chronological ground-resolution DAGs

This module is the semantic normal form between source-preserving TSTP syntax
and the generic whole-problem authority.  It retains TSTP formula names and
parent names, resolves them once from left to right, and emits the exact
numeric skeleton and dependent rule certificates consumed by the generic
chronological checker.

It is not a TSTP parser.  A concrete-syntax lowering must separately prove or
qualify that its parsed nodes produce this carrier without changing names,
formulae, sources, roles, or parent order.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpGroundResolutionNamedDAG

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.TPTP.NIKAuthority
open Mettapedia.Languages.TPTP.ProblemAuthority
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionEvidenceSynthesis

/-- How a named edge obtains the calculus evidence checked at the public
verification boundary.  Reconstruction is local: it enumerates only the
literal occurrences of the two named parent clauses. -/
inductive EvidenceSource where
  | supplied (evidence : ResolutionEvidence)
  | reconstruct

/-- One TSTP-style named inference after formula lowering.  Rule evidence is
separate from the formula graph and remains checked by the supplied calculus
authority. -/
structure NamedInference where
  name : String
  key : RuleKey
  parents : List String
  inferred : SemanticFormula
  evidence : EvidenceSource

/-- An admitted parsed problem plus the claimed chronological derivation and
selected result.  Initial formula names come only from the parsed problem;
the proof cannot authenticate its own leaves. -/
structure NamedSubmission where
  problem : ParsedProblem
  nodes : List NamedInference
  root : String
  expected : SemanticFormula

structure NameEntry where
  name : String
  id : Nat
  formula : SemanticFormula

abbrev NameTable := List NameEntry

def lookupEntry? : NameTable -> String -> Option NameEntry
  | [], _ => none
  | entry :: entries, requested =>
      if entry.name = requested then some entry
      else lookupEntry? entries requested

def lookupName? : NameTable -> String -> Option Nat
  | entries, requested => (lookupEntry? entries requested).map NameEntry.id

def resolveNames? (entries : NameTable) : List String -> Option (List NameEntry)
  | [] => some []
  | name :: names => do
      let entry <- lookupEntry? entries name
      let resolved <- resolveNames? entries names
      some (entry :: resolved)

def initialNameTable (problem : ParsedProblem) : NameTable :=
  problem.clauses.map fun clause => {
    name := clause.name
    id := clause.id
    formula := .clause clause.literals
  }

def nextFreshId (problem : ParsedProblem) : Nat :=
  problem.clauses.foldl (fun next clause => max next (clause.id + 1)) 0

structure BuildState where
  names : NameTable
  nextId : Nat
  nodesRev : List (Node SemanticFormula)
  certificatesRev : List ruleFamily.PackedCertificate
  derivedNamesRev : List String
  usedParentsRev : List String

def reconstructEvidence? (key : RuleKey) (parents : List NameEntry)
    (inferred : SemanticFormula) : Option ResolutionEvidence := do
  if key != resolutionKey then none else
  match parents, inferred with
  | [left, right], .clause result =>
      match left.formula, right.formula with
      | .clause leftClause, .clause rightClause => do
          let evidence <-
            synthesizeEvidence? leftClause rightClause result
          some evidence.1
      | _, _ => none
  | _, _ => none

def selectEvidence? (source : EvidenceSource) (key : RuleKey)
    (parents : List NameEntry) (inferred : SemanticFormula) :
    Option ResolutionEvidence :=
  match source with
  | .supplied evidence => some evidence
  | .reconstruct => reconstructEvidence? key parents inferred

def compileNode (state : BuildState) (node : NamedInference) :
    Option BuildState := do
  if (lookupName? state.names node.name).isSome then none else
    let parents <- resolveNames? state.names node.parents
    let evidence <- selectEvidence? node.evidence node.key parents node.inferred
    let parentIds := parents.map NameEntry.id
    let id := state.nextId
    let compiled : Node SemanticFormula := {
      id := id
      key := node.key
      parentIds := parentIds
      inferred := node.inferred
    }
    let certificate : ruleFamily.PackedCertificate :=
      ⟨node.key, evidence⟩
    some {
      names := ({
        name := node.name
        id := id
        formula := node.inferred
      } : NameEntry) :: state.names
      nextId := id + 1
      nodesRev := compiled :: state.nodesRev
      certificatesRev := certificate :: state.certificatesRev
      derivedNamesRev := node.name :: state.derivedNamesRev
      usedParentsRev := node.parents.reverse ++ state.usedParentsRev
    }

def compileNodes : BuildState -> List NamedInference -> Option BuildState
  | state, [] => some state
  | state, node :: nodes => do
      let next <- compileNode state node
      compileNodes next nodes

/-- Every derived node except the selected root must feed a later inference.
For a finite chronological DAG this excludes disconnected derived components:
each such component would otherwise have a non-root sink. -/
def allDerivedRelevant (root : String) (state : BuildState) : Bool :=
  state.derivedNamesRev.all fun name =>
    name == root || state.usedParentsRev.contains name

structure CompiledSubmission where
  submission : Submission
  evidence : CompositeEvidence
  nameToId : NameTable

/-- Resolve names and construct the generic problem-authority input.  Missing
local pivot evidence may be compiled into a typed derivation of the authored
calculus; `verify` below still runs the exact whole-problem checker on the
result. -/
def compile? (input : NamedSubmission) : Option CompiledSubmission := do
  let initialNames := initialNameTable input.problem
  if !(initialNames.map NameEntry.name).Nodup then none else
  if !(input.problem.initialEntries.map Entry.id).Nodup then none else
  let initial : BuildState := {
    names := initialNames
    nextId := nextFreshId input.problem
    nodesRev := []
    certificatesRev := []
    derivedNamesRev := []
    usedParentsRev := []
  }
  let final <- compileNodes initial input.nodes
  if !allDerivedRelevant input.root final then none else
  let rootId <- lookupName? final.names input.root
  let skeleton : Skeleton SemanticFormula := {
    initial := input.problem.initialEntries
    nodes := final.nodesRev.reverse
    rootId := rootId
    expected := input.expected
  }
  let submission : Submission := {
    problem := input.problem
    derivation := skeleton
  }
  let evidence : CompositeEvidence :=
    ⟨(), final.certificatesRev.reverse, ()⟩
  some { submission, evidence, nameToId := final.names }

/-- Public semantic verification boundary for the normalized named DAG.  The
compilation pass only resolves names and constructs typed local evidence; the
generic whole-problem checker remains the only Boolean authority. -/
def verify (input : NamedSubmission) : Bool :=
  match compile? input with
  | none => false
  | some compiled =>
      compositeChecker.check compiled.submission compiled.evidence

theorem verify_sound {input : NamedSubmission}
    (accepted : verify input = true) :
    exists compiled,
      compile? input = some compiled /\ Objective compiled.submission := by
  unfold verify at accepted
  cases compiledEq : compile? input with
  | none => simp [compiledEq] at accepted
  | some compiled =>
      refine ⟨compiled, rfl, ?_⟩
      apply accepted_submission_sound
      simpa [compiledEq] using accepted

/-! ## Non-vacuous chronological controls -/

namespace Canary

def first : NamedInference := {
  name := "c3"
  key := resolutionKey
  parents := ["p_or_q", "not_p"]
  inferred := .clause
    TptpGroundResolutionProblemAuthority.Canary.positiveQ
  evidence := .supplied
    TptpGroundResolutionProblemAuthority.Canary.firstResolutionEvidence
}

def second : NamedInference := {
  name := "c4"
  key := resolutionKey
  parents := ["c3", "not_q"]
  inferred := .clause []
  evidence := .supplied
    TptpGroundResolutionProblemAuthority.Canary.secondResolutionEvidence
}

def valid : NamedSubmission := {
  problem := TptpGroundResolutionProblemAuthority.Canary.parsedProblem
  nodes := [first, second]
  root := "c4"
  expected := .clause []
}

theorem two_step_refutation_accepted : verify valid = true := by
  decide +kernel

theorem two_step_refutation_sound :
    exists compiled,
      compile? valid = some compiled /\ Objective compiled.submission :=
  verify_sound two_step_refutation_accepted

def reconstructed : NamedSubmission := {
  valid with
  nodes := [
    { first with evidence := .reconstruct },
    { second with evidence := .reconstruct }
  ]
}

theorem two_step_refutation_reconstructed : verify reconstructed = true := by
  decide +kernel

def duplicateName : NamedSubmission :=
  { valid with nodes := [first, { second with name := "c3" }] }

theorem duplicate_name_rejected : verify duplicateName = false := by
  decide +kernel

def forwardParent : NamedSubmission :=
  { valid with
    nodes := [{ first with parents := ["c4", "not_p"] }, second] }

theorem forward_parent_rejected : verify forwardParent = false := by
  decide +kernel

def missingParent : NamedSubmission :=
  { valid with
    nodes := [{ first with parents := ["missing", "not_p"] }, second] }

theorem missing_parent_rejected : verify missingParent = false := by
  decide +kernel

def disconnected : NamedSubmission :=
  { valid with nodes := [first, second, { first with name := "dead" }] }

theorem disconnected_derived_node_rejected : verify disconnected = false := by
  decide +kernel

def unknownRule : NamedSubmission :=
  { valid with
    nodes := [{ first with key := { rule := "unknown", status := .thm } },
      second] }

theorem unknown_rule_rejected : verify unknownRule = false := by
  decide +kernel

def inventedFormula : SemanticFormula :=
  .clause TptpGroundResolutionProblemAuthority.Canary.positiveP

def inventedFirst : NamedInference :=
  { first with inferred := inventedFormula }

def inventedResult : NamedSubmission :=
  { valid with nodes := [inventedFirst, second] }

theorem invented_result_rejected : verify inventedResult = false := by
  decide +kernel

def inventedReconstructed : NamedSubmission :=
  { valid with
    nodes := [
      { inventedFirst with evidence := .reconstruct },
      { second with evidence := .reconstruct }
    ] }

theorem invented_result_not_reconstructed :
    verify inventedReconstructed = false := by
  decide +kernel

def noComplementReconstructed : NamedSubmission := {
  problem := valid.problem
  nodes := [{
    first with
    parents := ["not_p", "not_q"]
    inferred := .clause []
    evidence := .reconstruct
  }]
  root := "c3"
  expected := .clause []
}

theorem no_complement_not_reconstructed :
    verify noComplementReconstructed = false := by
  decide +kernel

def missingRoot : NamedSubmission := { valid with root := "absent" }

theorem missing_root_rejected : verify missingRoot = false := by
  decide +kernel

end Canary

#print axioms verify_sound
#print axioms Canary.two_step_refutation_accepted
#print axioms Canary.two_step_refutation_sound
#print axioms Canary.two_step_refutation_reconstructed
#print axioms Canary.duplicate_name_rejected
#print axioms Canary.forward_parent_rejected
#print axioms Canary.missing_parent_rejected
#print axioms Canary.disconnected_derived_node_rejected
#print axioms Canary.unknown_rule_rejected
#print axioms Canary.invented_result_rejected
#print axioms Canary.invented_result_not_reconstructed
#print axioms Canary.no_complement_not_reconstructed
#print axioms Canary.missing_root_rejected

end Mettapedia.GSLT.LanguageDef.TptpGroundResolutionNamedDAG
