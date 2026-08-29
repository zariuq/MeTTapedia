import Mettapedia.GSLT.LanguageDef.DerivationCheckMachine

/-!
# Calculus-neutral named derivations

This module compiles a chronological named derivation into the dense
instruction stream consumed by `DerivationCheckMachine`.  Compilation is
purely structural: it resolves names, rejects duplicate or forward
references, assigns dense identifiers, and constructs root-relevance
witnesses.  It does not inspect rule names, infer missing evidence, or decide
any calculus judgment.  Those operations remain the responsibility of the
service catalog during the single machine pass.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationCheckMachineNamed

open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine

variable {Formula Rule Evidence Provenance Obligation : Type}

structure NamedInput (Formula Provenance : Type) where
  name : String
  formula : Formula
  provenance : Provenance

structure NamedInference (Formula Rule Evidence : Type) where
  name : String
  rule : Rule
  parents : List String
  evidence : Evidence
  conclusion : Formula

structure NamedDerivation
    (Formula Rule Evidence Provenance Obligation : Type) where
  inputs : List (NamedInput Formula Provenance)
  nodes : List (NamedInference Formula Rule Evidence)
  root : String
  obligation : Obligation

abbrev Program (Formula Rule Evidence Provenance Obligation : Type) :=
  List (Instruction Formula Rule Evidence Provenance Obligation)

structure NameEntry (Formula : Type) where
  name : String
  id : Nat
  formula : Formula

def lookupEntry? : List (NameEntry Formula) -> String -> Option (NameEntry Formula)
  | [], _ => none
  | entry :: entries, requested =>
      if entry.name = requested then some entry
      else lookupEntry? entries requested

def lookupName? (entries : List (NameEntry Formula)) (requested : String) :
    Option Nat :=
  (lookupEntry? entries requested).map NameEntry.id

def resolveParents? (entries : List (NameEntry Formula)) :
    List String -> Option (List (NameEntry Formula))
  | [] => some []
  | name :: names => do
      let entry <- lookupEntry? entries name
      let rest <- resolveParents? entries names
      some (entry :: rest)

structure DenseInput (Formula Provenance : Type) where
  id : Nat
  formula : Formula
  provenance : Provenance

structure DenseNode (Formula Rule Evidence : Type) where
  id : Nat
  rule : Rule
  parents : List Nat
  evidence : Evidence
  conclusion : Formula

structure BuildState
    (Formula Rule Evidence Provenance : Type) where
  entries : List (NameEntry Formula)
  nextId : Nat
  inputsRev : List (DenseInput Formula Provenance)
  nodesRev : List (DenseNode Formula Rule Evidence)
  derivedNamesRev : List String
  usedParentsRev : List String

def compileInputs :
    List (NamedInput Formula Provenance) ->
      BuildState Formula Rule Evidence Provenance ->
      Option (BuildState Formula Rule Evidence Provenance)
  | [], state => some state
  | input :: inputs, state => do
      if (lookupName? state.entries input.name).isSome then none else
      let id := state.nextId
      compileInputs inputs {
        entries := {
          name := input.name
          id := id
          formula := input.formula
        } :: state.entries
        nextId := id + 1
        inputsRev := {
          id := id
          formula := input.formula
          provenance := input.provenance
        } :: state.inputsRev
        nodesRev := state.nodesRev
        derivedNamesRev := state.derivedNamesRev
        usedParentsRev := state.usedParentsRev
      }

def compileNodes :
    List (NamedInference Formula Rule Evidence) ->
      BuildState Formula Rule Evidence Provenance ->
      Option (BuildState Formula Rule Evidence Provenance)
  | [], state => some state
  | node :: nodes, state => do
      if (lookupName? state.entries node.name).isSome then none else
      let parents <- resolveParents? state.entries node.parents
      let id := state.nextId
      compileNodes nodes {
        entries := {
          name := node.name
          id := id
          formula := node.conclusion
        } :: state.entries
        nextId := id + 1
        inputsRev := state.inputsRev
        nodesRev := {
          id := id
          rule := node.rule
          parents := parents.map NameEntry.id
          evidence := node.evidence
          conclusion := node.conclusion
        } :: state.nodesRev
        derivedNamesRev := node.name :: state.derivedNamesRev
        usedParentsRev := node.parents.reverse ++ state.usedParentsRev
      }

/-- For a finite chronological graph, requiring every non-root derived name
to occur as a later parent excludes disconnected derived components. -/
def allDerivedRelevant (root : String)
    (state : BuildState Formula Rule Evidence Provenance) : Bool :=
  state.derivedNamesRev.all fun name =>
    name == root || state.usedParentsRev.contains name

structure DenseDerivation
    (Formula Rule Evidence Provenance Obligation : Type) where
  inputs : List (DenseInput Formula Provenance)
  nodes : List (DenseNode Formula Rule Evidence)
  rootId : Nat
  obligation : Obligation

structure RelevanceEntry where
  id : Nat
  witness : RelevanceWitness
deriving DecidableEq, Repr

def lookupRelevance? : List RelevanceEntry -> Nat -> Option RelevanceWitness
  | [], _ => none
  | entry :: entries, id =>
      if entry.id = id then some entry.witness
      else lookupRelevance? entries id

def insertRelevanceIfAbsent (entry : RelevanceEntry) :
    List RelevanceEntry -> List RelevanceEntry
  | entries =>
      if (lookupRelevance? entries entry.id).isSome then entries
      else entry :: entries

def markParents (child : DenseNode Formula Rule Evidence) (distance : Nat) :
    List Nat -> List RelevanceEntry -> List RelevanceEntry
  | [], entries => entries
  | parent :: parents, entries =>
      markParents child distance parents
        (insertRelevanceIfAbsent {
          id := parent
          witness := { distance := distance + 1, towardRoot := some child.id }
        } entries)

def propagateRelevance :
    List (DenseNode Formula Rule Evidence) ->
      List RelevanceEntry -> List RelevanceEntry
  | [], entries => entries
  | child :: children, entries =>
      let next := match lookupRelevance? entries child.id with
        | none => entries
        | some witness => markParents child witness.distance child.parents entries
      propagateRelevance children next

def buildRelevance
    (derivation : DenseDerivation Formula Rule Evidence Provenance Obligation) :
    List RelevanceEntry :=
  propagateRelevance derivation.nodes.reverse
    [{ id := derivation.rootId,
       witness := { distance := 0, towardRoot := none } }]

def compileDenseInputs (relevance : List RelevanceEntry) :
    List (DenseInput Formula Provenance) ->
      Option (Program Formula Rule Evidence Provenance Obligation)
  | [] => some []
  | input :: inputs => do
      let witness <- lookupRelevance? relevance input.id
      let rest <- compileDenseInputs relevance inputs
      some (.input input.id input.formula input.provenance witness :: rest)

def compileDenseNodes (relevance : List RelevanceEntry) :
    List (DenseNode Formula Rule Evidence) ->
      Option (Program Formula Rule Evidence Provenance Obligation)
  | [] => some []
  | node :: nodes => do
      let witness <- lookupRelevance? relevance node.id
      let rest <- compileDenseNodes relevance nodes
      some (.infer node.id node.rule node.parents node.evidence
        node.conclusion witness :: rest)

def compileDense?
    (derivation : DenseDerivation Formula Rule Evidence Provenance Obligation) :
    Option (Program Formula Rule Evidence Provenance Obligation) := do
  let relevance := buildRelevance derivation
  let inputs <- compileDenseInputs relevance derivation.inputs
  let nodes <- compileDenseNodes relevance derivation.nodes
  some (inputs ++ nodes ++ [.root derivation.rootId derivation.obligation,
    .finish])

/-- Compile names and graph shape only.  In particular, this function contains
no call to a calculus relation, evidence synthesizer, or proof checker. -/
def compile?
    (derivation : NamedDerivation Formula Rule Evidence Provenance Obligation) :
    Option (Program Formula Rule Evidence Provenance Obligation) := do
  let initial : BuildState Formula Rule Evidence Provenance := {
    entries := []
    nextId := 0
    inputsRev := []
    nodesRev := []
    derivedNamesRev := []
    usedParentsRev := []
  }
  let withInputs <- compileInputs derivation.inputs initial
  let final <- compileNodes derivation.nodes withInputs
  if !allDerivedRelevant derivation.root final then none else
  let rootId <- lookupName? final.entries derivation.root
  compileDense? {
    inputs := final.inputsRev.reverse
    nodes := final.nodesRev.reverse
    rootId := rootId
    obligation := derivation.obligation
  }

namespace Canary

def rootNode : NamedInference Nat Nat Nat := {
  name := "root"
  rule := 7
  parents := ["left", "right"]
  evidence := 11
  conclusion := 5
}

def named : NamedDerivation Nat Nat Nat Nat Nat := {
  inputs := [
    { name := "left", formula := 2, provenance := 2 },
    { name := "right", formula := 3, provenance := 3 }
  ]
  nodes := [rootNode]
  root := "root"
  obligation := 5
}

theorem compilation_succeeds : (compile? named).isSome = true := by
  decide +kernel

def services : Services Nat Nat Nat Nat Nat Unit where
  initial := ()
  input := fun state provenance formula =>
    if formula = provenance then some state else none
  infer := fun state rule parents evidence conclusion =>
    if rule = 7 && parents = [2, 3] && evidence = 11 && conclusion = 5 then
      some state
    else none
  root := fun _ formula obligation => formula == obligation

theorem compiled_program_verifies :
    (match compile? named with
    | none => false
    | some program =>
        match execute services program with
        | .halted (.verified root) => root.obligation == 5
        | _ => false) = true := by
  decide +kernel

def forwardParent : NamedDerivation Nat Nat Nat Nat Nat := {
  named with
  nodes := [{ rootNode with parents := ["later", "right"] },
    { name := "later", rule := 7, parents := ["left", "right"],
      evidence := 11, conclusion := 5 }]
}

theorem forward_parent_rejected : compile? forwardParent = none := by
  decide +kernel

def duplicateName : NamedDerivation Nat Nat Nat Nat Nat := {
  named with nodes := [{ rootNode with name := "left" }]
}

theorem duplicate_name_rejected : compile? duplicateName = none := by
  decide +kernel

def disconnectedInput : NamedDerivation Nat Nat Nat Nat Nat := {
  named with inputs := named.inputs ++
    [{ name := "unused", formula := 13, provenance := 13 }]
}

theorem disconnected_input_rejected : compile? disconnectedInput = none := by
  decide +kernel

end Canary

#print axioms Canary.compilation_succeeds
#print axioms Canary.compiled_program_verifies
#print axioms Canary.forward_parent_rejected
#print axioms Canary.duplicate_name_rejected
#print axioms Canary.disconnected_input_rejected

end Mettapedia.GSLT.LanguageDef.DerivationCheckMachineNamed
