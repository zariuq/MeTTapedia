import Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission

/-!
# Calculus-neutral programs from admitted official TSTP derivations

This module compiles one explicitly selected root of an admitted official
TSTP derivation into the generic `DerivationCheckMachine`.  The compiler owns
only graph structure: root selection, ancestor closure, dense relocation,
parent order and multiplicity, and forward-checkable relevance witnesses.

Formula decoding, input provenance, inference rules, evidence, and root
meaning are supplied by a target projection.  Their semantics are supplied
separately by `DerivationCheckMachine.SoundServices`; this module therefore
contains no resolution rule, proof search, or TPTP rule-name dispatch.

The list implementation is the theorem-level reference compiler.  A native
artifact may replace its association lists by direct finite arenas, but must
refine the program produced here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram

open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}

abbrev Program := List
  (Instruction Formula Rule Evidence Provenance Obligation)

/-! ## Structural dependency projection -/

structure DependencyNode where
  id : Nat
  parents : List Nat
  deriving DecidableEq, Repr

def dependencies (compiled : CompiledDerivation) : List DependencyNode :=
  compiled.nodes.map fun node =>
    { id := node.id, parents := node.parentIds }

structure RelevanceEntry where
  id : Nat
  witness : RelevanceWitness
  deriving DecidableEq, Repr

def lookupRelevance? : List RelevanceEntry → Nat → Option RelevanceWitness
  | [], _ => none
  | entry :: entries, id =>
      if entry.id = id then some entry.witness
      else lookupRelevance? entries id

def insertRelevanceIfAbsent (entry : RelevanceEntry) :
    List RelevanceEntry → List RelevanceEntry
  | entries =>
      if (lookupRelevance? entries entry.id).isSome then entries
      else entry :: entries

/-- Mark every listed parent, preserving repeated parent positions in the
source node while storing one occurrence-level relevance witness per ID. -/
def markParents (child : DependencyNode) (distance : Nat) :
    List Nat → List RelevanceEntry → List RelevanceEntry
  | [], entries => entries
  | parent :: parents, entries =>
      markParents child distance parents
        (insertRelevanceIfAbsent {
          id := parent
          witness := { distance := distance + 1, towardRoot := some child.id }
        } entries)

def propagateRelevance :
    List DependencyNode → List RelevanceEntry → List RelevanceEntry
  | [], entries => entries
  | child :: children, entries =>
      let next := match lookupRelevance? entries child.id with
        | none => entries
        | some witness => markParents child witness.distance child.parents entries
      propagateRelevance children next

/-- Compute one concrete path-to-root witness for every ancestor of the
selected root.  The reverse scan is valid because structural admission has
already proved that every parent ID is smaller than its child ID. -/
def buildRelevance (nodes : List DependencyNode) (rootId : Nat) :
    List RelevanceEntry :=
  propagateRelevance nodes.reverse
    [{ id := rootId, witness := { distance := 0, towardRoot := none } }]

/-! ## Dense relocation of the selected closure -/

structure Relocation where
  oldId : Nat
  newId : Nat
  deriving DecidableEq, Repr

def lookupRelocation? : List Relocation → Nat → Option Nat
  | [], _ => none
  | entry :: entries, id =>
      if entry.oldId = id then some entry.newId
      else lookupRelocation? entries id

structure RelocationState where
  entries : List Relocation
  nextId : Nat
  deriving DecidableEq, Repr

def collectRelocations (relevance : List RelevanceEntry) :
    List DependencyNode → RelocationState → RelocationState
  | [], state => state
  | node :: nodes, state =>
      match lookupRelevance? relevance node.id with
      | none => collectRelocations relevance nodes state
      | some _ =>
          collectRelocations relevance nodes {
            entries := { oldId := node.id, newId := state.nextId } :: state.entries
            nextId := state.nextId + 1
          }

def relocateIds? (relocations : List Relocation) :
    List Nat → Option (List Nat)
  | [] => some []
  | id :: ids => do
      let relocated <- lookupRelocation? relocations id
      let rest <- relocateIds? relocations ids
      some (relocated :: rest)

def relocateWitness? (relocations : List Relocation)
    (witness : RelevanceWitness) : Option RelevanceWitness := do
  let towardRoot <- match witness.towardRoot with
    | none => some none
    | some child => (lookupRelocation? relocations child).map some
  some { distance := witness.distance, towardRoot }

/-! ## Calculus-specific projection boundary -/

inductive StructuralMode where
  | input
  | infer
  deriving DecidableEq, Repr

/-- External and annotation-free formulae are leaves.  Every local named,
inference, introduced, or alternative source is a derivation step.  An
unknown source remains a leaf-shaped record so that a provenance service can
reject or classify it as unsupported without inventing a rule. -/
def structuralMode : NodeOrigin → StructuralMode
  | .unannotated => .input
  | .sourced _ (.external _) _ => .input
  | .sourced _ .unknown _ => .input
  | .sourced _ (.named _) _ => .infer
  | .sourced _ (.inference _ _ _) _ => .infer
  | .sourced _ (.introduced _ _ _) _ => .infer
  | .sourced _ (.alternatives _) _ => .infer

/-- Projection failure means that this separately validated calculus does not
claim the node.  Semantic falsity is not a projection failure: it is decided
later by the calculus service during the single checking pass. -/
inductive ProjectionFailure where
  | unsupported
  | malformed
  deriving DecidableEq, Repr

/-- A separately validated calculus supplies only the semantic payloads.
The generic compiler supplies IDs, exact parent positions, and relevance. -/
structure TargetProjection
    (Formula Rule Evidence Provenance Obligation : Type) where
  input? : AdmittedNode → Except ProjectionFailure (Formula × Provenance)
  infer? : AdmittedNode → Except ProjectionFailure (Rule × Evidence × Formula)
  root? : AdmittedNode → Except ProjectionFailure Obligation

inductive CompileFailure where
  | missingRoot (name : String)
  | inconsistentGraph
  | projection (failure : ProjectionFailure)
  | irrelevantNodes (names : List String)
  deriving DecidableEq, Repr

def requireSome {α : Type} (failure : CompileFailure) :
    Option α → Except CompileFailure α
  | none => .error failure
  | some value => .ok value

def lookupNode? : List AdmittedNode → Nat → Option AdmittedNode
  | [], _ => none
  | node :: nodes, id =>
      if node.id = id then some node else lookupNode? nodes id

def compileSelectedNodes?
    (projection : TargetProjection Formula Rule Evidence Provenance Obligation)
    (relevance : List RelevanceEntry) (relocations : List Relocation) :
    List AdmittedNode → Except CompileFailure
      (List (Instruction Formula Rule Evidence Provenance Obligation))
  | [] => .ok []
  | node :: nodes =>
      match lookupRelevance? relevance node.id with
      | none => compileSelectedNodes? projection relevance relocations nodes
      | some oldWitness => do
          let id <- requireSome .inconsistentGraph
            (lookupRelocation? relocations node.id)
          let witness <- requireSome .inconsistentGraph
            (relocateWitness? relocations oldWitness)
          let rest <- compileSelectedNodes? projection relevance relocations nodes
          match structuralMode node.source.origin with
          | .input =>
              match projection.input? node with
              | .error failure => .error (.projection failure)
              | .ok (formula, provenance) =>
                  .ok (.input id formula provenance witness :: rest)
          | .infer =>
              match relocateIds? relocations node.parentIds with
              | none => .error .inconsistentGraph
              | some parents =>
                  match projection.infer? node with
                  | .error failure => .error (.projection failure)
                  | .ok (rule, evidence, conclusion) =>
                      .ok (.infer id rule parents evidence conclusion witness :: rest)

structure Artifact
    (Formula Rule Evidence Provenance Obligation : Type) where
  rootName : String
  rootOldId : Nat
  rootId : Nat
  selectedNames : List String
  omittedNames : List String
  program : List (Instruction Formula Rule Evidence Provenance Obligation)

def partitionNames (relevance : List RelevanceEntry) :
    List AdmittedNode → List String × List String
  | [] => ([], [])
  | node :: nodes =>
      let (selected, omitted) := partitionNames relevance nodes
      if (lookupRelevance? relevance node.id).isSome then
        (node.source.name :: selected, omitted)
      else
        (selected, node.source.name :: omitted)

def compileSelected?
    (projection : TargetProjection Formula Rule Evidence Provenance Obligation)
    (compiled : CompiledDerivation) (rootName : String) :
    Except CompileFailure
      (Artifact Formula Rule Evidence Provenance Obligation) := do
  let rootEntry <- requireSome (.missingRoot rootName)
    (lookupEntry? compiled.names rootName)
  let rootNode <- requireSome .inconsistentGraph
    (lookupNode? compiled.nodes rootEntry.id)
  let dependencyGraph := dependencies compiled
  let relevance := buildRelevance dependencyGraph rootEntry.id
  let relocationState := collectRelocations relevance dependencyGraph
    { entries := [], nextId := 0 }
  let rootId <- requireSome .inconsistentGraph
    (lookupRelocation? relocationState.entries rootEntry.id)
  let instructions <- compileSelectedNodes? projection relevance
    relocationState.entries compiled.nodes
  let obligation <- match projection.root? rootNode with
    | .error failure => .error (.projection failure)
    | .ok obligation => .ok obligation
  let (selectedNames, omittedNames) := partitionNames relevance compiled.nodes
  .ok {
    rootName
    rootOldId := rootEntry.id
    rootId
    selectedNames
    omittedNames
    program := instructions ++ [.root rootId obligation, .finish]
  }

/-- A selected-root artifact verifies only the named root's dependency
closure.  Whole-derivation verification additionally rejects every omitted
node instead of silently treating it as checked. -/
def compileWhole?
    (projection : TargetProjection Formula Rule Evidence Provenance Obligation)
    (compiled : CompiledDerivation) (rootName : String) :
    Except CompileFailure
      (Artifact Formula Rule Evidence Provenance Obligation) := do
  let artifact <- compileSelected? projection compiled rootName
  if artifact.omittedNames.isEmpty then .ok artifact
  else .error (.irrelevantNodes artifact.omittedNames)

def compileAdmittedSelected?
    (projection : TargetProjection Formula Rule Evidence Provenance Obligation)
    (admitted : AdmittedDerivation) (rootName : String) :=
  compileSelected? projection admitted.compiled rootName

def compileAdmittedWhole?
    (projection : TargetProjection Formula Rule Evidence Provenance Obligation)
    (admitted : AdmittedDerivation) (rootName : String) :=
  compileWhole? projection admitted.compiled rootName

theorem accepted_artifact_sound
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (sound : SoundServices services)
    (artifact : Artifact Formula Rule Evidence Provenance Obligation)
    (root : RootClaim Formula Obligation)
    (accepted : execute services artifact.program = .halted (.verified root)) :
    sound.Objective root.obligation :=
  execute_verified_sound sound artifact.program root accepted

/-! ## Structural controls -/

namespace Canary

def branchingGraph : List DependencyNode := [
  { id := 0, parents := [] },
  { id := 1, parents := [] },
  { id := 2, parents := [0] },
  { id := 3, parents := [1] },
  { id := 4, parents := [2] }
]

theorem selected_root_closure_exact :
    buildRelevance branchingGraph 4 = [
      { id := 0, witness := { distance := 2, towardRoot := some 2 } },
      { id := 2, witness := { distance := 1, towardRoot := some 4 } },
      { id := 4, witness := { distance := 0, towardRoot := none } }
    ] := by
  rfl

def repeatedParentGraph : List DependencyNode := [
  { id := 0, parents := [] },
  { id := 1, parents := [0, 0] }
]

def repeatedParentRelevance : List RelevanceEntry :=
  buildRelevance repeatedParentGraph 1

def repeatedParentRelocations : RelocationState :=
  collectRelocations repeatedParentRelevance repeatedParentGraph
    { entries := [], nextId := 0 }

theorem repeated_parent_positions_relocate_exactly :
    relocateIds? repeatedParentRelocations.entries [0, 0] = some [0, 0] := by
  rfl

theorem missing_root_has_no_relocation :
    lookupRelocation?
      (collectRelocations (buildRelevance branchingGraph 99) branchingGraph
        { entries := [], nextId := 0 }).entries 99 = none := by
  rfl

end Canary

#print axioms accepted_artifact_sound
#print axioms Canary.selected_root_closure_exact
#print axioms Canary.repeated_parent_positions_relocate_exactly
#print axioms Canary.missing_root_has_no_relocation

end Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram
