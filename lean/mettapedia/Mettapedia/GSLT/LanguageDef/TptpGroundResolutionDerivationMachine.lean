import Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionNamedDAG

/-!
# Ground TSTP resolution specialized to the derivation-check machine

This module is the first calculus specialization of the reusable
`DerivationCheckMachine`.  It converts the already admitted named ground-CNF
derivation into a compact, chronological instruction stream.  Source clause
identities are reindexed densely, parent references are relocated, and a
forward-checkable relevance witness is generated for every retained node.

The machine services contain no proof search.  Initial admission is tied to
the parsed problem, local inference delegates to the supplied authored
ground-resolution authority, and root admission is exact formula equality.
The generic machine soundness theorem then turns any `verified` outcome into
semantic consequence of the parsed problem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.GSLT.LanguageDef.TptpGroundResolutionDerivationMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionNamedDAG
open Mettapedia.Languages.TPTP
open Mettapedia.Languages.TPTP.NIKAuthority
open Mettapedia.Languages.TPTP.StatusSemantics
open Mettapedia.Languages.TPTP.GroundCNFAuthority

abbrev Formula := SemanticFormula
abbrev Rule := RuleKey
abbrev Evidence := ResolutionEvidence
abbrev Provenance := ParsedClause Pattern
abbrev Obligation := SemanticFormula
abbrev Program := List
  (Instruction Formula Rule Evidence Provenance Obligation)

/-! ## Semantic service specialization -/

def RelativeTheorem (problem : ParsedProblem) (formula : Formula) : Prop :=
  ∀ valuation,
    (Formula.semantics (Atom := Pattern)).SatisfiesAll valuation
      problem.formulas →
    (Formula.semantics (Atom := Pattern)).satisfies valuation formula

def services (problem : ParsedProblem) :
    Services Formula Rule Evidence Provenance Obligation Unit where
  initial := ()
  input := fun state provenance formula =>
    if decide (provenance ∈ problem.clauses ∧
        formula = .clause provenance.literals) then some state else none
  infer := fun state rule parents evidence conclusion =>
    if TptpGroundResolutionProblemAuthority.evidenceCheck rule
        { parents := parents, inferred := conclusion } evidence then
      some state
    else none
  root := fun _ formula obligation => decide (formula = obligation)

def services_sound (problem : ParsedProblem) :
    SoundServices (services problem) where
  Valid := RelativeTheorem problem
  Objective := RelativeTheorem problem
  StateValid := fun _ => True
  initial_sound := trivial
  input_sound := by
    intro state provenance formula nextState accepted _stateValid
    simp [services] at accepted
    constructor
    · intro valuation problemSatisfied
      rw [accepted.2]
      apply problemSatisfied
      exact List.mem_map.mpr ⟨provenance, accepted.1, rfl⟩
    · trivial
  infer_sound := by
    intro state rule parents evidence conclusion nextState accepted
      _stateValid parentsValid
    simp [services] at accepted
    constructor
    · have localMeaning :=
        TptpGroundResolutionProblemAuthority.evidenceCheck_sound rule
        ({ parents := parents, inferred := conclusion } : RelationClaim Formula)
        evidence accepted
      simp only [TptpGroundResolutionProblemAuthority.evidenceCheck,
        Bool.and_eq_true] at accepted
      have ruleShape : rule =
          TptpGroundResolutionProblemAuthority.resolutionKey :=
        of_decide_eq_true accepted.1
      subst rule
      have localTheorem :
          (Formula.semantics (Atom := Pattern)).TheoremRelation
            { parents := parents, inferred := conclusion } := by
        simpa [TptpGroundResolutionProblemAuthority.resolutionKey,
          ClassicalModelSemantics.commonStatusMeaning]
          using localMeaning
      intro valuation problemSatisfied
      apply localTheorem valuation
      intro parent membership
      exact parentsValid parent membership valuation problemSatisfied
    · trivial
  root_sound := by
    intro _state formula obligation accepted _stateValid valid
    have equal : formula = obligation := of_decide_eq_true accepted
    simpa [equal] using valid

/-! ## Dense relocation -/

structure Relocation where
  oldId : Nat
  newId : Nat
deriving DecidableEq, Repr

def lookupRelocation? : List Relocation → Nat → Option Nat
  | [], _ => none
  | entry :: entries, id =>
      if entry.oldId = id then some entry.newId
      else lookupRelocation? entries id

def relocateParents? (relocations : List Relocation) :
    List Nat → Option (List Nat)
  | [] => some []
  | id :: ids => do
      let relocated ← lookupRelocation? relocations id
      let rest ← relocateParents? relocations ids
      some (relocated :: rest)

structure DenseInput where
  id : Nat
  source : Provenance
deriving DecidableEq, Repr

structure DenseNode where
  id : Nat
  rule : Rule
  parents : List Nat
  evidence : Evidence
  conclusion : Formula

structure DenseState where
  relocations : List Relocation
  nextId : Nat
  inputsRev : List DenseInput
  nodesRev : List DenseNode

def reindexInputs : List Provenance → DenseState → Option DenseState
  | [], state => some state
  | source :: sources, state => do
      if (lookupRelocation? state.relocations source.id).isSome then none else
      let id := state.nextId
      reindexInputs sources {
        relocations := { oldId := source.id, newId := id } :: state.relocations
        nextId := id + 1
        inputsRev := { id := id, source := source } :: state.inputsRev
        nodesRev := state.nodesRev
      }

def reindexNodes :
    List (NIKAuthority.Node Formula) →
    List ruleFamily.PackedCertificate → DenseState → Option DenseState
  | [], [], state => some state
  | node :: nodes, certificate :: certificates, state => do
      if (lookupRelocation? state.relocations node.id).isSome then none else
      if certificate.1 != node.key then none else
      let parents ← relocateParents? state.relocations node.parentIds
      let id := state.nextId
      reindexNodes nodes certificates {
        relocations := { oldId := node.id, newId := id } :: state.relocations
        nextId := id + 1
        inputsRev := state.inputsRev
        nodesRev := {
          id := id
          rule := node.key
          parents := parents
          evidence := certificate.2
          conclusion := node.inferred
        } :: state.nodesRev
      }
  | _, _, _ => none

structure DenseDerivation where
  inputs : List DenseInput
  nodes : List DenseNode
  rootId : Nat
  expected : Formula

def reindexCompiled? (compiled : CompiledSubmission) :
    Option DenseDerivation := do
  let initial : DenseState := {
    relocations := []
    nextId := 0
    inputsRev := []
    nodesRev := []
  }
  let withInputs ← reindexInputs compiled.submission.problem.clauses initial
  let final ← reindexNodes compiled.submission.derivation.nodes
    compiled.evidence.2.1 withInputs
  let rootId ← lookupRelocation? final.relocations
    compiled.submission.derivation.rootId
  some {
    inputs := final.inputsRev.reverse
    nodes := final.nodesRev.reverse
    rootId := rootId
    expected := compiled.submission.derivation.expected
  }

/-! ## Forward-checkable root relevance -/

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

def markParents (child : DenseNode) (distance : Nat) :
    List Nat → List RelevanceEntry → List RelevanceEntry
  | [], entries => entries
  | parent :: parents, entries =>
      markParents child distance parents
        (insertRelevanceIfAbsent {
          id := parent
          witness := { distance := distance + 1, towardRoot := some child.id }
        } entries)

def propagateRelevance :
    List DenseNode → List RelevanceEntry → List RelevanceEntry
  | [], entries => entries
  | child :: children, entries =>
      let next := match lookupRelevance? entries child.id with
        | none => entries
        | some witness => markParents child witness.distance child.parents entries
      propagateRelevance children next

def buildRelevance (derivation : DenseDerivation) : List RelevanceEntry :=
  propagateRelevance derivation.nodes.reverse
    [{ id := derivation.rootId,
       witness := { distance := 0, towardRoot := none } }]

def compileInputs? (relevance : List RelevanceEntry) :
    List DenseInput → Option Program
  | [] => some []
  | input :: inputs => do
      let witness ← lookupRelevance? relevance input.id
      let rest ← compileInputs? relevance inputs
      some (.input input.id (.clause input.source.literals) input.source
        witness :: rest)

def compileNodes? (relevance : List RelevanceEntry) :
    List DenseNode → Option Program
  | [] => some []
  | node :: nodes => do
      let witness ← lookupRelevance? relevance node.id
      let rest ← compileNodes? relevance nodes
      some (.infer node.id node.rule node.parents node.evidence
        node.conclusion witness :: rest)

def compileProgram? (derivation : DenseDerivation) : Option Program := do
  let relevance := buildRelevance derivation
  let inputs ← compileInputs? relevance derivation.inputs
  let nodes ← compileNodes? relevance derivation.nodes
  some (inputs ++ nodes ++ [.root derivation.rootId derivation.expected,
    .finish])

def compileNamed? (submission : NamedSubmission) : Option Program := do
  let compiled ← TptpGroundResolutionNamedDAG.compile? submission
  let dense ← reindexCompiled? compiled
  compileProgram? dense

/-! ## End-to-end semantic theorem and controls -/

theorem verified_program_sound
    (problem : ParsedProblem) (program : Program)
    (root : RootClaim Formula Obligation)
    (accepted : execute (services problem) program =
      .halted (.verified root)) :
    RelativeTheorem problem root.obligation :=
  execute_verified_sound (services_sound problem) program root accepted

namespace Canary

def program : Program :=
  (compileNamed? TptpGroundResolutionNamedDAG.Canary.valid).getD []

theorem compilation_succeeds :
    (compileNamed? TptpGroundResolutionNamedDAG.Canary.valid).isSome = true := by
  decide +kernel

def acceptsEmpty :
    Config Formula Rule Evidence Provenance Obligation Unit → Bool
  | .halted (.verified root) => decide (root.obligation = .clause [])
  | _ => false

theorem program_verified :
    ∃ root,
      execute (services
        TptpGroundResolutionProblemAuthority.Canary.parsedProblem) program =
          .halted (.verified root) ∧
      root.obligation = .clause [] := by
  have accepted :
      acceptsEmpty
        (execute (services
          TptpGroundResolutionProblemAuthority.Canary.parsedProblem)
          program) = true := by
    decide +kernel
  cases result :
      execute (services
        TptpGroundResolutionProblemAuthority.Canary.parsedProblem) program with
  | running state => simp [acceptsEmpty, result] at accepted
  | halted outcome =>
      cases outcome with
      | fault failure => simp [acceptsEmpty, result] at accepted
      | verified root =>
          refine ⟨root, rfl, ?_⟩
          exact of_decide_eq_true (by
            simpa [acceptsEmpty, result] using accepted)

theorem refutation_sound :
    RelativeTheorem
      TptpGroundResolutionProblemAuthority.Canary.parsedProblem (.clause []) :=
  by
    obtain ⟨root, accepted, obligation⟩ := program_verified
    have sound := verified_program_sound
      TptpGroundResolutionProblemAuthority.Canary.parsedProblem program
      root accepted
    simpa [obligation] using sound

def disconnected : NamedSubmission := {
  TptpGroundResolutionNamedDAG.Canary.valid with
  problem := {
    TptpGroundResolutionProblemAuthority.Canary.parsedProblem with
    clauses := TptpGroundResolutionProblemAuthority.Canary.parsedProblem.clauses ++
      [{ id := 17, name := "unused", role := .axiom,
         literals := TptpGroundResolutionProblemAuthority.Canary.positiveP }]
  }
}

theorem disconnected_input_not_compiled : compileNamed? disconnected = none := by
  decide +kernel

end Canary

#print axioms verified_program_sound
#print axioms Canary.compilation_succeeds
#print axioms Canary.program_verified
#print axioms Canary.refutation_sound
#print axioms Canary.disconnected_input_not_compiled

end Mettapedia.GSLT.LanguageDef.TptpGroundResolutionDerivationMachine
