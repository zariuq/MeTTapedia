import Mettapedia.GSLT.LanguageDef.DerivationWordMachineFiniteExecution

/-!
# State-stable compilation for the derivation word machine

Some derivation services carry a finite control state that remains unchanged
through a particular compiled program.  This module turns that semantic fact
into the representation-closure obligation required by the authored
derivation-word `LanguageDef`.

The hypothesis is program-local.  It does not claim that the service is
globally stateless: a different program may contain instructions which move
the service state and require a larger proof-local state arena.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineStateStableCompilation

open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineOneRecordSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineFiniteExecution

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}
variable [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState]

/-- Every successful service callback named by this program leaves the fixed
service state unchanged.  Graph faults and structural instructions need no
service-state premise. -/
def ProgramServiceStateStable
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) : Prop :=
  ∀ instruction ∈ program,
    match instruction with
    | .input _ formula provenance _ =>
        ∀ next,
          services.input fixed provenance formula = some next → next = fixed
    | .infer _ rule _ evidence conclusion _ =>
        ∀ parents next,
          services.infer fixed rule parents evidence conclusion = some next →
            next = fixed
    | _ => True

/-- The exact finite host generated from a state-stable semantic program. -/
def finiteHost
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    Host Formula Rule Evidence Provenance Obligation ServiceState where
  codecs := finiteCodecsOfProgram program
  serviceStates := ⟨[fixed]⟩
  services := services

/-- Runtime host assembled from a compiler-returned finite artifact.  This is
the public execution form: clients need not recompute or unfold the arenas
which the compiler already retained. -/
def artifactHost
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (artifact :
      FiniteProgramArtifact Formula Rule Evidence Provenance Obligation) :
    Host Formula Rule Evidence Provenance Obligation ServiceState where
  codecs := artifact.codecs
  serviceStates := ⟨[fixed]⟩
  services := services

omit [DecidableEq ServiceState] in
/-- A compiler-returned artifact host is exactly the proof-local finite host
derived from its semantic source program. -/
theorem artifactHost_eq_finiteHost
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (artifact :
      FiniteProgramArtifact Formula Rule Evidence Provenance Obligation)
    (compiled : compileFiniteProgram? program = some artifact) :
    artifactHost services fixed artifact = finiteHost services fixed program := by
  unfold compileFiniteProgram? at compiled
  dsimp only at compiled
  split at compiled
  · simp at compiled
  · cases compiled
    rfl

omit [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation] in
theorem artifactServiceState_encodes
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (artifact :
      FiniteProgramArtifact Formula Rule Evidence Provenance Obligation) :
    encodeServiceState? (artifactHost services fixed artifact) fixed =
      some (serviceStateRef 0) := by
  simp [encodeServiceState?, artifactHost, FiniteAtomCodec.encode?,
    findAtomIndex?]

/-- Canonical authored source term retained by a finite program artifact. -/
def artifactStart
    (artifact :
      FiniteProgramArtifact Formula Rule Evidence Provenance Obligation) :
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern :=
  run (recordsPattern artifact.words) nodesNil indexZero rootNone
    (serviceStateRef 0)

/-- A compiler-returned finite artifact canonically represents the initial
semantic configuration of its source program. -/
theorem artifactStart_encodes
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (artifact :
      FiniteProgramArtifact Formula Rule Evidence Provenance Obligation)
    (compiled : compileFiniteProgram? program = some artifact)
    (initialEq : services.initial = fixed) :
    EncodesConfig (artifactHost services fixed artifact) artifact.words
      (initial services program) (artifactStart artifact) := by
  change EncodesRunning (artifactHost services fixed artifact) artifact.words
    { instructions := program
      nodes := []
      nextId := 0
      root? := none
      serviceState := services.initial }
    (artifactStart artifact)
  constructor
  · exact compileFiniteProgram?_decodes program artifact compiled
  · show runningPattern? (artifactHost services fixed artifact) artifact.words
      { instructions := program
        nodes := []
        nextId := 0
        root? := none
        serviceState := services.initial } = some (artifactStart artifact)
    rw [initialEq]
    unfold runningPattern?
    simp only [nodesPattern?, rootPattern?]
    rw [artifactServiceState_encodes services fixed artifact]
    rfl

theorem fixedServiceState_encodes
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    encodeServiceState? (finiteHost services fixed program) fixed =
      some (serviceStateRef 0) := by
  simp [encodeServiceState?, finiteHost, FiniteAtomCodec.encode?,
    findAtomIndex?]

/-- Every instruction selected from the program is representable in the
program-derived atom arenas.  State stability supplies the only dynamic
arena obligation. -/
theorem stepRepresentationClosed_of_mem
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (stable : ProgramServiceStateStable services fixed program)
    (instruction : Instruction Formula Rule Evidence Provenance Obligation)
    (membership : instruction ∈ program) :
    StepRepresentationClosed (finiteHost services fixed program) fixed
      instruction := by
  have stateStable := stable instruction membership
  obtain ⟨record, recordEq⟩ :=
    exists_encodeInstructionFinite?_eq_some_of_mem program instruction
      membership
  cases instruction with
  | input id formula provenance relevance =>
      cases formulaEq :
          (finiteCodecsOfProgram program).formula.encode? formula with
      | none =>
          simp [encodeInstructionFinite?, formulaEq] at recordEq
      | some formulaIndex =>
          cases provenanceEq :
              (finiteCodecsOfProgram program).provenance.encode? provenance with
          | none =>
              simp [encodeInstructionFinite?, formulaEq, provenanceEq]
                at recordEq
          | some provenanceIndex =>
              refine ⟨⟨formulaRef formulaIndex, ?_⟩,
                ⟨provenanceRef provenanceIndex, ?_⟩, ?_⟩
              · simp [encodeFormula?, finiteHost, formulaEq]
              · simp [encodeProvenance?, finiteHost, provenanceEq]
              · intro next accepted
                rw [stateStable next accepted]
                exact ⟨serviceStateRef 0,
                  fixedServiceState_encodes services fixed program⟩
  | infer id rule parents evidence conclusion relevance =>
      cases ruleEq : (finiteCodecsOfProgram program).rule.encode? rule with
      | none =>
          simp [encodeInstructionFinite?, ruleEq] at recordEq
      | some ruleIndex =>
          cases evidenceEq :
              (finiteCodecsOfProgram program).evidence.encode? evidence with
          | none =>
              simp [encodeInstructionFinite?, ruleEq, evidenceEq] at recordEq
          | some evidenceIndex =>
              cases conclusionEq :
                  (finiteCodecsOfProgram program).formula.encode? conclusion with
              | none =>
                  simp [encodeInstructionFinite?, ruleEq, evidenceEq,
                    conclusionEq] at recordEq
              | some conclusionIndex =>
                  refine ⟨⟨ruleRef ruleIndex, ?_⟩,
                    ⟨evidenceRef evidenceIndex, ?_⟩,
                    ⟨formulaRef conclusionIndex, ?_⟩, ?_⟩
                  · simp [encodeRule?, finiteHost, ruleEq]
                  · simp [encodeEvidence?, finiteHost, evidenceEq]
                  · simp [encodeFormula?, finiteHost, conclusionEq]
                  · intro parentFormulas next accepted
                    rw [stateStable parentFormulas next accepted]
                    exact ⟨serviceStateRef 0,
                      fixedServiceState_encodes services fixed program⟩
  | drop id =>
      trivial
  | root id obligation =>
      cases obligationEq :
          (finiteCodecsOfProgram program).obligation.encode? obligation with
      | none =>
          simp [encodeInstructionFinite?, obligationEq] at recordEq
      | some obligationIndex =>
          exact ⟨obligationRef obligationIndex, by
            simp [encodeObligation?, finiteHost, obligationEq]⟩
  | finish =>
      trivial

omit [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState] in
/-- A running semantic transition cannot move the service state when its
instruction is covered by the program-local stability contract. -/
theorem advance_running_preservesServiceState
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (stable : ProgramServiceStateStable services fixed program)
    (instruction : Instruction Formula Rule Evidence Provenance Obligation)
    (membership : instruction ∈ program)
    (state nextState :
      State Formula Rule Evidence Provenance Obligation ServiceState)
    (stateEq : state.serviceState = fixed)
    (hasTrailing : Bool)
    (advanced : advance services hasTrailing instruction state =
      .running nextState) :
    nextState.serviceState = fixed := by
  have instructionStable := stable instruction membership
  rcases state with
    ⟨instructions, nodes, nextId, rootState, serviceState⟩
  simp only at stateEq
  subst serviceState
  cases instruction with
  | input id formula provenance relevance =>
      simp only [advance] at advanced
      split at advanced <;> try { simp [haltFault] at advanced }
      split at advanced <;> try { simp [haltFault] at advanced }
      next _ =>
        cases serviceEq : services.input fixed provenance formula with
        | none =>
            simp [serviceEq, haltFault] at advanced
        | some next =>
            simp [serviceEq] at advanced
            subst nextState
            exact instructionStable next serviceEq
  | infer id rule parents evidence conclusion relevance =>
      simp only [advance] at advanced
      split at advanced <;> try { simp [haltFault] at advanced }
      split at advanced <;> try { simp [haltFault] at advanced }
      next _ =>
        cases parentsEq :
            resolveParents? id relevance.distance parents nodes with
        | error failure =>
            simp [parentsEq, haltFault] at advanced
        | ok resolved =>
            obtain ⟨parentFormulas, nextNodes⟩ := resolved
            cases serviceEq :
                services.infer fixed rule parentFormulas evidence conclusion with
            | none =>
                simp [parentsEq, serviceEq, haltFault] at advanced
            | some next =>
                simp [parentsEq, serviceEq] at advanced
                subst nextState
                exact instructionStable parentFormulas next serviceEq
  | drop id =>
      simp only [advance] at advanced
      cases dropped : dropNode? id nodes with
      | none =>
          simp [dropped, haltFault] at advanced
      | some nextNodes =>
          simp [dropped] at advanced
          subst nextState
          rfl
  | root id obligation =>
      simp only [advance] at advanced
      cases rootState with
      | some root =>
          simp [haltFault] at advanced
      | none =>
          cases found : lookupNode? id nodes with
          | none =>
              simp [found, haltFault] at advanced
          | some node =>
              simp [found] at advanced
              split at advanced
              · simp [haltFault] at advanced
              · simp at advanced
                subst nextState
                rfl
  | finish =>
      simp only [advance] at advanced
      split at advanced <;> try { simp [haltFault] at advanced }
      next _ =>
        cases rootState with
        | none =>
            simp [haltFault] at advanced
        | some root =>
            cases irrelevant : firstIrrelevant? root.id nodes with
            | some id =>
                simp [irrelevant, haltFault] at advanced
            | none =>
                simp [irrelevant] at advanced
                split at advanced <;> simp [haltFault] at advanced

omit [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState] in
/-- One successful list-machine step preserves both the program suffix and
the fixed service state. -/
theorem step_running_preservesInvariant
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (stable : ProgramServiceStateStable services fixed program)
    (state nextState :
      State Formula Rule Evidence Provenance Obligation ServiceState)
    (suffix : state.instructions <:+ program)
    (stateEq : state.serviceState = fixed)
    (stepped : step? services (.running state) = some (.running nextState)) :
    nextState.instructions <:+ program ∧ nextState.serviceState = fixed := by
  cases instructionEq : state.instructions with
  | nil =>
      simp [step?, instructionEq, haltFault] at stepped
  | cons instruction rest =>
      have instructionMem : instruction ∈ program := by
        rw [List.suffix_iff_eq_append] at suffix
        have member : instruction ∈
            List.take (program.length - state.instructions.length) program ++
              state.instructions :=
          List.mem_append_right _ (by simp [instructionEq])
        rw [suffix] at member
        exact member
      have restSuffix : rest <:+ program := by
        have localSuffix : rest <:+ state.instructions := by
          rw [instructionEq]
          exact List.suffix_cons instruction rest
        exact localSuffix.trans suffix
      simp only [step?, instructionEq] at stepped
      cases advancedEq :
          advance services (!rest.isEmpty) instruction state with
      | halted outcome =>
          simp [replaceInstructions, advancedEq] at stepped
      | running advancedState =>
          simp [replaceInstructions, advancedEq] at stepped
          have stateShape :
              nextState = { advancedState with instructions := rest } :=
            stepped.symm
          subst nextState
          constructor
          · exact restSuffix
          · exact advance_running_preservesServiceState services fixed program
              stable instruction instructionMem state advancedState stateEq
              (!rest.isEmpty) advancedEq

def ExecutionInvariant
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation)) :
    Config Formula Rule Evidence Provenance Obligation ServiceState → Prop
  | .halted _ => True
  | .running state =>
      state.instructions <:+ program ∧ state.serviceState = fixed

/-- The finite-arena representation is closed for every bounded execution
whose current configuration satisfies the suffix/state invariant. -/
theorem executionRepresentationClosed
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (stable : ProgramServiceStateStable services fixed program)
    (fuel : Nat)
    (config : Config Formula Rule Evidence Provenance Obligation ServiceState)
    (invariant : ExecutionInvariant fixed program config) :
    ExecutionRepresentationClosed (finiteHost services fixed program) fuel
      config := by
  induction fuel generalizing config with
  | zero =>
      trivial
  | succ fuel induction =>
      cases config with
      | halted outcome =>
          trivial
      | running state =>
          rcases invariant with ⟨suffix, stateEq⟩
          cases instructionEq : state.instructions with
          | nil =>
              unfold ExecutionRepresentationClosed
              constructor
              · simp [instructionEq]
              · intro next stepped
                have optionEq :
                    some (.halted (.fault .missingFinish) :
                      Config Formula Rule Evidence Provenance Obligation
                        ServiceState) = some next := by
                  simpa [step?, instructionEq, haltFault] using stepped
                have nextEq : next = .halted (.fault .missingFinish) :=
                  (Option.some.inj optionEq).symm
                rw [nextEq]
                exact induction _ trivial
          | cons instruction rest =>
              unfold ExecutionRepresentationClosed
              rw [instructionEq]
              constructor
              · rw [stateEq]
                apply stepRepresentationClosed_of_mem services fixed program
                  stable instruction
                rw [List.suffix_iff_eq_append] at suffix
                have member : instruction ∈
                    List.take (program.length - state.instructions.length)
                        program ++ state.instructions :=
                  List.mem_append_right _ (by simp [instructionEq])
                rw [suffix] at member
                exact member
              · intro next stepped
                apply induction next
                cases next with
                | halted outcome =>
                    trivial
                | running nextState =>
                    exact step_running_preservesInvariant services fixed
                      program stable state nextState suffix stateEq stepped

/-- Initial execution is representation-closed whenever the service's
declared initial state is the stable state. -/
theorem initialExecutionRepresentationClosed
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (stable : ProgramServiceStateStable services fixed program)
    (initialEq : services.initial = fixed)
    (fuel : Nat) :
    ExecutionRepresentationClosed (finiteHost services fixed program) fuel
      (initial services program) := by
  apply executionRepresentationClosed services fixed program stable fuel
    (initial services program)
  exact ⟨List.suffix_refl program, initialEq⟩

/-- The compiler-returned artifact host is representation-closed along the
same bounded initial execution, without requiring clients to unfold or
recompute its concrete arenas. -/
theorem artifactExecutionRepresentationClosed
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (fixed : ServiceState)
    (program : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (artifact :
      FiniteProgramArtifact Formula Rule Evidence Provenance Obligation)
    (compiled : compileFiniteProgram? program = some artifact)
    (stable : ProgramServiceStateStable services fixed program)
    (initialEq : services.initial = fixed)
    (fuel : Nat) :
    ExecutionRepresentationClosed (artifactHost services fixed artifact) fuel
      (initial services program) := by
  rw [artifactHost_eq_finiteHost services fixed program artifact compiled]
  exact initialExecutionRepresentationClosed services fixed program stable
    initialEq fuel

#print axioms fixedServiceState_encodes
#print axioms artifactHost_eq_finiteHost
#print axioms artifactServiceState_encodes
#print axioms artifactStart_encodes
#print axioms stepRepresentationClosed_of_mem
#print axioms advance_running_preservesServiceState
#print axioms step_running_preservesInvariant
#print axioms executionRepresentationClosed
#print axioms initialExecutionRepresentationClosed
#print axioms artifactExecutionRepresentationClosed

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineStateStableCompilation
