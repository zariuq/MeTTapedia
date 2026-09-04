import Mettapedia.GSLT.LanguageDef.DerivationWordMachineStateStableCompilation
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionStatusIndexedMachine
import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationWordArtifact

/-!
# Status-indexed official ground resolution through finite word arenas

This module compiles the status- and provenance-preserving official TSTP
canary to proof-local finite arenas and compact word records.  The binary
machine is a representation of the same semantic program: successful word
execution is decoded back to that program before the independently proved
status-indexed soundness theorem is used.

No resolution rule or TSTP status policy is implemented by the word layer.
Those remain owned by the declared calculus service and composition policy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionStatusIndexedWordMachine

open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineFiniteExecution
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineStateStableCompilation
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
open Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionStatusIndexedMachine
open Mettapedia.GSLT.LanguageDef.TptpOfficialStatusIndexedService

namespace Canary

open TptpOfficialGroundResolutionSelectedRoot.Canary

/-! ## Source-derived semantic and word artifacts -/

def compiledOption : Option CompiledGroundRoot :=
  (compileWhole? validAdmitted "empty").toOption

theorem compiledOption_isSome : compiledOption.isSome = true :=
  TptpOfficialGroundResolutionStatusIndexedMachine.Canary.valid_compilation_succeeds

def compiled : CompiledGroundRoot :=
  compiledOption.get compiledOption_isSome

/-- The retained semantic artifact is exactly the result of official
admission and status-indexed projection, not a separately maintained program. -/
theorem officialCompilation_exact :
    compileWhole? validAdmitted "empty" = .ok compiled := by
  have someEq : some compiled = compiledOption :=
    Option.some_get compiledOption_isSome
  cases resultEq : compileWhole? validAdmitted "empty" with
  | error failure =>
      rw [compiledOption, resultEq] at someEq
      cases someEq
  | ok value =>
      rw [compiledOption, resultEq] at someEq
      have valueEq : value = compiled := (Option.some.inj someEq).symm
      rw [valueEq]

/-- The generic calculus-neutral stage retained inside the status-indexed
compiler produced exactly the semantic artifact exposed by that compiler. -/
theorem genericSemanticCompilation_exact :
    TptpOfficialDerivationProgram.compileAdmittedWhole?
        TptpOfficialGroundResolutionStatusIndexedMachine.projection
        validAdmitted "empty" = .ok compiled.artifact := by
  exact TptpOfficialGroundResolutionStatusIndexedMachine.compileWhole?_semantic_exact
    officialCompilation_exact

def program : MachineProgram := compiled.artifact.program

def statusServices :=
  TptpOfficialGroundResolutionStatusIndexedMachine.services
    compiled.problem compiled.initialSymbols

def wordArtifactOption : Option
    (FiniteProgramArtifact MachineFormula Rule MachineEvidence Provenance
      Obligation) :=
  compileFiniteProgram? program

theorem wordArtifactOption_isSome : wordArtifactOption.isSome = true := by
  obtain ⟨artifact, compiledEq⟩ := exists_compileFiniteProgram?_eq_some program
  simp [wordArtifactOption, compiledEq]

def wordArtifact :
    FiniteProgramArtifact MachineFormula Rule MachineEvidence Provenance
      Obligation :=
  wordArtifactOption.get wordArtifactOption_isSome

/-- The finite artifact is produced by the generic compiler from the exact
status-indexed program. -/
theorem wordArtifact_compiles :
    compileFiniteProgram? program = some wordArtifact := by
  exact (Option.some_get wordArtifactOption_isSome).symm

/-- The semantic and finite stages are retained in one source-authenticated
artifact.  Its type records the admitted official derivation, selected root,
and calculus projection that produced the word stream. -/
def officialWordArtifact :
    TptpOfficialDerivationWordArtifact.Artifact
      TptpOfficialGroundResolutionStatusIndexedMachine.projection
      validAdmitted "empty" where
  semantic := compiled.artifact
  semanticCompiled := genericSemanticCompilation_exact
  finite := wordArtifact
  finiteCompiled := wordArtifact_compiles

/-- Proof-local word records decode to the exact status-indexed semantic
program, including official evidence and provenance payloads. -/
theorem wordArtifact_decodes :
    decodeProgramUsing? wordArtifact.codecs.decoders wordArtifact.words =
      some program :=
  TptpOfficialDerivationWordArtifact.decodes_exact officialWordArtifact

/-! ## Program-local service-state closure -/

def initialMetadata : MetadataState := statusServices.initial

/-- Executable check used only to discharge the finite canary's exact static
signature bound.  The generic state-stability theorem below consumes the
propositional consequence, not this Boolean as semantic authority. -/
def payloadBoundedB :
    Instruction MachineFormula Rule MachineEvidence Provenance Obligation →
      Bool
  | .input _ formula _ _ =>
      finsetSubsetB formula.principalSymbols compiled.initialSymbols
  | .infer _ _ _ _ conclusion _ =>
      finsetSubsetB conclusion.principalSymbols compiled.initialSymbols
  | _ => true

theorem allPayloadsBoundedB : program.all payloadBoundedB = true := by
  decide +kernel

theorem payload_bounded
    (instruction :
      Instruction MachineFormula Rule MachineEvidence Provenance Obligation)
    (membership : instruction ∈ program) :
    match instruction with
    | .input _ formula _ _ =>
        formula.principalSymbols ⊆ compiled.initialSymbols
    | .infer _ _ _ _ conclusion _ =>
        conclusion.principalSymbols ⊆ compiled.initialSymbols
    | _ => True := by
  have bounded :=
    (List.all_eq_true.mp allPayloadsBoundedB) instruction membership
  cases instruction <;>
    simp_all [payloadBoundedB, finsetSubsetB]

/-- Every successful callback named by the exact official canary preserves
the proof-local metadata state.  Inputs are state-neutral by the generic
service contract; every inference conclusion uses only the admitted initial
signature, so its set union is also state-neutral. -/
theorem programServiceStateStable :
    ProgramServiceStateStable statusServices initialMetadata program := by
  intro instruction membership
  have bounded := payload_bounded instruction membership
  cases instruction with
  | input id formula provenance relevance =>
      intro next accepted
      change
        (machineServices
          Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.service
          (boundary compiled.problem compiled.initialSymbols)).input
            initialMetadata provenance formula = some next at accepted
      exact (machineServices_input_exact
        Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.service
        (boundary compiled.problem compiled.initialSymbols)
        initialMetadata next provenance formula accepted).2
  | infer id rule parents evidence conclusion relevance =>
      intro parentFormulas next accepted
      change
        (machineServices
          Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.service
          (boundary compiled.problem compiled.initialSymbols)).infer
            initialMetadata rule parentFormulas evidence conclusion =
              some next at accepted
      have sound := machineServices_infer_sound
        Mettapedia.GSLT.LanguageDef.TptpGroundResolutionStatusIndexedService.service
        (boundary compiled.problem compiled.initialSymbols)
        initialMetadata next rule parentFormulas evidence conclusion accepted
      rcases sound with
        ⟨_normalized, _calculusAccepted, _origin, _signatureExact,
          _metadataAccepted, nextEq, _ruleStatus, _conclusionRole,
          _parentsSupported⟩
      rw [nextEq]
      change
        ({ knownSymbols :=
            initialMetadata.knownSymbols ∪ conclusion.principalSymbols } :
          MetadataState) = initialMetadata
      have bounded' :
          conclusion.principalSymbols ⊆ initialMetadata.knownSymbols := by
        simpa [initialMetadata, statusServices,
          TptpOfficialGroundResolutionStatusIndexedMachine.services,
          boundary, machineServices] using bounded
      exact congrArg
        (fun known => ({ knownSymbols := known } : MetadataState))
        (Finset.union_eq_left.mpr bounded')
  | drop id =>
      trivial
  | root id obligation =>
      trivial
  | finish =>
      trivial

/-! ## Execution reflection and semantic consequence -/

theorem wordExecution_refines :
    executeFiniteArtifact statusServices wordArtifact =
      .ofConfig (execute statusServices program) :=
  executeFiniteArtifact_eq_of_compile statusServices program wordArtifact
    wordArtifact_compiles

/-- The qualification fixture reaches the expected root through the exact
officially compiled status-indexed program.  Logical soundness is not obtained
from this closed computation; it comes from `verifiedWord_unsatisfiable`. -/
theorem semanticExecution_verified :
    execute statusServices program =
      .halted (.verified
        TptpOfficialGroundResolutionStatusIndexedMachine.Canary.validRoot) := by
  have observed :=
    TptpOfficialGroundResolutionStatusIndexedMachine.Canary.compiled_stream_executes_exactly
  unfold TptpOfficialGroundResolutionStatusIndexedMachine.Canary.executeCompiled?
    at observed
  rw [officialCompilation_exact] at observed
  exact Option.some.inj observed

/-! ## Continuous LanguageDef execution -/

def wordHost := artifactHost statusServices initialMetadata wordArtifact

def wordStart : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern :=
  artifactStart wordArtifact

/-- The source term is the canonical representation of the exact decoded
status-indexed program and its initial semantic configuration. -/
theorem wordStart_encodes :
    EncodesConfig wordHost wordArtifact.words
      (initial statusServices program) wordStart := by
  exact artifactStart_encodes statusServices initialMetadata program
    wordArtifact wordArtifact_compiles rfl

theorem executionRepresentationClosed :
    ExecutionRepresentationClosed wordHost (program.length + 1)
      (initial statusServices program) := by
  exact artifactExecutionRepresentationClosed statusServices initialMetadata
    program wordArtifact wordArtifact_compiles programServiceStateStable rfl
    (program.length + 1)

/-- The exact official program runs as a continuous trace of the declared
derivation-word `LanguageDef`.  The final relative theorem is supplied by the
independently proved status-indexed service invariant, not by replaying the
closed canary result. -/
theorem wordTrace_sound :
    ∃ finalWords target length,
      ExactRewriteTrace wordHost wordStart target length ∧
        length ≤ program.length + 1 ∧
        finalWords <:+ wordArtifact.words ∧
        EncodesConfig wordHost finalWords
          (.halted (.verified
            TptpOfficialGroundResolutionStatusIndexedMachine.Canary.validRoot))
          target ∧
        TptpGroundResolutionCheckService.RelativeTheorem compiled.problem
          TptpOfficialGroundResolutionStatusIndexedMachine.Canary.validRoot.obligation := by
  exact execute_verified_word_language_trace_sound wordHost
    (servicesSound compiled.problem compiled.initialSymbols)
    program wordArtifact.words wordStart
    TptpOfficialGroundResolutionStatusIndexedMachine.Canary.validRoot
    wordStart_encodes executionRepresentationClosed
    semanticExecution_verified

/-- The continuous word-language trace and the logical refutation are one theorem:
the latter is derived from the objective carried by the generic trace theorem,
not paired with an unrelated closed computation. -/
theorem wordTrace_unsatisfiable :
    ∃ finalWords target length,
      ExactRewriteTrace wordHost wordStart target length ∧
        length ≤ program.length + 1 ∧
        finalWords <:+ wordArtifact.words ∧
        EncodesConfig wordHost finalWords
          (.halted (.verified
            TptpOfficialGroundResolutionStatusIndexedMachine.Canary.validRoot))
          target ∧
        ProblemUnsatisfiable compiled.problem := by
  rcases wordTrace_sound with
    ⟨finalWords, target, length, trace, bound, suffix, encoded, objective⟩
  refine ⟨finalWords, target, length, trace, bound, suffix, encoded, ?_⟩
  change TptpGroundResolutionCheckService.RelativeTheorem compiled.problem
    (.clause []) at objective
  intro valuation problemSatisfied
  have emptySatisfied := objective valuation problemSatisfied
  rcases emptySatisfied with ⟨literal, membership, _⟩
  simp at membership

theorem wordExecution_verified :
    executeFiniteArtifact statusServices wordArtifact =
      .halted (.verified
        TptpOfficialGroundResolutionStatusIndexedMachine.Canary.validRoot) := by
  rw [wordExecution_refines, semanticExecution_verified]
  rfl

/-- Acceptance by the compact word machine reflects to acceptance by the
status-indexed semantic machine.  The latter's independently proved calculus
and composition laws then establish unsatisfiability. -/
theorem verifiedWord_unsatisfiable
    (root : RootClaim MachineFormula Obligation)
    (accepted : executeFiniteArtifact statusServices wordArtifact =
      .halted (.verified root))
    (emptyRoot : root.obligation = .clause []) :
    ProblemUnsatisfiable compiled.problem := by
  have mapped :
      WordConfig.ofConfig (execute statusServices program) =
        .halted (.verified root) :=
    wordExecution_refines.symm.trans accepted
  have semanticAccepted :
      execute statusServices program = .halted (.verified root) := by
    cases executed : execute statusServices program with
    | running state =>
        simp [WordConfig.ofConfig, executed] at mapped
    | halted outcome =>
        have outcomeShape : outcome = .verified root := by
          simpa [WordConfig.ofConfig, executed] using mapped
        exact congrArg Config.halted outcomeShape
  exact acceptedEmptyRoot_unsatisfiable compiled root semanticAccepted emptyRoot

/-- The generic authenticated-word theorem reaches the exact independent
relative-theorem objective supplied by the selected status-indexed calculus.
This is the reusable semantic boundary; the empty-clause theorem below is its
ground-resolution specialization. -/
theorem authenticatedWord_relativeTheorem
    (root : RootClaim MachineFormula Obligation)
    (accepted : executeFiniteArtifact statusServices wordArtifact =
      .halted (.verified root)) :
    TptpGroundResolutionCheckService.RelativeTheorem compiled.problem
      root.obligation := by
  exact TptpOfficialDerivationWordArtifact.accepted_sound statusServices
    (servicesSound compiled.problem compiled.initialSymbols)
    officialWordArtifact root accepted

theorem wordExecution_unsatisfiable :
    ProblemUnsatisfiable compiled.problem :=
  verifiedWord_unsatisfiable
    TptpOfficialGroundResolutionStatusIndexedMachine.Canary.validRoot
    wordExecution_verified rfl

/-! ## Representation controls -/

theorem wordCount_exact : wordArtifact.words.length = 7 := by
  decide +kernel

theorem outOfArenaFormula_rejected :
    decodeInstructionUsing? wordArtifact.codecs.decoders
      [opcodeInput, 0, wordArtifact.codecs.formula.entries.length, 0, 2, 4] =
        none := by
  decide +kernel

theorem malformedParentCount_rejected :
    decodeInstructionUsing? wordArtifact.codecs.decoders
      [opcodeInfer, 3, 0, 0, 3, 1, 5, 3, 0, 1] = none := by
  decide +kernel

theorem unknownOpcode_rejected :
    decodeInstructionUsing? wordArtifact.codecs.decoders [99] = none := by
  decide +kernel

end Canary

#print axioms Canary.officialCompilation_exact
#print axioms Canary.wordArtifact_compiles
#print axioms Canary.officialWordArtifact
#print axioms Canary.wordArtifact_decodes
#print axioms Canary.programServiceStateStable
#print axioms Canary.wordExecution_refines
#print axioms Canary.semanticExecution_verified
#print axioms Canary.wordStart_encodes
#print axioms Canary.executionRepresentationClosed
#print axioms Canary.wordTrace_sound
#print axioms Canary.wordTrace_unsatisfiable
#print axioms Canary.wordExecution_verified
#print axioms Canary.verifiedWord_unsatisfiable
#print axioms Canary.authenticatedWord_relativeTheorem
#print axioms Canary.wordExecution_unsatisfiable
#print axioms Canary.wordCount_exact
#print axioms Canary.outOfArenaFormula_rejected
#print axioms Canary.malformedParentCount_rejected
#print axioms Canary.unknownOpcode_rejected

end Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionStatusIndexedWordMachine
