import Mettapedia.GSLT.LanguageDef.DerivationWordMachineOneRecordSimulation

/-!
# Finite execution of the authored derivation-word machine

The one-record square is composed here into a continuous execution result.
Each semantic transition contributes one exact singleton rewrite of the
authored `LanguageDef`; halted configurations contribute no target rewrite.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DerivationWordMachineFiniteExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineLanguageDef
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineInputSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineOneRecordSimulation

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}
variable [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
  [DecidableEq Provenance] [DecidableEq Obligation]
  [DecidableEq ServiceState]

/-- A proof-relevant authored execution path.  Every edge records exact
singleton reduction, excluding both duplicated and invented successors. -/
inductive ExactRewriteTrace
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState) :
    Pattern → Pattern → Nat → Prop where
  | refl (term : Pattern) : ExactRewriteTrace host term term 0
  | step {source middle target : Pattern} {length : Nat}
      (head :
        rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
          [middle])
      (tail : ExactRewriteTrace host middle target length) :
      ExactRewriteTrace host source target (length + 1)

/-- The empty semantic instruction stream takes the explicit missing-finish
step.  No decode relation is consulted and every other authored row is
excluded by its root constructor or nonempty-record pattern. -/
theorem missing_finish_rewriteAt_exact
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (nodes nextId root serviceState : Pattern) :
    rewriteAt (engineBasePremises (relationEnv host)) language 1
      (run recordsNil nodes nextId root serviceState) =
        [halted
          (DerivationCheckMachineLanguageDef.outcomeFault
            (DerivationWordMachineLanguageDef.a
              "dcm:fault-missing-finish"))
          nodes] := by
  change language.rewrites.flatMap (fun rule =>
      applyRuleUsing (engineBasePremises (relationEnv host)) language
        (fun _ => []) rule
        (run recordsNil nodes nextId root serviceState)) = _
  rw [show language.rewrites = transitions by rfl]
  simp [transitions, liftedTransitions,
    DerivationCheckMachineLanguageDef.transitions, applyRuleUsing,
    malformedRecordTransition, liftRewrite, sourceInstruction?, liftLeft,
    liftPattern, DerivationCheckMachineLanguageDef.missingFinishTransition,
    DerivationCheckMachineLanguageDef.inputIndexFaultTransition,
    DerivationCheckMachineLanguageDef.inputRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.inputDecisionFaultTransition,
    DerivationCheckMachineLanguageDef.inputAcceptTransition,
    DerivationCheckMachineLanguageDef.inferIndexFaultTransition,
    DerivationCheckMachineLanguageDef.inferRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.inferParentFaultTransition,
    DerivationCheckMachineLanguageDef.inferRuleFaultTransition,
    DerivationCheckMachineLanguageDef.inferAcceptTransition,
    DerivationCheckMachineLanguageDef.dropFaultTransition,
    DerivationCheckMachineLanguageDef.dropAcceptTransition,
    DerivationCheckMachineLanguageDef.duplicateRootTransition,
    DerivationCheckMachineLanguageDef.rootFaultTransition,
    DerivationCheckMachineLanguageDef.rootAcceptTransition,
    DerivationCheckMachineLanguageDef.finishTrailingTransition,
    DerivationCheckMachineLanguageDef.finishMissingRootTransition,
    DerivationCheckMachineLanguageDef.finishRelevanceFaultTransition,
    DerivationCheckMachineLanguageDef.finishRootFaultTransition,
    DerivationCheckMachineLanguageDef.finishVerifiedTransition,
    DerivationCheckMachineLanguageDef.run,
    DerivationCheckMachineLanguageDef.instructionsNil,
    DerivationCheckMachineLanguageDef.instructionsCons,
    DerivationCheckMachineLanguageDef.rootNone,
    DerivationCheckMachineLanguageDef.rootSome,
    DerivationCheckMachineLanguageDef.a,
    DerivationCheckMachineLanguageDef.v, run, halted, recordsNil, recordsCons,
    DerivationWordMachineLanguageDef.a, v, matchPattern, matchArgs,
    mergeBindings, premisesUsing, applyBindings]
  simp [DerivationCheckMachineLanguageDef.halted,
    DerivationCheckMachineLanguageDef.outcomeFault,
    DerivationCheckMachineLanguageDef.a, liftPattern, applyBindings]

#print axioms missing_finish_rewriteAt_exact

/-- The semantic missing-finish step and the authored empty-record step form
the same exact square. -/
theorem missing_finish_semantic_square
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (rootState : Option (RootClaim Formula Obligation))
    (rootPatternValue : Pattern) (oldNodes : List (Node Formula))
    (nextId : Nat) (serviceState : ServiceState)
    (serviceStatePattern nodesPatternValue : Pattern)
    (rootEncoded : rootPattern? host rootState = some rootPatternValue)
    (serviceStateEncoded :
      encodeServiceState? host serviceState = some serviceStatePattern)
    (nodesEncoded : nodesPattern? host oldNodes = some nodesPatternValue) :
    let before :
        State Formula Rule Evidence Provenance Obligation ServiceState := {
      instructions := []
      nodes := oldNodes
      nextId := nextId
      root? := rootState
      serviceState := serviceState
    }
    let source := run recordsNil nodesPatternValue (indexPattern nextId)
      rootPatternValue serviceStatePattern
    let target := halted
      (DerivationCheckMachineLanguageDef.outcomeFault
        (faultPattern .missingFinish))
      nodesPatternValue
    EncodesConfig host [] (.running before) source ∧
      step? host.services (.running before) =
        some (.halted (.fault .missingFinish)) ∧
      rewriteAt (engineBasePremises (relationEnv host)) language 1 source =
        [target] ∧
      EncodesConfig host [] (.halted (.fault .missingFinish)) target := by
  dsimp only
  constructor
  · constructor
    · rfl
    · simp [runningPattern?, nodesEncoded, rootEncoded, serviceStateEncoded,
        recordsPattern, recordsNil, DerivationWordMachineRelationEnv.a,
        DerivationWordMachineLanguageDef.a]
  constructor
  · simp [step?, haltFault]
  constructor
  · exact missing_finish_rewriteAt_exact host nodesPatternValue
      (indexPattern nextId) rootPatternValue serviceStatePattern
  · exact fault_target_encodes_halted host [] oldNodes .missingFinish
      nodesPatternValue nodesEncoded

#print axioms missing_finish_semantic_square

/-- Closure of the proof-local representation along a bounded semantic run.
The condition follows the actual deterministic successor.  It does not demand
global encodability of the semantic carrier. -/
def ExecutionRepresentationClosed
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState) :
    Nat →
      Config Formula Rule Evidence Provenance Obligation ServiceState → Prop
  | 0, _ => True
  | _ + 1, .halted _ => True
  | fuel + 1, .running state =>
      (match state.instructions with
      | [] => True
      | instruction :: _ =>
          StepRepresentationClosed host state.serviceState instruction) ∧
      ∀ next,
        step? host.services (.running state) = some next →
          ExecutionRepresentationClosed host fuel next

/-- Bounded semantic execution is represented by a continuous authored trace.

The target frontier is an actual suffix of the source word stream, every
semantic step is represented by one exact singleton rewrite, and early
semantic halting produces a shorter trace rather than administrative target
steps. -/
theorem runFuel_exact_authored_trace
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (fuel : Nat)
    (words : DerivationCheckMachineBinary.WordProgram)
    (config :
      Config Formula Rule Evidence Provenance Obligation ServiceState)
    (source : Pattern)
    (encoded : EncodesConfig host words config source)
    (closed : ExecutionRepresentationClosed host fuel config) :
    ∃ finalWords target length,
      ExactRewriteTrace host source target length ∧
        length ≤ fuel ∧
        finalWords <:+ words ∧
        EncodesConfig host finalWords
          (runFuel host.services fuel config) target := by
  induction fuel generalizing words config source with
  | zero =>
      exact ⟨words, source, 0, .refl source, Nat.zero_le 0,
        List.suffix_refl words, by simpa [runFuel] using encoded⟩
  | succ fuel induction =>
      cases config with
      | halted outcome =>
          exact ⟨words, source, 0, .refl source, Nat.zero_le _,
            List.suffix_refl words, by simpa [runFuel, step?] using encoded⟩
      | running state =>
          rcases state with
            ⟨stateInstructions, stateNodes, stateNextId, stateRoot,
              stateService⟩
          rcases encoded with ⟨instructionsDecoded, sourceEncoded⟩
          cases stateInstructions with
          | nil =>
              cases words with
              | nil =>
                  unfold runningPattern? at sourceEncoded
                  cases nodesResult : nodesPattern? host stateNodes with
                  | none => simp [nodesResult] at sourceEncoded
                  | some nodesPatternValue =>
                      cases rootResult : rootPattern? host stateRoot with
                      | none =>
                          simp [nodesResult, rootResult] at sourceEncoded
                      | some rootPatternValue =>
                          cases serviceResult :
                              encodeServiceState? host stateService with
                          | none =>
                              simp [nodesResult, rootResult, serviceResult]
                                at sourceEncoded
                          | some serviceStatePattern =>
                              simp [nodesResult, rootResult, serviceResult]
                                at sourceEncoded
                              subst source
                              rcases closed with ⟨_, nextClosed⟩
                              rcases missing_finish_semantic_square host
                                  stateRoot rootPatternValue stateNodes
                                  stateNextId stateService
                                  serviceStatePattern nodesPatternValue
                                  rootResult serviceResult nodesResult with
                                ⟨_, semanticStep, authoredStep,
                                  targetEncoded⟩
                              have closedAfter :
                                  ExecutionRepresentationClosed host fuel
                                    (.halted (.fault .missingFinish)) :=
                                nextClosed (.halted (.fault .missingFinish))
                                  semanticStep
                              obtain ⟨finalWords, finalTarget, tailLength,
                                  tailTrace, tailBound, finalSuffix,
                                  finalEncoded⟩ :=
                                induction [] (.halted (.fault .missingFinish))
                                  _ targetEncoded closedAfter
                              refine ⟨finalWords, finalTarget, tailLength + 1,
                                .step authoredStep tailTrace, ?_, ?_, ?_⟩
                              · omega
                              · exact finalSuffix
                              · simpa [runFuel, semanticStep] using finalEncoded
              | cons record remainingRecords =>
                  cases recordDecoded :
                      DerivationCheckMachineBinary.decodeInstructionUsing?
                        host.codecs.decoders record with
                  | none =>
                      simp [DerivationCheckMachineBinary.decodeProgramUsing?,
                        recordDecoded] at instructionsDecoded
                  | some instruction =>
                      cases remainingDecoded :
                          DerivationCheckMachineBinary.decodeProgramUsing?
                            host.codecs.decoders remainingRecords with
                      | none =>
                          simp [DerivationCheckMachineBinary.decodeProgramUsing?,
                            recordDecoded, remainingDecoded]
                            at instructionsDecoded
                      | some instructions =>
                          simp [DerivationCheckMachineBinary.decodeProgramUsing?,
                            recordDecoded, remainingDecoded]
                            at instructionsDecoded
          | cons instruction remainingInstructions =>
              cases words with
              | nil =>
                  simp [DerivationCheckMachineBinary.decodeProgramUsing?]
                    at instructionsDecoded
              | cons record remainingRecords =>
                  cases recordDecoded :
                      DerivationCheckMachineBinary.decodeInstructionUsing?
                        host.codecs.decoders record with
                  | none =>
                      simp [DerivationCheckMachineBinary.decodeProgramUsing?,
                        recordDecoded] at instructionsDecoded
                  | some decodedInstruction =>
                      cases remainingDecoded :
                          DerivationCheckMachineBinary.decodeProgramUsing?
                            host.codecs.decoders remainingRecords with
                      | none =>
                          simp [DerivationCheckMachineBinary.decodeProgramUsing?,
                            recordDecoded, remainingDecoded]
                            at instructionsDecoded
                      | some decodedInstructions =>
                          simp [DerivationCheckMachineBinary.decodeProgramUsing?,
                            recordDecoded, remainingDecoded]
                            at instructionsDecoded
                          rcases instructionsDecoded with ⟨rfl, rfl⟩
                          unfold runningPattern? at sourceEncoded
                          cases nodesResult : nodesPattern? host stateNodes with
                          | none => simp [nodesResult] at sourceEncoded
                          | some nodesPatternValue =>
                              cases rootResult : rootPattern? host stateRoot with
                              | none =>
                                  simp [nodesResult, rootResult] at sourceEncoded
                              | some rootPatternValue =>
                                  cases serviceResult : encodeServiceState? host
                                      stateService with
                                  | none =>
                                      simp [nodesResult, rootResult,
                                        serviceResult] at sourceEncoded
                                  | some serviceStatePattern =>
                                      simp [nodesResult, rootResult,
                                        serviceResult] at sourceEncoded
                                      subst source
                                      rcases closed with
                                        ⟨stepClosed, nextClosed⟩
                                      rcases
                                          one_record_semantic_square_encoded_root
                                            host decodedInstruction stateRoot
                                            rootPatternValue record
                                            remainingRecords
                                            decodedInstructions stateNodes
                                            stateNextId stateService
                                            serviceStatePattern nodesPatternValue
                                            recordDecoded remainingDecoded
                                            serviceResult nodesResult rootResult
                                            stepClosed with
                                        ⟨_, next, middle, semanticStep,
                                          authoredStep, middleEncoded⟩
                                      have closedAfter :
                                          ExecutionRepresentationClosed host
                                            fuel next :=
                                        nextClosed next semanticStep
                                      obtain ⟨finalWords, finalTarget,
                                          tailLength, tailTrace, tailBound,
                                          finalSuffix, finalEncoded⟩ :=
                                        induction remainingRecords next middle
                                          middleEncoded closedAfter
                                      refine ⟨finalWords, finalTarget,
                                        tailLength + 1,
                                        .step authoredStep tailTrace, ?_, ?_,
                                        ?_⟩
                                      · omega
                                      · exact finalSuffix.trans
                                          (List.suffix_cons record
                                            remainingRecords)
                                      · simpa [runFuel, semanticStep] using
                                          finalEncoded

#print axioms runFuel_exact_authored_trace

/-- Complete bounded semantic execution has an authored target trace from the
same encoded initial configuration. -/
theorem execute_exact_authored_trace
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (instructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (words : DerivationCheckMachineBinary.WordProgram) (source : Pattern)
    (encoded :
      EncodesConfig host words (initial host.services instructions) source)
    (closed :
      ExecutionRepresentationClosed host (instructions.length + 1)
        (initial host.services instructions)) :
    ∃ finalWords target length,
      ExactRewriteTrace host source target length ∧
        length ≤ instructions.length + 1 ∧
        finalWords <:+ words ∧
        EncodesConfig host finalWords
          (execute host.services instructions) target := by
  simpa [execute] using
    runFuel_exact_authored_trace host (instructions.length + 1) words
      (initial host.services instructions) source encoded closed

#print axioms execute_exact_authored_trace

/-- When a separately proved calculus service accepts the root, the continuous
authored execution trace ends at a representation of that verified outcome
and the declared logical objective follows. -/
theorem execute_verified_authored_trace_sound
    (host : Host Formula Rule Evidence Provenance Obligation ServiceState)
    (sound : SoundServices host.services)
    (instructions : List
      (Instruction Formula Rule Evidence Provenance Obligation))
    (words : DerivationCheckMachineBinary.WordProgram) (source : Pattern)
    (root : RootClaim Formula Obligation)
    (encoded :
      EncodesConfig host words (initial host.services instructions) source)
    (closed :
      ExecutionRepresentationClosed host (instructions.length + 1)
        (initial host.services instructions))
    (accepted :
      execute host.services instructions = .halted (.verified root)) :
    ∃ finalWords target length,
      ExactRewriteTrace host source target length ∧
        length ≤ instructions.length + 1 ∧
        finalWords <:+ words ∧
        EncodesConfig host finalWords (.halted (.verified root)) target ∧
        sound.Objective root.obligation := by
  obtain ⟨finalWords, target, length, trace, bound, suffix,
      finalEncoded⟩ :=
    execute_exact_authored_trace host instructions words source encoded closed
  have objective : sound.Objective root.obligation :=
    execute_verified_sound sound instructions root accepted
  rw [accepted] at finalEncoded
  exact ⟨finalWords, target, length, trace, bound, suffix, finalEncoded,
    objective⟩

#print axioms execute_verified_authored_trace_sound

end Mettapedia.GSLT.LanguageDef.DerivationWordMachineFiniteExecution
