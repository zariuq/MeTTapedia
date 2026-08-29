import Mettapedia.GSLT.LanguageDef.DerivationWordMachineFiniteExecution
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordLanguageExecution

/-!
# Continuous authored trace for the official ground-resolution canary

This module instantiates the generic finite-execution theorem.  The result is
derived from the seven compact records, their proof-local arenas, and the
separately proved ground-resolution service; it does not normalize the whole
contextual evaluator to establish target execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordLanguageTrace

open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineRelationEnv
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineOneRecordSimulation
open Mettapedia.GSLT.LanguageDef.DerivationWordMachineFiniteExecution
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
open Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordMachine
open Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordLanguageExecution

namespace Canary

open TptpOfficialGroundResolutionSelectedRoot.Canary

theorem provenance_zero_encodes :
    DerivationWordMachineRelationEnv.encodeProvenance?
        TptpOfficialGroundResolutionWordLanguageExecution.Canary.host
        firstClause =
      some (DerivationWordMachineRelationEnv.provenanceRef 0) := by
  rfl

theorem provenance_one_encodes :
    DerivationWordMachineRelationEnv.encodeProvenance?
        TptpOfficialGroundResolutionWordLanguageExecution.Canary.host
        secondClause =
      some (DerivationWordMachineRelationEnv.provenanceRef 1) := by
  rfl

theorem provenance_two_encodes :
    DerivationWordMachineRelationEnv.encodeProvenance?
        TptpOfficialGroundResolutionWordLanguageExecution.Canary.host
        thirdClause =
      some (DerivationWordMachineRelationEnv.provenanceRef 2) := by
  rfl

theorem rule_zero_encodes :
    DerivationWordMachineRelationEnv.encodeRule?
        TptpOfficialGroundResolutionWordLanguageExecution.Canary.host
        TptpGroundResolutionProblemAuthority.resolutionKey =
      some (DerivationWordMachineRelationEnv.ruleRef 0) := by
  rfl

theorem evidence_zero_encodes :
    DerivationWordMachineRelationEnv.encodeEvidence?
        TptpOfficialGroundResolutionWordLanguageExecution.Canary.host () =
      some (DerivationWordMachineRelationEnv.evidenceRef 0) := by
  rfl

private abbrev Host :=
  TptpOfficialGroundResolutionWordLanguageExecution.Canary.host

private def node0 (linked : Bool) : Node Formula := {
  id := 0
  formula := .clause firstClause.literals
  relevance := { distance := 2, towardRoot := some 3 }
  linked := linked
}

private def node1 (linked : Bool) : Node Formula := {
  id := 1
  formula := .clause secondClause.literals
  relevance := { distance := 2, towardRoot := some 3 }
  linked := linked
}

private def node2 (linked : Bool) : Node Formula := {
  id := 2
  formula := .clause thirdClause.literals
  relevance := { distance := 1, towardRoot := some 4 }
  linked := linked
}

private def node3 (linked : Bool) : Node Formula := {
  id := 3
  formula := .clause [.positive q]
  relevance := { distance := 1, towardRoot := some 4 }
  linked := linked
}

private def node4 : Node Formula := {
  id := 4
  formula := .clause []
  relevance := { distance := 0, towardRoot := none }
}

private def state0 : State Formula Rule Evidence Provenance Obligation Unit := {
  instructions := validProgram
  nodes := []
  nextId := 0
  root? := none
  serviceState := ()
}

private def state1 : State Formula Rule Evidence Provenance Obligation Unit := {
  instructions := validProgram.drop 1
  nodes := [node0 false]
  nextId := 1
  root? := none
  serviceState := ()
}

private def state2 : State Formula Rule Evidence Provenance Obligation Unit := {
  instructions := validProgram.drop 2
  nodes := [node1 false, node0 false]
  nextId := 2
  root? := none
  serviceState := ()
}

private def state3 : State Formula Rule Evidence Provenance Obligation Unit := {
  instructions := validProgram.drop 3
  nodes := [node2 false, node1 false, node0 false]
  nextId := 3
  root? := none
  serviceState := ()
}

private def state4 : State Formula Rule Evidence Provenance Obligation Unit := {
  instructions := validProgram.drop 4
  nodes := [node3 false, node2 false, node1 true, node0 true]
  nextId := 4
  root? := none
  serviceState := ()
}

private def state5 : State Formula Rule Evidence Provenance Obligation Unit := {
  instructions := validProgram.drop 5
  nodes := [node4, node3 true, node2 true, node1 true, node0 true]
  nextId := 5
  root? := none
  serviceState := ()
}

private def state6 : State Formula Rule Evidence Provenance Obligation Unit := {
  instructions := validProgram.drop 6
  nodes := [node4, node3 true, node2 true, node1 true, node0 true]
  nextId := 5
  root? := some validRoot
  serviceState := ()
}

private theorem unit_service_state_encodable (state : Unit) :
    ∃ pattern,
      DerivationWordMachineRelationEnv.encodeServiceState? Host state =
        some pattern := by
  cases state
  exact ⟨DerivationWordMachineRelationEnv.serviceStateRef 0,
    TptpOfficialGroundResolutionWordLanguageExecution.Canary.service_state_zero_encodes⟩

private theorem input0_closed :
    StepRepresentationClosed Host () validProgram[0] := by
  refine ⟨⟨_,
      TptpOfficialGroundResolutionWordLanguageExecution.Canary.formula_zero_encodes⟩,
    ⟨_, provenance_zero_encodes⟩, ?_⟩
  intro next _
  exact unit_service_state_encodable next

private theorem input1_closed :
    StepRepresentationClosed Host () validProgram[1] := by
  refine ⟨⟨_,
      TptpOfficialGroundResolutionWordLanguageExecution.Canary.formula_one_encodes⟩,
    ⟨_, provenance_one_encodes⟩, ?_⟩
  intro next _
  exact unit_service_state_encodable next

private theorem input2_closed :
    StepRepresentationClosed Host () validProgram[2] := by
  refine ⟨⟨_,
      TptpOfficialGroundResolutionWordLanguageExecution.Canary.formula_two_encodes⟩,
    ⟨_, provenance_two_encodes⟩, ?_⟩
  intro next _
  exact unit_service_state_encodable next

private theorem infer3_closed :
    StepRepresentationClosed Host () validProgram[3] := by
  refine ⟨⟨_, rule_zero_encodes⟩, ⟨_, evidence_zero_encodes⟩,
    ⟨_,
      TptpOfficialGroundResolutionWordLanguageExecution.Canary.formula_three_encodes⟩,
    ?_⟩
  intro _ next _
  exact unit_service_state_encodable next

private theorem infer4_closed :
    StepRepresentationClosed Host () validProgram[4] := by
  refine ⟨⟨_, rule_zero_encodes⟩, ⟨_, evidence_zero_encodes⟩,
    ⟨_,
      TptpOfficialGroundResolutionWordLanguageExecution.Canary.formula_four_encodes⟩,
    ?_⟩
  intro _ next _
  exact unit_service_state_encodable next

private theorem root5_closed :
    StepRepresentationClosed Host () validProgram[5] :=
  ⟨_,
    TptpOfficialGroundResolutionWordLanguageExecution.Canary.obligation_zero_encodes⟩

private theorem finish6_closed :
    StepRepresentationClosed Host () validProgram[6] := trivial

private theorem state0_step :
    step? (services problem) (.running state0) = some (.running state1) := by
  simp [state0, state1, validProgram, step?, advance, replaceInstructions,
    RelevanceWitness.wellFormedFor, first_input_accepted, node0]

private theorem state1_step :
    step? (services problem) (.running state1) = some (.running state2) := by
  simp [state1, state2, validProgram, step?, advance, replaceInstructions,
    RelevanceWitness.wellFormedFor, second_input_accepted, node0, node1]

private theorem state2_step :
    step? (services problem) (.running state2) = some (.running state3) := by
  simp [state2, state3, validProgram, step?, advance, replaceInstructions,
    RelevanceWitness.wellFormedFor, third_input_accepted, node0, node1, node2]

private theorem state3_step :
    step? (services problem) (.running state3) = some (.running state4) := by
  simp [state3, state4, validProgram, step?, advance, replaceInstructions,
    resolveParents?, resolveParentsFrom?, useParent?,
    RelevanceWitness.wellFormedFor, services, first_inference_accepted,
    node0, node1, node2, node3]

private theorem state4_step :
    step? (services problem) (.running state4) = some (.running state5) := by
  simp [state4, state5, validProgram, step?, advance, replaceInstructions,
    resolveParents?, resolveParentsFrom?, useParent?,
    RelevanceWitness.wellFormedFor, services, second_inference_accepted,
    node0, node1, node2, node3, node4]

private theorem state5_step :
    step? (services problem) (.running state5) = some (.running state6) := by
  simp [state5, state6, validProgram, step?, advance, replaceInstructions,
    lookupNode?, node0, node1, node2, node3, node4, validRoot]

private theorem state6_step :
    step? (services problem) (.running state6) =
      some (.halted (.verified validRoot)) := by
  simp [state6, validProgram, step?, advance, replaceInstructions,
    firstIrrelevant?, correct_root_obligation_accepted,
    node0, node1, node2, node3, node4, validRoot]

theorem valid_execution_representation_closed :
    ExecutionRepresentationClosed
      TptpOfficialGroundResolutionWordLanguageExecution.Canary.host
      (validProgram.length + 1)
      (initial (services problem) validProgram) := by
  change ExecutionRepresentationClosed Host 8 (.running state0)
  change StepRepresentationClosed Host () validProgram[0] ∧ _
  constructor
  · exact input0_closed
  · intro next stepped
    have nextEq : next = .running state1 :=
      Option.some.inj (stepped.symm.trans state0_step)
    subst next
    change StepRepresentationClosed Host () validProgram[1] ∧ _
    constructor
    · exact input1_closed
    · intro next stepped
      have nextEq : next = .running state2 :=
        Option.some.inj (stepped.symm.trans state1_step)
      subst next
      change StepRepresentationClosed Host () validProgram[2] ∧ _
      constructor
      · exact input2_closed
      · intro next stepped
        have nextEq : next = .running state3 :=
          Option.some.inj (stepped.symm.trans state2_step)
        subst next
        change StepRepresentationClosed Host () validProgram[3] ∧ _
        constructor
        · exact infer3_closed
        · intro next stepped
          have nextEq : next = .running state4 :=
            Option.some.inj (stepped.symm.trans state3_step)
          subst next
          change StepRepresentationClosed Host () validProgram[4] ∧ _
          constructor
          · exact infer4_closed
          · intro next stepped
            have nextEq : next = .running state5 :=
              Option.some.inj (stepped.symm.trans state4_step)
            subst next
            change StepRepresentationClosed Host () validProgram[5] ∧ _
            constructor
            · exact root5_closed
            · intro next stepped
              have nextEq : next = .running state6 :=
                Option.some.inj (stepped.symm.trans state5_step)
              subst next
              change StepRepresentationClosed Host () validProgram[6] ∧ _
              constructor
              · exact finish6_closed
              · intro next stepped
                have nextEq : next = .halted (.verified validRoot) :=
                  Option.some.inj (stepped.symm.trans state6_step)
                subst next
                trivial

#print axioms valid_execution_representation_closed

/-- The semantic seven-record canary executes by the same seven structural
steps used to establish representation closure.  This avoids normalizing the
whole contextual evaluator. -/
theorem valid_program_verified_structural :
    execute (services problem) validProgram =
      .halted (.verified validRoot) := by
  change runFuel (services problem) 8 (.running state0) =
    .halted (.verified validRoot)
  calc
    _ = runFuel (services problem) 7 (.running state1) := by
      rw [runFuel, state0_step]
    _ = runFuel (services problem) 6 (.running state2) := by
      rw [runFuel, state1_step]
    _ = runFuel (services problem) 5 (.running state3) := by
      rw [runFuel, state2_step]
    _ = runFuel (services problem) 4 (.running state4) := by
      rw [runFuel, state3_step]
    _ = runFuel (services problem) 3 (.running state5) := by
      rw [runFuel, state4_step]
    _ = runFuel (services problem) 2 (.running state6) := by
      rw [runFuel, state5_step]
    _ = runFuel (services problem) 1 (.halted (.verified validRoot)) := by
      rw [runFuel, state6_step]
    _ = .halted (.verified validRoot) := by rfl

#print axioms valid_program_verified_structural

/-- The official ground-resolution canary has one continuous exact trace in
the authored word-machine `LanguageDef`; the separately proved calculus
service establishes the logical objective at the verified root. -/
theorem valid_authored_trace_sound :
    ∃ finalWords target length,
      ExactRewriteTrace Host
          TptpOfficialGroundResolutionWordLanguageExecution.Canary.start
          target length ∧
        length ≤ validProgram.length + 1 ∧
        finalWords <:+
          TptpOfficialGroundResolutionWordMachine.Canary.words ∧
        EncodesConfig Host finalWords (.halted (.verified validRoot)) target ∧
        RelativeTheorem problem validRoot.obligation := by
  apply execute_verified_authored_trace_sound Host (services_sound problem)
      validProgram TptpOfficialGroundResolutionWordMachine.Canary.words
      TptpOfficialGroundResolutionWordLanguageExecution.Canary.start
      validRoot
  · exact
      TptpOfficialGroundResolutionWordLanguageExecution.Canary.start_encodes_initial
  · exact valid_execution_representation_closed
  · simpa [Host,
      TptpOfficialGroundResolutionWordLanguageExecution.Canary.host] using
      valid_program_verified_structural

#print axioms valid_authored_trace_sound

end Canary

end Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordLanguageTrace
