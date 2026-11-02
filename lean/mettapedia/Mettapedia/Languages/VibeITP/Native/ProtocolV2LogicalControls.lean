import Mettapedia.Languages.VibeITP.Native.ProtocolV2Soundness
import Mettapedia.Languages.VibeITP.Spec.ProtocolV2Controls
import Mettapedia.Languages.VibeITP.Spec.SimultaneousInstantiationControls

/-!
# Closed witnesses for the versioned logical protocol

The same definition-derived crossing-substitution program used by the native
byte controls now supplies a derivation of its independently written goal.
The initial invariant, byte bounds and challenge tracking are constructed,
rather than passed in as undischarged assumptions.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Native.ProtocolV2LogicalControls

open Spec Spec.ProtocolV2 Spec.ProtocolV2.Controls Spec.ProtocolV2Invariant
open Spec.ProtocolExecution Spec.ProtocolInvariant Spec.ProtocolChallenges
open Spec.ProtocolChallengePreservation Spec.ProtocolMaintenance Spec.ProtocolAdmission
open Mettapedia.Languages.VibeITP.Presentation

def setupState : State := preparedState.get preparedState_exists

theorem setup_run : ProtocolV2.runInstrs initialState 0 (setup 2 4) = .ok setupState := by
  have present := Option.eq_some_of_isSome preparedState_exists
  change preparedState = some setupState at present
  unfold preparedState at present
  cases run : ProtocolV2.runInstrs initialState 0 (setup 2 4) with
  | error index error => simp [run] at present
  | unsupported index => simp [run] at present
  | ok state =>
      simp only [run, Option.some.injEq] at present
      exact congrArg RunResult.ok present

theorem setup_invariant : Invariant setupState [] :=
  runInstrs_preserves (setup 2 4) 0 (before := initialState) (after := setupState) (observations := [])
    (initial_invariantFor DerivesWithExecutionV2)
    (by decide +kernel) setup_run

theorem setup_accounting : Accounting setupState :=
  (runInstrs_tracks (setup 2 4) 0 (before := initialState) (after := setupState)
    initial_accounting setup_run).1

theorem setup_phase : setupState.phase = .setup :=
  (runInstrs_tracks (setup 2 4) 0 (before := initialState) (after := setupState)
    initial_accounting setup_run).2.1

theorem before_invariant : Invariant beforeCrossing [] :=
  enterProofs_preserves setupState setup_invariant

theorem before_accounting : Accounting beforeCrossing :=
  enterProofs_accounting setupState setup_phase setup_accounting

theorem after_crossing_invariant : Invariant afterCrossing [] :=
  executeMany_preserves (before := beforeCrossing) (after := afterCrossing) (observations := [])
    1 2 [(13, 2), (14, 4)] before_invariant crossing_accepted

theorem original_goal_registered : beforeCrossing.challenges 0 = some crossingResult := by decide +kernel

theorem original_goal_tracked : Tracked beforeCrossing crossingResult :=
  Or.inr ⟨0, original_goal_registered⟩

def proofInstructions : List Instruction := proof [(13, 2), (14, 4)]

theorem proof_bounded : ∀ instruction ∈ proofInstructions, instruction.Bounded :=
  ProtocolV2Bounds.file_establishes (ProtocolV2.encodeFile proofInstructions) proofInstructions
    crossing_roundtrip

theorem crossing_instruction_bounded : (Instruction.instantiateMany 1 [(13, 2), (14, 4)] 2).Bounded :=
  ProtocolV2Bounds.file_establishes (ProtocolV2.encodeFile proofInstructions) proofInstructions
    crossing_roundtrip (.instantiateMany 1 [(13, 2), (14, 4)] 2) (by decide +kernel)

def completion : Option State :=
  match ProtocolV2.runInstrs beforeCrossing 0 proofInstructions with
  | .ok state => some state
  | _ => none

theorem completion_exists : completion.isSome = true := by decide +kernel

def finalState : State := completion.get completion_exists

theorem proof_run : ProtocolV2.runInstrs beforeCrossing 0 proofInstructions = .ok finalState := by
  have present := Option.eq_some_of_isSome completion_exists
  change completion = some finalState at present
  unfold completion at present
  cases run : ProtocolV2.runInstrs beforeCrossing 0 proofInstructions with
  | error index error => simp [run] at present
  | unsupported index => simp [run] at present
  | ok state =>
      simp only [run, Option.some.injEq] at present
      exact congrArg RunResult.ok present

theorem no_open_challenges : finalState.openChallenges = 0 := by decide +kernel

theorem registered_goal_derived : DerivesV2 finalState.theory crossingResult :=
  ProtocolV2Soundness.decoded_run_derives_registered_goal
    (ProtocolV2.encodeFile proofInstructions) proofInstructions 0
    (before := beforeCrossing) (after := finalState) (observations := []) (goal := crossingResult)
    crossing_roundtrip
    before_invariant before_accounting original_goal_tracked proof_run no_open_challenges

theorem final_invariant : Invariant finalState [] :=
  runInstrs_preserves proofInstructions 0 (before := beforeCrossing) (after := finalState)
    (observations := []) before_invariant proof_bounded proof_run

def grownState : State := (finalState.allocate (SymInfo.fvarOf 1)).2

theorem growth_allocates_new_symbol :
    grownState.sig (.fresh finalState.nextFresh) = some (SymInfo.fvarOf 1) := by
  simp [grownState, State.allocate, State.sig, sigOf, setSlot]

theorem old_signature_lacks_new_symbol : finalState.sig (.fresh finalState.nextFresh) = none := by
  cases found : finalState.sig (.fresh finalState.nextFresh) with
  | none => rfl
  | some info =>
      have impossible := (final_invariant.theory.fresh finalState.nextFresh).mp (by
        simpa only [State.theory, found] using (show (some info).isSome = true from rfl))
      exact False.elim (Nat.lt_irrefl _ impossible)

theorem registered_goal_survives_growth : DerivesV2 grownState.theory crossingResult :=
  allocate_derivation finalState (SymInfo.fvarOf 1) final_invariant registered_goal_derived

def setupBytes : List (List UInt8) := [ProtocolV2.encodeFile (setup 2 4)]

/-- One setup registration and two proof-phase registrations of the same
statement, consumed separately using the same retained theorem. -/
def duplicateInstructions : List Instruction :=
  [.instantiateMany 1 [(13, 2), (14, 4)] 2,
   .legacy (.challengeAdd 7 1), .legacy (.challengeAdd 7 2),
   .legacy (.challengeSatisfy 0 2), .legacy (.challengeSatisfy 1 2),
   .legacy (.challengeSatisfy 2 2)]

def duplicateBytes : List (List UInt8) := [ProtocolV2.encodeFile duplicateInstructions]

theorem duplicate_verdict : ProtocolV2.checkRun setupBytes duplicateBytes = .proofs 1 2 0 := by
  decide +kernel

theorem duplicate_success : (ProtocolV2.checkRun setupBytes duplicateBytes).success = true := by
  rw [duplicate_verdict]
  decide +kernel

theorem duplicate_registration_trace : ProtocolV2Soundness.registeredGoals setupBytes duplicateBytes =
    [crossingResult, crossingResult, crossingResult] := by decide +kernel

theorem complete_bytes_derive_goal :
    ∃ final, ProtocolV2Soundness.ProofCompletion setupBytes duplicateBytes final ∧
      final.satisfied.length = 3 ∧ DerivesV2 final.theory crossingResult := by
  obtain ⟨final, completed, _, total, _, derived⟩ :=
    ProtocolV2Soundness.raw_bytes_success_registered_goals_derived setupBytes duplicateBytes duplicate_success
  have goal := derived crossingResult (by rw [duplicate_registration_trace]; simp)
  obtain ⟨decoded, prepared, decodedRead, setupRun, empty, proofRun⟩ := completed
  have counters : final.setupChallenges = 1 ∧ final.proofChallenges = 2 := by
    have verdict := duplicate_verdict
    simp only [ProtocolV2.checkRun, decodedRead, setupRun, empty, Bool.false_eq_true,
      if_false, proofRun, Verdict.proofs.injEq] at verdict
    exact ⟨verdict.1, verdict.2.1⟩
  refine ⟨final, ⟨decoded, prepared, decodedRead, setupRun, empty, proofRun⟩, ?_, goal⟩
  simpa [counters.1, counters.2] using total

theorem duplicate_partial_refused :
    (ProtocolV2.checkRun setupBytes
      [ProtocolV2.encodeFile (duplicateInstructions.take 4)]).success = false := by decide +kernel

theorem no_challenge_is_not_success :
    (ProtocolV2.checkRun [] [ProtocolV2.encodeFile []]).success = false := by decide +kernel

def completionCases : List Case := [
  ⟨"proof-phase-duplicates", setupBytes, duplicateBytes, .proofs 1 2 0⟩,
  ⟨"proof-phase-partial", setupBytes,
    [ProtocolV2.encodeFile (duplicateInstructions.take 4)], .proofs 1 2 2⟩,
  ⟨"no-challenges", [], [ProtocolV2.encodeFile []], .proofs 0 0 0⟩]

theorem completion_cases_agree :
    (completionCases.map fun entry =>
      decide (ProtocolV2.checkRun entry.setupFiles entry.proofFiles = entry.expected)).all id = true := by
  decide +kernel

namespace Formation

open SimultaneousInstantiation.Controls

def replacements : List (SymId × Term) := [(F, g), (G, .natLit 7)]

theorem values_formed : SimultaneousFormation.ValuesShape sig replacements := by
  have checked : ∀ pair ∈ replacements, WellFormed sig pair.2 = true := by decide +kernel
  exact fun pair member => wellFormed_termShape sig pair.2 (checked pair member)

theorem source_shape : TermShape sig pair := wellFormed_termShape sig pair (by decide +kernel)

theorem result_shape : TermShape sig (.eq g (.natLit 7)) :=
  SimultaneousFormation.statement_shape sig replacements pair (.eq g (.natLit 7))
    values_formed source_shape crossing_replacements

def extendedSig : Sig := fun symbol =>
  if symbol = .fresh 99 then some (SymInfo.fvarOf 0) else sig symbol

theorem signature_extension : SigExt sig extendedSig := by
  intro symbol info present
  by_cases newest : symbol = .fresh 99
  · subst symbol
    have absent : sig (.fresh 99) = none := by decide +kernel
    rw [absent] at present
    cases present
  · simpa [extendedSig, newest] using present

theorem extension_nontrivial : sig (.fresh 99) = none ∧
    extendedSig (.fresh 99) = some (SymInfo.fvarOf 0) := by decide +kernel

theorem survives_extension :
    SimultaneousInstantiation.statement extendedSig replacements pair = some (.eq g (.natLit 7)) :=
  SimultaneousExtension.statement_success_sigExt signature_extension replacements pair (.eq g (.natLit 7))
    values_formed source_shape crossing_replacements

end Formation

def unknownValue : Term := .app (.fresh 99) []

/-- Depth checks alone do not establish replacement formation, even when an
entry is shadowed. The protocol invariant supplies the missing formation. -/
theorem shadowed_formation_is_not_implied_by_success :
    SimultaneousInstantiation.statement SimultaneousInstantiation.Controls.sig
      [(SimultaneousInstantiation.Controls.F, .natLit 8),
       (SimultaneousInstantiation.Controls.F, unknownValue)] SimultaneousInstantiation.Controls.f =
        some (.natLit 8) ∧
    WellFormed SimultaneousInstantiation.Controls.sig unknownValue = false := by decide +kernel

#print axioms registered_goal_derived
#print axioms registered_goal_survives_growth
#print axioms complete_bytes_derive_goal
#print axioms shadowed_formation_is_not_implied_by_success

end Mettapedia.Languages.VibeITP.Native.ProtocolV2LogicalControls
