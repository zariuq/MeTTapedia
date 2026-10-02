import Mettapedia.Languages.VibeITP.Spec.ProtocolLogicalRuns
import Mettapedia.Languages.VibeITP.Native.ProtocolRunSoundness
import Mettapedia.Languages.VibeITP.Native.ProtocolRunControls
import Mettapedia.Languages.VibeITP.Presentation.CompleteCorrespondence
import Mettapedia.GSLT.LanguageDef.BootstrapCell.Replay

/-!
The completed raw-byte protocol model presents its execution-free theorems to
NIK's generic certificate replay. Hosted-theory conditions are derived from the
run. This bridge requires no physical execution contract for static results.
It does not prove lowering of the guest's operational functions or a compiled
checker. Results with execution observations retain the native-operation
boundary of the observation-bearing derivation relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.ProtocolReplayBridge

open Spec Spec.ProtocolExecution Spec.ProtocolObserved Spec.ProtocolRuns
open Spec.ProtocolInvariant Spec.ProtocolLogicalRuns Presentation
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.BootstrapCell

theorem derives_iff_replay {theory : Theory} {allocated : Nat}
    (hosted : Hosted theory allocated) (statement : Term) :
    Derives theory statement ↔ ∃ certificate : RawProof,
      (nikSignature (kernelValidated theory allocated)).replay
        (jThm (encTerm theory.sig statement)) certificate = true := by
  constructor
  · intro derived
    obtain ⟨certificate, accepted⟩ := complete_article hosted derived
    exact ⟨certificate, by rwa [← checkRaw_eq_replay]⟩
  · rintro ⟨certificate, accepted⟩
    apply (derives_iff_checkRaw hosted statement).mpr
    exact ⟨certificate, by rwa [checkRaw_eq_replay]⟩

theorem completed_logical {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final) :
    LogicalInvariant final :=
  ProtocolLogicalRuns.completed_logical capability setup proofs verdict final
    (fun decoded valid => ProtocolRunSoundness.decoded_files_bounded (setup ++ proofs) 0 decoded valid)
    accepted

theorem completed_static_theorems_checkRaw {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final)
    (eventFree : final.observations = []) :
    ∀ slot statement, final.kernel.theorems slot = some statement →
      ∃ certificate : RawProof,
        checkRaw (kernelValidated final.kernel.theory final.kernel.nextFresh)
          (jThm (encTerm final.kernel.theory.sig statement)) certificate = true := by
  have logical := completed_logical capability setup proofs verdict final accepted
  intro slot statement stored
  have derived := logical.theorems slot statement stored
  rw [eventFree] at derived
  exact complete_article logical.theory (execution_free_derives_static derived)

theorem completed_static_theorems_replay {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final)
    (eventFree : final.observations = []) :
    ∀ slot statement, final.kernel.theorems slot = some statement →
      ∃ certificate : RawProof,
        (nikSignature (kernelValidated final.kernel.theory final.kernel.nextFresh)).replay
          (jThm (encTerm final.kernel.theory.sig statement)) certificate = true := by
  intro slot statement stored
  obtain ⟨certificate, checked⟩ :=
    completed_static_theorems_checkRaw capability setup proofs verdict final accepted eventFree slot statement stored
  exact ⟨certificate, by rwa [← checkRaw_eq_replay]⟩

theorem completed_static_registered_goals_checkRaw {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final)
    (success : verdict.success = true) (eventFree : final.observations = []) :
    ∀ goal ∈ Spec.ProtocolRegistrations.check capability setup proofs,
      ∃ certificate : RawProof,
        checkRaw (kernelValidated final.kernel.theory final.kernel.nextFresh)
          (jThm (encTerm final.kernel.theory.sig goal)) certificate = true := by
  have logical := completed_logical capability setup proofs verdict final accepted
  have accounted := ProtocolLogicalRuns.completed_accounting capability setup proofs verdict final accepted
  have closed := (ProtocolRunSoundness.completed_success_shape capability setup proofs verdict final accepted success).2.1
  intro goal registered
  have tracked := ProtocolRunSoundness.completed_registrations_tracked capability setup proofs verdict final accepted goal registered
  have derived := Spec.ProtocolChallengePreservation.closed_tracked_is_derived logical accounted closed tracked
  rw [eventFree] at derived
  exact complete_article logical.theory (execution_free_derives_static derived)

theorem decoded_static_run_theorems_checkRaw {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (decoded : List (List Instr))
    (decodedRead : decodeFiles 0 (setup ++ proofs) = .ok decoded)
    (static : NoExecutionFiles decoded) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final) :
    ∀ slot statement, final.kernel.theorems slot = some statement →
      ∃ certificate : RawProof,
        checkRaw (kernelValidated final.kernel.theory final.kernel.nextFresh)
          (jThm (encTerm final.kernel.theory.sig statement)) certificate = true :=
  completed_static_theorems_checkRaw capability setup proofs verdict final accepted
    (decoded_nonexecution_completed_ledger capability setup proofs decoded decodedRead static verdict final accepted)

theorem decoded_static_run_goals_checkRaw {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (decoded : List (List Instr))
    (decodedRead : decodeFiles 0 (setup ++ proofs) = .ok decoded)
    (static : NoExecutionFiles decoded) (verdict : Verdict) (final : ObservedState)
    (accepted : ProtocolRuns.checkRun capability setup proofs = .completed verdict final)
    (success : verdict.success = true) :
    ∀ goal ∈ Spec.ProtocolRegistrations.check capability setup proofs,
      ∃ certificate : RawProof,
        checkRaw (kernelValidated final.kernel.theory final.kernel.nextFresh)
          (jThm (encTerm final.kernel.theory.sig goal)) certificate = true :=
  completed_static_registered_goals_checkRaw capability setup proofs verdict final accepted success
    (decoded_nonexecution_completed_ledger capability setup proofs decoded decodedRead static verdict final accepted)

theorem static_slot_maintenance_admitted :
    NoExecution [.symbolSwap 0 1, .termSwap 0 1, .thmSwap 0 1] := by
  intro instruction member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | second | third <;> subst instruction <;> rfl

theorem jit_is_not_a_static_stream : ¬ NoExecution [.jit 0 1 0] := by
  intro static
  have refused := static (.jit 0 1 0) List.mem_cons_self
  cases refused

theorem literal_complete_run_has_nik_certificates :
    ∃ verdict final,
      ProtocolRuns.checkRun ProtocolRunControls.unavailable
        ProtocolRunControls.literalSetup ProtocolRunControls.literalProof = .completed verdict final ∧
      verdict.success = true ∧
      ∀ goal ∈ Spec.ProtocolRegistrations.check ProtocolRunControls.unavailable
        ProtocolRunControls.literalSetup ProtocolRunControls.literalProof,
        ∃ certificate : RawProof,
          checkRaw (kernelValidated final.kernel.theory final.kernel.nextFresh)
            (jThm (encTerm final.kernel.theory.sig goal)) certificate = true := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  apply completed_static_registered_goals_checkRaw
  · rfl
  · rfl
  · rfl

theorem wrong_literal_goal_run_rejects :
    ProtocolRuns.checkRun ProtocolRunControls.unavailable ProtocolRunControls.literalSetup
      [[18, 2, 0, 14, 0, 0]] = .rejected 1 1 (.protocol .challengeMismatch) :=
  ProtocolRunControls.wrong_literal_goal_refused

end Mettapedia.Languages.VibeITP.Native.ProtocolReplayBridge
