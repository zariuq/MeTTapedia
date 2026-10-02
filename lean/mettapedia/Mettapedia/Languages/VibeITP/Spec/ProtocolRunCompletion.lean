import Mettapedia.Languages.VibeITP.Spec.ProtocolRuns

/-! Exact successful control flow of the raw-file protocol runner. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolRunCompletion

open ProtocolExecution ProtocolObserved ProtocolRuns

def Completion {ε : Type} (capability : Capability ε) (setup proofs : List (List UInt8))
    (verdict : Verdict) (final : ObservedState) : Prop :=
  ∃ decoded prepared,
    decodeFiles 0 (setup ++ proofs) = .ok decoded ∧
    ProtocolRuns.runFiles capability initial 0 (decoded.take setup.length) = .ok prepared ∧
    if proofs.isEmpty then final = prepared ∧ verdict = .setupOnly prepared.kernel.openChallenges
    else ProtocolRuns.runFiles capability (proofBoundary prepared) setup.length (decoded.drop setup.length) = .ok final ∧
      verdict = .proofs final.kernel.setupChallenges final.kernel.proofChallenges final.kernel.openChallenges

theorem checkRun_completed_iff {ε : Type} (capability : Capability ε)
    (setup proofs : List (List UInt8)) (verdict : Verdict) (final : ObservedState) :
    ProtocolRuns.checkRun capability setup proofs = .completed verdict final ↔
      Completion capability setup proofs verdict final := by
  constructor
  · intro accepted
    cases decodedRead : decodeFiles 0 (setup ++ proofs) with
    | error error =>
      rcases error with ⟨file, error⟩
      simp [ProtocolRuns.checkRun, decodedRead] at accepted
    | ok decoded =>
      cases setupRun : ProtocolRuns.runFiles capability initial 0 (decoded.take setup.length) with
      | error error =>
        rcases error with ⟨file, index, error⟩
        simp [ProtocolRuns.checkRun, decodedRead, setupRun] at accepted
      | ok prepared =>
        by_cases empty : proofs.isEmpty = true
        · simp only [ProtocolRuns.checkRun, decodedRead, setupRun, if_pos empty] at accepted
          have equal := CheckResult.completed.inj accepted
          refine ⟨decoded, prepared, decodedRead, setupRun, ?_⟩
          simp only [if_pos empty]
          exact ⟨equal.2.symm, equal.1.symm⟩
        · cases proofRun : ProtocolRuns.runFiles capability (proofBoundary prepared) setup.length
              (decoded.drop setup.length) with
          | error error =>
            rcases error with ⟨file, index, error⟩
            simp [ProtocolRuns.checkRun, decodedRead, setupRun, empty, proofRun] at accepted
          | ok result =>
            simp only [ProtocolRuns.checkRun, decodedRead, setupRun, if_neg empty, proofRun] at accepted
            rcases CheckResult.completed.inj accepted with ⟨sameVerdict, sameState⟩
            subst final
            refine ⟨decoded, prepared, decodedRead, setupRun, ?_⟩
            simp only [if_neg empty]
            exact ⟨proofRun, sameVerdict.symm⟩
  · rintro ⟨decoded, prepared, decodedRead, setupRun, completed⟩
    simp only [ProtocolRuns.checkRun, decodedRead, setupRun]
    by_cases empty : proofs.isEmpty = true
    · simp only [if_pos empty] at completed ⊢
      rcases completed with ⟨rfl, rfl⟩
      rfl
    · simp only [if_neg empty] at completed ⊢
      rw [completed.1, completed.2]

end Mettapedia.Languages.VibeITP.Spec.ProtocolRunCompletion
