import Mettapedia.Logic.TierZero.Kernel2.AdmissionInterface
import Mettapedia.Logic.TierZero.Kernel2.AdmissionLocalControl

/-!
# Executable admission-interface controls

The accepted local claim exposes its local obligation through the executable
`checkClaim` path. Removing the declared local sort makes the same message fail
the board-level gate and prevents both acceptance and interface publication.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2.AdmissionInterface.Controls

open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins.LocalControl

def ready : World String :=
  ⟨⟨[("object", 1), ("witness", 0)], ["object"], [("from-object", fromObject)]⟩,
    [], [], [], []⟩

theorem ready_determined : EnvDetermined ready.env := by
  intro name rule found
  unfold ready World.env envOf at found
  simp only [List.lookup_cons, List.lookup_nil] at found
  split at found
  · simp only [Option.some.injEq] at found
    subst rule
    decide
  · cases found

theorem local_message_passes_board_gate : ready.L.claimOk localClaim = true := by decide

theorem local_message_is_accepted :
    (checkClaim ready localClaim).T = ["local-witness"] := by decide +kernel

theorem accepted_message_exposes_interface :
    ∃ hypotheses goal proof root used,
      localClaim.cbHyps = some hypotheses ∧ localClaim.goal = some goal ∧
      localClaim.translate = some (proof, root) ∧ localClaim.inferUsed = some used ∧
      localClaim.inferredInterface = some ⟨used, localClaim.usedOrigins used⟩ ∧
      Mettapedia.Logic.TierZero.ProofInterface.Supports
        (P := presOf ready.env localClaim.frame) hypotheses [] used goal := by
  have accepted : localClaim.id ∈ (checkClaim ready localClaim).T := by
    rw [local_message_is_accepted]
    simp [localClaim]
  exact (checkClaim_accepts_interface ready_determined (by simp [ready])
    accepted (target := [])).2

def missingSort : World String :=
  ⟨⟨[("object", 1), ("witness", 0)], [], [("from-object", fromObject)]⟩,
    [], [], [], []⟩

theorem missing_local_sort_fails_gate : missingSort.L.claimOk localClaim = false := by decide

theorem missing_local_sort_is_not_accepted :
    (checkClaim missingSort localClaim).T = [] := by decide +kernel

end Mettapedia.Logic.TierZero.Kernel2.AdmissionInterface.Controls
