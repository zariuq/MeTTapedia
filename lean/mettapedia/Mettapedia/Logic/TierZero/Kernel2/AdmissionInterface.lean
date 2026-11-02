import Mettapedia.Logic.TierZero.Kernel2.ClaimInterface
import Mettapedia.Logic.TierZero.Kernel2.Spaces

/-!
# Executable acceptance exposes the independent proof interface

Acceptance by the five-space kernel implies both the board-level statement
checks and the proof-use interface theorem. The latter is stated only with
`Derivable`, independently of mailboxes, rights, scheduling, and the shared
store implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2.AdmissionInterface

open Mettapedia.Logic.TierZero.ProofInterface
open Mettapedia.Logic.TierZero.Kernel2

variable {R : Type} [DecidableEq R]

theorem checkClaim_accepts_claimOk {world : World R} {claim : Claim R}
    (fresh : claim.id ∉ world.T) (accepted : claim.id ∈ (checkClaim world claim).T) :
    world.L.claimOk claim = true := by
  unfold checkClaim at accepted
  by_cases blocked : (world.used claim.id || !world.L.claimOk claim) = true
  · rw [if_pos blocked] at accepted
    exact False.elim (fresh accepted)
  · rw [if_neg blocked] at accepted
    cases qualified : world.L.claimOk claim with
    | true => rfl
    | false => simp [qualified] at blocked

/-- Direct executable acceptance yields the exact checked-proof interface in
every target context. -/
theorem checkClaim_accepts_interface {world : World R} {claim : Claim R}
    (determined : EnvDetermined world.env) (fresh : claim.id ∉ world.T)
    (accepted : claim.id ∈ (checkClaim world claim).T) {target : List Tm} :
    world.L.claimOk claim = true ∧
      ∃ hypotheses goal proof root used,
        claim.cbHyps = some hypotheses ∧ claim.goal = some goal ∧
        claim.translate = some (proof, root) ∧ claim.inferUsed = some used ∧
        claim.inferredInterface = some ⟨used, claim.usedOrigins used⟩ ∧
        Supports (P := presOf world.env claim.frame) hypotheses target used goal := by
  refine ⟨checkClaim_accepts_claimOk fresh accepted, ?_⟩
  have sharedAccepted := checkClaim_accepts fresh accepted
  have treeAccepted : claim.verdict world.env determined = true := by
    rw [← Claim.verdictR_eq_verdict world.env determined]
    exact sharedAccepted
  exact Claim.verdict_interface (target := target) treeAccepted

/-- The selected hypotheses themselves give a concrete independent
derivation of every directly accepted conclusion. -/
theorem checkClaim_accepts_selected {world : World R} {claim : Claim R}
    (determined : EnvDetermined world.env) (fresh : claim.id ∉ world.T)
    (accepted : claim.id ∈ (checkClaim world claim).T) :
    ∃ hypotheses goal proof root used,
      claim.cbHyps = some hypotheses ∧ claim.goal = some goal ∧
      claim.translate = some (proof, root) ∧ claim.inferUsed = some used ∧
      Derivable (presOf world.env claim.frame)
        (select (P := presOf world.env claim.frame) used hypotheses) goal := by
  have sharedAccepted := checkClaim_accepts fresh accepted
  have treeAccepted : claim.verdict world.env determined = true := by
    rw [← Claim.verdictR_eq_verdict world.env determined]
    exact sharedAccepted
  unfold Claim.verdict at treeAccepted
  simp only [Bool.and_eq_true] at treeAccepted
  obtain ⟨_, checked⟩ := treeAccepted
  cases hypothesesRead : claim.cbHyps with
  | none => simp [hypothesesRead] at checked
  | some hypotheses =>
      cases goalRead : claim.goal with
      | none => simp [hypothesesRead, goalRead] at checked
      | some goal =>
          cases translated : claim.translate with
          | none => simp [hypothesesRead, goalRead, translated] at checked
          | some result =>
              obtain ⟨proof, root⟩ := result
              simp only [hypothesesRead, goalRead, translated] at checked
              obtain ⟨used, inferred, derivation⟩ :=
                checkCB_selected (matcherOf world.env claim.frame determined) checked
              have claimInferred : claim.inferUsed = some used := by
                unfold Claim.inferUsed
                rw [hypothesesRead, translated]
                exact inferred
              exact ⟨hypotheses, goal, proof, root, used, rfl, rfl, rfl,
                claimInferred, derivation⟩

/-- Strengthening the existing kernel-step theorem: when the next claim is
accepted, its statement checks passed and its selected proof interface is
sufficient in the independent derivability judgment. -/
theorem kernelStep_accepts_interface {world next : World R}
    (reachable : Reachable world) (step : kernelStep world = some next)
    {claim : Claim R} (fresh : claim.id ∉ world.T) (accepted : claim.id ∈ next.T)
    (atHead : world.A = [] ∧ world.W.head? = some claim) {target : List Tm} :
    world.L.claimOk claim = true ∧
      ∃ hypotheses goal proof root used,
        claim.cbHyps = some hypotheses ∧ claim.goal = some goal ∧
        claim.translate = some (proof, root) ∧ claim.inferUsed = some used ∧
        claim.inferredInterface = some ⟨used, claim.usedOrigins used⟩ ∧
        Supports (P := presOf world.env claim.frame) hypotheses target used goal := by
  obtain ⟨admissionsEmpty, atHead⟩ := atHead
  unfold kernelStep at step
  rw [admissionsEmpty] at step
  cases pending : world.W with
  | nil => rw [pending] at atHead; cases atHead
  | cons actual rest =>
      rw [pending] at atHead step
      simp only [List.head?_cons, Option.some.injEq] at atHead
      subst actual
      simp only [Option.some.injEq] at step
      subst next
      have determined : EnvDetermined ({ world with A := [], W := rest } : World R).env := by
        exact reachable_rules_determined (w := world) reachable
      exact checkClaim_accepts_interface
        (world := { world with A := [], W := rest })
        determined fresh accepted

end Mettapedia.Logic.TierZero.Kernel2.AdmissionInterface
