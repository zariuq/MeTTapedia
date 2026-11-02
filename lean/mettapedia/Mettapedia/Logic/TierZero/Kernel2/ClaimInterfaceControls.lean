import Mettapedia.Logic.TierZero.Kernel2.ClaimInterface
import Mettapedia.Logic.TierZero.Kernel2.AdmissionLocalControl

/-!
# Controls for inferred claim obligations

The controls distinguish the three hypothesis regions and preserve authored
premise positions across side conditions. They also apply the sufficiency
theorem to the accepted local-assumption example.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2.ClaimInterfaceControls

open Mettapedia.Logic.TierZero.ProofInterface
open Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins.LocalControl

theorem local_obligation_is_visible :
    localClaim.inferredInterface = some
      { used := {0}, origins := {.localDecl 0} } := by decide

def termClaim : Claim String :=
  ⟨"term", [], [], [], [], [], pjd "goal" [], [(17, psym "datum")],
    [⟨0, "uses-term", [.term 17]⟩], .node 0⟩

theorem cited_term_obligation_is_visible :
    termClaim.inferredInterface = some
      { used := {0}, origins := {.term 0} } := by decide

/-- Source premise 0 is a side condition. The proof cites source premise 2,
which is position 1 in the checker's judgment-hypothesis list. -/
def sourcePositionClaim : Claim String :=
  ⟨"position", [], [],
    [.differ (psym "a") (psym "b"), .judg (pjd "p" [psym "a"]),
      .judg (pjd "q" [psym "b"])],
    [], [], pjd "goal" [], [], [⟨0, "uses-hyp", [.hyp 2]⟩], .node 0⟩

theorem authored_judgment_position_is_retained :
    sourcePositionClaim.inferredInterface = some
      { used := {1}, origins := {.judgment 2} } := by decide

def localEnv : Env String := envOf [("from-object", fromObject)]

theorem localEnv_determined : EnvDetermined localEnv := by
  intro name rule found
  unfold localEnv envOf at found
  simp only [List.lookup_cons, List.lookup_nil] at found
  split at found
  · simp only [Option.some.injEq] at found
    subst rule
    decide
  · cases found

theorem localClaim_checked : localClaim.verdict localEnv localEnv_determined = true := by decide

/-- The accepted proof cannot be generalized by looking only at its closed
conclusion: its inferred interface contains the local premise. -/
theorem accepted_local_claim_retains_its_assumption :
    ∃ hypotheses goal proof root used,
      localClaim.cbHyps = some hypotheses ∧ localClaim.goal = some goal ∧
      localClaim.translate = some (proof, root) ∧ localClaim.inferUsed = some used ∧
      localClaim.inferredInterface = some ⟨used, localClaim.usedOrigins used⟩ ∧
      Supports (P := presOf localEnv localClaim.frame) hypotheses [] used goal :=
  Claim.verdict_interface (target := []) localClaim_checked

end Mettapedia.Logic.TierZero.Kernel2.ClaimInterfaceControls
