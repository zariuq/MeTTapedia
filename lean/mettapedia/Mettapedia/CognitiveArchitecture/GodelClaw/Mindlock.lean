import Mettapedia.CognitiveArchitecture.GodelClaw.PolicyKernel

/-!
# GodelClaw Mindlock: Artifact State Machine

Lean formalization of the mindlock state machine from `vericore-policy/src/mindlock.rs`.

The mindlock is the trust boundary for artifact movement:
  In/Out/Work (staging) → PendingZar → Promoted
                        → Rejected

Terminal states (Promoted, Rejected) have no valid outgoing transitions.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Mindlock

/-! ## State Machine -/

/-- Mindlock stages, mapped from runtime directory names. -/
inductive Stage where
  | «in»       -- incoming artifacts
  | out        -- outgoing artifacts
  | work       -- revision working area
  | pendingZar -- awaiting human approval
  | rejected   -- security review rejected
  | promoted   -- approved and placed
  deriving DecidableEq

instance : Fintype Stage where
  elems := { .«in», .out, .work, .pendingZar, .rejected, .promoted }
  complete x := by cases x <;> simp

/-- Transition authorization. -/
inductive TransitionAuth where
  | reviewerAllow
  | reviewerRequestRevision
  | reviewerRequireZarApproval
  | reviewerReject
  | agentMove
  | zarApprove
  | zarReject
  deriving DecidableEq

/-- Is this a staging area? -/
def Stage.isStaging : Stage → Bool
  | .«in» | .out | .work => true
  | _ => false

/-- Is this a terminal state? -/
def Stage.isTerminal : Stage → Bool
  | .rejected | .promoted => true
  | _ => false

/-- Is this a valid source for artifact moves? -/
def Stage.isValidMoveSource : Stage → Bool
  | .«in» | .out | .work | .pendingZar => true
  | _ => false

/-- Valid state transition relation. -/
def validTransition : Stage → Stage → TransitionAuth → Bool
  -- Staging → Promoted via reviewer Allow
  | .«in»,  .promoted,   .reviewerAllow => true
  | .out,    .promoted,   .reviewerAllow => true
  | .work,   .promoted,   .reviewerAllow => true
  -- Staging → Work via reviewer RequestRevision
  | .«in»,  .work,       .reviewerRequestRevision => true
  | .out,    .work,       .reviewerRequestRevision => true
  | .work,   .work,       .reviewerRequestRevision => true
  -- Staging → PendingZar via reviewer RequireZarApproval
  | .«in»,  .pendingZar, .reviewerRequireZarApproval => true
  | .out,    .pendingZar, .reviewerRequireZarApproval => true
  | .work,   .pendingZar, .reviewerRequireZarApproval => true
  -- Staging → Rejected via reviewer Reject
  | .«in»,  .rejected,   .reviewerReject => true
  | .out,    .rejected,   .reviewerReject => true
  | .work,   .rejected,   .reviewerReject => true
  -- Agent moves between staging dirs
  | .«in»,  .out,        .agentMove => true
  | .out,    .«in»,      .agentMove => true
  | .«in»,  .work,       .agentMove => true
  | .out,    .work,       .agentMove => true
  | .work,   .«in»,      .agentMove => true
  | .work,   .out,        .agentMove => true
  -- Agent escalation to PendingZar
  | .«in»,  .pendingZar, .agentMove => true
  | .out,    .pendingZar, .agentMove => true
  | .work,   .pendingZar, .agentMove => true
  -- PendingZar exits via Zar
  | .pendingZar, .promoted, .zarApprove => true
  | .pendingZar, .rejected, .zarReject  => true
  -- Everything else
  | _, _, _ => false

/-! ## Key Properties -/

/-- Nothing can leave Rejected. -/
theorem rejected_is_terminal (to_ : Stage) (auth : TransitionAuth) :
    validTransition .rejected to_ auth = false := by
  cases to_ <;> cases auth <;> rfl

/-- Nothing can leave Promoted. -/
theorem promoted_is_terminal (to_ : Stage) (auth : TransitionAuth) :
    validTransition .promoted to_ auth = false := by
  cases to_ <;> cases auth <;> rfl

/-- Terminal states are not valid move sources. -/
theorem terminal_not_valid_move_source (s : Stage) (h : s.isTerminal = true) :
    s.isValidMoveSource = false := by
  cases s <;> simp [Stage.isTerminal, Stage.isValidMoveSource] at *

/-- Valid move sources are exactly staging ∪ {pendingZar}. -/
theorem valid_move_source_iff (s : Stage) :
    s.isValidMoveSource = true ↔ (s.isStaging = true ∨ s = .pendingZar) := by
  cases s <;> simp [Stage.isValidMoveSource, Stage.isStaging]

/-- Agent moves never reach terminal states. -/
theorem agent_move_stays_safe (from_ to_ : Stage)
    (h : validTransition from_ to_ .agentMove = true) :
    to_.isTerminal = false := by
  cases from_ <;> cases to_ <;> simp [validTransition, Stage.isTerminal] at *

/-- PendingZar can only exit via ZarApprove or ZarReject. -/
theorem pending_requires_zar (to_ : Stage) (auth : TransitionAuth)
    (h : validTransition .pendingZar to_ auth = true) :
    auth = .zarApprove ∨ auth = .zarReject := by
  cases to_ <;> cases auth <;> simp [validTransition] at *

/-- Staging → Promoted requires ReviewerAllow. -/
theorem staging_promote_requires_review (from_ : Stage) (auth : TransitionAuth)
    (hStaging : from_.isStaging = true)
    (hTrans : validTransition from_ .promoted auth = true) :
    auth = .reviewerAllow := by
  cases from_ <;> cases auth <;> simp [Stage.isStaging, validTransition] at *

/-! ## Cleanup eligibility -/

/-- An artifact is cleanup-eligible iff terminal and old enough. -/
def cleanupEligible (stage : Stage) (ageDays retentionDays : ℕ) : Bool :=
  stage.isTerminal && (ageDays ≥ retentionDays)

/-- Staging artifacts are never cleanup-eligible. -/
theorem staging_never_cleanup (s : Stage) (h : s.isStaging = true)
    (age ret : ℕ) : cleanupEligible s age ret = false := by
  cases s <;> simp [Stage.isStaging, cleanupEligible, Stage.isTerminal] at *

end Mettapedia.CognitiveArchitecture.GodelClaw.Mindlock
