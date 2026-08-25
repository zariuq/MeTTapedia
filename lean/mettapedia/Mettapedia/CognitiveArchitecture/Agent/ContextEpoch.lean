import Mettapedia.CognitiveArchitecture.Agent.WorldState

/-!
# Atomic context epochs

Source provenance: adapted from GödelClaw commit
`25e339eb66a5447bdaaa735ef9f3bee745b8957d`; only module packaging and
taxonomy-facing names were changed during integration.

A model-visible coding context is meaningful only relative to the operational
workspace and source revisions from which it was built.  Those coordinates
must move together.  In particular, instruction scope must not be resolved
against an implicit process working directory while the view describes a
different task workspace.

This file treats a context epoch as one product value.  A completed refresh
replaces the whole product; failure, interruption, or absence of a completed
candidate leaves the previous epoch live.  Source discovery and compaction are
replaceable policies outside this transition.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.ContextEpoch

open Mettapedia.CognitiveArchitecture.Agent.WorldState

/-- One model-visible context and the exact references under which it was
constructed.  The commitment field is a protected projection, not the
authoritative commitment store. -/
structure Epoch
    (Workspace OperationalRevision InstructionRevision
      CommitmentProjection View : Type*) where
  sequence : Nat
  workspace : Workspace
  operationalRevision : OperationalRevision
  instructionRevision : InstructionRevision
  commitments : CommitmentProjection
  view : View
deriving Repr, DecidableEq

/-- A refresh either produces one complete candidate epoch or fails before
promotion. -/
inductive Refresh (EpochType : Type*) where
  | success (next : EpochType)
  | failure
deriving Repr, DecidableEq

/-- The atomic promotion boundary. -/
def promote (live : EpochType) : Refresh EpochType → EpochType
  | .success next => next
  | .failure => live

@[simp] theorem successful_refresh_replaces_epoch
    (live next : EpochType) :
    promote live (.success next) = next := by
  rfl

@[simp] theorem failed_refresh_preserves_epoch (live : EpochType) :
    promote live .failure = live := by
  rfl

/-- Promotion cannot synthesize a torn mixture: the result is exactly the old
epoch or exactly the completed candidate. -/
theorem promotion_is_atomic (live : EpochType) (refresh : Refresh EpochType) :
    promote live refresh = live ∨
      ∃ next, refresh = .success next ∧ promote live refresh = next := by
  cases refresh with
  | failure => exact Or.inl rfl
  | success next => exact Or.inr ⟨next, rfl, rfl⟩

/-- Workspace and instruction revision are installed from the same successful
candidate, rather than from independently mutable fields. -/
theorem successful_refresh_binds_workspace_and_instructions
    (live next :
      Epoch Workspace OperationalRevision InstructionRevision
        CommitmentProjection View) :
    (promote live (.success next)).workspace = next.workspace ∧
      (promote live (.success next)).instructionRevision =
        next.instructionRevision := by
  exact ⟨rfl, rfl⟩

/-- A failed refresh cannot silently drop protected commitment context. -/
theorem failed_refresh_preserves_commitment_projection
    (live :
      Epoch Workspace OperationalRevision InstructionRevision
        CommitmentProjection View) :
    (promote live .failure).commitments = live.commitments := by
  rfl

/-- Inability to obtain a completed epoch preserves the last-known live
epoch.  `observed none` here means that no complete epoch was produced; source-
local deletion is handled before epoch construction. -/
def promoteObservation (live : EpochType) :
    SourceObservation EpochType → EpochType
  | .unavailable => live
  | .observed none => live
  | .observed (some next) => next

@[simp] theorem unavailable_epoch_stutters (live : EpochType) :
    promoteObservation live .unavailable = live := by
  rfl

@[simp] theorem incomplete_epoch_stutters (live : EpochType) :
    promoteObservation live (.observed none) = live := by
  rfl

@[simp] theorem completed_epoch_promotes (live next : EpochType) :
    promoteObservation live (.observed (some next)) = next := by
  rfl

/-- A context request carries the epoch as one value.  Consumers may project
coordinates, but cannot receive a workspace from one epoch and a view from
another through this constructor. -/
structure Request (EpochType Payload : Type*) where
  epoch : EpochType
  payload : Payload
deriving Repr, DecidableEq

def prepare (epoch : EpochType) (payload : Payload) : Request EpochType Payload :=
  ⟨epoch, payload⟩

@[simp] theorem prepared_request_uses_exact_epoch
    (epoch : EpochType) (payload : Payload) :
    (prepare epoch payload).epoch = epoch := by
  rfl

end Mettapedia.CognitiveArchitecture.Agent.ContextEpoch

#print axioms Mettapedia.CognitiveArchitecture.Agent.ContextEpoch.promotion_is_atomic
#print axioms Mettapedia.CognitiveArchitecture.Agent.ContextEpoch.successful_refresh_binds_workspace_and_instructions
#print axioms Mettapedia.CognitiveArchitecture.Agent.ContextEpoch.failed_refresh_preserves_commitment_projection
