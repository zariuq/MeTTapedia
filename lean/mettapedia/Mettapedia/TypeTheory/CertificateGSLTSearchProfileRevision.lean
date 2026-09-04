import Mettapedia.TypeTheory.CertificateGSLTSearchAuthorityBoundary

/-!
# Revision of certificate-search profiles

Exact resumption belongs to one fixed branching system.  Revising a
certificate-search profile changes that system's successor map, so an old
closed frontier cannot discover newly offered candidates merely by running
again: every branching runner leaves an empty frontier fixed.

This module compares three revision mechanisms.

* Naive resumption preserves the old closed snapshot and misses every added
  candidate.
* Prefix-preserving restart retains the event history and reseeds the root.
  It is sound, but re-emits already observed nodes and can duplicate logical
  evidence operationally.
* Certified delta reopening retains the old event history and enqueues only
  explicitly added checked successors of previously observed nodes.  Under a
  monotone profile refinement, the migrated snapshot is sound for the revised
  search system.

The delta interface is an acceleration boundary, not a completeness claim.
A separate coverage theorem is still required before a revised closed search
can establish negative logical information.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.TypeTheory.CertificateGSLTScheduledHistory
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile
open Mettapedia.TypeTheory.CertificateGSLTCoherentRunObservation
open Mettapedia.TypeTheory.CertificateGSLTSearchAuthorityBoundary

noncomputable section

/-! ## Fixed-profile resumption versus authority revision -/

/-- An empty frontier remains fixed even if the successor authority is
replaced by an arbitrary new candidate profile.  A closed snapshot therefore
contains no resumable work for discovering profile additions. -/
theorem closed_snapshot_stuck_under_profile_revision
    {definition : ValidatedCalculusLanguageDef}
    (revised : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots))
    (closed : snapshot.frontier = []) (fuel : Nat) :
    run (branchingSystem revised roots) scheduler fuel snapshot = snapshot :=
  run_eq_self_of_frontier_nil (branchingSystem revised roots) scheduler
    snapshot closed fuel

/-! ## Prefix-preserving restart -/

/-- Retain the complete old event prefix while reseeding the initial root.
This restarts exploration without discarding audit history. -/
def prefixPreservingRestart
    {definition : ValidatedCalculusLanguageDef} {roots : GoalState}
    (snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :
    Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots) where
  events := snapshot.events
  frontier := [initialNode definition roots]

@[simp] theorem prefixPreservingRestart_events
    {definition : ValidatedCalculusLanguageDef} {roots : GoalState}
    (snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :
    (prefixPreservingRestart snapshot).events = snapshot.events :=
  rfl

@[simp] theorem prefixPreservingRestart_frontier
    {definition : ValidatedCalculusLanguageDef} {roots : GoalState}
    (snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :
    (prefixPreservingRestart snapshot).frontier =
      [initialNode definition roots] :=
  rfl

/-- Every revised execution extends the retained old event prefix. -/
theorem prefix_restart_retains_events
    {definition : ValidatedCalculusLanguageDef}
    (revised : ScheduledSearchProfile definition) (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) (fuel : Nat) :
    snapshot.events.IsPrefix
      (run (branchingSystem revised roots) scheduler fuel
        (prefixPreservingRestart snapshot)).events := by
  simpa using events_prefix_run (branchingSystem revised roots) scheduler fuel
    (prefixPreservingRestart snapshot)

/-- The first breadth-first restart tick re-emits the root after the retained
event prefix.  This is exact and independent of which revised successors are
offered. -/
theorem prefix_restart_first_tick_events
    {definition : ValidatedCalculusLanguageDef}
    (revised : ScheduledSearchProfile definition) (roots : GoalState)
    (snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :
    (run (branchingSystem revised roots) Scheduler.breadthFirst 1
      (prefixPreservingRestart snapshot)).events =
        snapshot.events ++
          [⟨initialNode definition roots, initialNode definition roots⟩] :=
  rfl

/-- The empty profile monotonically refines to every candidate profile. -/
theorem empty_refines
    {definition : ValidatedCalculusLanguageDef}
    (later : ScheduledSearchProfile definition) :
    (empty definition).Refines later := by
  intro source candidate member
  simp [empty] at member

/-- A prefix-preserving restart is sound under a monotone profile revision.
Old events retain their generated origins, and the reseeded root is generated
by definition. -/
theorem prefixPreservingRestart_sound
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition}
    (refines : earlier.Refines later) (roots : GoalState)
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (sound : snapshot.Sound (branchingSystem earlier roots)
      [initialNode definition roots]) :
    (prefixPreservingRestart snapshot).Sound
      (branchingSystem later roots) [initialNode definition roots] := by
  constructor
  · intro node member
    simp only [prefixPreservingRestart_frontier, List.mem_singleton] at member
    subst node
    exact .root (by simp)
  · intro event member
    have valid := sound.2 event member
    exact ⟨generated_mono refines valid.1, by
      simpa [branchingSystem] using valid.2⟩

/-! ## Certified delta reopening -/

/-- One newly offered checked successor of a node that occurred in the old
snapshot.  Absence from the earlier profile and presence in the later profile
are retained independently. -/
structure RevisionAddition
    {definition : ValidatedCalculusLanguageDef}
    (earlier later : ScheduledSearchProfile definition) (roots : GoalState)
    (snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) where
  parentEvent : Emission (ScheduledSearchNode definition roots)
    (ScheduledSearchNode definition roots)
  observed : parentEvent ∈ snapshot.events
  candidate : ScheduledCandidate definition parentEvent.value.state
  absentEarlier : candidate ∉ earlier.candidates parentEvent.value.state
  offeredLater : candidate ∈ later.candidates parentEvent.value.state

namespace RevisionAddition

/-- The newly activated child retains its parent's complete checked history. -/
def child
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (addition : RevisionAddition earlier later roots snapshot) :
    ScheduledSearchNode definition roots :=
  addition.parentEvent.value.extend addition.candidate

@[simp] theorem child_state
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (addition : RevisionAddition earlier later roots snapshot) :
    addition.child.state = addition.candidate.target :=
  rfl

end RevisionAddition

/-- A finite revision batch records monotonicity and rejects duplicate child
nodes.  It need not claim that every addition has been enumerated. -/
structure RevisionBatch
    {definition : ValidatedCalculusLanguageDef}
    (earlier later : ScheduledSearchProfile definition) (roots : GoalState)
    (snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) where
  refines : earlier.Refines later
  additions : List (RevisionAddition earlier later roots snapshot)
  childrenNodup : (additions.map RevisionAddition.child).Nodup

/-- Reopen exactly the certified added children while preserving the old
event prefix byte-for-byte at the mathematical list level. -/
def reopenWithDelta
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (batch : RevisionBatch earlier later roots snapshot) :
    Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots) where
  events := snapshot.events
  frontier := batch.additions.map RevisionAddition.child

@[simp] theorem reopenWithDelta_events
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (batch : RevisionBatch earlier later roots snapshot) :
    (reopenWithDelta batch).events = snapshot.events :=
  rfl

@[simp] theorem reopenWithDelta_frontier
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (batch : RevisionBatch earlier later roots snapshot) :
    (reopenWithDelta batch).frontier =
      batch.additions.map RevisionAddition.child :=
  rfl

/-- A nonempty certified delta reopens a genuinely live frontier. -/
theorem reopenWithDelta_live
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (batch : RevisionBatch earlier later roots snapshot)
    (nonempty : batch.additions ≠ []) :
    (reopenWithDelta batch).frontier ≠ [] := by
  simp [reopenWithDelta, nonempty]

/-- A sound old event identifies a node generated under the old profile. -/
theorem event_value_generated_of_sound
    {definition : ValidatedCalculusLanguageDef}
    {profile : ScheduledSearchProfile definition} {roots : GoalState}
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (sound : snapshot.Sound (branchingSystem profile roots)
      [initialNode definition roots])
    {event : Emission (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (member : event ∈ snapshot.events) :
    Generated (branchingSystem profile roots)
      [initialNode definition roots] event.value := by
  have valid := sound.2 event member
  have same : event.origin = event.value := by
    simpa [branchingSystem] using valid.2
  exact same ▸ valid.1

/-- Delta reopening is sound for the revised branching system.  The proof
uses profile monotonicity for old events and explicit later-profile membership
for every newly activated child. -/
theorem reopenWithDelta_sound
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (sound : snapshot.Sound (branchingSystem earlier roots)
      [initialNode definition roots])
    (batch : RevisionBatch earlier later roots snapshot) :
    (reopenWithDelta batch).Sound
      (branchingSystem later roots) [initialNode definition roots] := by
  constructor
  · intro child member
    rcases List.mem_map.mp member with ⟨addition, inBatch, childEquality⟩
    subst child
    exact .successor
      (generated_mono batch.refines
        (event_value_generated_of_sound sound addition.observed))
      (extend_mem_successors later addition.parentEvent.value
        addition.candidate addition.offeredLater)
  · intro event member
    have valid := sound.2 event member
    exact ⟨generated_mono batch.refines valid.1, by
      simpa [branchingSystem] using valid.2⟩

/-- Revised execution extends the old prefix after a delta migration. -/
theorem delta_reopen_retains_events
    {definition : ValidatedCalculusLanguageDef}
    {earlier later : ScheduledSearchProfile definition} {roots : GoalState}
    {snapshot : Snapshot (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (batch : RevisionBatch earlier later roots snapshot)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) :
    snapshot.events.IsPrefix
      (run (branchingSystem later roots) scheduler fuel
        (reopenWithDelta batch)).events := by
  simpa using events_prefix_run (branchingSystem later roots) scheduler fuel
    (reopenWithDelta batch)

/-! ## Empty-to-singleton revision canary -/

namespace Canary

variable {definition : ValidatedCalculusLanguageDef}
variable {goal : Pattern} {ruleInstance : RuleInstance}

abbrev rootEvent : Emission (ScheduledSearchNode definition [goal])
    (ScheduledSearchNode definition [goal]) :=
  ⟨initialNode definition [goal], initialNode definition [goal]⟩

/-- The old sound-but-incomplete profile closes after emitting its root. -/
def oldClosedSnapshot (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) :
    Snapshot (ScheduledSearchNode definition [goal])
      (ScheduledSearchNode definition [goal]) :=
  { events := [rootEvent]
    frontier := [] }

theorem oldClosedSnapshot_eq
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    oldClosedSnapshot definition goal =
      { events := [rootEvent]
        frontier := [] } :=
  rfl

/-- The canonical closed snapshot is exactly the first observation of the
empty candidate profile.  Its literal representation is therefore not an
invented test artifact. -/
theorem oldClosedSnapshot_eq_observation
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    oldClosedSnapshot definition goal =
      (scheduledTrajectory (empty definition) [goal]
        Scheduler.breadthFirst).observation 1 := by
  rw [scheduledTrajectory_observation,
    ScheduledSearchProfile.Canary.empty_run_successor ([goal] : GoalState) 0]
  rfl

theorem oldClosedSnapshot_closed
    (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    (oldClosedSnapshot definition goal).frontier = [] := by
  rw [oldClosedSnapshot_eq]

/-- The revised profile adds exactly the checked zero-premise occurrence. -/
def revisedProfile
    (application : RuleApplication definition ruleInstance [] goal) :
    ScheduledSearchProfile definition :=
  singletonOccurrence
    (CertificateGSLTScheduledHistory.Canary.sole application)

/-- Naively running the revised system from the old closed snapshot remains
stuck forever. -/
theorem naive_resume_misses_added_candidate
    (application : RuleApplication definition ruleInstance [] goal)
    (fuel : Nat) :
    run (branchingSystem (revisedProfile application) [goal])
        Scheduler.breadthFirst fuel (oldClosedSnapshot definition goal) =
      oldClosedSnapshot definition goal :=
  closed_snapshot_stuck_under_profile_revision
    (revisedProfile application) [goal] Scheduler.breadthFirst
    (oldClosedSnapshot definition goal)
    (oldClosedSnapshot_closed definition goal) fuel

/-- Prefix-preserving restart is sound but emits the already retained root a
second time on its first revised tick. -/
theorem prefix_restart_duplicates_root
    (application : RuleApplication definition ruleInstance [] goal) :
    (run (branchingSystem (revisedProfile application) [goal])
      Scheduler.breadthFirst 1
      (prefixPreservingRestart (oldClosedSnapshot definition goal))).events =
        [rootEvent, rootEvent] := by
  rw [prefix_restart_first_tick_events, oldClosedSnapshot_eq]
  rfl

/-- The sole new candidate, tied to the retained root occurrence. -/
def soleAddition
    (application : RuleApplication definition ruleInstance [] goal) :
    RevisionAddition (empty definition) (revisedProfile application) [goal]
      (oldClosedSnapshot definition goal) where
  parentEvent := rootEvent
  observed := by rw [oldClosedSnapshot_eq]; simp
  candidate := ScheduledCandidate.mk []
    (CertificateGSLTScheduledHistory.Canary.sole application)
  absentEarlier := by simp [empty]
  offeredLater := singletonOccurrence_offers
    (CertificateGSLTScheduledHistory.Canary.sole application)

/-- The one-addition batch has no duplicate child nodes. -/
def soleBatch
    (application : RuleApplication definition ruleInstance [] goal) :
    RevisionBatch (empty definition) (revisedProfile application) [goal]
      (oldClosedSnapshot definition goal) where
  refines := empty_refines (revisedProfile application)
  additions := [soleAddition application]
  childrenNodup := by simp

/-- The delta migration preserves the single old root event and reopens only
the newly checked complete child. -/
theorem sole_delta_snapshot_eq
    (application : RuleApplication definition ruleInstance [] goal) :
    reopenWithDelta (soleBatch application) =
      { events := [rootEvent]
        frontier :=
          [(initialNode definition [goal]).extend
            (ScheduledCandidate.mk []
              (CertificateGSLTScheduledHistory.Canary.sole application))] } :=
  rfl

/-- One revised tick emits the new complete child without re-emitting the
root. -/
theorem delta_reopen_emits_complete_child
    (application : RuleApplication definition ruleInstance [] goal) :
    let occurrence := CertificateGSLTScheduledHistory.Canary.sole application
    let path : ScheduledProofSearchPath definition [goal] [] :=
      .cons occurrence (.refl [])
    (⟨(initialNode definition [goal]).follow path,
        (initialNode definition [goal]).follow path⟩ :
      Emission (ScheduledSearchNode definition [goal])
        (ScheduledSearchNode definition [goal])) ∈
      (run (branchingSystem (revisedProfile application) [goal])
        Scheduler.breadthFirst 1
        (reopenWithDelta (soleBatch application))).events := by
  dsimp only
  rw [sole_delta_snapshot_eq]
  simp only [run]
  let occurrence := CertificateGSLTScheduledHistory.Canary.sole application
  let child : ScheduledSearchNode definition [goal] :=
    (initialNode definition [goal]).extend
      (ScheduledCandidate.mk [] occurrence)
  have selectedChild :
      selected Scheduler.breadthFirst [child] = some child :=
    rfl
  have emitted :
      (⟨child, child⟩ : Emission (ScheduledSearchNode definition [goal])
        (ScheduledSearchNode definition [goal])) ∈
        (tick (branchingSystem (revisedProfile application) [goal])
          Scheduler.breadthFirst
          { events := [rootEvent]
            frontier := [child] }).events :=
    event_mem_tick_of_selected
      (branchingSystem (revisedProfile application) [goal])
      Scheduler.breadthFirst
      { events := [rootEvent]
        frontier := [child] }
      selectedChild rfl
  have followed :
      (initialNode definition [goal]).follow
          (.cons occurrence (.refl [])) = child := by
    rfl
  change
    (⟨(initialNode definition [goal]).follow
          (.cons occurrence (.refl [])),
        (initialNode definition [goal]).follow
          (.cons occurrence (.refl []))⟩ :
      Emission (ScheduledSearchNode definition [goal])
        (ScheduledSearchNode definition [goal])) ∈
      (tick (branchingSystem (revisedProfile application) [goal])
        Scheduler.breadthFirst
        { events := [rootEvent]
          frontier := [child] }).events
  rw [followed]
  exact emitted

/-- The discriminator's complete first revised prefix is exact: the retained
root occurs once and the newly activated child occurs once. -/
theorem delta_reopen_first_tick_events
    (application : RuleApplication definition ruleInstance [] goal) :
    let occurrence := CertificateGSLTScheduledHistory.Canary.sole application
    let child : ScheduledSearchNode definition [goal] :=
      (initialNode definition [goal]).extend
        (ScheduledCandidate.mk [] occurrence)
    (run (branchingSystem (revisedProfile application) [goal])
      Scheduler.breadthFirst 1
      (reopenWithDelta (soleBatch application))).events =
        [rootEvent, ⟨child, child⟩] := by
  dsimp only
  rw [sole_delta_snapshot_eq]
  rfl

/-- The newly emitted child is visible as the original checked axiom
derivation. -/
theorem delta_reopen_establishes_axiom
    (application : RuleApplication definition ruleInstance [] goal) :
    let derivations :=
      CertificateGSLTSearchAuthorityBoundary.Canary.axiomDerivations application
    derivations ∈ completedDerivations
      (run (branchingSystem (revisedProfile application) [goal])
        Scheduler.breadthFirst 1
        (reopenWithDelta (soleBatch application))) := by
  let occurrence := CertificateGSLTScheduledHistory.Canary.sole application
  let path : ScheduledProofSearchPath definition [goal] [] :=
    .cons occurrence (.refl [])
  have emitted := delta_reopen_emits_complete_child application
  have observed := completedDerivation_mem_of_complete_emission path emitted
  simpa [path, occurrence,
    CertificateGSLTSearchAuthorityBoundary.Canary.axiomDerivations,
    CertificateGSLTScheduledHistory.Canary.sole_prepend_nil,
    scheduledPathToDerivationList,
    scheduledPathPrependDerivations] using observed

/-- The one-addition migrated snapshot is sound under the revised profile. -/
theorem sole_delta_snapshot_sound
    (application : RuleApplication definition ruleInstance [] goal) :
    (reopenWithDelta (soleBatch application)).Sound
      (branchingSystem (revisedProfile application) [goal])
      [initialNode definition [goal]] := by
  apply reopenWithDelta_sound
  rw [oldClosedSnapshot_eq_observation]
  exact scheduled_observation_sound (empty definition) [goal]
    Scheduler.breadthFirst 1

end Canary

/-! ## Audited theorem crowns -/

#print axioms closed_snapshot_stuck_under_profile_revision
#print axioms prefix_restart_retains_events
#print axioms prefix_restart_first_tick_events
#print axioms prefixPreservingRestart_sound
#print axioms reopenWithDelta_live
#print axioms event_value_generated_of_sound
#print axioms reopenWithDelta_sound
#print axioms delta_reopen_retains_events
#print axioms Canary.naive_resume_misses_added_candidate
#print axioms Canary.prefix_restart_duplicates_root
#print axioms Canary.delta_reopen_emits_complete_child
#print axioms Canary.delta_reopen_first_tick_events
#print axioms Canary.delta_reopen_establishes_axiom
#print axioms Canary.sole_delta_snapshot_sound

end

end Mettapedia.TypeTheory.CertificateGSLTSearchProfileRevision
