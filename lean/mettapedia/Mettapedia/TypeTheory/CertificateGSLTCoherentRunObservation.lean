import Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
import Mettapedia.Coalgebra.CoherentPrefixTower

/-!
# Coherent open-ended observations of scheduled certificate search

A finite search receipt is useful only if later work resumes it rather than
silently restarting under a different history.  This module packages the
entire deterministic orbit of one branching system, scheduler, and initial
snapshot as a resumable trajectory.  Its observation at fuel `n` is the full
snapshot after `n` ticks: chronological events and the still-live frontier.

The trajectory laws say that observing `first + extra` ticks is exactly the
same as resuming the `first`-tick snapshot for `extra` ticks.  The canonical
trajectory is unique, its event lists grow by prefix, and completion makes its
tail constant.  Taking all finite prefixes of the snapshot stream then gives
an ordinary coherent prefix tower, so the established stream/tower
equivalence reconstructs the complete open-ended run.

The certificate-GSLT specialization retains each emitted
`ScheduledSearchNode`, including its proof-relevant occurrence history.  A
negative control exhibits two checked schedules with the same endpoint and
the same proof justification but different operational histories.  Endpoint
projection is therefore not faithful.  A second negative control shows that
an arbitrary family of snapshots is not a run: even a constant family fails
the resumption equation for a one-step system.

No completeness, Horn, first-order, higher-order, or termination assumption
is made.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CertificateGSLTCoherentRunObservation

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.Coalgebra.StreamFinality
open Mettapedia.Coalgebra.CoherentPrefixTower

universe uNode uAnswer

/-! ## Generic resumable trajectories -/

/-- A stream of finite snapshots belonging to one fixed system and scheduler,
with exact resumption from every observation boundary. -/
structure ResumableTrajectory
    {Node : Type uNode} {Answer : Type uAnswer}
    (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node)
    (start : Snapshot Node Answer) where
  observation : Stream (Snapshot Node Answer)
  at_zero : observation 0 = start
  resume : ∀ first extra,
    observation (first + extra) =
      run system scheduler extra (observation first)

namespace ResumableTrajectory

variable {Node : Type uNode} {Answer : Type uAnswer}
variable {system : BranchingSystem Node Answer}
variable {scheduler : Scheduler Node}
variable {start : Snapshot Node Answer}

/-- The actual finite executions form a resumable trajectory. -/
def canonical
    (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node)
    (start : Snapshot Node Answer) :
    ResumableTrajectory system scheduler start where
  observation fuel := run system scheduler fuel start
  at_zero := rfl
  resume := by
    intro first extra
    exact run_add system scheduler first extra start

/-- Every purported trajectory is pointwise the canonical finite execution. -/
theorem observation_eq_run
    (trajectory : ResumableTrajectory system scheduler start)
    (fuel : Nat) :
    trajectory.observation fuel = run system scheduler fuel start := by
  calc
    trajectory.observation fuel =
        run system scheduler fuel (trajectory.observation 0) := by
      simpa using trajectory.resume 0 fuel
    _ = run system scheduler fuel start := by rw [trajectory.at_zero]

@[ext]
theorem ext
    (first second : ResumableTrajectory system scheduler start)
    (observations : first.observation = second.observation) :
    first = second := by
  cases first
  cases second
  cases observations
  rfl

/-- Exact resumption and the initial snapshot determine a unique trajectory. -/
theorem eq_canonical
    (trajectory : ResumableTrajectory system scheduler start) :
    trajectory = canonical system scheduler start := by
  apply ext
  funext fuel
  exact observation_eq_run trajectory fuel

/-- Later observations only append chronological events. -/
theorem events_prefix_after_resume
    (trajectory : ResumableTrajectory system scheduler start)
    (first extra : Nat) :
    (trajectory.observation first).events.IsPrefix
      (trajectory.observation (first + extra)).events := by
  rw [trajectory.resume]
  exact events_prefix_run system scheduler extra
    (trajectory.observation first)

/-- A genuinely completed finite observation is stable under every later
resumption. -/
theorem observation_constant_after_completion
    (trajectory : ResumableTrajectory system scheduler start)
    (first extra : Nat)
    (complete : (trajectory.observation first).frontier = []) :
    trajectory.observation (first + extra) =
      trajectory.observation first := by
  rw [trajectory.resume]
  exact run_eq_self_of_frontier_nil system scheduler
    (trajectory.observation first) complete extra

/-- Soundness of the initial snapshot propagates to every finite
observation. -/
theorem sound
    (trajectory : ResumableTrajectory system scheduler start)
    (roots : List Node) (startSound : start.Sound system roots)
    (fuel : Nat) :
    (trajectory.observation fuel).Sound system roots := by
  rw [trajectory.observation_eq_run]
  exact sound_run system scheduler startSound fuel

/-- Every resumable trajectory supplies a coherent tower of its finite stream
prefixes. -/
def coherentTower
    (trajectory : ResumableTrajectory system scheduler start) :
    Tower (Snapshot Node Answer) :=
  Tower.ofStream trajectory.observation

/-- The complete coherent tower reconstructs the exact trajectory stream. -/
@[simp]
theorem toStream_coherentTower
    (trajectory : ResumableTrajectory system scheduler start) :
    Tower.toStream trajectory.coherentTower = trajectory.observation :=
  Tower.toStream_ofStream trajectory.observation

/-- Resumption remains visible after reconstruction from the coherent tower. -/
theorem reconstructed_resume
    (trajectory : ResumableTrajectory system scheduler start)
    (first extra : Nat) :
    Tower.toStream trajectory.coherentTower (first + extra) =
      run system scheduler extra
        (Tower.toStream trajectory.coherentTower first) := by
  simpa only [toStream_coherentTower] using trajectory.resume first extra

end ResumableTrajectory

/-! ## Certificate-GSLT scheduled search specialization -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory.CertificateGSLTScheduledHistory
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration
open Mettapedia.TypeTheory.CertificateGSLTFiniteSearchAcceleration.ScheduledSearchProfile

section Scheduled

variable {definition : ValidatedCalculusLanguageDef}

/-- The unique open-ended trajectory of one finite candidate profile and
scheduler. -/
def scheduledTrajectory
    (profile : ScheduledSearchProfile definition)
    (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots)) :
    ResumableTrajectory (branchingSystem profile roots) scheduler
      (initial [initialNode definition roots]) :=
  ResumableTrajectory.canonical _ _ _

/-- Its coherent tower retains every finite run snapshot. -/
def scheduledObservationTower
    (profile : ScheduledSearchProfile definition)
    (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots)) :
    Tower (Snapshot
      (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)) :=
  (scheduledTrajectory profile roots scheduler).coherentTower

@[simp]
theorem scheduledTrajectory_observation
    (profile : ScheduledSearchProfile definition)
    (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) :
    (scheduledTrajectory profile roots scheduler).observation fuel =
      run (branchingSystem profile roots) scheduler fuel
        (initial [initialNode definition roots]) :=
  rfl

/-- The coherent observation tower reconstructs the complete scheduled run
stream, not merely its endpoints. -/
theorem scheduledTower_recovers_runs
    (profile : ScheduledSearchProfile definition)
    (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots)) :
    Tower.toStream (scheduledObservationTower profile roots scheduler) =
      fun fuel =>
        run (branchingSystem profile roots) scheduler fuel
          (initial [initialNode definition roots]) := by
  exact ResumableTrajectory.toStream_coherentTower
    (scheduledTrajectory profile roots scheduler)

/-- Events in any earlier scheduled-search observation form a chronological
prefix of every later observation. -/
theorem scheduled_events_mono
    (profile : ScheduledSearchProfile definition)
    (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    {earlier later : Nat} (bounded : earlier ≤ later) :
    ((scheduledTrajectory profile roots scheduler).observation earlier).events.IsPrefix
      ((scheduledTrajectory profile roots scheduler).observation later).events := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bounded
  exact ResumableTrajectory.events_prefix_after_resume
    (scheduledTrajectory profile roots scheduler) earlier extra

/-- Every finite scheduled observation is sound relative to the selected
roots. -/
theorem scheduled_observation_sound
    (profile : ScheduledSearchProfile definition)
    (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat) :
    ((scheduledTrajectory profile roots scheduler).observation fuel).Sound
      (branchingSystem profile roots) [initialNode definition roots] := by
  apply ResumableTrajectory.sound
  exact initial_sound (branchingSystem profile roots)
    [initialNode definition roots]

/-- Every emitted event has a generated origin, retains that origin exactly,
and carries a checked semantic GSLT path from the selected roots. -/
theorem emitted_history_sound
    (profile : ScheduledSearchProfile definition)
    (roots : GoalState)
    (scheduler : Scheduler (ScheduledSearchNode definition roots))
    (fuel : Nat)
    {event : Emission
      (ScheduledSearchNode definition roots)
      (ScheduledSearchNode definition roots)}
    (member : event ∈
      ((scheduledTrajectory profile roots scheduler).observation fuel).events) :
    Generated (branchingSystem profile roots)
        [initialNode definition roots] event.origin ∧
      event.value = event.origin ∧
      (scheduledProofSearchGSLT definition).MultiStep
        roots event.value.state := by
  have historySound := ScheduledSearchProfile.emittedHistory_sound
    profile scheduler fuel member
  exact ⟨historySound.1, historySound.2,
    ScheduledSearchNode.semanticPath event.value⟩

end Scheduled

/-! ## Negative controls -/

namespace Canary

/-! ### Arbitrary snapshots need not form a resumable run -/

/-- A finite system whose only live node is consumed silently in one tick. -/
def oneStepSystem : BranchingSystem Bool Bool where
  emit _ := none
  successors _ := []

abbrev oneStepStart : Snapshot Bool Bool := initial [false]

/-- The constant raw family repeats the initial snapshot even after the live
node should have been consumed. -/
def constantRawObservation : Stream (Snapshot Bool Bool) :=
  fun _ => oneStepStart

@[simp]
theorem oneStep_run_one :
    run oneStepSystem Scheduler.breadthFirst 1 oneStepStart =
      (⟨[], []⟩ : Snapshot Bool Bool) :=
  rfl

/-- A raw family of finite snapshots is not automatically coherent under
execution resumption. -/
theorem constantRawObservation_not_resumable :
    ¬ ∃ trajectory : ResumableTrajectory oneStepSystem
        Scheduler.breadthFirst oneStepStart,
      trajectory.observation = constantRawObservation := by
  rintro ⟨trajectory, observationEquation⟩
  have resumed := trajectory.resume 0 1
  rw [congrFun observationEquation 1,
    congrFun observationEquation 0] at resumed
  change oneStepStart =
    run oneStepSystem Scheduler.breadthFirst 1 oneStepStart at resumed
  rw [oneStep_run_one] at resumed
  have frontierEquation := congrArg Snapshot.frontier resumed
  simp [oneStepStart, initial] at frontierEquation

/-! ### Endpoint erasure loses proof-relevant schedules -/

variable {definition : ValidatedCalculusLanguageDef}
variable {goal : Pattern} {ruleInstance : RuleInstance}

/-- Package the left-first complete schedule as a retained search node. -/
def leftNode
    (application : RuleApplication definition ruleInstance [] goal) :
    ScheduledSearchNode definition [goal, goal] where
  state := []
  history :=
    CertificateGSLTScheduledHistory.Canary.leftFirst application

/-- Package the right-first complete schedule as a retained search node. -/
def rightNode
    (application : RuleApplication definition ruleInstance [] goal) :
    ScheduledSearchNode definition [goal, goal] where
  state := []
  history :=
    CertificateGSLTScheduledHistory.Canary.rightFirst application

@[simp]
theorem parallel_nodes_same_endpoint
    (application : RuleApplication definition ruleInstance [] goal) :
    (leftNode application).state = (rightNode application).state :=
  rfl

/-- The nodes remain distinct because their operational focus histories are
distinct. -/
theorem leftNode_ne_rightNode
    (application : RuleApplication definition ruleInstance [] goal) :
    leftNode application ≠ rightNode application := by
  intro equal
  have traceEqual := congrArg
    (fun node : ScheduledSearchNode definition [goal, goal] =>
      focusTrace node.history)
    equal
  change focusTrace
      (CertificateGSLTScheduledHistory.Canary.leftFirst application) =
    focusTrace
      (CertificateGSLTScheduledHistory.Canary.rightFirst application)
    at traceEqual
  rw [CertificateGSLTScheduledHistory.Canary.leftFirst_focusTrace,
    CertificateGSLTScheduledHistory.Canary.rightFirst_focusTrace]
    at traceEqual
  cases traceEqual

/-- Endpoint projection is not faithful even for two schedules that finish at
the same obligation state. -/
theorem state_projection_not_injective
    (application : RuleApplication definition ruleInstance [] goal) :
    ¬ Function.Injective
      (fun node : ScheduledSearchNode definition [goal, goal] => node.state) := by
  intro injective
  exact leftNode_ne_rightNode application
    (injective (parallel_nodes_same_endpoint application))

/-- The lost distinction is schedule, not proof justification: both nodes
replay to the same checked derivation forest. -/
theorem parallel_nodes_same_justification
    (application : RuleApplication definition ruleInstance [] goal) :
    SameJustification (leftNode application).history
      (rightNode application).history :=
  by
    change SameJustification
      (CertificateGSLTScheduledHistory.Canary.leftFirst application)
      (CertificateGSLTScheduledHistory.Canary.rightFirst application)
    exact
      CertificateGSLTScheduledHistory.Canary.leftFirst_sameJustification_rightFirst
        application

end Canary

/-! ## Audited theorem crowns -/

#print axioms ResumableTrajectory.observation_eq_run
#print axioms ResumableTrajectory.eq_canonical
#print axioms ResumableTrajectory.events_prefix_after_resume
#print axioms ResumableTrajectory.observation_constant_after_completion
#print axioms ResumableTrajectory.toStream_coherentTower
#print axioms ResumableTrajectory.reconstructed_resume
#print axioms scheduledTower_recovers_runs
#print axioms scheduled_events_mono
#print axioms scheduled_observation_sound
#print axioms emitted_history_sound
#print axioms Canary.constantRawObservation_not_resumable
#print axioms Canary.state_projection_not_injective
#print axioms Canary.parallel_nodes_same_justification

end Mettapedia.TypeTheory.CertificateGSLTCoherentRunObservation
