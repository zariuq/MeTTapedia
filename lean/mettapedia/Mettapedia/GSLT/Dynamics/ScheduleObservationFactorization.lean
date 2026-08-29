import Mettapedia.GSLT.Core.ScheduleProgramFactorization
import Mettapedia.GSLT.Dynamics.ObservationPolicyFamilyUniversal

/-!
# Capability-indexed observations driving open schedules

This module connects the proof-relevant observation architecture to open
schedule programs.  An observation readout may drive a schedule exactly when
it retains every command and every possible next-state readout requested by
that schedule.  The condition is the least-sufficient policy-family criterion;
it does not require a scalar score, an additive carrier, a total order, or a
fairness proof.

Execution authority remains upstream.  The compiled schedule changes only
controller memory and occurrence order, while the branching system remains
the sole source of emissions and successors.  Exact finite-run commutation
therefore preserves the ordered event stream, live frontier, and resumable
controller view.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.ScheduleProgramFactorization

universe uState uExecution uScore uNode uAnswer uCommand

namespace CapabilityIndexedObservationArchitecture.SchedulerReadout

variable {State : Type uState}
variable {Execution : State -> State -> Type uExecution}
variable {architecture :
  CapabilityIndexedObservationArchitecture State Execution}
variable {Score : Type uScore}
variable {Node : Type uNode} {Answer : Type uAnswer}
variable {Command : Type uCommand}

/-- The complete family of present-command and future-update observations
requested by one open schedule program. -/
def scheduleFamily
    (view : architecture.SchedulerReadout Score)
    (program : Controller.Program Node Answer Command
      architecture.domain.Candidate) :
    PolicyFamily architecture.domain.Candidate :=
  ScheduleProgramFactorization.observationFamily program
    view.candidateReadout

/-- A semantic observation supports a schedule when it retains executable
runners for every command and update coordinate of the schedule. -/
def SupportsSchedule
    (view : architecture.SchedulerReadout Score)
    (program : Controller.Program Node Answer Command
      architecture.domain.Candidate) : Prop :=
  view.SupportsFamily (view.scheduleFamily program)

/-- Executable data witnessing that the semantic readout is sufficient for
the complete schedule program. -/
abbrev ScheduleRealization
    (view : architecture.SchedulerReadout Score)
    (program : Controller.Program Node Answer Command
      architecture.domain.Candidate) :=
  ScheduleProgramFactorization.Realization program view.candidateReadout

/-- Supporting an open schedule is exactly factorization onto its canonical
command-and-update vector. -/
theorem supportsSchedule_iff_vectorFactors
    (view : architecture.SchedulerReadout Score)
    (program : Controller.Program Node Answer Command
      architecture.domain.Candidate) :
    view.SupportsSchedule program <->
      NonFactorization.Factors view.candidateReadout
        (view.scheduleFamily program).vector :=
  view.supportsFamily_iff_vectorFactors (view.scheduleFamily program)

/-- The support proposition contains precisely an executable schedule
realization; it is not a Boolean admission flag. -/
theorem supportsSchedule_iff_nonempty_realization
    (view : architecture.SchedulerReadout Score)
    (program : Controller.Program Node Answer Command
      architecture.domain.Candidate) :
    view.SupportsSchedule program <->
      Nonempty (view.ScheduleRealization program) :=
  Iff.rfl

/-- Compile an admitted rich-memory schedule to the supported semantic
readout, retaining the authored open command type. -/
def ScheduleRealization.compile
    {view : architecture.SchedulerReadout Score}
    {program : Controller.Program Node Answer Command
      architecture.domain.Candidate}
    (realization : view.ScheduleRealization program) :
    Controller.Program Node Answer Command Score :=
  ScheduleProgramFactorization.Realization.compile realization

/-- Compiling through an admitted observation preserves every finite run
exactly after controller-memory readout. -/
theorem ScheduleRealization.compile_run_agrees
    {view : architecture.SchedulerReadout Score}
    {program : Controller.Program Node Answer Command
      architecture.domain.Candidate}
    (realization : view.ScheduleRealization program)
    (system : BranchingSystem Node Answer)
    (interpret : Command -> Scheduler Node)
    (fuel : Nat)
    (snapshot : InferenceControl.Snapshot Node Answer
      architecture.domain.Candidate) :
    ScheduleProgramFactorization.compressSnapshot view.candidateReadout
        (InferenceControl.Snapshot.run system
          (program.realize interpret) fuel snapshot) =
      InferenceControl.Snapshot.run system
        (realization.compile.realize interpret) fuel
        (ScheduleProgramFactorization.compressSnapshot
          view.candidateReadout snapshot) :=
  ScheduleProgramFactorization.compressSnapshot_run system program interpret
    view.candidateReadout realization fuel snapshot

end CapabilityIndexedObservationArchitecture.SchedulerReadout

/-! ## Positive and negative schedule controls -/

namespace ScheduleObservationFactorizationCanary

open CapabilityIndexedObservationArchitecture
open CapabilityIndexedObservationArchitecture.SchedulerReadout
open CapabilityIndexedObservationCanary

private def leftCandidate : provenanceArchitecture.domain.Candidate :=
  ⟨[Canary.Event.left, Canary.Event.right],
    ⟨[Canary.Event.left, Canary.Event.right], rfl⟩⟩

private def rightCandidate : provenanceArchitecture.domain.Candidate :=
  ⟨[Canary.Event.right, Canary.Event.left],
    ⟨[Canary.Event.right, Canary.Event.left], rfl⟩⟩

/-- A lossy length observation drives a schedule whose present and future
control depends only on length. -/
def lengthProgram :
    Controller.Program Unit Unit Nat
      provenanceArchitecture.domain.Candidate where
  initialMemory := leftCandidate
  command candidate := candidate.1.length
  advance candidate _ _ _ := candidate

def lengthProgramRealization :
    lengthScheduler.ScheduleRealization lengthProgram where
  run
    | .command => fun observed => ULift.up observed
    | .advance _ _ _ => fun observed => ULift.up observed
  agrees := by
    intro coordinate candidate
    cases coordinate <;> rfl

theorem lengthScheduler_supports_lengthProgram :
    lengthScheduler.SupportsSchedule lengthProgram :=
  ⟨lengthProgramRealization⟩

/-- Equal-length histories can require different order-sensitive commands. -/
def beginsLeftProgram :
    Controller.Program Unit Unit Bool
      provenanceArchitecture.domain.Candidate where
  initialMemory := leftCandidate
  command candidate := beginsLeft candidate.1
  advance candidate _ _ _ := candidate

/-- The length readout is refused for an order-sensitive schedule even though
it supports the length schedule over the same retained semantic candidates. -/
theorem lengthScheduler_refuses_beginsLeftProgram :
    Not (lengthScheduler.SupportsSchedule beginsLeftProgram) := by
  apply lengthScheduler.not_supportsFamily_of_policy_collision
      (lengthScheduler.scheduleFamily beginsLeftProgram)
      (first := leftCandidate) (second := rightCandidate) rfl
      (ScheduleProgramFactorization.Coordinate.command)
  change (ULift.up true : ULift Bool) ≠ ULift.up false
  decide

/-- Lossiness is relative to the requested schedule: one readout may support
one open program and correctly refuse another. -/
theorem lossy_readout_is_schedule_relative :
    lengthScheduler.Lossy /\
      lengthScheduler.SupportsSchedule lengthProgram /\
      Not (lengthScheduler.SupportsSchedule beginsLeftProgram) :=
  ⟨lengthScheduler_isLossy,
    lengthScheduler_supports_lengthProgram,
    lengthScheduler_refuses_beginsLeftProgram⟩

end ScheduleObservationFactorizationCanary

#print axioms CapabilityIndexedObservationArchitecture.SchedulerReadout.supportsSchedule_iff_vectorFactors
#print axioms CapabilityIndexedObservationArchitecture.SchedulerReadout.supportsSchedule_iff_nonempty_realization
#print axioms CapabilityIndexedObservationArchitecture.SchedulerReadout.ScheduleRealization.compile_run_agrees
#print axioms ScheduleObservationFactorizationCanary.lengthScheduler_supports_lengthProgram
#print axioms ScheduleObservationFactorizationCanary.lengthScheduler_refuses_beginsLeftProgram
#print axioms ScheduleObservationFactorizationCanary.lossy_readout_is_schedule_relative

end Mettapedia.GSLT.Dynamics
