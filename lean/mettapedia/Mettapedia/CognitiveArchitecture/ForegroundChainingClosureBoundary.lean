import Mettapedia.CognitiveArchitecture.ForegroundChainingActivationPolicy
import Mettapedia.GSLT.Dynamics.SpaceExecutionClosureBoundary

/-!
# Foreground chaining: activation versus closure

The background premise-service example already exposes its real given-clause
store as an activation policy.  This file gives that policy an exact selected
driver and carries the worked two-step execution through the generic closure
boundary.

The first activation consumes the premise supplied by a background service and
exposes the goal occurrence.  It is a valid step, but not closure.  The second
activation proves the goal and reaches an inspected quiescent store.  Thus
background assistance, one OS-style activation, and run-to-quiescence remain
three distinct facts over one foreground store.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ForegroundChainingClosureBoundary

open Mettapedia.CognitiveArchitecture.ForegroundChainingActivationPolicy
open Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
open Mettapedia.GSLT.Core.ClosureCriteria
open Mettapedia.GSLT.Core.GivenClauseLoop
open Mettapedia.GSLT.Core.OpenTotalityObservation
open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.GSLT.Dynamics.SpaceExecutionClosureBoundary

noncomputable section

/-- The exact breadth-first selector over the real foreground continuation
store.  Selection retains the chosen occurrence as both cause and receipt;
the target is the existing `Snapshot.tick`. -/
def foregroundDriver : ActivationDriver foregroundPolicy where
  State := Unit
  select snapshot _control :=
    match selected : snapshot.passive.selected snapshot.cursor with
    | none => none
    | some occurrence =>
        some
          { cause := .requested () occurrence
            target := Snapshot.tick chainingSystem Snapshot.breadthOnly snapshot
            receipt := occurrence
            nextControl := ()
            realized := ⟨selected, rfl, rfl⟩ }

/-- The admitted premise is the exact first selected activation. -/
theorem admitted_driver_step :
    foregroundDriver.toHostedDriver.step admittedSnapshot () =
      some (afterBridge, ()) :=
  rfl

/-- The first activation exposes the exact goal occurrence as the next
selected activation. -/
theorem bridge_driver_step :
    foregroundDriver.toHostedDriver.step afterBridge () =
      some (solvedSnapshot, ()) :=
  rfl

/-- The solved store has no remaining selected occurrence. -/
theorem solved_driver_quiescent :
    foregroundDriver.toHostedDriver.step solvedSnapshot () = none :=
  rfl

/-- One valid foreground activation is only a resumable prefix: the newly
exposed goal still has to run. -/
theorem one_activation_expires :
    foregroundDriver.toHostedDriver.runReport admittedSnapshot () 1 =
      .expired afterBridge () :=
  rfl

/-- Two activations reach the actual solved and inspected-quiescent store. -/
theorem two_activations_complete :
    foregroundDriver.toHostedDriver.runReport admittedSnapshot () 2 =
      .completed solvedSnapshot () :=
  rfl

def solvedClosure :
    ActivationDriver.FiniteClosure foregroundDriver admittedSnapshot () where
  fuel := 2
  target := solvedSnapshot
  finalControl := ()
  completed := two_activations_complete

/-- The closure witness retains both object-level policy reachability and
actual driver quiescence. -/
theorem solved_is_reachable_and_quiescent :
    (policyGSLT foregroundPolicy).MultiStep admittedSnapshot solvedSnapshot ∧
      foregroundDriver.toHostedDriver.step solvedSnapshot () = none :=
  ⟨solvedClosure.target_reachable, solvedClosure.target_quiescent⟩

def oneActivationObservation :
    ActivationDriver.RunObservation foregroundDriver ClauseOccurrence
      (fun _configuration _revision => False) :=
  foregroundDriver.observeBoundedRun [] admittedSnapshot () 1

def solvedObservation :
    ActivationDriver.RunObservation foregroundDriver ClauseOccurrence
      (fun _configuration _revision => False) :=
  foregroundDriver.observeBoundedRun [] admittedSnapshot () 2

/-- An empty answer prefix after consuming only the admitted premise is not a
refutation: the exact residual still exposes the goal activation. -/
theorem one_activation_empty_prefix_is_not_refutation :
    ¬ oneActivationObservation.EstablishesClosedAbsence := by
  rintro ⟨_empty, coverage, completion⟩
  cases completion

/-- A background service enables the real foreground run, but neither its
admission nor the first selected activation silently claims completion.  The
separately witnessed second activation reaches the exact goal receipt and a
quiescent store. -/
theorem background_assistance_enables_but_does_not_collapse_execution :
    admittedSnapshot.passive.live = [selectedOccurrenceAt 0] ∧
      foregroundPolicy.CanFire admittedSnapshot
        (.requested () (selectedOccurrenceAt 0)) ∧
      foregroundDriver.toHostedDriver.runReport admittedSnapshot () 1 =
        .expired afterBridge () ∧
      foregroundDriver.toHostedDriver.runReport admittedSnapshot () 2 =
        .completed solvedSnapshot () ∧
      solvedSnapshot.events =
        [⟨goalFrom (selectedOccurrenceAt 0), ProofResult.proved⟩] ∧
      foregroundDriver.toHostedDriver.step solvedSnapshot () = none := by
  exact ⟨admission_enables_but_does_not_execute.2.2.1,
    admission_enables_but_does_not_execute.2.2.2,
    one_activation_expires, two_activations_complete,
    background_premise_service_unblocks_foreground.2.2.2.1,
    solved_driver_quiescent⟩

/-- Negative control: extra execution demand at the stalled foreground cannot
manufacture the missing background service result. -/
theorem closure_demand_cannot_replace_background_service :
    Mettapedia.GSLT.Core.GivenClauseLoop.Snapshot.run chainingSystem
        Mettapedia.GSLT.Core.GivenClauseLoop.Snapshot.breadthOnly 2
        stalledSnapshot = stalledSnapshot ∧
      (Mettapedia.GSLT.Core.GivenClauseLoop.Snapshot.run chainingSystem
        Mettapedia.GSLT.Core.GivenClauseLoop.Snapshot.breadthOnly 2
        stalledSnapshot).events = [] :=
  foreground_fuel_cannot_replace_service

#print axioms admitted_driver_step
#print axioms bridge_driver_step
#print axioms solved_driver_quiescent
#print axioms one_activation_expires
#print axioms two_activations_complete
#print axioms solved_is_reachable_and_quiescent
#print axioms one_activation_empty_prefix_is_not_refutation
#print axioms background_assistance_enables_but_does_not_collapse_execution
#print axioms closure_demand_cannot_replace_background_service

end

end Mettapedia.CognitiveArchitecture.ForegroundChainingClosureBoundary
