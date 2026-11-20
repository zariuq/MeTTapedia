import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentCanonicalDiamond
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentExecutedSwapMaps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunTripleAdmission

/-!
# The two complete three-exchange routes of actual dependent executions

The existing all-faces admission cell supplies all six residual schedules.
Every adjacent comparison is built from the actual admitted orders and
canonical helper diamond. Both routes reverse the three events and have
the same complete endpoint comparison, including every helper projection.
Equality of the raw free-groupoid certificates is not asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open BlockTriple DependentRun Transport.RunRearrangement

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {state : State rules O}
  {first second third : HelperFiring levels O state}

noncomputable def exchangeFirst
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule second first third) :
    Cell (helperTransport levels O) one.run two.run :=
  (diamond_of_admitted_orders first second one.firstAccepted two.firstAccepted
    one.secondAccepted two.secondAccepted).cellThree third one.thirdAccepted

noncomputable def exchangeLast
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule first third second) :
    Cell (helperTransport levels O) one.run two.run :=
  lastCell first second third one.firstAccepted
    (diamond_of_admitted_orders (helperResidual first one.firstAccepted second)
      (helperResidual first one.firstAccepted third) one.secondAccepted two.secondAccepted
      one.thirdAccepted two.thirdAccepted)

theorem exchangeFirst_frame
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule second first third) :
    (RunStateGroupoid.endpointMap levels O (exchangeFirst one two)).frame.hom =
      iteratedSwapFirst second.helpers first.helpers third.helpers :=
  Diamond.cellThree_frame _ _ _

theorem exchangeLast_frame
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule first third second) :
    (RunStateGroupoid.endpointMap levels O (exchangeLast one two)).frame.hom =
      iteratedSwapLast first.helpers third.helpers second.helpers :=
  lastCell_frame _ _ _ _ _

theorem exchangeFirst_event
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule second first third) (event : Fin one.run.word.length) :
    (events (helperTransport levels O) (exchangeFirst one two) event).val = ProofRelevantRuns.swapAt 0 event.val :=
  Diamond.three_event_positions
    (diamond_of_admitted_orders first second one.firstAccepted two.firstAccepted
      one.secondAccepted two.secondAccepted) third one.thirdAccepted event

theorem exchangeLast_event
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule first third second) (event : Fin one.run.word.length) :
    (events (helperTransport levels O) (exchangeLast one two) event).val = ProofRelevantRuns.swapAt 1 event.val :=
  lastCell_events _ _ _ _ _ event

variable (schedules : (helperTransport levels O).SixSchedules first second third)

noncomputable def leftRoute : Cell (helperTransport levels O) schedules.abc.run schedules.cba.run :=
  exchangeFirst schedules.abc schedules.bac ≫ exchangeLast schedules.bac schedules.bca ≫
    exchangeFirst schedules.bca schedules.cba

noncomputable def rightRoute : Cell (helperTransport levels O) schedules.abc.run schedules.cba.run :=
  exchangeLast schedules.abc schedules.acb ≫ exchangeFirst schedules.acb schedules.cab ≫
    exchangeLast schedules.cab schedules.cba

theorem frame_braid :
    (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).frame.hom =
      (RunStateGroupoid.endpointMap levels O (rightRoute schedules)).frame.hom := by
  simp only [leftRoute, rightRoute, RunStateGroupoid.endpointMap_comp, PlainIso.trans, Iso.trans_hom,
    exchangeFirst_frame, exchangeLast_frame]
  simpa only [Category.assoc] using iterated_braid third.helpers second.helpers first.helpers

theorem boundary_braid :
    RunStateGroupoid.endpointMap levels O (leftRoute schedules) =
      RunStateGroupoid.endpointMap levels O (rightRoute schedules) :=
  RunStateGroupoid.iso_ext levels O (Iso.ext (frame_braid schedules))

private theorem position_braid (index : Nat) :
    ProofRelevantRuns.swapAt 0 (ProofRelevantRuns.swapAt 1 (ProofRelevantRuns.swapAt 0 index)) =
      ProofRelevantRuns.swapAt 1 (ProofRelevantRuns.swapAt 0 (ProofRelevantRuns.swapAt 1 index)) := by
  unfold ProofRelevantRuns.swapAt
  by_cases zero : index = 0
  · subst index; decide
  by_cases one : index = 1
  · subst index; decide
  by_cases two : index = 2
  · subst index; decide
  simp [zero, one, two]

theorem event_braid :
    events (helperTransport levels O) (leftRoute schedules) =
      events (helperTransport levels O) (rightRoute schedules) := by
  apply Equiv.ext
  intro event
  apply Fin.ext
  simp only [leftRoute, rightRoute, events_comp, Equiv.trans_apply, exchangeFirst_event, exchangeLast_event]
  exact position_braid event.val

/-- The admission object is the existing native cell, and both constructed
comparison paths retain its complete event and contextual interpretations. -/
theorem admitted_cell_braid (cell : (helperTransport levels O).Cell state [first, second, third]) :
    let schedules := cell.six_schedules
    events (helperTransport levels O) (leftRoute schedules) = events (helperTransport levels O) (rightRoute schedules) ∧
      RunStateGroupoid.endpointMap levels O (leftRoute schedules) =
        RunStateGroupoid.endpointMap levels O (rightRoute schedules) :=
  ⟨event_braid cell.six_schedules, boundary_braid cell.six_schedules⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid.admitted_cell_braid
