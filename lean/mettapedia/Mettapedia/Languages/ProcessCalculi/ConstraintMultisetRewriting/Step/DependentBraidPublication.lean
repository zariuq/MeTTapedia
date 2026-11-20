import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentExecutionBraid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentPublicationConsumer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationOriginLedger

/-!
# Typed source consumers of the complete native execution braid

Both actual exchange routes induce the same full contextual map. Subsequent
substitution, retained source code, typed readouts and the complete transported
publication continuation therefore agree. The retained origin ledger agrees
too. This compares the two justified routes; it does not erase raw syntax
between arbitrary isomorphic frames.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open TypedPublication

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {state : State rules O}
  {first second third : HelperFiring levels O state}
  (schedules : (helperTransport levels O).SixSchedules first second third)

theorem refinement_after_braid {observer : Context rules}
    (refinement : observer ⟶ schedules.cba.run.last.frame) :
    refinement ≫ (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).frame.hom =
      refinement ≫ (RunStateGroupoid.endpointMap levels O (rightRoute schedules)).frame.hom :=
  congrArg (fun map => refinement ≫ map) (frame_braid schedules)

theorem code_after_braid (code : Code schedules.abc.run.last.frame) :
    code.reindex (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).frame.hom =
      code.reindex (RunStateGroupoid.endpointMap levels O (rightRoute schedules)).frame.hom :=
  congrArg code.reindex (frame_braid schedules)

theorem license_after_braid (code : Code schedules.abc.run.last.frame) {observer : Context rules}
    (refinement : observer ⟶ schedules.cba.run.last.frame) :
    code.At (refinement ≫ (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).frame.hom) ↔
      code.At (refinement ≫ (RunStateGroupoid.endpointMap levels O (rightRoute schedules)).frame.hom) := by
  rw [refinement_after_braid schedules refinement]

theorem readout_after_braid (code : Code schedules.abc.run.last.frame) {observer : Context rules}
    (refinement : observer ⟶ schedules.cba.run.last.frame)
    (licensed : code.At (refinement ≫ (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).frame.hom)) :
    code.readout (refinement ≫ (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).frame.hom) licensed =
      code.readout (refinement ≫ (RunStateGroupoid.endpointMap levels O (rightRoute schedules)).frame.hom)
        ((license_after_braid schedules code refinement).mp licensed) := by
  simp only [refinement_after_braid schedules refinement]

theorem complete_continuations_equal (continuation : (realizationStep levels O).Run schedules.abc.run.last) :
    PublicationConsumer.continueAfter (leftRoute schedules) continuation =
      PublicationConsumer.continueAfter (rightRoute schedules) continuation :=
  congrArg (fun comparison => RunTransport.move comparison continuation) (boundary_braid schedules)

theorem source_ledgers_equal {program : Program levels O}
    {permission : {state : State rules O} → Candidate program state → Prop}
    (execution : program.Execution permission schedules.abc.run.last) :
    RunTransport.ledger (RunStateGroupoid.endpointMap levels O (leftRoute schedules)) execution =
      RunTransport.ledger (RunStateGroupoid.endpointMap levels O (rightRoute schedules)) execution :=
  congrArg (fun comparison => RunTransport.ledger comparison execution) (boundary_braid schedules)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid.complete_continuations_equal
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid.source_ledgers_equal
