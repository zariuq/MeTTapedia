import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRunTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationVector
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationResidualControls

/-!
# Dependent vector execution after an actual context exchange

The call frame has k : nat, ys : vec k, m : nat. Exchange the independent
ys and m declarations over k, then carry the real two-event vector program:
settle m = zero, publish ys at vec(add zero k), and consume it at vec k.
The source raw variable positions change; the final dependent result and
composed refinement are preserved. A separate residual control rules out
dropping unresolved equations after transport.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransportControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open ContextualDependentParameterExchange
open ProgrammingOnTheStep.VectorPackage NativeTypesOnTheStep.VectorAppend

abbrev reversedFrame := context (vnat ctxK) vecK

def exchange : reversedFrame ≅ callFrame := swapIso (vnat ctxK) vecK

def reversedState : State vrules Nat where
  frame := reversedFrame
  knowledge := (frames vlevels).applyStore exchange.hom callState.knowledge
  present := callState.present
  label occurrence := (callState.label occurrence).reindex exchange.hom

def stateIso : PlainIso vlevels callState reversedState :=
  ⟨exchange, fun _ _ => Iff.rfl, rfl, fun _ => rfl⟩

theorem exchange_changes_parameter_position :
    exchange.hom.substitution 0 = .var ⟨1, by decide⟩ := swap_zero (vnat ctxK) vecK

theorem old_raw_position_is_not_preserved :
    exchange.hom.substitution 0 ≠ .var ⟨0, by decide⟩ := by
  rw [exchange_changes_parameter_position]
  decide

def moved : (realizationStep vlevels Nat).Run reversedState := RunTransport.move stateIso Vector.run

theorem two_actual_events : moved.word.length = 2 :=
  (RunTransport.event_count stateIso Vector.run).trans Vector.two_actual_events

theorem final_occurrences : moved.last.present = {1} :=
  (RunTransport.endpoint stateIso Vector.run).present.symm.trans Vector.final_occurrences

theorem final_row : moved.last.label 1 = Vector.run.last.label 1 := by
  have row := RunTransport.typed_results stateIso Vector.run 1
  change moved.last.label 1 = (Vector.run.last.label 1).reindex (𝟙 ctxKY) at row
  exact row.trans (ContextualDependentEta.reindex_id _)

theorem final_dependent_type :
    (moved.last.label 1).1.code = vecC (.var ⟨1, by decide⟩) := by
  rw [final_row]
  exact Vector.final_type

theorem final_value : (moved.last.label 1).2.code = .var ⟨0, by decide⟩ := by
  rw [final_row]
  exact Vector.final_value

theorem complete_refinement_square :
    moved.toLast ≫ exchange.hom =
      (RunTransport.endpoint stateIso Vector.run).frame.hom ≫ Vector.run.toLast :=
  RunTransport.refinement_square stateIso Vector.run

def movedResidual : Application DependentFull.Controls.setting.levels Nat ResidualControls.before :=
  RunTransport.application (PlainIso.refl ResidualControls.before) ResidualControls.application

theorem residual_equations_kept : movedResidual.basis.knowledge = ResidualControls.residual := rfl

theorem residual_cannot_be_replaced_by_empty :
    ¬ (frames DependentFull.Controls.setting.levels).Models (𝟙 ResidualControls.target)
      movedResidual.basis.knowledge := ResidualControls.identity_does_not_solve_residual

theorem residual_application_still_admitted :
    (realizationStep DependentFull.Controls.setting.levels Nat).Admits movedResidual :=
  (RunTransport.admits (PlainIso.refl ResidualControls.before) ResidualControls.application).mpr ResidualControls.admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransportControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransportControls.final_dependent_type
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.RunTransportControls.residual_cannot_be_replaced_by_empty
