import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentExecutionBraid

/-!
# Finite certificates retaining event movement and helper transport once

The expected event reversal is computed on three positions. The expected
frame map is reconstructed directly from the three block projections,
independently of either execution comparison route. The certificate checks
both actual routes against those retained data. Its type fixes the theory,
source and target executions and the observation being certified.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

namespace BlockTriple

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

noncomputable def reverseFrame (first second third : Helpers Γ) :
    iteratedFrame first second third ⟶ iteratedFrame third second first :=
  (normalize first second third).hom ≫
    into third second first (toThird first second third) (toSecond first second third) (toFirst first second third)
      ((third_base first second third).trans (second_base first second third).symm)
      ((third_base first second third).trans (first_base first second third).symm) ≫
        (normalize third second first).inv

theorem reverse_first (first second third : Helpers Γ) :
    reverseFrame first second third ≫ iteratedFirst third second first = iteratedLift first second third := by
  simp only [reverseFrame, Category.assoc, normalize_inverse_first, into_first, normalize_third]

theorem reverse_second (first second third : Helpers Γ) :
    reverseFrame first second third ≫ iteratedSecond third second first = iteratedSecond first second third := by
  simp only [reverseFrame, Category.assoc, normalize_inverse_second, into_second, normalize_second]

theorem reverse_third (first second third : Helpers Γ) :
    reverseFrame first second third ≫ iteratedLift third second first = iteratedFirst first second third := by
  simp only [reverseFrame, Category.assoc, normalize_inverse_third, into_third, normalize_first]

end BlockTriple

namespace BraidCertificate

open ExecutionBraid BlockTriple Transport.RunRearrangement

def reverseThree : Fin 3 ≃ Fin 3 where
  toFun index := ⟨2 - index.val, by omega⟩
  invFun index := ⟨2 - index.val, by omega⟩
  left_inv index := by apply Fin.ext; dsimp; omega
  right_inv index := by apply Fin.ext; dsimp; omega

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {state : State rules O}
  {first second third : HelperFiring levels O state}
  (schedules : (helperTransport levels O).SixSchedules first second third)

theorem left_movement : events (helperTransport levels O) (leftRoute schedules) = reverseThree := by
  apply Equiv.ext
  intro event
  apply Fin.ext
  simp only [leftRoute, events_comp, Equiv.trans_apply, exchangeFirst_event, exchangeLast_event]
  change ProofRelevantRuns.swapAt 0 (ProofRelevantRuns.swapAt 1 (ProofRelevantRuns.swapAt 0 event.val)) = 2 - event.val
  have bound : event.val < 3 := event.isLt
  have cases : event.val = 0 ∨ event.val = 1 ∨ event.val = 2 := by omega
  rcases cases with h | h | h <;> simp [ProofRelevantRuns.swapAt, h]

theorem left_boundary :
    (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).frame.hom =
      reverseFrame third.helpers second.helpers first.helpers := by
  apply iterated_hom_ext first.helpers second.helpers third.helpers <;>
    simp only [leftRoute, RunStateGroupoid.endpointMap_comp, PlainIso.trans, Iso.trans_hom,
      exchangeFirst_frame, exchangeLast_frame, Category.assoc, iteratedSwapFirst_first,
      iteratedSwapFirst_second, iteratedSwapFirst_third, iteratedSwapLast_first,
      iteratedSwapLast_second, iteratedSwapLast_third, reverse_first, reverse_second, reverse_third]

structure Certificate where
  movement : Fin schedules.abc.run.word.length ≃ Fin schedules.cba.run.word.length
  boundary : schedules.cba.run.last.frame ⟶ schedules.abc.run.last.frame
  leftMovement : events (helperTransport levels O) (leftRoute schedules) = movement
  rightMovement : events (helperTransport levels O) (rightRoute schedules) = movement
  leftBoundary : (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).frame.hom = boundary
  rightBoundary : (RunStateGroupoid.endpointMap levels O (rightRoute schedules)).frame.hom = boundary

noncomputable def checked : Certificate schedules where
  movement := reverseThree
  boundary := reverseFrame third.helpers second.helpers first.helpers
  leftMovement := left_movement schedules
  rightMovement := (event_braid schedules).symm.trans (left_movement schedules)
  leftBoundary := left_boundary schedules
  rightBoundary := (frame_braid schedules).symm.trans (left_boundary schedules)

theorem typed_rows (certificate : Certificate schedules) (occurrence : O) :
    schedules.cba.run.last.label occurrence =
      (schedules.abc.run.last.label occurrence).reindex certificate.boundary := by
  rw [← certificate.leftBoundary]
  exact (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).label occurrence

theorem knowledge (certificate : Certificate schedules) :
    (ContextualDependentEta.frames levels).Equivalent
      ((ContextualDependentEta.frames levels).applyStore certificate.boundary schedules.abc.run.last.knowledge)
      schedules.cba.run.last.knowledge := by
  rw [← certificate.leftBoundary]
  exact (RunStateGroupoid.endpointMap levels O (leftRoute schedules)).knowledge

theorem movement_is_nonidentity : reverseThree (0 : Fin 3) ≠ 0 := by decide

end BraidCertificate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BraidCertificate.checked
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BraidCertificate.typed_rows
