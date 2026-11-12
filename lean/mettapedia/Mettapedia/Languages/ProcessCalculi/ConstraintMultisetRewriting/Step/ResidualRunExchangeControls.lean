import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunChecks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulHelper
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoherentSolutionJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CellsHelper

/-!
# Native exchange across successive fresh declaration frames

Two real helper-creating steps exchange with a third helper event. The
consumer uses the contextual helper model and its proved coherence and
closing isomorphisms, rather than a first-order or constant-frame instance.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ResidualRunExchangeControls

open Helpers
open Helpers.Consumer (tiny start first second start_solvable constant)

abbrev P := (helperStep (S := tiny) (O := Nat)).toStep
abbrev T := helperTransport (S := tiny) (O := Nat)

theorem first_admitted : P.Admits first := by
  obtain ⟨allowed, _, _, _, _⟩ := Helpers.Consumer.independent
  exact allowed

theorem second_admitted : P.Admits second := by
  obtain ⟨_, allowed, _, _, _⟩ := Helpers.Consumer.independent
  exact allowed

def third : Helpers.Firing start := ⟨3, ([(), ()], ()), constant 9, []⟩

theorem first_third_independent : T.Independent start first third :=
  Helpers.independent_iff.mpr ⟨start_solvable, by decide, by decide, by decide, asks_nil, asks_nil⟩

theorem third_admitted : P.Admits third := by
  obtain ⟨_, allowed, _, _, _⟩ := first_third_independent
  exact allowed

theorem second_after_first : P.Admits (T.residual first first_admitted second) :=
  (Helpers.Consumer.independent.residual_permissions first_admitted second_admitted).1

theorem third_after_first : P.Admits (T.residual first first_admitted third) :=
  (first_third_independent.residual_permissions first_admitted third_admitted).1

theorem later_independent : T.Independent (P.result first first_admitted)
    (T.residual first first_admitted second) (T.residual first first_admitted third) := by
  apply Helpers.independent_iff.mpr
  refine ⟨?_, ?_, ?_, by decide, asks_nil, asks_nil⟩
  · change (Frames.contextual tiny).Solvable first.information
    exact information_solvable first start_solvable
  · change 2 ∉ P.present (P.result first first_admitted)
    rw [P.present_result]
    simp [first, Helpers.Firing.selection, Selection.commit,
      MeTTaCalculus.OccurrenceCommits.fire, Helpers.Consumer.start]
  · change 3 ∉ P.present (P.result first first_admitted)
    rw [P.present_result]
    simp [first, Helpers.Firing.selection, Selection.commit,
      MeTTaCalculus.OccurrenceCommits.fire, Helpers.Consumer.start]

def twoStepRun : P.Run start :=
  .cons first first_admitted (.cons (T.residual first first_admitted second) second_after_first (.nil _))

def crossing : T.Crossing twoStepRun third third_admitted :=
  .cons (first_third_independent.residual_permissions first_admitted third_admitted).2
    third_after_first (Transport.Crossing.single later_independent second_after_first third_after_first)

def closing : T.Closing := Helpers.helperClosing

noncomputable def exchange : T.Exchange twoStepRun third third_admitted := crossing.exchange closing

theorem exchanged_run_length : exchange.residualRun.word.length = 2 := exchange.length_preserved

theorem exchanged_run_same_endpoint :
    T.Same exchange.residualRun.last (P.result exchange.residualFiring exchange.residualAdmitted) :=
  exchange.same_endpoint

theorem compatible_solution_checks :
    Transport.CrossChecks Helpers.helperCoherent twoStepRun third third_admitted :=
  (Transport.crossing_iff_checks Helpers.helperCoherent twoStepRun third third_admitted).mp ⟨crossing⟩

theorem native_run_really_changes_frame : twoStepRun.last.frame ≠ start.frame := by
  intro same
  have names := congrArg Frames.Frame.Names same
  let created : twoStepRun.last.frame.Names := .inr ()
  have impossible : start.frame.Names := names ▸ created
  exact impossible.elim

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ResidualRunExchangeControls
