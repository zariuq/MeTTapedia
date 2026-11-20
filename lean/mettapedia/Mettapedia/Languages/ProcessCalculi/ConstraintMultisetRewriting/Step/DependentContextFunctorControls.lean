import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextBoundaryFunctor
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentRunControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextGradeControls

/-!
# Positive and negative native context-placement controls

A path-helper and point-helper exchange survives beside a retained fourth
occurrence, with the original event exchange and helper boundary. The actual
counting counterexample cannot even enter the qualified domain on its bad
side; a bare original trace comparison supplies no placement license.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextFunctorControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open DependentFull.Controls TelescopeControls
open ContextPlacement Transport.RunRearrangement

theorem forward_safe : RunSafe {4} DependentRun.Controls.diamond.forward := by
  refine ⟨⟨by decide, by decide, ?_⟩, ⟨⟨by decide, by decide, ?_⟩, True.intro⟩⟩
  all_goals
    intro observer solution solved query member
    exact False.elim (List.not_mem_nil member)

theorem backward_safe : RunSafe {4} DependentRun.Controls.diamond.backward := by
  refine ⟨⟨by decide, by decide, ?_⟩, ⟨⟨by decide, by decide, ?_⟩, True.intro⟩⟩
  all_goals
    intro observer solution solved query member
    exact False.elim (List.not_mem_nil member)

noncomputable def qualifiedSwap :
    qualifiedObject (T := helperTransport setting.levels Nat) DependentRun.Controls.diamond.forward forward_safe ⟶
      qualifiedObject (T := helperTransport setting.levels Nat) DependentRun.Controls.diamond.backward backward_safe :=
  (@Quiver.FreeGroupoid.of (Qualified (helperTransport setting.levels Nat)
    (RunSafe (state := baseState) {4}))
      (qualifiedQuiver (T := helperTransport setting.levels Nat) (RunSafe (state := baseState) {4}))).map
        (.inr DependentRun.Controls.diamond.witness)

noncomputable def placedSwap := (placementFunctor (levels := setting.levels) {4} baseState).map qualifiedSwap

def firstEvent : Fin DependentRun.Controls.diamond.forward.word.length := ⟨0, by change 0 < 2; decide⟩

theorem first_origin_moves_to_second :
    (events (helperTransport setting.levels Nat) placedSwap
      (finCongr (placeRun_event_count {4} DependentRun.Controls.diamond.forward forward_safe).symm firstEvent)).val = 1 := by
  have forgetMapped :
      (forgetFunctor (T := helperTransport setting.levels Nat) (RunSafe (state := baseState) {4})).map qualifiedSwap =
        generator (helperTransport setting.levels Nat) (.inr DependentRun.Controls.diamond.witness) :=
    Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec
      (forgetGenerators (T := helperTransport setting.levels Nat) (RunSafe (state := baseState) {4}) ⋙q
        Quiver.FreeGroupoid.of (Object (helperTransport setting.levels Nat) baseState)))
      (X := ⟨DependentRun.Controls.diamond.forward, forward_safe⟩)
      (Y := ⟨DependentRun.Controls.diamond.backward, backward_safe⟩)
      (.inr DependentRun.Controls.diamond.witness)
  have preserved := placement_events {4} baseState
    (first := ⟨DependentRun.Controls.diamond.forward, forward_safe⟩)
    (second := ⟨DependentRun.Controls.diamond.backward, backward_safe⟩) qualifiedSwap firstEvent
  rw [forgetMapped, events_generator] at preserved
  exact preserved

theorem surrounding_occurrence_retained :
    4 ∈ (placeRun {4} DependentRun.Controls.diamond.forward forward_safe).last.present ∧
      4 ∈ (placeRun {4} DependentRun.Controls.diamond.backward backward_safe).last.present := by
  constructor
  · exact Eq.mpr (congrArg (fun state : State Tower.rules Nat => 4 ∈ state.present)
      (placeRun_last {4} DependentRun.Controls.diamond.forward forward_safe))
        (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  · exact Eq.mpr (congrArg (fun state : State Tower.rules Nat => 4 ∈ state.present)
      (placeRun_last {4} DependentRun.Controls.diamond.backward backward_safe))
        (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem helper_boundary_retained :
    frameMap (RunStateGroupoid.endpointMap setting.levels Nat
      (interchangeCell {4} DependentRun.Controls.diamond.witness forward_safe backward_safe)) =
      frameMap DependentRun.Controls.diamond.close :=
  interchangeCell_frame {4} DependentRun.Controls.diamond.witness forward_safe backward_safe

theorem count_failure_excluded_from_domain :
    ¬ ∃ run : Qualified (helperTransport setting.levels Nat) (RunSafe (state := ContextGradeControls.start) {1}),
      run.val = ContextGradeControls.badRun := by
  rintro ⟨run, same⟩
  exact ContextGradeControls.bad_grade (same ▸ run.property)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextFunctorControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextFunctorControls.first_origin_moves_to_second
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextFunctorControls.helper_boundary_retained
