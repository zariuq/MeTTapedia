import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceControls

/-! # Complete-state coexistence without native closure or a common native frame -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.SystemsControls

open EffectCore.Systems
open Coexistence.Controls (singleCell discreteFrames DiscreteHom no_common_native_frame)
open AdmissionObservationCover.Controls (World frame)

def pair : singleCell.Systems := append singleCell (atom singleCell 0) (atom singleCell 1)

def pairPlacement : Placement singleCell pair () := fun _ _ => frame.id ()

theorem pair_solved : Models singleCell pair () pairPlacement :=
  fun _ _ => Frames.models_nil _

theorem pair_realization :
    (realize singleCell pair pairPlacement).present = ({0, 1} : Finset Nat) := by
  rw [realize_present]
  simp [pair, append, atom, present, singleCell]

theorem pair_has_no_native_representative : ¬∃ n,
    singleCell.configuration n = realize singleCell pair pairPlacement := by
  rintro ⟨n, same⟩
  have count := congrArg
    (fun state : Configuration (World → Bool) Nat => state.present.card) same
  rw [pair_realization] at count
  simp [EffectCore.configuration, singleCell] at count

theorem shared_cell_keeps_two_components :
    (append singleCell (atom singleCell 0) (atom singleCell 0)).length = 2 ∧
      present singleCell (append singleCell (atom singleCell 0) (atom singleCell 0)) = {0} := by
  constructor
  · rfl
  · simp [append, atom, present, singleCell]

/-- A multiplicity observer separates two aliased components from one. -/
theorem multiplicity_is_retained :
    fold singleCell (M := Multiplicative Nat) (fun _ => Multiplicative.ofAdd 1)
      (append singleCell (atom singleCell 0) (atom singleCell 0)) ≠
    fold singleCell (M := Multiplicative Nat) (fun _ => Multiplicative.ofAdd 1) (atom singleCell 0) := by
  decide

def disconnected : EffectCore discreteFrames Nat Bool (fun _ => Unit) where
  frame state := state
  knowledge _ := []
  present _ := ∅
  selection _ := ⟨[], [], []⟩
  target {s} _ := s
  extension {s} _ := discreteFrames.id s
  information _ := []
  information_refines := by
    intro _s _f _b _σ _solved
    exact Frames.models_nil _
  Shapes _ := ([] : List Nat).Nodup
  preparedResult {s} _ _ := s
  present_preparedResult _ _ := by
    simp [Selection.commit, MeTTaCalculus.OccurrenceCommits.fire]
  preparedSettle {s} _ _ := discreteFrames.id s
  result_refines := by
    intro _s _f _p _b _σ _solved
    exact Frames.models_nil _

theorem disconnected_prepares (state : Bool) : disconnected.Prepares (s := state) () := by
  refine ⟨List.nodup_nil, ?_, ⟨state, discreteFrames.id state, Frames.models_nil _⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [disconnected, Selection.commit]

def differentFrames : disconnected.Systems :=
  append disconnected (atom disconnected false) (atom disconnected true)

theorem different_frames_coexist : differentFrames.length = 2 := rfl

theorem different_frames_have_no_native_placement :
    ¬∃ target : Bool, Nonempty (Placement disconnected differentFrames target) := by
  rintro ⟨target, ⟨placement⟩⟩
  apply no_common_native_frame
  refine ⟨target, ⟨placement false ?_⟩, ⟨placement true ?_⟩⟩ <;>
    simp [differentFrames, append, atom, disconnected]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.SystemsControls
