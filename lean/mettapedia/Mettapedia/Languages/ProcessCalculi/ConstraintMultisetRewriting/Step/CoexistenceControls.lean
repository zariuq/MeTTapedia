import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Coexistence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedStep

/-! # Coexistence, inconsistent knowledge, and the native-carrier boundary -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.Controls

open AdmissionObservationCover.Controls (World frame)
open PreparedStep.Controls (bit no)

def yes : World → Bool := fun _ => true

def zero : Configuration (World → Bool) Nat := ⟨[(bit, no)], {7}⟩
def one : Configuration (World → Bool) Nat := ⟨[(bit, yes)], {7}⟩

theorem zero_solvable : frame.Solvable (a := ()) zero.equations := by
  refine ⟨(), (fun _ _ => false), ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem one_solvable : frame.Solvable (a := ()) one.equations := by
  refine ⟨(), (fun _ _ => true), ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

/-- Coexistence retains a shared occurrence even with inconsistent joint knowledge. -/
theorem shared_occurrence_coexists : (tensor zero one).present = {7} := by
  simp [tensor, zero, one]

theorem individually_solvable_jointly_inconsistent :
    frame.Solvable (a := ()) zero.equations ∧ frame.Solvable (a := ()) one.equations ∧
      ¬frame.Solvable (a := ()) (tensor zero one).equations := by
  refine ⟨zero_solvable, one_solvable, ?_⟩
  rintro ⟨b, σ, solved⟩
  cases b
  obtain ⟨left, right⟩ := (models_tensor frame (a := ()) (b := ()) σ zero one).mp solved
  have first := left (bit, no) (by simp [zero])
  have second := right (bit, yes) (by simp [one])
  change frame.act (a := ()) (b := ()) σ bit = no at first
  change frame.act (a := ()) (b := ()) σ bit = yes at second
  have impossible := congrFun (first.symm.trans second) (fun _ => false)
  cases impossible

theorem symmetry_is_semantic : Same frame (a := ()) (tensor zero one) (tensor one zero) :=
  tensor_comm frame (a := ()) zero one

theorem symmetry_is_not_literal : tensor zero one ≠ tensor one zero := by
  intro same
  have outputs := congrArg
    (fun (state : Configuration (World → Bool) Nat) =>
      state.equations.map fun equation => equation.2 (fun _ => false)) same
  simp [tensor, zero, one, no, yes] at outputs

/-- A real effect core with an inhabited, single-cell native state carrier. -/
def singleCell : EffectCore frame Nat Nat (fun _ => Unit) where
  frame _ := ()
  knowledge _ := []
  present n := {n}
  selection {s} _ := ⟨[], [s], []⟩
  target _ := ()
  extension _ := frame.id ()
  information _ := []
  information_refines := by
    intro _s _f _b _σ _solved
    exact Frames.models_nil _
  Shapes _ := ([] : List Nat).Nodup
  preparedResult {s} _ _ := s
  present_preparedResult _ _ := by
    simp [Selection.commit, MeTTaCalculus.OccurrenceCommits.fire]
  preparedSettle _ _ := frame.id ()
  result_refines := by
    intro _s _f _p _b _σ _solved
    exact Frames.models_nil _

theorem singleCell_prepares (n : Nat) : singleCell.Prepares (s := n) () := by
  refine ⟨List.nodup_nil, ?_, ⟨(), frame.id (), Frames.models_nil _⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [singleCell, Selection.commit]

/-- The native carrier cannot supply the empty configuration. -/
theorem singleCell_has_no_native_unit : ¬∃ n, singleCell.present n = ∅ := by
  rintro ⟨n, empty⟩
  exact Finset.singleton_ne_empty n empty

/-- Closure under coexistence is not a consequence of the effect-core fields. -/
theorem singleCell_not_closed : ¬∃ n,
    singleCell.configuration n = tensor (singleCell.configuration 0) (singleCell.configuration 1) := by
  rintro ⟨n, equal⟩
  have counts := congrArg (fun (state : Configuration (World → Bool) Nat) => state.present.card) equal
  simp [EffectCore.configuration, singleCell, tensor] at counts

abbrev DiscreteHom (a b : Bool) := PLift (a = b)

/-- Two disconnected frame objects with genuine Boolean term fibres. -/
def discreteFrames : Frames (fun _ : Bool => Bool) DiscreteHom where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act _ term := term
  id _ := ⟨rfl⟩
  comp later earlier := ⟨earlier.down.trans later.down⟩
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by intro _ _ _ _ _ same; exact same

theorem no_common_native_frame : ¬∃ target : Bool,
    Nonempty (DiscreteHom false target) ∧ Nonempty (DiscreteHom true target) := by
  rintro ⟨target, ⟨left⟩, ⟨right⟩⟩
  have impossible : false = true := left.down.trans right.down.symm
  cases impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.Controls
