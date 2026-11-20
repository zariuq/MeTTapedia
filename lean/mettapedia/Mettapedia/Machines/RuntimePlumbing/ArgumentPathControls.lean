import Mettapedia.Machines.RuntimePlumbing.ContextualArgumentPaths

/-!
# Caller-bound nested arguments and distinct local variables

The argument has the shape `((eq z b))`. Its caller's `z` denotes `b`,
while an unrelated variable with the same local number in the callee denotes
`c`. Correct lazy projection and the full-image route agree. Reinterpreting
the syntax in the callee's frame changes a ground comparison's result.

These controls isolate lexical and current-binding obligations. They do not
assert that this is the exact cause of any particular native regression.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.ArgumentPathControls

open Mettapedia.Machines.ContextualSequenceObservation
open ContextualArgumentPaths

def argument : Term Nat Nat := .expr [.expr [.leaf 5, .var 0, .leaf 2]]

def store : Store Nat Nat Nat := fun frame cell =>
  if frame = 2 ∧ cell = 9 then some ⟨argument, 1⟩
  else if cell = 0 then some ⟨.leaf (if frame = 1 then 2 else 3), frame⟩
  else none

def callerImage : Term (Nat × Nat) Nat := .expr [.expr [.leaf 5, .leaf 2, .leaf 2]]
def wrongImage : Term (Nat × Nat) Nat := .expr [.expr [.leaf 5, .leaf 3, .leaf 2]]
def indirect : Value Nat Nat Nat := ⟨.var 9, 2⟩

theorem caller_image : Image store ⟨argument, 1⟩ callerImage := by
  apply Image.expression
  apply Images.cons
  · apply Image.expression
    apply Images.cons .leaf
    apply Images.cons
    · exact .binding (entered := ⟨.leaf 2, 1⟩) (by simp [store]) .leaf
    · exact .cons .leaf .nil
  · exact .nil

theorem indirect_image : Image store indirect callerImage := by
  exact .binding (entered := ⟨argument, 1⟩) rfl caller_image

theorem callee_reinterpretation_image : Image store ⟨argument, 2⟩ wrongImage := by
  apply Image.expression
  apply Images.cons
  · apply Image.expression
    apply Images.cons .leaf
    apply Images.cons
    · exact .binding (entered := ⟨.leaf 3, 2⟩) (by simp [store]) .leaf
    · exact .cons .leaf .nil
  · exact .nil

theorem entered_argument_frame : RootRead store indirect ⟨argument, 1⟩ := by
  exact .binding rfl .expression

theorem nested_left_reads_caller_binding :
    ∃ target, Projection store indirect [0, 1] target ∧ Image store target (.leaf 2) := by
  exact (projection_image_iff indirect_image [0, 1]).mp rfl

theorem nested_right_reads_same_ground_value :
    ∃ target, Projection store indirect [0, 2] target ∧ Image store target (.leaf 2) := by
  exact (projection_image_iff indirect_image [0, 2]).mp rfl

theorem ground_comparison_agrees : EqualFields store indirect [0, 1] [0, 2] := by
  exact (equal_fields_iff indirect_image _ _).mpr ⟨.leaf 2, rfl, rfl⟩

theorem dropping_the_entered_frame_changes_admission :
    ¬ EqualFields store ⟨argument, 2⟩ [0, 1] [0, 2] := by
  rw [equal_fields_iff callee_reinterpretation_image]
  simp [wrongImage, atPath]

theorem out_of_range_is_a_semantic_missing_path : Report store indirect [0, 3] none := by
  apply Report.missing
  intro target projected
  obtain ⟨selected, found, _⟩ := projection_sound projected indirect_image
  simp [callerImage, atPath] at found

def before : Store Nat Nat Nat := fun frame cell =>
  if frame = 2 ∧ cell = 9 then some ⟨argument, 1⟩ else none

def earlierImage : Term (Nat × Nat) Nat := .expr [.expr [.leaf 5, .var (1, 0), .leaf 2]]

theorem before_binding_image : Image before indirect earlierImage := by
  apply Image.binding (entered := ⟨argument, 1⟩) rfl
  apply Image.expression
  apply Images.cons
  · apply Image.expression
    apply Images.cons .leaf
    apply Images.cons
    · exact .free (by simp [before])
    · exact .cons .leaf .nil
  · exact .nil

theorem retained_root_does_not_freeze_a_descendant :
    RootRead before indirect ⟨argument, 1⟩ ∧ RootRead store indirect ⟨argument, 1⟩ := by
  exact ⟨.binding rfl .expression, entered_argument_frame⟩

theorem earlier_field_image_is_not_current :
    ¬ Image store indirect earlierImage := by
  intro old
  have same := image_unique old indirect_image
  cases same

end Mettapedia.Machines.RuntimePlumbing.ArgumentPathControls
