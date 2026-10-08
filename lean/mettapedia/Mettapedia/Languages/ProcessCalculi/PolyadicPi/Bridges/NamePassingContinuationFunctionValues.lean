import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationValues

/-!
# Complete abstraction receiver comparisons

A supplied argument-and-return function determines the entire binary
receiver. Its ordered evaluation, change of stage and source abstraction
readings use the closed adjunction on whole arrows.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationFunctionValues

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation (abstraction)
open NamePassingContinuationOperations NamePassingContinuationValues

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (operations : Operations C)

def receiver {Z : C} (function : Z ⟶ operations.boundBodyObject) :
    Z ⟶ ((operations.names ⊗ operations.names) ⟶[C] operations.processes) :=
  abstraction
    (call (call (fst Z (operations.names ⊗ operations.names) ≫ function)
      (snd Z (operations.names ⊗ operations.names) ≫ fst operations.names operations.names))
      (snd Z (operations.names ⊗ operations.names) ≫ snd operations.names operations.names))

theorem receiver_natural {Z W : C} (change : W ⟶ Z)
    (function : Z ⟶ operations.boundBodyObject) :
    change ≫ receiver operations function = receiver operations (change ≫ function) := by
  unfold receiver
  rw [abstraction_natural]
  apply congrArg abstraction
  rw [← call_natural, ← call_natural]
  simp only [whiskerRight_fst_assoc, whiskerRight_snd_assoc]

theorem receiver_evaluation {Z : C} (function : Z ⟶ operations.boundBodyObject)
    (argument result : Z ⟶ operations.names) :
    call (receiver operations function) (lift argument result) = call (call function argument) result := by
  unfold receiver
  rw [← Category.id_comp (abstraction _), call_abstraction]
  simp [call, comp_lift_assoc]

theorem abstraction_value {Z : C} (function : Z ⟶ operations.boundBodyObject)
    (channel : Z ⟶ operations.names) :
    call (function ≫ operations.abstraction) channel =
      lift channel (receiver operations function) ≫ operations.receive := by
  change call (function ≫ abstraction
    (lift (snd operations.boundBodyObject operations.names)
      (receiver operations (fst operations.boundBodyObject operations.names)) ≫ operations.receive)) channel = _
  rw [call_abstraction, comp_lift_assoc, lift_snd, receiver_natural, lift_fst]

omit operations in
theorem call_postcomposition {Z A E P : C} (function : Z ⟶ (A ⟶[C] E))
    (argument : Z ⟶ A) (endpoint : E ⟶ P) :
    call function argument ≫ endpoint = call (function ≫ (ihom A).map endpoint) argument := by
  rw [NamePassingBindingClosedSchemas.call_as_evaluation,
    NamePassingBindingClosedSchemas.call_as_evaluation]
  have paired : lift argument (function ≫ (ihom A).map endpoint) =
      lift argument function ≫ (A ◁ (ihom A).map endpoint) := by
    apply hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd,
      whiskerLeft_fst, whiskerLeft_snd, lift_snd_assoc]
  have evaluation := (ihom.ev A).naturality endpoint
  change (A ◁ (ihom A).map endpoint) ≫ (ihom.ev A).app P =
    (ihom.ev A).app E ≫ endpoint at evaluation
  rw [paired]
  simp only [Category.assoc]
  rw [evaluation]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationFunctionValues
