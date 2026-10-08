import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedSchemasBinderSemantics

/-!
# Whole categorical evaluations of continuation constructors

The supplied stage, function and names are arbitrary arrows. Products,
currying and evaluation compute the independently constructed continuation
operations on those whole inputs. The private-name body retains the stored
function and the distinct argument and return positions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationValues

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation (abstraction exchange)
open NamePassingContinuationOperations
open NamePassingBindingClosedSchemas (call_as_evaluation appliedBody)

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

omit [MonoidalClosed C] in
theorem exchange_natural {X Y A : C} (before : Y ⟶ X) :
    (A ◁ before) ≫ exchange A X = exchange A Y ≫ (before ▷ A) := by
  apply hom_ext <;> simp [exchange]

theorem abstraction_natural {X Y A P : C} (before : Y ⟶ X) (body : X ⊗ A ⟶ P) :
    before ≫ abstraction body = abstraction (before ▷ A ≫ body) := by
  unfold abstraction
  rw [← MonoidalClosed.curry_natural_left]
  rw [← Category.assoc, exchange_natural, Category.assoc]

theorem call_natural {X Y A P : C} (before : Y ⟶ X)
    (function : X ⟶ (A ⟶[C] P)) (argument : X ⟶ A) :
    call (before ≫ function) (before ≫ argument) = before ≫ call function argument := by
  unfold call
  rw [← Category.assoc, comp_lift]

theorem call_abstraction {X Y A P : C} (before : Y ⟶ X) (argument : Y ⟶ A)
    (body : X ⊗ A ⟶ P) :
    call (before ≫ abstraction body) argument = lift before argument ≫ body := by
  rw [call_as_evaluation]
  have paired : lift argument (before ≫ abstraction body) =
      lift argument before ≫ (A ◁ abstraction body) := by
    apply hom_ext <;> simp only [Category.assoc, lift_fst, lift_snd, lift_snd_assoc,
      whiskerLeft_fst, whiskerLeft_snd]
  rw [paired, Category.assoc]
  unfold abstraction
  rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app, ← Category.assoc]
  congr 1
  apply hom_ext <;> simp [exchange]

variable (operations : Operations C)

theorem bindFresh_natural {X Y : C} (before : Y ⟶ X)
    (body : X ⊗ operations.names ⟶ operations.processes) :
    before ≫ bindFresh operations body = bindFresh operations (before ▷ operations.names ≫ body) := by
  unfold bindFresh
  rw [← Category.assoc, abstraction_natural]

theorem application_value {Z : C} (function : Z ⟶ operations.termObject)
    (argument result : Z ⟶ operations.names) :
    call (lift function argument ≫ operations.application) result =
      bindFresh operations
        (lift (call (fst Z operations.names ≫ function) (snd Z operations.names))
          (lift (snd Z operations.names)
            (lift (fst Z operations.names ≫ argument) (fst Z operations.names ≫ result)) ≫
              operations.send) ≫ operations.parallel) := by
  unfold Operations.application
  rw [call_abstraction, bindFresh_natural]
  apply congrArg (bindFresh operations)
  simp [call, comp_lift_assoc]

theorem carrier_value {Z : C} (name : Z ⟶ operations.names)
    (value body : Z ⟶ operations.termObject) (result : Z ⟶ operations.names) :
    call (lift name (lift value body) ≫ operations.carrier) result =
      lift (call body result) (lift name value ≫ operations.input) ≫ operations.parallel := by
  unfold Operations.carrier
  rw [call_abstraction]
  simp [call, comp_lift_assoc]

theorem definition_value {Z : C} (value : Z ⟶ operations.termObject)
    (body : Z ⟶ operations.boundBodyObject) (result : Z ⟶ operations.names) :
    call (lift value body ≫ operations.definition) result =
      bindFresh operations
        (lift (call (call (fst Z operations.names ≫ body) (snd Z operations.names))
            (fst Z operations.names ≫ result))
          (lift (snd Z operations.names) (fst Z operations.names ≫ value) ≫
            operations.input ≫ operations.replication) ≫ operations.parallel) := by
  unfold Operations.definition
  rw [call_abstraction, bindFresh_natural]
  apply congrArg (bindFresh operations)
  simp [call, comp_lift_assoc]

theorem appliedBody_value {Z : C} (body : Z ⟶ operations.boundBodyObject)
    (argument reference : Z ⟶ operations.names) :
    call (lift body argument ≫ appliedBody operations) reference =
      lift (call body reference) argument ≫ operations.application := by
  unfold appliedBody
  rw [call_abstraction]
  simp [call, comp_lift_assoc]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationValues
