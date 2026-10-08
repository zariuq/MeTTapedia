import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicNativeMeaning
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateControls
import Mathlib.CategoryTheory.Category.ULift

/-!
# Complete generated logical-operator interpretation controls

The base is an actual raised category of small types, with the Boolean-to-unit
map retained as a source arrow. The independently interpreted quotient arrows
are read at a proper predicate depending on both its Boolean argument and a
number parameter. Their universal and existential answers differ, and a real
future parameter map changes the universal answer. The implication retains
both supplied predicate inputs.

An independently supplied interpretation replacing universal operations by
existential ones cannot realize the authored declarations. This rejection is
derived from necessary local admission and complete operation uniqueness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open RelativeClosedSyntax GeneratedCategory
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier
open HigherOrderInternalPredicateControls ElementaryTypePredicateReadout

abbrev Base := AsSmall.{0} Type
def base : Base ⥤ Type := AsSmall.down
def boolean : Base := AsSmall.up.obj Bool
def unit : Base := AsSmall.up.obj PUnit
def fold : boolean ⟶ unit := AsSmall.up.map forgetBoolean

abbrev native := NativeMeaning.meaning base logic

theorem actual_source_fold_is_retained : base.map fold = forgetBoolean := rfl

theorem local_diagrams_realize_the_generated_equations :
    RelativeClosedSyntax.Interpretation.Realization (lawfulSignature (C := Base))
      (Interpretation.lawfulAssignment base native) := NativeMeaning.realized base logic

def universalImage : HigherOrderInternalPredicateQuantifier.power logic Bool ⟶
    HigherOrderInternalPredicateQuantifier.power logic PUnit :=
  NativeMeaning.imageAt base logic (universalRaw fold)
    (Interpretation.power_read base native boolean)
    (Interpretation.power_read base native unit)

theorem universalImage_complete : universalImage = quantifier.operation :=
  NativeMeaning.imageAt_readout base logic (universalRaw fold)
    (Interpretation.power_read base native boolean)
    (Interpretation.power_read base native unit) quantifier.operation rfl

def existentialImage : HigherOrderInternalPredicateQuantifier.power logic Bool ⟶
    HigherOrderInternalPredicateQuantifier.power logic PUnit :=
  NativeMeaning.imageAt base logic (existentialRaw fold)
    (Interpretation.power_read base native boolean)
    (Interpretation.power_read base native unit)

theorem existentialImage_complete : existentialImage = existential.operation :=
  NativeMeaning.imageAt_readout base logic (existentialRaw fold)
    (Interpretation.power_read base native boolean)
    (Interpretation.power_read base native unit) existential.operation rfl

theorem generated_universal_retains_both_coordinates (parameter : Nat) :
    Contains (family logic (suppliedName ≫ universalImage)) (PUnit.unit, parameter) ↔ parameter > 1 := by
  rw [universalImage_complete]
  exact complete_output_read parameter

theorem the_actual_interpreted_operations_disagree :
    Contains (family logic (suppliedName ≫ existentialImage)) (PUnit.unit, 1) ∧
      ¬ Contains (family logic (suppliedName ≫ universalImage)) (PUnit.unit, 1) := by
  rw [universalImage_complete, existentialImage_complete]
  exact the_existential_keeps_an_actual_supplied_coordinate

theorem interpreted_universal_is_nonconstant :
    Contains (family logic (suppliedName ≫ universalImage)) (PUnit.unit, 2) ∧
      ¬ Contains (family logic (suppliedName ≫ universalImage)) (PUnit.unit, 1) := by
  rw [universalImage_complete]
  exact the_complete_native_answer_is_not_constant

theorem an_actual_future_changes_the_interpreted_answer :
    ¬ Contains (family logic (suppliedName ≫ universalImage)) (PUnit.unit, 1) ∧
      Contains (family logic ((future ≫ suppliedName) ≫ universalImage)) (PUnit.unit, 1) := by
  rw [universalImage_complete]
  exact the_actual_future_changes_the_answer

def implicationImage : logic.generic.object ⊗ logic.generic.object ⟶ logic.generic.object :=
  NativeMeaning.imageAt base logic (implicationRaw (C := Base))
    ((Interpretation.assignment base native).evaluate_product
      (Interpretation.omega_read base native) (Interpretation.omega_read base native))
    (Interpretation.omega_read base native)

theorem implicationImage_complete : implicationImage = implication.operation :=
  NativeMeaning.imageAt_readout base logic (implicationRaw (C := Base))
    ((Interpretation.assignment base native).evaluate_product
      (Interpretation.omega_read base native) (Interpretation.omega_read base native))
    (Interpretation.omega_read base native) implication.operation rfl

def interpretedImplication : Nat ⟶ logic.generic.object :=
  InternalPredicateImplication.applyOperation (operations logic) implicationImage
    antecedentName consequentName

theorem generated_implication_retains_both_inputs (parameter : Nat) :
    Contains (decode logic interpretedImplication) parameter ↔ (parameter > 0 → parameter > 1) := by
  unfold interpretedImplication
  rw [implicationImage_complete]
  exact complete_implication_read parameter

theorem neither_input_projection_is_the_interpreted_implication :
    Contains (decode logic interpretedImplication) 0 ∧
      ¬ Contains suppliedConsequent 0 ∧ Contains suppliedAntecedent 1 ∧
      ¬ Contains (decode logic interpretedImplication) 1 ∧
      Contains (decode logic interpretedImplication) 2 := by
  unfold interpretedImplication
  rw [implicationImage_complete]
  exact implication_retains_both_supplied_inputs

def wrongMeaning : Interpretation.Meaning base :=
  { native with universal := fun route => native.existential route }

theorem the_wrong_quantifier_has_no_local_admission : ¬ Interpretation.Admission base wrongMeaning := by
  intro admitted
  let candidate : InternalPredicateQuantifier.Universal (operations logic) forgetBoolean := {
    operation := existential.operation
    monotonicity := admitted.universalMonotonicity fold
    unit := admitted.universalUnit fold
    counit := admitted.universalCounit fold }
  have complete : existential.operation = quantifier.operation :=
    InternalPredicateLogicalUniqueness.universal_operation_unique (operations logic)
      (laws logic) forgetBoolean candidate quantifier
  have separator := the_existential_keeps_an_actual_supplied_coordinate
  apply separator.2
  change Contains (family logic (suppliedName ≫ quantifier.operation)) (PUnit.unit, 1)
  rw [← complete]
  exact separator.1

theorem the_wrong_quantifier_cannot_realize_the_generated_equations :
    ¬ RelativeClosedSyntax.Interpretation.Realization (lawfulSignature (C := Base))
      (Interpretation.lawfulAssignment base wrongMeaning) := by
  intro realized
  exact the_wrong_quantifier_has_no_local_admission
    (Interpretation.necessary_admission base wrongMeaning realized)

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.Controls
