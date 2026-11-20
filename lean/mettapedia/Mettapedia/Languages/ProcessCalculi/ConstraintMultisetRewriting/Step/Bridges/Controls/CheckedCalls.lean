import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.CheckedCalls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Unsaturated

/-!
# Recursive append reaches its typed native answer; checking alone is insufficient

The actual checked append definition, whose result type calls the earlier
addition definition, reaches `[2, 3]` through the fixed directed program.
Its original constant evaluated by its own rows has exactly that answer.
The accepted unsaturated recursive definition remains outside the stronger
row-completeness class at its declared recursion index; successful checking
alone does not license that bridge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.CheckedCalls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing NativeTypesOnTheStep.Computing.Definitions
open NativeTypesOnTheStep.Computing.DirectedAnswers
open TelescopeAbstraction (applyClosed)
open TowerVectorsModel (numC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg level1)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (two twoThree single)

theorem append_native_answer :
    Bridges.CheckedCalls.NativeAnswer appendR_checked groundSub_typed twoThree := by
  obtain ⟨value, _, compiled, same⟩ := appendR_ground_general.2
  subst value
  exact (Bridges.CheckedCalls.compiled_answer_iff_native appendR_checked groundSub_typed twoThree).mp compiled

theorem append_row_answer_iff_native (value : Tower.Tm 0) :
    DirectedAnswer addAppendExt (applyClosed appendRDef.telescope groundSub (.const appendName)) value ↔
      Bridges.CheckedCalls.NativeAnswer appendR_checked groundSub_typed value :=
  Bridges.CheckedCalls.row_answer_iff_native addAppend_devCheck addAppend_rules appendR_checked
    append_rowsReach groundSub_typed (fun _ => .refl _) (appendR_result_data groundSub_typed .num) value

theorem append_source_and_actual_answer :
    DirectedAnswer addAppendExt (applyClosed appendRDef.telescope groundSub (.const appendName)) twoThree ∧
      Bridges.CheckedCalls.NativeAnswer appendR_checked groundSub_typed twoThree :=
  ⟨(append_row_answer_iff_native twoThree).mpr append_native_answer, append_native_answer⟩

theorem append_native_result_typed : Typed pkg .nil twoThree (subst groundSub appendRDef.result) :=
  Bridges.CheckedCalls.native_answer_keeps_type appendR_checked groundSub_typed append_native_answer

theorem declared_result_type_computes :
    Conv pkg.headEq (subst groundSub appendRDef.result) (vecC numC two) pkg.computation :=
  joins_conv (fuel := 60) (by decide +kernel)

theorem shorter_native_answer_refused :
    ¬ Bridges.CheckedCalls.NativeAnswer appendR_checked groundSub_typed (single two) := by
  intro shorter
  have actual := (Bridges.CheckedCalls.compiled_answer_iff_native appendR_checked groundSub_typed _).mpr
    append_native_answer
  have short := (Bridges.CheckedCalls.compiled_answer_iff_native appendR_checked groundSub_typed _).mpr shorter
  have same := DirectedAnswer.unique (Vectors.vectorConstructors level1) short actual
  exact (by decide : (single two : Tower.Tm 0) ≠ twoThree) same

theorem checking_does_not_imply_rowsReach :
    Checked twistDef 0 twistTerm ∧ ¬ RowsReach twistDef twistTerm twistName twistRows 1 1 := by
  refine ⟨twist_checked, ?_⟩
  intro reach
  exact twist_not_recursive reach.recursive

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.CheckedCalls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.CheckedCalls.append_source_and_actual_answer
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.CheckedCalls.append_native_result_typed
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.CheckedCalls.checking_does_not_imply_rowsReach
