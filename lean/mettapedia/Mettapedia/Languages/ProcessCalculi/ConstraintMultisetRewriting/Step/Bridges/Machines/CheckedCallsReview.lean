import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Controls.CheckedCalls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.ReadingCorrespondence

/-!
# Checked calls, actual execution, and the limits of compiled readings

Append's native answer needs at least one actual firing. A checked non-data
call also executes, but its answer need not be a data value. These controls
separate execution from the data-value licence in the row-answer theorem.

The existing addition reading relates a stuck partial row call to a compiled
partial that can reduce. Their raw answers differ. Hence the general reading
correspondence cannot replace the stronger row-completeness hypothesis or
supply positive step reflection. All terms and relations below are those of
the checked-definition and descriptor-program developments.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.CheckedCallsReview

open Interface Interface.Bridges
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing NativeTypesOnTheStep.Computing.Definitions
open NativeTypesOnTheStep.Computing.DirectedAnswers
open TelescopeAbstraction (applyClosed)
open TowerVectorsModel (numC succC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg level1)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one twoThree)

local instance headPolicy : DecidableRel CheckedCalls.setting.R.headEq := Classical.decRel _

theorem append_requires_actual_firing :
    ∃ run : (Directed.restricted CheckedCalls.program CheckedCalls.qualified).Run
      (CheckedCalls.input appendR_checked groundSub_typed).state,
      run.word ≠ [] ∧ Directed.Represents (S := CheckedCalls.setting) (twoThree : Tower.Tm 0) run.last ∧
        ContextualDependentExecutableJoin.Normal pkg (twoThree : Tower.Tm 0) := by
  obtain ⟨run, represented, normal⟩ := Controls.CheckedCalls.append_native_answer
  refine ⟨run, ?_, represented, normal⟩
  cases run with
  | nil =>
      have starts := Computation.represents_configuration
        (CheckedCalls.input appendR_checked groundSub_typed) rfl
      have equal := Directed.represents_functional represented starts
      exact False.elim ((by decide +kernel : twoThree ≠
        applyClosed appendRDef.telescope groundSub appendRTerm) equal)
  | cons => simp [Interface.Step.Run.word]

theorem checked_nondata_call_executes :
    CheckedCalls.NativeAnswer small_checked (smallArgs_typed (nat_typed 1))
      (.pi numC numC) ∧
      ¬ DataType (subst (smallArgs one) smallDef.result) ∧
      ¬ ∃ value, Value value ∧
        CheckedCalls.NativeAnswer small_checked (smallArgs_typed (nat_typed 1)) value := by
  refine ⟨(CheckedCalls.compiled_answer_iff_native small_checked
    (smallArgs_typed (nat_typed 1)) _).mp small_one_answer, small_control.2.1, ?_⟩
  rintro ⟨value, isValue, native⟩
  exact small_control.2.2.2 ⟨value, isValue,
    (CheckedCalls.compiled_answer_iff_native small_checked
      (smallArgs_typed (nat_typed 1)) value).mpr native⟩

abbrev rowPartial : Tower.Tm 0 := .app (.const addName) one
abbrev compiledPartial : Tower.Tm 0 := .app addTerm one
abbrev compiledValue : Tower.Tm 0 := .lam (succC (.var 0))

theorem rowPartial_normal : ConstructorSystem.Normal addAppendExt rowPartial := by
  refine ConstructorSystem.Normal.app (ConstructorSystem.Normal.const _ ?_) ?_
    (fun body h => by cases h) ?_
  · intro target step
    obtain ⟨name, head, positive, _⟩ := dev_root_spine addAppend_devCheck addAppend_rules step
    have computed : ConstructorSystem.spineHead (.const addName : Tower.Tm 0) = some (addName, 0) := rfl
    rw [computed] at head
    simp only [Option.some.injEq, Prod.mk.injEq] at head
    obtain ⟨rfl, arity⟩ := head
    omega
  · intro target step
    obtain ⟨baseStep, _⟩ := dev_step_old addAppend_devCheck addAppend_rules step one_old
    exact Vectors.succ_normal level1 (Vectors.const_normal level1 (by decide)) baseStep
  · intro target step
    obtain ⟨name, head, _, _⟩ := dev_root_spine addAppend_devCheck addAppend_rules step
    have computed : ConstructorSystem.spineHead rowPartial = some (addName, 1) := rfl
    rw [computed] at head
    simp only [Option.some.injEq, Prod.mk.injEq] at head
    obtain ⟨rfl, arity⟩ := head
    exact absurd arity (by decide)

theorem reading_related_partials : addAppendCorrespondence.related rowPartial compiledPartial := by
  have reading : ConstantExpansion.expand addAppendReading rowPartial = compiledPartial := by
    decide +kernel
  show Conv pkg.headEq (ConstantExpansion.expand addAppendReading rowPartial) compiledPartial pkg.computation
  rw [reading]
  exact .refl _

theorem reading_has_different_raw_answers :
    addAppendCorrespondence.related rowPartial compiledPartial ∧
      DirectedAnswer addAppendExt rowPartial rowPartial ∧
      DirectedAnswer pkg compiledPartial compiledValue ∧ rowPartial ≠ compiledValue :=
  ⟨reading_related_partials, ⟨.refl, directedNormal_of_normal rowPartial_normal⟩,
    add_one_control.2.1, by decide⟩

theorem reading_does_not_reflect_same_answer :
    ¬ DirectedAnswer addAppendExt rowPartial compiledValue := by
  intro answer
  have equal := DirectedAnswer.unique (devConstructors addAppend_devCheck addAppend_rules)
    answer (⟨.refl, directedNormal_of_normal rowPartial_normal⟩ :
      DirectedAnswer addAppendExt rowPartial rowPartial)
  exact (by decide : compiledValue ≠ rowPartial) equal

theorem related_but_not_convertible_in_extension :
    addAppendCorrespondence.related rowPartial compiledPartial ∧
      ¬ Conv addAppendExt.headEq rowPartial compiledPartial addAppendExt.computation :=
  ⟨reading_related_partials, partial_not_convertible⟩

theorem compiled_partial_has_step :
    ∃ after, StrongNormalization.Reduces pkg compiledPartial after := by
  unfold compiledPartial addTerm
  exact ⟨_, .betaPi _ _⟩

theorem silent_reading_not_positive_step_reflection :
    addAppendCorrespondence.related rowPartial compiledPartial ∧
      (∃ after, StrongNormalization.Reduces pkg compiledPartial after) ∧
      ¬ ∃ after, StrongNormalization.Reduces addAppendExt rowPartial after :=
  ⟨reading_related_partials, compiled_partial_has_step,
    fun ⟨_, step⟩ => rowPartial_normal (step_of_reduces step)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.CheckedCallsReview

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Machines.CheckedCallsReview
#print axioms append_requires_actual_firing
#print axioms checked_nondata_call_executes
#print axioms rowPartial_normal
#print axioms reading_related_partials
#print axioms reading_has_different_raw_answers
#print axioms reading_does_not_reflect_same_answer
#print axioms related_but_not_convertible_in_extension
#print axioms compiled_partial_has_step
#print axioms silent_reading_not_positive_step_reflection
