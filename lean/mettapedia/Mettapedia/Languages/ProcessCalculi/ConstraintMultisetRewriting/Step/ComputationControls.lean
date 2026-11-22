import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Qualified
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.AppendReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.AppendOnTheStep

/-!
# Actual computation, resource reuse and refusal controls

The program reduces add zero (add zero zero) by the package's declared
addition equation. Two full-step firings alternate between occurrences zero
and one. Thus freshness at a firing does not require unbounded allocation.
The physical location and raw syntax change while the declared type remains.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Controls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (numC zeroC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D numType)

abbrev setting := TowerVectorsModel.setting level1 (fun _ => 0)
abbrev qualified := Vectors.vectors_qualified level1 (fun _ => 0)
abbrev presentation := Vectors.vectorPresentation level1

def start : Configuration (S := setting) where
  state := ⟨empty pkg, [], {0}, fun _ => ⟨numType (empty pkg),
    ⟨addC zeroC (addC zeroC zeroC), TowerVectorsPrograms.add_typed level1 D.zero_typed
      (TowerVectorsPrograms.add_typed level1 D.zero_typed D.zero_typed)⟩⟩⟩
  active := 0
  present := Finset.mem_singleton_self _
  consistent := ⟨empty pkg, 𝟙 _, Frames.models_nil _⟩

def zeroAction (argument : Tower.Tm 0) : ComputationSyntax.Action presentation 0 :=
  .declared (addC zeroC (.var 0)) (.var 0)
    (by
      change (⟨1, (addC zeroC (.var 0), .var 0)⟩ :
        Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ Vectors.vectorEquations
      decide)
    (fun _ => argument)

def first : Instruction presentation start :=
  ⟨⟨0, .hole, zeroAction (addC zeroC zeroC)⟩, rfl⟩

theorem one_fresh : 1 ∉ start.state.present := by decide

def middle : Configuration (S := setting) := first.next qualified 1 one_fresh

theorem middle_code : middle.code = addC zeroC zeroC := first.next_code qualified 1 one_fresh

def second : Instruction presentation middle :=
  ⟨⟨0, .hole, zeroAction zeroC⟩, middle_code.symm⟩

theorem old_slot_free : 0 ∉ middle.state.present := by decide

def finish : Configuration (S := setting) := second.next qualified 0 old_slot_free

def program : Execution qualified presentation start :=
  .cons first 1 one_fresh (.cons second 0 old_slot_free (.nil finish))

theorem result_zero : program.term = zeroC := second.next_code qualified 0 old_slot_free

theorem two_actual_events : program.toRun.word.length = 2 := rfl

theorem reused_old_slot : program.toRun.last.present = {0} ∧ finish.active = 0 := by
  constructor
  · decide
  · rfl

theorem only_two_slots_needed : start.state.present ∪ middle.state.present ∪ finish.state.present = {0, 1} := by decide

theorem wrong_freshness_refused : ¬ (step setting.levels Nat).Admits (first.compile qualified 0) := by
  rw [first.admitted_iff qualified 0]
  exact fun absent => absent start.present

theorem first_result_typed : Typed pkg .nil middle.code numC :=
  (qualified.subjectReduction (empty pkg).formed (.single first.reduction)
    (start.state.label start.active).2.typed).1

theorem complete_result_typed : Typed pkg .nil program.term numC := program.typed.1

theorem raw_code_changed : start.code ≠ program.term := by
  rw [result_zero]
  decide

theorem occurrence_observer_changed : 0 ∈ start.state.present ∧ 0 ∉ middle.state.present := by decide

theorem source_answer_and_actual_run :
    NativeTypesOnTheStep.Computing.Answer pkg start.code zeroC ∧
      Nonempty (RunProfile qualified presentation start program.toRun) := by
  refine ⟨⟨?_, ?_⟩, ⟨program.profile⟩⟩
  · have source : ConversionCoherence.StepStar pkg start.code program.term := program.reduces
    rw [result_zero] at source
    exact source
  · exact Vectors.const_normal level1 (by decide)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Controls.two_actual_events
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Controls.source_answer_and_actual_run
