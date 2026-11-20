import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.HostedFinishedReadings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.HostedAnswerReadingsControls

/-!
# A value-shaped instance is not universal finishedness

The same present shared unknown has a completed-value model and an evaluation model. Its actual
native row has a value-shaped instance, but the full source `StateFinished` observation fails. It
cannot represent a source branch. A completed constant row supplies the positive universal control
and retains a value-shaped instance through a proper dead-name extension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedFinishedReadingsControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit Hosting
open RuleSyntax.StepWeb.HostedNative
open NativeClosedReadings HostedAnswerReadings HostedFinishedReadings
open HostedAnswerReadingsControls (N value hosted presented grownHost grownPresented extension source_reads_one)

def declarations : Unit → MetaArity MSig := fun _ => ([], ())
def unknown : Term (signature MSig declarations) [] () := generator declarations ()

def ambiguous : HostState MSig := ⟨⟨Unit, declarations⟩, [], {0}, fun _ => observe unknown⟩

def ambiguousPresented : Presented [] () ambiguous where
  term _ := unknown
  label_eq _ := rfl

def valueOutput : ClosedTerm MSig [] () := answerPattern N value

def activeOutput : ClosedTerm MSig [] () :=
  altN N (evalN N (retN N (Rigid.includeTerm (closedArity MSig) value))) (emptyN N)

def valueModel : Assignment declarations (closedArity MSig) := fun _ => valueOutput
def activeModel : Assignment declarations (closedArity MSig) := fun _ => activeOutput

theorem value_reading :
    rowReads ambiguous 0 ⟨Empty, closedArity MSig⟩ (observe valueOutput) := by
  refine ⟨valueModel, (Frames.contextual MSig).models_nil _, ?_⟩
  change observe (instantiate valueModel (generator declarations ())) = observe valueOutput
  rw [instantiate_generator]
  rfl

theorem active_reading :
    rowReads ambiguous 0 ⟨Empty, closedArity MSig⟩ (observe activeOutput) := by
  refine ⟨activeModel, (Frames.contextual MSig).models_nil _, ?_⟩
  change observe (instantiate activeModel (generator declarations ())) = observe activeOutput
  rw [instantiate_generator]
  rfl

theorem actual_value_instance :
    HasValueInstance N (state mkeys ambiguous ambiguousPresented ∅) 0 := by
  apply (hosted_valueInstance_iff N ambiguous ambiguousPresented ∅ 0).mpr
  exact ⟨by simp [ambiguous], ⟨Empty, closedArity MSig⟩,
    Rigid.includeTerm (closedArity MSig) value, value_reading⟩

theorem ambiguous_not_finished : ¬ StateFinished N ambiguous 0 := by
  intro finished
  obtain ⟨datum, same⟩ := finished.2 ⟨Empty, closedArity MSig⟩ (observe activeOutput) active_reading
  have terms := observe_injective same
  have focus := (vec2_inj (N.args_eq terms)).1
  have tags := N.tag_eq focus
  cases tags

theorem value_instance_is_not_finished :
    HasValueInstance N (state mkeys ambiguous ambiguousPresented ∅) 0 ∧
      ¬ StateFinished N ambiguous 0 :=
  ⟨actual_value_instance, ambiguous_not_finished⟩

theorem ambiguous_not_source_representation {D : Discipline MSig [] ()}
    {P : SourceLanguage.Program mkeys [] () D.Ty} (scope : Nat) (branch : Branch mkeys [] () D.Ty) :
    ¬ Represents N P scope branch ambiguous 0 := by
  intro represented
  apply ambiguous_not_finished
  apply (represented_value_reading_iff_finished N (D := D) represented).mp
  exact ⟨⟨Empty, closedArity MSig⟩, Rigid.includeTerm (closedArity MSig) value, value_reading⟩

theorem completed_finished : StateFinished N (hosted {0}) 0 := by
  obtain ⟨initialTarget, reads⟩ := source_reads_one {0} 0
  refine ⟨⟨initialTarget, _, reads⟩, ?_⟩
  rintro target reading ⟨candidate, _, same⟩
  change observe (instantiate candidate
    (closedAt (closedArity MSig) (answerPattern N value))) = reading at same
  have output := (congrArg observe (closedAt_natural candidate (answerPattern N value))).symm.trans same
  exact ⟨Rigid.includeTerm target.arity value,
    output.symm.trans (congrArg observe (closedAt_answerPattern N target.arity value))⟩

theorem completed_value_instance :
    HasValueInstance N (state mkeys (hosted {0}) (presented {0}) ∅) 0 := by
  apply (hosted_valueInstance_iff N (hosted {0}) (presented {0}) ∅ 0).mpr
  obtain ⟨target, reads⟩ := source_reads_one {0} 0
  exact ⟨by simp [hosted], target, Rigid.includeTerm target.arity value, reads⟩

theorem proper_extension_value_instance :
    HasValueInstance N (state mkeys (grownHost {0}) (grownPresented {0}) ∅) 0 :=
  (deadExtension_valueInstance_iff N (extension {0}) 0).mpr completed_value_instance

theorem universal_and_existential_are_distinct :
    StateFinished N (hosted {0}) 0 ∧
      HasValueInstance N (state mkeys (grownHost {0}) (grownPresented {0}) ∅) 0 ∧
      HasValueInstance N (state mkeys ambiguous ambiguousPresented ∅) 0 ∧
      ¬ StateFinished N ambiguous 0 :=
  ⟨completed_finished, proper_extension_value_instance, actual_value_instance, ambiguous_not_finished⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedFinishedReadingsControls
