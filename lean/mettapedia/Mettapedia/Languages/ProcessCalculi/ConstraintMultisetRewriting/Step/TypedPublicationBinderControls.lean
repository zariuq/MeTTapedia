import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationConservativity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentSchemaPolymorphismControls

/-!
# A dependent schema retains its type and value alternatives

The existing schema opens A : U0 followed by x : A. Its actual typed
publication is embedded by the identity residual route, retaining both the
Ground-valued and function-valued interpretations. A source execution and
its native run keep the rule origin and the full published state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.BinderControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

abbrev levels := DependentProgram.Controls.levels
abbrev start := DependentProgram.Controls.start
abbrev oldCandidate := DependentProgram.PolymorphismControls.candidate

theorem outputs_typed (context : Context Tower.rules) :
    ∀ made ∈ (DependentProgram.PolymorphismControls.polymorphicSchema context).makes, made.WellTyped := by
  intro made member
  obtain rfl := List.mem_singleton.mp member
  exact Make.ofRow_wellTyped _

def table : Program levels Nat := fun context =>
  [FrameTyped.schema (DependentProgram.PolymorphismControls.polymorphicSchema context) (outputs_typed context)]

def candidate : Candidate table start where
  ruleIndex := ⟨0, by decide⟩
  pick := FrameTyped.pick oldCandidate.schema (outputs_typed _) oldCandidate.pick
  target := oldCandidate.schema.helpers.frame
  answer := 𝟙 _
  basis := .residual (ContextualDependentUpdate.Update.pending levels _)
    (FrameTyped.output_license oldCandidate.schema (outputs_typed _))

theorem source_admitted : candidate.schema.Admits candidate.pick :=
  (realization_admits_iff candidate.application).mp
    ((FrameTyped.admits_iff oldCandidate.schema (outputs_typed _) oldCandidate.pick).mpr
      DependentProgram.PolymorphismControls.admits_polymorphic_application)

/-- This example gives every source candidate permission; admission still
checks its resource, information, guard and typing obligations. -/
def permission : {state : State Tower.rules Nat} → Candidate table state → Prop := fun _ => True

def execution : table.Execution permission start :=
  .cons candidate source_admitted True.intro (.nil (candidate.application.sourceResult source_admitted))

theorem source_and_native_last : execution.toRun.last = execution.last := execution.toRun_last

theorem one_actual_event : execution.toRun.word.length = 1 := by
  rw [Program.Execution.toRun_word]
  rfl

theorem rule_origin_retained : execution.word = [⟨start, candidate⟩] := rfl

theorem published_eq_original : execution.last = DependentProgram.PolymorphismControls.execution.last := by
  have original := FrameTyped.result_eq oldCandidate.schema (outputs_typed _) oldCandidate.pick
    DependentProgram.PolymorphismControls.admits_polymorphic_application
  have native := realization_result candidate.application source_admitted
  exact native.symm.trans original

theorem published_code_origin : execution.last.label 7 =
    DependentProgram.PolymorphismControls.publishedRow start.frame := rfl

theorem both_type_arguments_survive :
    (frames levels).Models
      (DependentProgram.PolymorphismControls.groundModel (𝟙 DependentFull.Controls.point))
      execution.last.knowledge ∧
    (frames levels).Models
      (DependentProgram.PolymorphismControls.arrowModel (𝟙 DependentFull.Controls.point))
      execution.last.knowledge :=
  DependentProgram.PolymorphismControls.both_arguments_survive

theorem distinct_typed_readouts :
    ¬ (frames levels).E
      ((execution.last.label 7).reindex
        (DependentProgram.PolymorphismControls.groundModel (𝟙 DependentFull.Controls.point)))
      ((execution.last.label 7).reindex
        (DependentProgram.PolymorphismControls.arrowModel (𝟙 DependentFull.Controls.point))) :=
  DependentProgram.PolymorphismControls.retained_types_are_distinct

/-- Every supplied dependent tuple retains the old environment exactly.
This is the actual telescope opening law, not a condition imposed on a map. -/
theorem no_capture {target : Context Tower.rules} (baseMap : target ⟶ start.frame)
    (arguments : candidate.schema.helpers.Arguments baseMap) :
    candidate.schema.helpers.instantiate baseMap arguments ≫ candidate.schema.helpers.weaken = baseMap :=
  candidate.schema.helpers.instantiate_weaken baseMap arguments

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.BinderControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.BinderControls.published_eq_original
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.BinderControls.distinct_typed_readouts
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.BinderControls.no_capture
