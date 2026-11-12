import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationQuotedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersInterface

/-!
# Binding-aware scalar source and admitted contextual event paths

The quoted-lambda source reader feeds the existing contextual equation
program through the shared effect/admission interface. Its events retain the
chosen equation and active context; finite paths retain every firing. The
source correspondence observes the final reading, without identifying the
event paths that produce it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuotedEvents

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open QuotedLambda (sig)
open LambdaContextualRung (Srt)
open ProgramBinders Interface QuotedSource

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)

abbrev program (Γ : Ctx sig) := contextProgram Quoted.grammar (Quoted.schema Γ)
abbrev step (Γ : Ctx sig) := InterfaceProfile.step (program Γ)
abbrev Object (Γ : Ctx sig) := EffectCore.EventObject (step Γ).effectCore (step Γ).eventAdmission

theorem source_run_iff {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (Reduces Γ) (source call) (source answer) ↔
      ∃ run : (step Γ).Run (initial call), Reads (program Γ) run.last answer := by
  rw [contextual_execution_iff]
  constructor
  · rintro ⟨after, execution, reads⟩
    obtain ⟨run, rfl⟩ := InterfaceProfile.transition_run (program Γ) execution
    exact ⟨run, reads⟩
  · rintro ⟨run, reads⟩
    exact ⟨run.last, InterfaceProfile.run_transition (program Γ) run, reads⟩

theorem source_path_iff {Γ : Ctx sig} (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (Reduces Γ) (source call) (source answer) ↔
      ∃ target : Object Γ, Nonempty (@Quiver.Path (Object Γ) _ (initial call) target) ∧
        Reads (program Γ) target answer := by
  rw [source_run_iff]
  constructor
  · rintro ⟨run, reads⟩
    exact ⟨run.last, ⟨run.eventPath (step Γ)⟩, reads⟩
  · rintro ⟨target, ⟨path⟩, reads⟩
    obtain ⟨run, rfl⟩ := (step Γ).runOfEventPath path
    exact ⟨run, reads⟩

theorem reduction_has_event {Γ : Ctx sig} {call answer : Term sig Γ .term}
    (reduced : QuotedLambda.Step Γ call answer) :
    ∃ target : Object Γ, Nonempty ((step Γ).effectCore.Event (step Γ).eventAdmission (initial call) target) ∧
      Reads (program Γ) target answer :=
  InterfaceProfile.rewrite_has_event (program Γ)
    ((context_rewrites_iff (Quoted.schema Γ) call answer).mpr
      ((Quoted.quoted_rewrites_iff call answer).mpr reduced))

theorem quote_has_no_event {Γ : Ctx sig} (body : Term sig Γ .term) (target : Object Γ) :
    ¬ Nonempty ((step Γ).effectCore.Event (step Γ).eventAdmission
      (initial (QuotedLambda.quote body)) target) := by
  rintro ⟨event⟩
  obtain ⟨answer, rewritten⟩ := InterfaceProfile.admitted_has_answer (program Γ)
    (QuotedLambda.quote body) event.firing event.permitted
  exact QuotedLambda.quote_is_inert body answer
    ((Quoted.quoted_rewrites_iff _ _).mp ((context_rewrites_iff (Quoted.schema Γ) _ _).mp rewritten))

namespace Controls

open QuotedLambda.Controls

theorem named_code_executes :
    ∃ run : (step []).Run (initial quotedArgumentProgram), Reads (program []) run.last identity :=
  (source_run_iff _ _).mp QuotedSource.Controls.named_code_then_activation

theorem captures_survive_execution :
    ∃ run : (step [.term]).Run (initial capturedProgram), Reads (program [.term]) run.last capturedResult :=
  (source_run_iff _ _).mp QuotedSource.Controls.nested_binder_capture_preserved

theorem loop_has_an_actual_event :
    ∃ target : Object [], Nonempty ((step []).effectCore.Event (step []).eventAdmission (initial looping) target) ∧
      Reads (program []) target looping :=
  reduction_has_event the_unquoted_body_can_reduce_forever_one_step_at_a_time

theorem quoted_loop_has_no_event (target : Object []) :
    ¬ Nonempty ((step []).effectCore.Event (step []).eventAdmission
      (initial (QuotedLambda.quote looping)) target) := quote_has_no_event looping target

theorem event_changes_occurrence {Γ : Ctx sig} {call : Term sig Γ .term} {target : Object Γ}
    (event : (step Γ).effectCore.Event (step Γ).eventAdmission (initial call) target) : target.2 = 1 := by
  rw [← event.target_eq]
  rfl

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuotedEvents
