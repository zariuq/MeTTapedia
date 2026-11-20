import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NativePublic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ProgramHeads

/-!
# Actual public protocol executions and rejected non-done replies

These controls test the query protocol independently of object evaluation.
A reached done reply becomes a public answer through real source and native
execution. An unrelated literal reply cannot be presented as a result.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

theorem fixedSeparated : HeadSeparated (ProgramLayout.rows [] []) activeTag doneTag :=
  ProgramHeads.assembled [] [] (fun _ member => (List.not_mem_nil member).elim)
    (fun _ member => (List.not_mem_nil member).elim)

theorem done_reply_is_a_public_answer (D : Discipline MSig [] ()) (supply : Nat → MClosed) (value : MClosed) :
    ∃ after, Runs D (BinderCore.program (ProgramLayout.rows [] [])) supply
      (Config.initial (fun _ => 0) (PublicQuery.query [] [] (doneC value))) after ∧
      HasAnswer (D := D) (ProgramLayout.rows [] []) after value :=
  (PublicAnswers.public_answers_iff [] [] D supply fixedSeparated (doneC value) value (.inr rfl)).mp .refl

theorem done_reply_is_a_native_answer (D : Discipline MSig [] ()) (N : Hosting.Nodes MSig [] ())
    (supply : Nat → MClosed) (value : MClosed) :
    ∃ next, (FrontierArrow.target (D := D) N (BinderCore.program (ProgramLayout.rows [] []))).MultiStep
      (FrontierArrow.initialState (D := D) N (BinderCore.program (ProgramLayout.rows [] []))
        (PublicQuery.query [] [] (doneC value))) next ∧
      NativePublic.Contains (FrontierArrow.answers N next) value :=
  (NativePublic.public_answers_by_native [] [] D N supply fixedSeparated (doneC value) value (.inr rfl)).mp .refl

def otherReply : MClosed := nodeC "ordinary-reply" []

theorem other_has_no_machine_step (after : MClosed) :
    ¬ ProgramBinders.Rewrites (ProgramLayout.rows [] []).get otherReply after := by
  rintro ⟨index, assignment, matched, _⟩
  have head := literalHead_instantiate
    (((ProgramLayout.rows [] []).get index).assign assignment (ProgramBinders.ground MSig))
    (fixedSeparated.lhs index)
  rw [matched, literalHead_include] at head
  have impossible : ("ordinary-reply" : String) = activeTag := Option.some.inj head
  exact (by decide : ("ordinary-reply" : String) ≠ activeTag) impossible

theorem other_never_reaches_done (value : MClosed) :
    ¬ PublicInvariant.Reach [] [] otherReply (doneC value) := by
  intro executed
  have stays : ∀ {after}, PublicInvariant.Reach [] [] otherReply after → after = otherReply := by
    intro after steps
    induction steps with
    | refl => rfl
    | tail _ last same => exact False.elim (other_has_no_machine_step _ (same ▸ last))
  have same := congrArg closedHead (stays executed)
  exact (by decide : (doneTag : String) ≠ "ordinary-reply") (Option.some.inj same)

theorem other_reply_is_not_a_public_answer (D : Discipline MSig [] ()) (supply : Nat → MClosed)
    (value : MClosed) :
    ¬ ∃ after, Runs D (BinderCore.program (ProgramLayout.rows [] [])) supply
      (Config.initial (fun _ => 0) (PublicQuery.query [] [] otherReply)) after ∧
      HasAnswer (D := D) (ProgramLayout.rows [] []) after value := by
  rintro ⟨after, executed, answered⟩
  exact other_never_reaches_done value
    (PublicInvariant.public_answer_reflected [] [] D supply executed answered)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicControls.done_reply_is_a_native_answer
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicControls.other_reply_is_not_a_public_answer
