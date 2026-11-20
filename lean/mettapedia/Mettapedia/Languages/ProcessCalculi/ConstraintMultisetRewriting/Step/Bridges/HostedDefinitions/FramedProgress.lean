import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.BranchProgress

/-!
# Ground equation execution beneath one returning source bind

The pending continuation returns data and performs no further call. Its
actual bind and return moves terminate even if the bind rejects the reply.
This is the continuation used by the public interpreter query.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.FramedProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

variable (rows : List (ProgramBinders.Equation MSig [] ()))
  (D : Discipline MSig [] ()) (supply : Nat → MClosed)

theorem return_normalizes (K : List (Constraint (BinderCore.keys rows) [] ()))
    (term : Data (BinderCore.keys rows) [] ()) :
    Acc (BranchProgress.Child rows D supply) ⟨K, .eval (.ret term), [], []⟩ := by
  refine .intro _ ?_
  rintro after ⟨_, world, nextWorld, children, moved, member, _⟩
  cases moved with
  | ret =>
      rw [Multiset.mem_singleton.mp member]
      exact BranchProgress.value_normalizes rows D supply K term

theorem value_to_return_normalizes (K : List (Constraint (BinderCore.keys rows) [] ()))
    (term : Data (BinderCore.keys rows) [] ()) (site : (BinderCore.keys rows).Site)
    (pattern result : Data (BinderCore.keys rows) [] ()) :
    Acc (BranchProgress.Child rows D supply) ⟨K, .value term, [.bindTo site pattern (.ret result)], []⟩ := by
  refine .intro _ ?_
  rintro after ⟨_, world, nextWorld, children, moved, member, _⟩
  cases moved with
  | letBind =>
      rw [Multiset.mem_singleton.mp member]
      exact return_normalizes rows D supply _ _

variable (grounded : ∀ rule ∈ rows, GroundRead.Grounding rule)

include grounded

theorem call_normalizes (call : MClosed)
    (normalizing : Acc (fun after before => ProgramBinders.Rewrites rows.get before after) call)
    (K : List (Constraint (BinderCore.keys rows) [] ()))
    (term : Data (BinderCore.keys rows) [] ()) (determined : Determines K term call)
    (site : (BinderCore.keys rows).Site) (pattern result : Data (BinderCore.keys rows) [] ()) :
    Acc (BranchProgress.Child rows D supply)
      ⟨K, .eval (.apply term), [.bindTo site pattern (.ret result)], []⟩ := by
  induction normalizing generalizing K term with
  | intro call _ smaller =>
      refine .intro _ ?_
      rintro after ⟨_, world, nextWorld, children, moved, member, live⟩
      cases moved with
      | apply =>
          obtain ⟨index, rfl⟩ := (BinderCore.mem_callBranches rows D).mp (Multiset.mem_coe.mp member)
          obtain ⟨answer, answered, output⟩ := GroundCall.selected_determines rows index world.scope
            K term call determined (grounded _ (List.get_mem _ _)) live
          exact smaller answer ⟨index, answered⟩ _ _ output
      | unmatched =>
          rw [Multiset.mem_singleton.mp member]
          exact value_to_return_normalizes rows D supply K term site pattern result

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.FramedProgress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.FramedProgress.call_normalizes
