import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.GroundCall

/-!
# Actual source branch descent for ground equation programs

A descendant is a live child of an actual source move, with its world and
all generated siblings retained in the witness. This auxiliary relation
records execution of the existing source semantics. Ground dependencies
connect each live equation child to a genuine closed rewrite.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.BranchProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration

variable (rows : List (ProgramBinders.Equation MSig [] ()))
  (D : Discipline MSig [] ()) (supply : Nat → MClosed)

def Child (after before : Branch (BinderCore.keys rows) [] () D.Ty) : Prop :=
  Solvable before.store ∧ ∃ world nextWorld children,
    Move D (BinderCore.program rows) supply world before nextWorld children ∧
      after ∈ children ∧ Solvable after.store

theorem value_normalizes (K : List (Constraint (BinderCore.keys rows) [] ()))
    (term : Data (BinderCore.keys rows) [] ()) :
    Acc (Child rows D supply) ⟨K, .value term, [], []⟩ := by
  refine .intro _ ?_
  rintro after ⟨_, world, nextWorld, children, moved, _, _⟩
  cases moved

variable (grounded : ∀ rule ∈ rows, GroundRead.Grounding rule)

include grounded

theorem call_normalizes (call : MClosed)
    (normalizing : Acc (fun after before => ProgramBinders.Rewrites rows.get before after) call)
    (K : List (Constraint (BinderCore.keys rows) [] ()))
    (term : Data (BinderCore.keys rows) [] ()) (determined : Determines K term call) :
    Acc (Child rows D supply) ⟨K, .eval (.apply term), [], []⟩ := by
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
          exact value_normalizes rows D supply K term

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.BranchProgress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.BranchProgress.call_normalizes
