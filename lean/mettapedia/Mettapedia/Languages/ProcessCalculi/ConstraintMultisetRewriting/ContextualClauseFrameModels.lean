import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRealizations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseFrames

/-!
# Source clause models fill their native activation frame without new assumptions

The source family already has query images and a scoped copy of every old
private arity. Native slots outside the selected frame may reuse those
images. The resulting valuation retracts the source-frame embedding, in
the same future family. This is needed when several ports are interpreted
jointly, without silently changing their shared query assignment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseFrameModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualConjunctiveQueries ContextualClauseFrames ContextualConditionalRealizations

variable {S : Signature} {Local Query Shared Next : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {next : Next → MetaArity S}

def expand (occupied : Finset Nat) (images : Assignment (family queries locals captures) next) :
    Assignment (nativeActive queries locals captures) next
  | .inl ⟨scope, .inl name⟩ => images (.inr (.inl ⟨scope - occupied.sup id, name⟩))
  | .inl ⟨_, .inr name⟩ => images (.inl name)
  | .inr name => images (.inr (.inr name))

theorem expand_square (occupied : Finset Nat) (images : Assignment (family queries locals captures) next) :
    Assignment.compose (expand queries locals captures occupied images)
      (frame queries locals captures occupied).assignment = images := by
  funext name
  dsimp only [Assignment.compose]
  rcases name with name | name | name
  · erw [frame_query, instantiate_generator]
    rfl
  · erw [frame_row, instantiate_generator]
    change images (.inr (.inl ⟨occupied.sup id + name.scope - occupied.sup id, name.name⟩)) = _
    cases name with
    | mk scope name =>
        let atScope : Nat → Term (signature S next) (locals name).1 (locals name).2 :=
          fun index => by exact images (.inr (.inl ⟨index, name⟩))
        exact congrArg atScope (Nat.add_sub_cancel_left (occupied.sup id) scope)
  · erw [frame_capture, instantiate_generator]
    rfl

theorem models_expand (occupied : Finset Nat) (images : Assignment (family queries locals captures) next)
    (problem : ContextualResidual.Problem (family queries locals captures)) :
    ContextualResidual.Models (expand queries locals captures occupied images)
      (ContextualResidual.mapProblem (frame queries locals captures occupied).assignment problem) ↔
      ContextualResidual.Models images problem := by
  rw [ContextualResidual.models_mapProblem, expand_square]

theorem answer_frame_iff (occupied : Finset Nat)
    (problem : ContextualResidual.Problem (family queries locals captures))
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S (family queries locals captures)) Γ sort)
    (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    AnswerRealizes ⟨ContextualResidual.mapProblem (frame queries locals captures occupied).assignment problem,
      instantiate (frame queries locals captures occupied).assignment value⟩ next pattern ↔
      AnswerRealizes ⟨problem, value⟩ next pattern := by
  constructor
  · rintro ⟨images, model, same⟩
    exact ⟨Assignment.compose images (frame queries locals captures occupied).assignment,
      (ContextualResidual.models_mapProblem _ _ _).mp model,
      (Assignment.instantiate_compose images (frame queries locals captures occupied).assignment value).trans same⟩
  · rintro ⟨images, model, same⟩
    refine ⟨expand queries locals captures occupied images, (models_expand queries locals captures occupied images problem).mpr model, ?_⟩
    rw [← Assignment.instantiate_compose, expand_square]
    exact same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseFrameModels
