import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication

/-!
# Actual unfinished updates still give exact conditional answers

A returned value carries its remaining equations. Both are interpreted in
one returned declaration family and opened together in a future family.
An arbitrary actual update preserves exactly the original source instances
in this form. Completing the queue recovers ordinary reusable values.

This is an answer semantics, not an additional stored-row constructor or a
completed native publication protocol. The logical equation package does
not prescribe physical copying or a store representation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalAnswers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching

variable {S : Signature} {V W Next : Type} {source : V → MetaArity S}

structure Answer (declaration : W → MetaArity S) (context : Ctx S) (sort : S.Srt) where
  obligations : ContextualResidual.Problem declaration
  value : Term (signature S declaration) context sort

def Answer.Instances {declaration : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    (answer : Answer declaration Γ sort) (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) : Prop :=
  ContextualPublication.SourceInstances answer.obligations answer.value next pattern

def ofUpdate {problem : ContextualResidual.Problem source} (update : ContextualFrameUpdate.Update problem)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S source) Γ sort) : Answer update.declaration Γ sort :=
  ⟨update.remaining, instantiate update.answer value⟩

/-- No empty-queue assumption is needed: the original source meaning is
exactly the computed value together with its actual residual obligations. -/
theorem ofUpdate_exact {problem : ContextualResidual.Problem source} (update : ContextualFrameUpdate.Update problem)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S source) Γ sort)
    (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    (ofUpdate update value).Instances next pattern ↔ ContextualPublication.SourceInstances problem value next pattern := by
  constructor
  · rintro ⟨extension, images, obligations, same⟩
    refine ⟨extension, Assignment.compose images update.answer,
      update.valid.sound extension.declarations images obligations, ?_⟩
    exact (Assignment.instantiate_compose images update.answer value).trans same
  · rintro ⟨extension, candidate, model, same⟩
    obtain ⟨images, obligations, components⟩ := update.factors extension.declarations candidate model
    refine ⟨extension, images, obligations, ?_⟩
    exact (ContextualFrameUnifier.factor_terms candidate update.answer images components value).symm.trans same

theorem forget_obligations {declaration : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    (answer : Answer declaration Γ sort) (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort)
    (matched : answer.Instances next pattern) : ContextualPublication.Instances declaration answer.value next pattern := by
  obtain ⟨extension, images, _, same⟩ := matched
  exact ⟨extension, images, same⟩

theorem finished_ordinary_iff {declaration : W → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    (answer : Answer declaration Γ sort) (finished : answer.obligations = [])
    (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    answer.Instances next pattern ↔ ContextualPublication.Instances declaration answer.value next pattern := by
  constructor
  · exact forget_obligations answer next pattern
  · rintro ⟨extension, images, same⟩
    refine ⟨extension, images, ?_, same⟩
    rw [finished]
    intro equation member
    cases member

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalAnswers
