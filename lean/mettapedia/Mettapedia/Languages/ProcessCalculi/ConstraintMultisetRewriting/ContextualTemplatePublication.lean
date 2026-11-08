import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplateSource
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationExecution

/-!
# Publishing a constructed template with declared shared captures

Template-private variables and actor references have different origins.
The former become private row keys; the latter retain their original source
identities in the actual post-solver declaration family. Constructor arguments,
object binders and repeated occurrences are transported by contextual
instantiation. Publication does not normalize a shared capture into an unrelated
returned helper or identify distinct production-port origins.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualTemplateSource
open ContextualScopeSupport

variable {S : Signature} {Local Inner Shared V : Type}
    (locals : Local → MetaArity S) (inners : Inner → MetaArity S)
    (captures : Shared → MetaArity S)

abbrev Post (returned : V → MetaArity S) :=
  ContextualComputedFreshFrame.active (Active locals inners captures) returned

def decoder (returned : V → MetaArity S) :
    Assignment (Post locals inners captures returned)
      (ContextualSelectionViews.source (Expanded locals inners) (Post locals inners captures returned))
  | .inl (.inl ⟨_, .inr entry⟩) =>
      generator (ContextualSelectionViews.source (Expanded locals inners) (Post locals inners captures returned))
        (.inl (.inr entry))
  | identity =>
      generator (ContextualSelectionViews.source (Expanded locals inners) (Post locals inners captures returned))
        (.inr identity)

theorem decoder_respects (returned : V → MetaArity S)
    (scopes : (ScopedVar (Local ⊕ (Nat × Inner)) ⊕ Shared) ⊕ (V ⊕ Empty) → Finset Nat) :
    Respects scopes (privateScopes (Local := Local ⊕ (Nat × Inner)) scopes)
      (decoder locals inners captures returned) := by
  intro identity
  cases identity with
  | inl identity =>
      cases identity with
      | inl identity =>
          rcases identity with ⟨scope, name⟩
          cases name with
          | inl name =>
              dsimp only [decoder, Covered]
              erw [term_generator]
              exact Finset.Subset.refl _
          | inr entry =>
              dsimp only [decoder, Covered]
              erw [term_generator]
              exact Finset.empty_subset _
      | inr name =>
          dsimp only [decoder, Covered]
          erw [term_generator]
          exact Finset.Subset.refl _
  | inr identity =>
      cases identity with
      | inl identity =>
          dsimp only [decoder, Covered]
          erw [term_generator]
          exact Finset.Subset.refl _
      | inr impossible => exact nomatch impossible

variable {problem : ContextualResidual.Problem (Active locals inners captures)}

def captureValues (update : ContextualFrameUpdate.Update problem) (scope : Nat) :
    Assignment (Actor locals captures) (Post locals inners captures update.declaration) :=
  Assignment.compose (ContextualComputedFreshFrame.includeSource update)
    (actorAt locals inners captures scope)

theorem included_generator (update : ContextualFrameUpdate.Update problem)
    (identity : ScopedVar (Local ⊕ (Nat × Inner)) ⊕ Shared) :
    instantiate (ContextualComputedFreshFrame.includeSource update)
        (generator (Active locals inners captures) identity) =
      generator (Post locals inners captures update.declaration) (.inl identity) :=
  (instantiate_generator (ContextualComputedFreshFrame.includeSource update) identity).trans
    (ContextualFreshFrameScopeLedger.includeSource_image update identity)

theorem capture_local (update : ContextualFrameUpdate.Update problem) (scope : Nat) (identity : Local) :
    captureValues locals inners captures update scope (.inl identity) =
      generator (Post locals inners captures update.declaration)
        (.inl (.inl (ScopedVar.at scope (.inl identity)))) :=
  (congrArg (instantiate (ContextualComputedFreshFrame.includeSource update))
    (actorAt_local locals inners captures scope identity)).trans
      (included_generator locals inners captures update (.inl (ScopedVar.at scope (.inl identity))))

theorem capture_shared (update : ContextualFrameUpdate.Update problem) (scope : Nat) (identity : Shared) :
    captureValues locals inners captures update scope (.inr identity) =
      generator (Post locals inners captures update.declaration) (.inl (.inr identity)) :=
  (congrArg (instantiate (ContextualComputedFreshFrame.includeSource update))
    (actorAt_shared locals inners captures scope identity)).trans
      (included_generator locals inners captures update (.inr identity))

theorem decoder_on_actor (update : ContextualFrameUpdate.Update problem) (scope : Nat)
    (identity : Local ⊕ Shared) :
    instantiate (decoder locals inners captures update.declaration)
        (captureValues locals inners captures update scope identity) =
      instantiate (ContextualSelectionViews.capturedSource (Expanded locals inners)
        (Post locals inners captures update.declaration))
        (captureValues locals inners captures update scope identity) := by
  cases identity with
  | inl identity =>
      have image := capture_local locals inners captures update scope identity
      have left := congrArg (instantiate (decoder locals inners captures update.declaration)) image
      have right := congrArg (instantiate (ContextualSelectionViews.capturedSource (Expanded locals inners)
        (Post locals inners captures update.declaration))) image
      exact left.trans ((instantiate_generator (decoder locals inners captures update.declaration) _).trans
        ((instantiate_generator (ContextualSelectionViews.capturedSource (Expanded locals inners)
          (Post locals inners captures update.declaration)) _).symm.trans right.symm))
  | inr identity =>
      have image := capture_shared locals inners captures update scope identity
      have left := congrArg (instantiate (decoder locals inners captures update.declaration)) image
      have right := congrArg (instantiate (ContextualSelectionViews.capturedSource (Expanded locals inners)
        (Post locals inners captures update.declaration))) image
      exact left.trans ((instantiate_generator (decoder locals inners captures update.declaration) _).trans
        ((instantiate_generator (ContextualSelectionViews.capturedSource (Expanded locals inners)
          (Post locals inners captures update.declaration)) _).symm.trans right.symm))

theorem stored_decodes_the_compiled_body (update : ContextualFrameUpdate.Update problem) (scope port : Nat)
    {Γ : Ctx S} {sort : S.Srt}
    (body : Term (signature S (Blueprint locals inners captures)) Γ sort) :
    instantiate (decoder locals inners captures update.declaration)
        (instantiate (ContextualComputedFreshFrame.includeSource update)
          (instantiate (templateAt locals inners captures scope port) body)) =
      ContextualStoredRows.asTemplate (Expanded locals inners) (Post locals inners captures update.declaration)
        (stored locals inners captures (captureValues locals inners captures update scope) port body) := by
  change _ = instantiate (storedBody locals inners captures
    (captureValues locals inners captures update scope) port) body
  have assignments : Assignment.compose
      (Assignment.compose (decoder locals inners captures update.declaration)
        (ContextualComputedFreshFrame.includeSource update)) (templateAt locals inners captures scope port) =
      storedBody locals inners captures (captureValues locals inners captures update scope) port := by
    funext identity
    have nested := Assignment.instantiate_compose (decoder locals inners captures update.declaration)
      (ContextualComputedFreshFrame.includeSource update) (templateAt locals inners captures scope port identity)
    refine nested.trans ?_
    cases identity with
    | inl identity =>
        have sourceImage := (congrArg (instantiate (ContextualComputedFreshFrame.includeSource update))
          (templateAt_private locals inners captures scope port identity)).trans
            (included_generator locals inners captures update (.inl (ScopedVar.at scope (.inr (port,identity)))))
        exact (congrArg (instantiate (decoder locals inners captures update.declaration)) sourceImage).trans
          (instantiate_generator (decoder locals inners captures update.declaration) _)
    | inr identity =>
        rw [templateAt_capture]
        exact decoder_on_actor locals inners captures update scope identity
  exact (Assignment.instantiate_compose (decoder locals inners captures update.declaration)
    (ContextualComputedFreshFrame.includeSource update)
    (instantiate (templateAt locals inners captures scope port) body)).symm.trans
      ((Assignment.instantiate_compose
        (Assignment.compose (decoder locals inners captures update.declaration)
          (ContextualComputedFreshFrame.includeSource update))
        (templateAt locals inners captures scope port) body).symm.trans
          (congrArg (fun assignment => instantiate assignment body) assignments))

theorem stored_covered (update : ContextualFrameUpdate.Update problem) (scope port : Nat)
    (scopes : (ScopedVar (Local ⊕ (Nat × Inner)) ⊕ Shared) ⊕ (update.Variables ⊕ Empty) → Finset Nat)
    (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (body : Term (signature S (Blueprint locals inners captures)) Γ sort)
    (covered : Covered scopes occupied
      (instantiate (ContextualComputedFreshFrame.includeSource update)
        (instantiate (templateAt locals inners captures scope port) body))) :
    row (Expanded locals inners) (Post locals inners captures update.declaration) scopes
      (stored locals inners captures (captureValues locals inners captures update scope) port body) ⊆ occupied := by
  unfold row
  rw [← stored_decodes_the_compiled_body]
  exact covered_instantiate_of_respects scopes _ occupied
    (decoder locals inners captures update.declaration)
    (decoder_respects locals inners captures update.declaration scopes) covered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTemplatePublication
