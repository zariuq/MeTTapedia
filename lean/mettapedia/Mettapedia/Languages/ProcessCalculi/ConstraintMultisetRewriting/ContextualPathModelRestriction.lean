import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathInclusions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFrameAsks

/-!
# Actual final equation models restrict to retained contextual prefixes

The original activation problem retains incoming equations under the pure
capture inclusion. The computed helper frame and endpoint equality preserve
that restriction. Composition gives the sound direction for entire actual
paths. No converse for the later physical state or additional equations is
asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualFrameUpdate

namespace ContextualComputedFreshFrame

variable {S : Signature} {Local Shared : Type}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def capturedDeclarationExtension
    {problem : ContextualResidual.Problem (ContextualActivatedStep.target locals captures)}
    (update : Update problem) : Extension captures where
  Names := (Mettapedia.Logic.LP.ScopedVar Local ⊕ Shared) ⊕ (update.Variables ⊕ Empty)
  declarations := active (ContextualActivatedStep.target locals captures) update.declaration
  name := Sum.inl ∘ Sum.inr
  injective := Sum.inl_injective.comp Sum.inr_injective
  preserves _ := rfl

theorem capturedDeclarationExtension_assignment
    {problem : ContextualResidual.Problem (ContextualActivatedStep.target locals captures)} (update : Update problem) :
    (capturedDeclarationExtension locals captures update).assignment =
      Assignment.compose (includeSource update) (ContextualSelectionViews.capturedTarget locals captures) := by
  funext name
  change generator (active (ContextualActivatedStep.target locals captures) update.declaration) (.inl (.inr name)) =
    instantiate (includeSource update) (generator (ContextualActivatedStep.target locals captures) (.inr name))
  rw [instantiate_generator]
  exact (ContextualFreshFrameScopeLedger.includeSource_image update (.inr name)).symm

end ContextualComputedFreshFrame

namespace ContextualExecution

variable {S : Signature} {Local O : Type} (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}

namespace Endpoint

variable {locals}

def equalityExtension {first second : Endpoint locals O Γ sort} (same : first = second) : Extension first.declarations where
  Names := second.Names
  declarations := second.declarations
  name := namesEquiv same
  injective := (namesEquiv same).injective
  preserves := namesEquiv_preserves same

theorem equalityExtension_identity (endpoint : Endpoint locals O Γ sort) :
    (equalityExtension (rfl : endpoint = endpoint)).assignment = generator endpoint.declarations := rfl

private theorem mapProblem_identity {V : Type} (declaration : V → MetaArity S)
    (problem : EquationStore (Term (signature S declaration) Γ sort)) :
    ContextualFrameUnifier.mapProblem (generator declaration) problem = problem := by
  induction problem with
  | nil => rfl
  | cons equation rest earlier =>
      change (instantiate (generator declaration) equation.1, instantiate (generator declaration) equation.2) ::
        ContextualFrameUnifier.mapProblem (generator declaration) rest = equation :: rest
      rw [ContextualFamily.instantiate_identity, ContextualFamily.instantiate_identity, earlier]

theorem configuration_map_equality {first second : Endpoint locals O Γ sort} (same : first = second) :
    ContextualTransportedActivation.configurationMap (equalityExtension same).assignment first.inventory.configuration =
      second.inventory.configuration := by
  cases same
  rw [equalityExtension_identity]
  exact congrArg (fun equations => Configuration.mk equations first.inventory.configuration.present)
    (mapProblem_identity first.declarations first.inventory.configuration.equations)

theorem models_pull_equality {first second : Endpoint locals O Γ sort} (same : first = second)
    {Future : Type} {future : Future → MetaArity S} (candidate : Assignment second.declarations future)
    (models : ContextualFrameUnifier.Models candidate second.inventory.configuration.equations) :
    ContextualFrameUnifier.Models (Assignment.compose candidate (equalityExtension same).assignment)
      first.inventory.configuration.equations := by
  cases same
  change ContextualFrameUnifier.Models (Assignment.compose candidate (generator first.declarations)) _
  rw [Assignment.compose_identity_right]
  exact models

end Endpoint

variable [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace Firing

variable {locals} {before after : Endpoint locals O Γ sort}

theorem captureExtension_split (firing : Firing locals before after) :
    firing.captureExtension =
      (ContextualComputedFreshFrame.capturedDeclarationExtension locals before.declarations firing.update).trans
        (Endpoint.equalityExtension firing.destination.symm) := rfl

theorem captureAssignment_split (firing : Firing locals before after) :
    firing.captureExtension.assignment = Assignment.compose
      (Endpoint.equalityExtension firing.destination.symm).assignment
      (Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
        (ContextualSelectionViews.capturedTarget locals before.declarations)) := by
  funext name
  change reindex firing.captureName firing.captureName_preserves name =
    instantiate (Endpoint.equalityExtension firing.destination.symm).assignment
      (instantiate (ContextualComputedFreshFrame.includeSource firing.update)
        (generator (ContextualActivatedStep.target locals before.declarations) (.inr name)))
  rw [instantiate_generator, ContextualFreshFrameScopeLedger.includeSource_image]
  change reindex firing.captureName firing.captureName_preserves name =
    instantiate (Endpoint.equalityExtension firing.destination.symm).assignment
      (generator (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals before.declarations)
        firing.update.declaration) (.inl (.inr name)))
  dsimp only [Endpoint.equalityExtension, computedTarget]
  rw [instantiate_generator]
  rfl

theorem models_refine_old (firing : Firing locals before after)
    {Future : Type} {future : Future → MetaArity S} (candidate : Assignment after.declarations future)
    (models : ContextualFrameUnifier.Models candidate after.inventory.configuration.equations) :
    ContextualFrameUnifier.Models (Assignment.compose candidate firing.captureExtension.assignment)
      before.inventory.configuration.equations := by
  let relocation : Assignment
      (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals before.declarations)
        firing.update.declaration) after.declarations :=
    (Endpoint.equalityExtension firing.destination.symm).assignment
  let moved : Assignment
      (ContextualComputedFreshFrame.active (ContextualActivatedStep.target locals before.declarations)
        firing.update.declaration) future := Assignment.compose candidate relocation
  have computedModel : ContextualFrameUnifier.Models moved
      (ContextualFrameUnifier.mapProblem (ContextualComputedFreshFrame.includeSource firing.update)
        (ContextualActivatedStep.problem locals before.declarations before.occupied firing.selection firing.rule
          before.inventory.rows before.inventory.configuration)) :=
    Endpoint.models_pull_equality firing.destination.symm candidate models
  have originalModel := (ContextualFrameUnifier.models_mapProblem (ContextualComputedFreshFrame.includeSource firing.update)
    moved (ContextualActivatedStep.problem locals before.declarations before.occupied firing.selection firing.rule
      before.inventory.rows before.inventory.configuration)).mp computedModel
  have oldModel := ContextualActivatedStep.models_refine_old_frame locals before.declarations future
    before.occupied firing.selection firing.rule before.inventory.rows before.inventory.configuration
    (Assignment.compose moved (ContextualComputedFreshFrame.includeSource firing.update)) originalModel
  rw [captureAssignment_split]
  change ContextualFrameUnifier.Models (Assignment.compose candidate
    (Assignment.compose relocation (Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
      (ContextualSelectionViews.capturedTarget locals before.declarations)))) _
  simpa only [Assignment.compose_associative, moved] using oldModel

end Firing

variable {locals}

theorem models_restrict_to_prefix {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target)
    {Future : Type} {future : Future → MetaArity S} (candidate : Assignment target.declarations future)
    (models : ContextualFrameUnifier.Models candidate target.inventory.configuration.equations) :
    ContextualFrameUnifier.Models (Assignment.compose candidate (pathAssignment path))
      source.inventory.configuration.equations := by
  induction path with
  | nil =>
      change ContextualFrameUnifier.Models (Assignment.compose candidate (generator source.declarations)) _
      rw [Assignment.compose_identity_right]
      exact models
  | cons past edge earlier =>
      have lastModel : ContextualFrameUnifier.Models
          (Assignment.compose candidate (pathAssignment (Quiver.Hom.toPath edge))) _ :=
        edge.models_refine_old candidate models
      have priorModel := earlier (Assignment.compose candidate (pathAssignment (Quiver.Hom.toPath edge))) lastModel
      change ContextualFrameUnifier.Models
        (Assignment.compose candidate (pathAssignment (past.comp (Quiver.Hom.toPath edge)))) _
      rw [pathAssignment_comp]
      rw [Assignment.compose_associative]
      exact priorModel

theorem final_model_satisfies_prefixSnapshot {source target : Endpoint locals O Γ sort} (path : Quiver.Path source target)
    {Future : Type} {future : Future → MetaArity S} (candidate : Assignment target.declarations future)
    (models : ContextualFrameUnifier.Models candidate target.inventory.configuration.equations) :
    ContextualFrameUnifier.Models candidate (prefixSnapshot path).configuration.equations :=
  (ContextualFrameUnifier.models_mapProblem (pathAssignment path) candidate source.inventory.configuration.equations).mpr
    (models_restrict_to_prefix path candidate models)

end ContextualExecution
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
