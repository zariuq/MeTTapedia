import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotionRecovery

/-!
# Common-frame transport computed from contextual certificate data

The injective capture map is computed from the prepared helper frames without
checking the guards or storing a source path. When the certificate is accepted,
the map agrees with the original execution path's capture map. This supplies a
common declaration frame for process data while retaining every earlier scope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessTransport

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualGuardMatching

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt}

def captureExtension {before : Endpoint locals O Γ sort} (prepared : Prepared locals before) :
    Extension before.declarations :=
  ContextualComputedFreshFrame.capturedDeclarationExtension locals before.declarations prepared.update

def namesAlong {source : Endpoint locals O Γ sort} : {target : Endpoint locals O Γ sort} →
    Certificate locals source target → source.Names → target.Names
  | _, .nil _ => id
  | _, .snoc past next => (captureExtension next).name ∘ namesAlong past

theorem namesAlong_injective {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) : Function.Injective (namesAlong certificate) := by
  induction certificate with
  | nil => exact Function.injective_id
  | snoc past next earlier => exact (captureExtension next).injective.comp earlier

theorem namesAlong_preserves {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) (name : source.Names) :
    target.declarations (namesAlong certificate name) = source.declarations name := by
  induction certificate with
  | nil => rfl
  | snoc past next earlier => exact ((captureExtension next).preserves _).trans earlier

def extension {source target : Endpoint locals O Γ sort} (certificate : Certificate locals source target) :
    Extension source.declarations where
  Names := target.Names
  declarations := target.declarations
  name := namesAlong certificate
  injective := namesAlong_injective certificate
  preserves := namesAlong_preserves certificate

def assignment {source target : Endpoint locals O Γ sort} (certificate : Certificate locals source target) :
    Assignment source.declarations target.declarations := (extension certificate).assignment

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
private theorem reindex_name_congr {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    {first second : V → W} (same : first = second)
    (firstPreserves : ∀ name, target (first name) = source name)
    (secondPreserves : ∀ name, target (second name) = source name) :
    reindex first firstPreserves = reindex second secondPreserves := by
  cases same
  rfl

theorem namesAlong_realize {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) (checked : Checked locals certificate.questions) :
    ContextualExecution.namesAlong (certificate.realize checked) = namesAlong certificate := by
  induction certificate with
  | nil => rfl
  | snoc past next earlier =>
      funext name
      change (next.firing _).captureName
        (ContextualExecution.namesAlong (past.realize _) name) =
          (captureExtension next).name (namesAlong past name)
      rw [earlier]
      rfl

theorem assignment_realize {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) (checked : Checked locals certificate.questions) :
    ContextualExecution.pathAssignment (certificate.realize checked) = assignment certificate := by
  unfold ContextualExecution.pathAssignment ContextualExecution.pathExtension assignment extension
  simp only [Extension.assignment]
  exact reindex_name_congr (namesAlong_realize certificate checked) _ _

theorem namesAlong_append {source middle target : Endpoint locals O Γ sort}
    (first : Certificate locals source middle) (second : Certificate locals middle target) :
    namesAlong (first.append second) = namesAlong second ∘ namesAlong first := by
  induction second with
  | nil => rfl
  | snoc past next earlier =>
      funext name
      change (captureExtension next).name (namesAlong (first.append past) name) =
        (captureExtension next).name (namesAlong past (namesAlong first name))
      rw [earlier]
      rfl

theorem assignment_append {source middle target : Endpoint locals O Γ sort}
    (first : Certificate locals source middle) (second : Certificate locals middle target) :
    assignment (first.append second) = Assignment.compose (assignment second) (assignment first) := by
  unfold assignment extension Extension.assignment
  rw [reindex_compose]
  exact reindex_name_congr (namesAlong_append first second) _ _

/-- Even unchecked guards do not weaken the equation prefix: the complete
prepared target contains the original equations under its pure capture map. -/
theorem prepared_models_refine {before : Endpoint locals O Γ sort} (prepared : Prepared locals before)
    {Future : Type} {future : Future → MetaArity S}
    (candidate : Assignment prepared.target.declarations future)
    (models : ContextualFrameUnifier.Models candidate prepared.target.inventory.configuration.equations) :
    ContextualFrameUnifier.Models (Assignment.compose candidate (captureExtension prepared).assignment)
      before.inventory.configuration.equations := by
  have original := (ContextualFrameUnifier.models_mapProblem
    (ContextualComputedFreshFrame.includeSource prepared.update) candidate _).mp models
  have prior := ContextualActivatedStep.models_refine_old_frame locals before.declarations future
    before.occupied prepared.selection prepared.rule before.inventory.rows before.inventory.configuration
    (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource prepared.update)) original
  dsimp only [captureExtension]
  rw [ContextualComputedFreshFrame.capturedDeclarationExtension_assignment]
  exact Eq.mpr (congrArg (fun change => ContextualFrameUnifier.Models change
    before.inventory.configuration.equations)
    (Assignment.compose_associative (ContextualSelectionViews.capturedTarget locals before.declarations)
      (ContextualComputedFreshFrame.includeSource prepared.update) candidate)) prior

theorem assignment_models_refine {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) {Future : Type} {future : Future → MetaArity S}
    (candidate : Assignment target.declarations future)
    (models : ContextualFrameUnifier.Models candidate target.inventory.configuration.equations) :
    ContextualFrameUnifier.Models (Assignment.compose candidate (assignment certificate))
      source.inventory.configuration.equations := by
  induction certificate with
  | nil =>
      change ContextualFrameUnifier.Models (Assignment.compose candidate (generator source.declarations)) _
      rw [Assignment.compose_identity_right]
      exact models
  | snoc past next earlier =>
      have prior := prepared_models_refine next candidate models
      have oldest := earlier (Assignment.compose candidate (captureExtension next).assignment) prior
      have combine : assignment (.snoc past next) =
          Assignment.compose (captureExtension next).assignment (assignment past) := by
        unfold assignment extension Extension.assignment
        rw [reindex_compose]
        rfl
      rw [combine]
      exact Eq.mpr (congrArg (fun change => ContextualFrameUnifier.Models change
        source.inventory.configuration.equations)
        (Assignment.compose_associative (assignment past) (captureExtension next).assignment candidate)) oldest

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessTransport
