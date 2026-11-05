import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAmalgamation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSourceState

/-!
# Comparing source worlds through returned names and conditional observations

Private declaration families may differ. Related models agree on the
exposed environment and on conditional row matches in every fresh future.
Both directions cover every model, allowing an injective extension for
unused private declarations. Physical occurrences remain identical.

The exposed family is an explicit parameter of the comparison. Arbitrary
inspection of private declaration tables is outside this observation
profile; object terms, quoted data and named spaces remain available.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows

variable {S : Signature} {Public Left Right Middle O Next : Type}
    {exposed : Public → MetaArity S} {lefts : Left → MetaArity S}
    {rights : Right → MetaArity S} {middles : Middle → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

structure Related (left : ContextualClauseSourceState.World lefts O Γ sort)
    (leftEnv : Assignment exposed left.declarations)
    (right : ContextualClauseSourceState.World rights O Γ sort)
    (rightEnv : Assignment exposed right.declarations)
    {next : Next → MetaArity S}
    (leftModel : Assignment left.declarations next) (rightModel : Assignment right.declarations next) : Prop where
  left_model : ContextualResidual.Models leftModel left.equations
  right_model : ContextualResidual.Models rightModel right.equations
  bindings : Assignment.compose leftModel leftEnv = Assignment.compose rightModel rightEnv
  rows : ∀ (later : Extension next) (pattern : Term (signature S later.declarations) Γ sort)
    (occurrence : O) (_present : occurrence ∈ left.present),
      Matches lefts left.declarations (Assignment.compose later.assignment leftModel) pattern (left.rows occurrence) ↔
        Matches rights right.declarations (Assignment.compose later.assignment rightModel) pattern (right.rows occurrence)

structure Equivalent (left : ContextualClauseSourceState.World lefts O Γ sort)
    (leftEnv : Assignment exposed left.declarations)
    (right : ContextualClauseSourceState.World rights O Γ sort)
    (rightEnv : Assignment exposed right.declarations) : Prop where
  physical : left.present = right.present
  forward : ∀ (Future : Type) (future : Future → MetaArity S)
    (candidate : Assignment left.declarations future), ContextualResidual.Models candidate left.equations →
      ∃ extension : Extension future, ∃ other : Assignment right.declarations extension.declarations,
        Related left leftEnv right rightEnv (Assignment.compose extension.assignment candidate) other
  backward : ∀ (Future : Type) (future : Future → MetaArity S)
    (candidate : Assignment right.declarations future), ContextualResidual.Models candidate right.equations →
      ∃ extension : Extension future, ∃ other : Assignment left.declarations extension.declarations,
        Related left leftEnv right rightEnv other (Assignment.compose extension.assignment candidate)

variable {left : ContextualClauseSourceState.World lefts O Γ sort}
    {right : ContextualClauseSourceState.World rights O Γ sort}
    {middle : ContextualClauseSourceState.World middles O Γ sort}
    {leftEnv : Assignment exposed left.declarations} {rightEnv : Assignment exposed right.declarations}
    {middleEnv : Assignment exposed middle.declarations} {next : Next → MetaArity S}
    {leftModel : Assignment left.declarations next} {rightModel : Assignment right.declarations next}
    {middleModel : Assignment middle.declarations next}

theorem Related.current_rows (related : Related left leftEnv right rightEnv leftModel rightModel)
    (pattern : Term (signature S next) Γ sort) (occurrence : O) (member : occurrence ∈ left.present) :
    Matches lefts left.declarations leftModel pattern (left.rows occurrence) ↔
      Matches rights right.declarations rightModel pattern (right.rows occurrence) := by
  have observed := related.rows (Extension.identity next) pattern occurrence member
  have unit : (Extension.identity next).assignment = generator next := rfl
  erw [unit, Assignment.compose_identity_left, Assignment.compose_identity_left] at observed
  exact observed

theorem Related.future (related : Related left leftEnv right rightEnv leftModel rightModel)
    (extension : Extension next) :
    Related left leftEnv right rightEnv (Assignment.compose extension.assignment leftModel)
      (Assignment.compose extension.assignment rightModel) := by
  refine ⟨ContextualResidual.models_compose related.left_model extension.assignment,
    ContextualResidual.models_compose related.right_model extension.assignment, ?_, ?_⟩
  · simpa only [Assignment.compose_associative] using
      congrArg (Assignment.compose extension.assignment) related.bindings
  · intro later pattern occurrence member
    have observed := related.rows (extension.trans later) pattern occurrence member
    erw [Extension.trans_assignment, ← Assignment.compose_associative, ← Assignment.compose_associative] at observed
    exact observed

theorem Related.symm (physical : left.present = right.present)
    (related : Related left leftEnv right rightEnv leftModel rightModel) :
    Related right rightEnv left leftEnv rightModel leftModel := by
  refine ⟨related.right_model, related.left_model, related.bindings.symm, ?_⟩
  intro later pattern occurrence member
  exact (related.rows later pattern occurrence (by rwa [physical])).symm

theorem Related.trans (physical : left.present = middle.present)
    (first : Related left leftEnv middle middleEnv leftModel middleModel)
    (second : Related middle middleEnv right rightEnv middleModel rightModel) :
    Related left leftEnv right rightEnv leftModel rightModel := by
  refine ⟨first.left_model, second.right_model, first.bindings.trans second.bindings, ?_⟩
  intro later pattern occurrence member
  exact (first.rows later pattern occurrence member).trans
    (second.rows later pattern occurrence (by rwa [← physical]))

theorem Related.restrict {Smaller : Type} {restricted : Smaller → MetaArity S}
    (related : Related left leftEnv right rightEnv leftModel rightModel)
    (environment : Assignment restricted exposed) :
    Related left (Assignment.compose leftEnv environment) right (Assignment.compose rightEnv environment)
      leftModel rightModel := by
  refine ⟨related.left_model, related.right_model, ?_, related.rows⟩
  rw [Assignment.compose_associative, Assignment.compose_associative, related.bindings]

theorem Equivalent.refl (world : ContextualClauseSourceState.World lefts O Γ sort)
    (environment : Assignment exposed world.declarations) : Equivalent world environment world environment := by
  have same : ∀ (Future : Type) (future : Future → MetaArity S)
      (candidate : Assignment world.declarations future), ContextualResidual.Models candidate world.equations →
      Related world environment world environment candidate candidate := by
    intro Future future candidate model
    exact ⟨model, model, rfl, fun _ _ _ _ => Iff.rfl⟩
  refine ⟨rfl, ?_, ?_⟩ <;> intro Future future candidate model
  · refine ⟨Extension.identity future, candidate, ?_⟩
    have unit : (Extension.identity future).assignment = generator future := rfl
    erw [unit, Assignment.compose_identity_left]
    exact same Future future candidate model
  · refine ⟨Extension.identity future, candidate, ?_⟩
    have unit : (Extension.identity future).assignment = generator future := rfl
    erw [unit, Assignment.compose_identity_left]
    exact same Future future candidate model

theorem Equivalent.symm (equivalent : Equivalent left leftEnv right rightEnv) :
    Equivalent right rightEnv left leftEnv := by
  refine ⟨equivalent.physical.symm, ?_, ?_⟩
  · intro Future future candidate model
    obtain ⟨extension, other, related⟩ := equivalent.backward Future future candidate model
    exact ⟨extension, other, related.symm equivalent.physical⟩
  · intro Future future candidate model
    obtain ⟨extension, other, related⟩ := equivalent.forward Future future candidate model
    exact ⟨extension, other, related.symm equivalent.physical⟩

theorem Equivalent.trans (first : Equivalent left leftEnv middle middleEnv)
    (second : Equivalent middle middleEnv right rightEnv) : Equivalent left leftEnv right rightEnv := by
  refine ⟨first.physical.trans second.physical, ?_, ?_⟩
  · intro Future future candidate model
    obtain ⟨earlier, intermediate, firstRelated⟩ := first.forward Future future candidate model
    obtain ⟨later, last, secondRelated⟩ := second.forward _ _ intermediate firstRelated.right_model
    refine ⟨earlier.trans later, last, ?_⟩
    erw [Extension.trans_assignment, ← Assignment.compose_associative]
    exact (firstRelated.future later).trans first.physical secondRelated
  · intro Future future candidate model
    obtain ⟨earlier, intermediate, secondRelated⟩ := second.backward Future future candidate model
    obtain ⟨later, initial, firstRelated⟩ := first.backward _ _ intermediate secondRelated.left_model
    refine ⟨earlier.trans later, initial, ?_⟩
    erw [Extension.trans_assignment, ← Assignment.compose_associative]
    exact firstRelated.trans first.physical (secondRelated.future later)

theorem Equivalent.restrict {Smaller : Type} {restricted : Smaller → MetaArity S}
    (equivalent : Equivalent left leftEnv right rightEnv) (environment : Assignment restricted exposed) :
    Equivalent left (Assignment.compose leftEnv environment) right (Assignment.compose rightEnv environment) := by
  refine ⟨equivalent.physical, ?_, ?_⟩
  · intro Future future candidate model
    obtain ⟨extension, other, related⟩ := equivalent.forward Future future candidate model
    exact ⟨extension, other, related.restrict environment⟩
  · intro Future future candidate model
    obtain ⟨extension, other, related⟩ := equivalent.backward Future future candidate model
    exact ⟨extension, other, related.restrict environment⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldComparison
