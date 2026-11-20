import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.FamilyInformation

/-!
# Every given joint model lifts through an actual native residual

The target of the given model is included into a genuine extension by unused
declarations. Its terms and observations remain injective. Carried private
locals retain the first model, the published original frame retains the
second, and unused private/helper names receive fresh generators.

The source/target equations are those of the actual execution and its actual
residual. No ground reading, replacement solver, or whole-state consistency
condition is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ResidualModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open NativeResidual

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {s : NativeState S O Γ sort}

variable (execution : ContextualConditionalExecution.Firing s.locals s.state)

def extension (target : Frames.Frame S) : ContextualGuardMatching.Extension target.arity :=
  ContextualGuardMatching.Extension.withLocals (laterTarget execution) target.arity

def extended (target : Frames.Frame S) : Frames.Frame S :=
  ⟨(extension execution target).Names,(extension execution target).declarations⟩

def inclusion (target : Frames.Frame S) : Assignment target.arity (extended execution target).arity :=
  (extension execution target).assignment

theorem inclusion_term_injective (target : Frames.Frame S) {Δ : Ctx S} {result : S.Srt} :
    Function.Injective (instantiate (Γ := Δ) (sort := result) (inclusion execution target)) :=
  (extension execution target).instantiate_injective

theorem inclusion_observation_injective (target : Frames.Frame S) :
    Function.Injective (instantiateObservation (inclusion execution target)) :=
  ContextualConditionalNaturality.observation_extension_injective (extension execution target)

theorem models_inclusion_iff {V : Type} {source : V → MetaArity S} (target : Frames.Frame S)
    (candidate : Assignment source target.arity) (problem : ContextualResidual.Problem source) :
    ContextualResidual.Models (Assignment.compose (inclusion execution target) candidate) problem ↔
      ContextualResidual.Models candidate problem := by
  constructor
  · intro model equation inside
    apply inclusion_observation_injective execution target
    exact (instantiateObservation_comp candidate (inclusion execution target) equation.1).trans
      ((model equation inside).trans (instantiateObservation_comp candidate (inclusion execution target) equation.2).symm)
  · intro model
    exact ContextualResidual.models_compose model (inclusion execution target)

variable {first second : ContextualResidual.Problem (ContextualActivatedStep.target s.locals s.state.declarations)}
  {target : Frames.Frame S}

def amalgam (joint : Joint s first second target) : Assignment (laterTarget execution) (extended execution target).arity
  | .inl ⟨scope,.inl name⟩ =>
      if shift execution ≤ scope then
        instantiate (inclusion execution target) (joint.left (.inl ⟨scope - shift execution,name⟩))
      else generator (extended execution target).arity (.inl (.inl ⟨scope,.inl name⟩))
  | .inl ⟨scope,.inr helper⟩ =>
      generator (extended execution target).arity (.inl (.inl ⟨scope,.inr helper⟩))
  | .inr (.inl name) => instantiate (inclusion execution target) (joint.right name)
  | .inr (.inr helper) => generator (extended execution target).arity (.inl (.inr (.inr helper)))

theorem amalgam_left (joint : Joint s first second target) :
    Assignment.compose (amalgam execution joint) (carry execution) =
      Assignment.compose (inclusion execution target) joint.left := by
  funext name
  cases name with
  | inl name =>
      refine (instantiate_generator (amalgam execution joint)
        (.inl (ScopedVar.at (name.scope + shift execution) (.inl name.name)))).trans ?_
      change (if shift execution ≤ name.scope + shift execution then _ else _) = _
      have bound : shift execution ≤ name.scope + shift execution := by omega
      refine (if_pos bound).trans ?_
      exact congrArg (fun openedScope : Nat => instantiate (Γ := (s.locals name.name).1) (sort := (s.locals name.name).2)
        (inclusion execution target)
        (joint.left (.inl (ScopedVar.at openedScope name.name)))) (Nat.add_sub_cancel name.scope (shift execution))
  | inr name =>
      exact (instantiate_generator (amalgam execution joint) (.inr (.inl (.inr name)))).trans
        (congrArg (instantiate (inclusion execution target)) (joint.agree_at name).symm)

theorem amalgam_right (joint : Joint s first second target) :
    Assignment.compose (Assignment.compose (amalgam execution joint) (laterCaptured execution))
        (ContextualComputedFreshFrame.includeSource execution.update) =
      Assignment.compose (inclusion execution target) joint.right := by
  funext name
  exact (congrArg (instantiate (Assignment.compose (amalgam execution joint) (laterCaptured execution)))
    (includeSource_apply execution name)).trans
      ((instantiate_generator (Assignment.compose (amalgam execution joint) (laterCaptured execution)) (.inl name)).trans
        (instantiate_generator (amalgam execution joint) (.inr (.inl name))))

theorem models_amalgam (firing : LiveFiring s)
    (unmade : ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read, occurrence ∉ execution.selection.made)
    (joint : Joint s firing.toNative.information (problemOf s execution.selection execution.rule) target) :
    ContextualResidual.Models (amalgam execution joint) (firing.residualAt execution).toNative.information := by
  apply (residual_models_iff execution firing unmade _).mpr
  constructor
  · rw [amalgam_right]
    exact ContextualResidual.models_compose joint.right_models (inclusion execution target)
  · rw [amalgam_left]
    exact ContextualResidual.models_compose
      ((models_problemOf_iff firing.selection firing.rule joint.left).mp joint.left_models).2 (inclusion execution target)

theorem read_left (joint : Joint s first second target) {Δ : Ctx S} {result : S.Srt}
    (term : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Δ result) :
    instantiate (amalgam execution joint) (instantiate (carry execution) term) =
      instantiate (inclusion execution target) (instantiate joint.left term) := by
  exact (instantiate_comp (carry execution) (amalgam execution joint) term).trans
    ((congrArg (fun assignment => instantiate assignment term) (amalgam_left execution joint)).trans
      (Assignment.instantiate_compose (inclusion execution target) joint.left term))

theorem read_right (joint : Joint s first second target) {Δ : Ctx S} {result : S.Srt}
    (term : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Δ result) :
    instantiate (Assignment.compose (Assignment.compose (amalgam execution joint) (laterCaptured execution))
        (ContextualComputedFreshFrame.includeSource execution.update)) term =
      instantiate (inclusion execution target) (instantiate joint.right term) := by
  exact (congrArg (fun assignment => instantiate assignment term) (amalgam_right execution joint)).trans
    (Assignment.instantiate_compose (inclusion execution target) joint.right term)

theorem read_left_equal_iff (joint : Joint s first second target) {Δ : Ctx S} {result : S.Srt}
    (left right : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Δ result) :
    instantiate (amalgam execution joint) (instantiate (carry execution) left) =
        instantiate (amalgam execution joint) (instantiate (carry execution) right) ↔
      instantiate joint.left left = instantiate joint.left right := by
  rw [read_left,read_left]
  exact ⟨fun equal => inclusion_term_injective execution target equal,
    congrArg (instantiate (inclusion execution target))⟩

theorem residual_solvable_iff_joint (firing : LiveFiring s)
    (unmade : ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read, occurrence ∉ execution.selection.made) :
    (Frames.contextual S).Solvable (a := ⟨_,laterTarget execution⟩) (firing.residualAt execution).toNative.information ↔
      ∃ target : Frames.Frame S, Nonempty (Joint s firing.toNative.information
        (problemOf s execution.selection execution.rule) target) := by
  constructor
  · rintro ⟨target,candidate,model⟩
    exact ⟨target,⟨Joint.ofResidual execution firing unmade candidate model⟩⟩
  · rintro ⟨target,⟨joint⟩⟩
    exact ⟨extended execution target,amalgam execution joint,models_amalgam execution firing unmade joint⟩

def publishedModel (right : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) target.arity) :
    Assignment execution.target.declarations (extended execution target).arity
  | .inl name => instantiate (inclusion execution target) (right name)
  | .inr helper => generator (extended execution target).arity (.inl (.inr (.inr helper)))

theorem amalgam_captured (joint : Joint s first second target) :
    Assignment.compose (amalgam execution joint) (laterCaptured execution) = publishedModel execution joint.right := by
  funext name
  refine (instantiate_generator (amalgam execution joint) (.inr name)).trans ?_
  cases name <;> rfl

def familyJoint {members : List (LiveFiring s)} (data : FamilyInformation.SolutionData s members target)
    (right : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) target.arity)
    (rightModel : ContextualResidual.Models right (problemOf s execution.selection execution.rule))
    (rightAgrees : Assignment.compose right (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) = data.shared)
    (index : Fin members.length) :
    Joint s (FamilyInformation.memberInformation members[index]) (problemOf s execution.selection execution.rule) target where
  left := data.member index
  right := right
  left_models := data.models index
  right_models := rightModel
  agree := (data.agrees index).trans rightAgrees.symm

def residualData {members : List (LiveFiring s)} (data : FamilyInformation.SolutionData s members target)
    (right : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) target.arity)
    (rightModel : ContextualResidual.Models right (problemOf s execution.selection execution.rule))
    (rightAgrees : Assignment.compose right (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) = data.shared)
    (unmade : ∀ firing ∈ members, ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read,
      occurrence ∉ execution.selection.made) :
    FamilyInformation.SolutionData (rawTarget execution) (members.map (fun firing => firing.residualAt execution))
      (extended execution target) where
  shared := publishedModel execution right
  member index :=
    amalgam execution (familyJoint execution data right rightModel rightAgrees
      ⟨index.val,by simpa only [List.length_map] using index.isLt⟩)
  agrees index := amalgam_captured execution _
  models index := by
    let original : Fin members.length := ⟨index.val,by simpa only [List.length_map] using index.isLt⟩
    have model := models_amalgam execution members[original] (unmade _ (List.getElem_mem ..))
      (familyJoint execution data right rightModel rightAgrees original)
    change ContextualResidual.Models (amalgam execution (familyJoint execution data right rightModel rightAgrees original))
      ((members.map (fun firing : LiveFiring s => firing.residualAt execution))[index.val]).toNative.information
    rw [List.getElem_map]
    exact model

theorem residualData_shared {members : List (LiveFiring s)} (data : FamilyInformation.SolutionData s members target)
    (right : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) target.arity)
    (rightModel : ContextualResidual.Models right (problemOf s execution.selection execution.rule))
    (rightAgrees : Assignment.compose right (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) = data.shared)
    (unmade : ∀ firing ∈ members, ∀ occurrence ∈ firing.selection.taken ++ firing.selection.read,
      occurrence ∉ execution.selection.made) :
    (residualData execution data right rightModel rightAgrees unmade).shared = publishedModel execution right := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ResidualModels
