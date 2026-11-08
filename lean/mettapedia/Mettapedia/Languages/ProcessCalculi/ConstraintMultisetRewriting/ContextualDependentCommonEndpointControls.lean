import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCommonEndpoint
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSupportControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentStrengtheningControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalCheckingTower

/-!
# Computed endpoint recovery and its annotation boundary

The dependent example reconstructs both A and x:A after removing an unrelated
declaration. The common-parameter example obtains its selection from two
actual typed variable inclusions. An identity function whose annotation
mentions a dropped type demonstrates why checking only value support fails.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCommonEndpoint.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTypedInversion
open ContextualDependentScopeConsequence

abbrev setting := ContextualDependentNormalSupport.Controls.setting
abbrev rigid := ContextualDependentNormalSupport.Controls.rigid_constants
abbrev normal := @ContextualDependentNormalSupport.Controls.stopped_normal
abbrev unique := @ContextualDependentNormalCheckingTower.head_typing_unique Nat inferInstance

namespace Dependent

abbrev selection := ContextualDependentStrengthening.Controls.selected
abbrev compatible := ContextualDependentStrengthening.Controls.selected_compatible
abbrev original : TotalTerm ContextualDependentInversion.Controls.large :=
  ⟨_, ContextualDependentInversion.Controls.target⟩

def result := ContextualDependentEndpointInversion.recover (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique TowerModel.complete
  ContextualDependentInversion.Controls.declarations_formed (root_reflection rigid)
  selection.inclusion compatible original (normal _ (by rfl')) (normal _ (by rfl'))

theorem annotation_and_value_computed : result.map (fun recovered =>
    (recovered.value.1.code, recovered.value.2.code)) =
    some (.var ContextualDependentStrengthening.Controls.typeIndex,
      .var ContextualDependentStrengthening.Controls.valueIndex) := by rfl'

theorem solves_original : ∃ recovered, result = some recovered ∧
    (frames setting.levels).E (recovered.value.reindex selection.inclusion.hom) original := by
  obtain ⟨recovered, computed, _⟩ := Option.map_eq_some_iff.mp annotation_and_value_computed
  exact ⟨recovered, computed, recovered.solves⟩

end Dependent

namespace Common

open ContextualDependentNormalSupport.Controls.CommonParameters
abbrev two := ContextualDependentNormalSupport.Controls.two

def leftInclusion : Inclusion two three where
  forward := left
  injective := by intro first second same; apply Fin.ext; simpa only [left] using congrArg Fin.val same
  typed := by intro index; fin_cases index <;> exact .var _

def rightInclusion : Inclusion two three where
  forward := right
  injective := by intro first second same; apply Fin.ext; have := congrArg Fin.val same; simp only [right] at this; omega
  typed := by intro index; fin_cases index <;> exact .var _

def annotation : TypeOver two := ContextualDependentInversion.Controls.universeType.reindex (toEmpty two)
def first : TotalTerm two := ⟨annotation, ⟨.var 1, .var 1⟩⟩
def second : TotalTerm two := ⟨annotation, ⟨.var 0, .var 0⟩⟩

theorem equality : (frames setting.levels).E (first.reindex leftInclusion.hom) (second.reindex rightInclusion.hom) :=
  ⟨(first.reindex leftInclusion.hom).1.isType.refl, .refl (.var 1)⟩

def selection := narrowed.get (by decide +kernel)

theorem compatible : CtxRen selection.source.raw two.raw selection.inclusion.forward :=
  ContextualDependentSelectionCompatibility.select_compatible (S := setting)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 two.raw two.formed (commonMask left right) selection (by rfl')

def result := ContextualDependentEndpointInversion.recover (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique TowerModel.complete
  ContextualDependentInversion.Controls.declarations_formed (root_reflection rigid)
  selection.inclusion compatible second (normal _ (by rfl')) (normal _ (by rfl'))

theorem equality_forces_actual_success : result.isSome = true :=
  selected_recovery_forced (S := setting) rigid TowerModel.complete TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra unique ContextualDependentInversion.Controls.declarations_formed
    leftInclusion rightInclusion first second equality
    (normal _ (by rfl')) (normal _ (by rfl')) (normal _ (by rfl')) (normal _ (by rfl')) selection compatible

theorem recovered_variable_is_the_shared_one : result.map (fun recovered =>
    match recovered.value.2.code with | .var index => some index.val | _ => none) = some (some 0) := by rfl'

def omittedAnnotation : TypeOver two :=
  ⟨.pi (.var 1) (.var 2), .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm (.var 1) (.sort _) (.var 2) (.sort _) (.sorts _ _)⟩
def identity : TotalTerm two :=
  ⟨omittedAnnotation, ⟨.lam (.var 0), .lamIntro omittedAnnotation.formed (.sort _) (.var 0)⟩⟩

theorem value_alone_fits :
    (ContextualDependentInversion.invert (ContextualDependentInversion.lookup selection.inclusion.forward)
      identity.2.code).isSome = true := by rfl'

theorem missing_annotation_blocks_typed_recovery :
    ContextualDependentEndpointInversion.recover (S := setting)
      TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed (root_reflection rigid)
      selection.inclusion compatible identity (normal _ (by rfl')) (normal _ (by rfl')) = none := by rfl'

end Common
end ContextualDependentCommonEndpoint.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
