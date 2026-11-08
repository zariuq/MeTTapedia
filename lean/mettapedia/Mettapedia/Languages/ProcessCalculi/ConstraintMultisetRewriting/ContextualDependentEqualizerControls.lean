import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEqualizerSelection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUnaryRecoveryControls

/-!
# Equalizers distinguish swapped arguments with identical images

The swap of x and y fixes their common type T. Its image intersection with
the identity contains every variable, whereas its equalizer retains only T.
The ordered pair (x,y) is not equal to its swapped instance. A fixed endpoint
recovers through the computed equalizer. A beta-erasing counterexample shows
why the pointwise restriction requires normal input.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEqualizerSelection.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion ContextualDependentNormalSelection ContextualDependentEta
open ContextualDependentScopeConsequence ContextualDependentRenameAgreement

abbrev setting := ContextualDependentNormalSupport.Controls.setting
abbrev rigid := ContextualDependentNormalSupport.Controls.rigid_constants
abbrev normal := @ContextualDependentNormalSupport.Controls.stopped_normal
abbrev unique := @ContextualDependentCommonEndpoint.Controls.unique
abbrev source := ContextualDependentUnaryRecovery.Controls.source

def swap : Ren 3 3 := fun index => if index.val = 0 then 1 else if index.val = 1 then 0 else 2

theorem swap_injective : Function.Injective swap := by
  intro first second same
  fin_cases first <;> fin_cases second <;> simp_all [swap]

def first : Inclusion source source := ⟨swap, swap_injective, by intro index; fin_cases index <;> exact .var _⟩
def second : Inclusion source source := ⟨idRen, Function.injective_id, identityTyped source.raw⟩
theorem first_compatible : CtxRen source.raw source.raw first.forward := by intro index; fin_cases index <;> rfl
theorem second_compatible : CtxRen source.raw source.raw second.forward := CtxRen.id _
theorem context_normal : NormalContext (S := setting) source.raw :=
  .snoc (.snoc (.snoc .nil (normal _ (by rfl'))) (normal _ (by rfl'))) (normal _ (by rfl'))

theorem image_intersection_keeps_everything : List.ofFn (commonMask first.forward second.forward) = [true, true, true] := by
  decide +kernel

theorem pointwise_equalizer_keeps_only_the_type : List.ofFn (mask first.forward second.forward) = [false, false, true] := by
  decide +kernel

def selected := selectEqualizer (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique
  TowerModel.complete ContextualDependentInversion.Controls.declarations_formed (root_reflection rigid)
  first second first_compatible second_compatible context_normal

theorem actual_selected_context : selected.source = ContextualDependentInversion.Controls.typeContext := by rfl'
theorem actual_selected_image : List.ofFn (fun index => (selected.inclusion.forward index).val) = [2] := by rfl'

def pairType : TypeOver source :=
  ⟨.sigma (.var 2) (.var 3), .sort (.max Tower.zero Tower.zero), .sort _,
    .sigmaForm (.var 2) (.sort _) (.var 3) (.sort _) (.sorts _ _)⟩
def pairValue : Term source pairType := ⟨.pair (.var 0) (.var 1), .pairIntro pairType.formed pairType.universeWitness (.var 0) (.var 1)⟩

theorem swapped_pair_has_same_support :
    (Presentation.rename first.forward pairValue.code).support =
      (Presentation.rename second.forward pairValue.code).support := by decide +kernel

theorem swapped_pair_is_not_equal : ¬ Equal Tower.rules source.raw
    (Presentation.rename first.forward pairValue.code) (Presentation.rename second.forward pairValue.code) pairType.code := by
  intro same
  have agreement := ContextualDependentNormalEqualizer.equal_agreement (S := setting) rigid TowerModel.complete
    source.formed pairValue.code first.forward second.forward same (normal _ (by rfl'))
  have impossible := agreement 0 (by decide +kernel)
  change (1 : Fin 3) = 0 at impossible
  exact (by decide : (1 : Fin 3) ≠ 0) impossible

def universeType : TypeOver source := ContextualDependentInversion.Controls.universeType.reindex (toEmpty source)
def fixedEndpoint : TotalTerm source := ⟨universeType, ⟨.var 2, .var 2⟩⟩

theorem endpoint_equation : (frames setting.levels).E (fixedEndpoint.reindex first.hom) (fixedEndpoint.reindex second.hom) :=
  ⟨(fixedEndpoint.reindex first.hom).1.isType.refl, .refl (.var 2)⟩

def recovered := recoverEqualizer (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique
  TowerModel.complete ContextualDependentInversion.Controls.declarations_formed rigid
  first second first_compatible second_compatible context_normal fixedEndpoint endpoint_equation
  (normal _ (by rfl')) (normal _ (by rfl'))

theorem actual_endpoint_recovery :
    recovered.value.2.code = (Tm.var (Head := Tower.Head) (0 : Fin 1)) := by rfl'

theorem recovered_endpoint_solves_original :
    (frames setting.levels).E (recovered.value.reindex selected.inclusion.hom) fixedEndpoint := recovered.solves

theorem selected_map_equalizes : ∀ index, first.forward (selected.inclusion.forward index) = second.forward (selected.inclusion.forward index) :=
  selected_equalizes (S := setting) first.forward second.forward selected

def fixedType : Inclusion ContextualDependentInversion.Controls.typeContext source :=
  ⟨(fun _ => 2), (by intro one two _; fin_cases one; fin_cases two; rfl), by intro index; fin_cases index; exact .var 2⟩
theorem fixedType_compatible : CtxRen ContextualDependentInversion.Controls.typeContext.raw source.raw fixedType.forward := by
  intro index; fin_cases index; rfl
theorem fixedType_equalizes (index : Fin ContextualDependentInversion.Controls.typeContext.arity) :
    first.forward (fixedType.forward index) = second.forward (fixedType.forward index) := rfl

def computedFactor := factor (S := setting) first.forward second.forward selected fixedType fixedType_compatible fixedType_equalizes

theorem actual_typed_factor : List.ofFn (fun index => (computedFactor.forward index).val) = [0] := by rfl'

theorem typed_factor_is_unique (candidate : Ren ContextualDependentInversion.Controls.typeContext.arity selected.source.arity)
    (image : ∀ index, selected.inclusion.forward (candidate index) = fixedType.forward index) :
    candidate = computedFactor.forward :=
  factor_unique (S := setting) first.forward second.forward selected fixedType fixedType_compatible fixedType_equalizes candidate image

namespace BetaBoundary

abbrev two := ContextualDependentNormalSupport.Controls.two
abbrev three := ContextualDependentNormalSupport.Controls.CommonParameters.three
abbrev left := ContextualDependentNormalSupport.Controls.CommonParameters.left
def right : Ren 2 3 := fun index => if index.val = 0 then 0 else 2
abbrev erased := ContextualDependentNormalSupport.Controls.erased

theorem right_injective : Function.Injective right := by
  intro first second same
  fin_cases first <;> fin_cases second <;> simp_all [right]

theorem left_compatible : CtxRen two.raw three.raw left := by intro index; fin_cases index <;> rfl
theorem right_compatible : CtxRen two.raw three.raw right := by intro index; fin_cases index <;> rfl

theorem unnormalized_images_are_equal : Equal Tower.rules three.raw
    (Presentation.rename left erased) (Presentation.rename right erased) (.head (.sort Tower.zero)) := by
  have first := ContextualDependentNormalSupport.Controls.typed_beta_erases_a_dependency.rename left_compatible
  have second := ContextualDependentNormalSupport.Controls.typed_beta_erases_a_dependency.rename right_compatible
  exact first.trans second.symm

theorem maps_disagree_on_raw_support : ¬ Agrees left right erased.support := by
  intro agreement
  have impossible := agreement 1 (by decide +kernel)
  change (1 : Fin 3) = 2 at impossible
  exact (by decide : (1 : Fin 3) ≠ 2) impossible

end BetaBoundary
end ContextualDependentEqualizerSelection.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
