import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionRecovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentContextIntersectionControls

/-!
# Common endpoint recovery factors both sides, including eta

The dependent recovered endpoint solves both original images. A function
eta control recovers the expanded function and proves it solves the bare
function endpoint through the intersection, despite unequal raw syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionRecovery.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTypedInversion ContextualDependentNormalSelection
open ContextualDependentScopeConsequence ContextualDependentContextIntersection

abbrev setting := ContextualDependentNormalSupport.Controls.setting
abbrev rigid := ContextualDependentNormalSupport.Controls.rigid_constants
abbrev normal := @ContextualDependentNormalSupport.Controls.stopped_normal
abbrev unique := @ContextualDependentCommonEndpoint.Controls.unique

namespace Dependent

open ContextualDependentNormalSelection.Controls.Common

theorem factors_both_original_sides :
    (frames setting.levels).E
      (recovered.value.reindex ContextualDependentContextIntersection.Controls.Dependent.leftLeg.hom) first ∧
    (frames setting.levels).E (recovered.value.reindex selected.inclusion.hom) second :=
  ⟨recovered_left (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    (root_reflection rigid) TowerModel.complete left right
    ContextualDependentNormalSelection.Controls.Common.left_compatible right_compatible selected
    first second equation recovered, recovered.solves⟩

end Dependent

namespace Eta

open Examples.TypedContextualControls

abbrev context := functionContext
def inclusion : Inclusion context context := ofCompatible (S := setting) idRen Function.injective_id (CtxRen.id context.raw)
theorem compatible : CtxRen context.raw context.raw inclusion.forward := CtxRen.id context.raw
theorem context_normal : NormalContext (S := setting) context.raw := .snoc .nil (normal _ (by rfl'))
def first : TotalTerm context := ⟨_, ContextualDependentStrengthening.Controls.Eta.sourceFunction⟩
def second : TotalTerm context := ⟨_, ContextualDependentStrengthening.Controls.Eta.sourceEta⟩

theorem equation : (frames setting.levels).E (first.reindex inclusion.hom) (second.reindex inclusion.hom) := by
  constructor
  · exact (first.reindex inclusion.hom).1.isType.refl
  · exact ContextualDependentStrengthening.Controls.Eta.reflected_function_eta

def selected := ContextualDependentCommonSelection.selectCommon (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique TowerModel.complete
  ContextualDependentInversion.Controls.declarations_formed (root_reflection rigid)
  inclusion inclusion compatible compatible context_normal

def recovered := ContextualDependentCommonSelection.recoverCommon (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique TowerModel.complete
  ContextualDependentInversion.Controls.declarations_formed rigid
  inclusion inclusion compatible compatible context_normal first second equation
  (normal _ (by rfl')) (normal _ (by rfl')) (normal _ (by rfl')) (normal _ (by rfl'))

def leftLeg := leftInclusion (S := setting) inclusion inclusion compatible compatible selected

theorem actual_eta_expansion_recovered :
    recovered.value.2.code = (.lam (.app (.var 1) (.var 0)) : Tower.Tm 1) := by rfl'

theorem solves_bare_function :
    (frames setting.levels).E (recovered.value.reindex leftLeg.hom) first :=
  recovered_left (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    (root_reflection rigid) TowerModel.complete inclusion inclusion compatible compatible selected first second equation recovered

theorem raw_syntax_is_distinct : (recovered.value.reindex leftLeg.hom).2.code ≠ first.2.code := by decide +kernel

end Eta
end ContextualDependentIntersectionRecovery.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
