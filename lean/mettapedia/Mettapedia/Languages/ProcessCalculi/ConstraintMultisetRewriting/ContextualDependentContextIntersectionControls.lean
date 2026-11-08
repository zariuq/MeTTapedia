import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentContextIntersection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSelectionControls

/-!
# A genuine overlapping intersection and its dependency controls

The images [0,1] and [1,2] intersect in one variable: index 1 on the left
and index 0 on the right. The computed cone factor is unique. A right-only
parameter cannot factor through this intersection. The dependent example
retains both a type parameter and its value while omitting an unrelated type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentContextIntersection.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion ContextualDependentNormalSelection ContextualDependentScopeConsequence

abbrev setting := ContextualDependentNormalSupport.Controls.setting
abbrev rigid := ContextualDependentNormalSupport.Controls.rigid_constants
abbrev normal := @ContextualDependentNormalSupport.Controls.stopped_normal
abbrev unique := @ContextualDependentCommonEndpoint.Controls.unique

namespace Overlap

abbrev two := ContextualDependentNormalSupport.Controls.two
abbrev three := ContextualDependentNormalSupport.Controls.CommonParameters.three
abbrev left := ContextualDependentCommonEndpoint.Controls.Common.leftInclusion
abbrev right := ContextualDependentCommonEndpoint.Controls.Common.rightInclusion

theorem left_compat : CtxRen two.raw three.raw left.forward := by intro index; fin_cases index <;> rfl
theorem right_compat : CtxRen two.raw three.raw right.forward := by intro index; fin_cases index <;> rfl
theorem normal_context : NormalContext (S := setting) two.raw :=
  .snoc (.snoc .nil (normal _ (by rfl'))) (normal _ (by rfl'))

def selected := ContextualDependentCommonSelection.selectCommon (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique TowerModel.complete
  ContextualDependentInversion.Controls.declarations_formed (root_reflection rigid)
  left right left_compat right_compat normal_context

def leftLeg := leftInclusion (S := setting) left right left_compat right_compat selected

theorem actual_intersection : selected.source.arity = 1 ∧
    List.ofFn (fun index => (leftLeg.forward index).val) = [1] ∧
    List.ofFn (fun index => (selected.inclusion.forward index).val) = [0] := by
  exact ⟨by rfl', by rfl', by rfl'⟩

abbrev source := ContextualDependentInversion.Controls.typeContext
def toLeft : Inclusion source two := ofCompatible (S := setting) (fun _ => 1)
  (by intro first second _; fin_cases first; fin_cases second; rfl)
  (by intro index; fin_cases index; rfl)
def toRight : Inclusion source two := ofCompatible (S := setting) (fun _ => 0)
  (by intro first second _; fin_cases first; fin_cases second; rfl)
  (by intro index; fin_cases index; rfl)
theorem toRight_compat : CtxRen source.raw two.raw toRight.forward := by intro index; fin_cases index; rfl
theorem commutes (index : Fin source.arity) : left.forward (toLeft.forward index) = right.forward (toRight.forward index) := rfl

def computed := coneFactor (S := setting) left right selected toLeft toRight toRight_compat commutes

theorem actual_factor : List.ofFn (fun index => (computed.forward index).val) = [0] := by rfl'

theorem unique_typed_factor : ∃! factor : Inclusion source selected.source,
    (∀ index, leftLeg.forward (factor.forward index) = toLeft.forward index) ∧
    (∀ index, selected.inclusion.forward (factor.forward index) = toRight.forward index) :=
  universal (S := setting) left right left_compat right_compat selected toLeft toRight toRight_compat commutes

theorem outside_parameter_not_in_intersection :
    ¬ ∃ position, selected.inclusion.forward position = (1 : Fin 2) := by
  intro image
  have retained := (selected.image 1).mp image
  change false = true at retained
  cases retained

theorem outside_parameter_has_no_factor :
    ¬ ∃ candidate : Ren 1 selected.source.arity, ∀ index, selected.inclusion.forward (candidate index) = (1 : Fin 2) := by
  rintro ⟨candidate, image⟩
  exact outside_parameter_not_in_intersection ⟨candidate 0, image 0⟩

end Overlap

namespace Dependent

open ContextualDependentNormalSelection.Controls.Common

def leftLeg := leftInclusion (S := setting) left right
  ContextualDependentNormalSelection.Controls.Common.left_compatible right_compatible selected

theorem dependent_intersection_images :
    List.ofFn (fun index => (leftLeg.forward index).val) = [0, 1] ∧
    List.ofFn (fun index => (selected.inclusion.forward index).val) = [0, 2] := by constructor <;> rfl'

theorem both_declaration_maps_compatible :
    CtxRen selected.source.raw small.raw leftLeg.forward ∧
    CtxRen selected.source.raw ContextualDependentInversion.Controls.large.raw selected.inclusion.forward :=
  ⟨ContextualDependentContextIntersection.left_compatible (S := setting) left right
      ContextualDependentNormalSelection.Controls.Common.left_compatible right_compatible selected,
    selected.compatible⟩

end Dependent
end ContextualDependentContextIntersection.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
