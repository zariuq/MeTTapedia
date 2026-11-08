import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCommonSelection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCommonEndpointControls

/-!
# Dependency-closed selection and total common-endpoint recovery

The normal-context selector computes the dependent subcontext A:U0, x:A,
refuses to retain x while deleting A, and has no checker-budget argument.
The common-context operation reconstructs that same context from actual
variable inclusions, then recovers a witnessed endpoint including its type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalSelection.Controls

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion ContextualDependentEta ContextualDependentScopeConsequence

abbrev setting := ContextualDependentCommonEndpoint.Controls.setting
abbrev rigid := ContextualDependentCommonEndpoint.Controls.rigid
abbrev normal := @ContextualDependentNormalSupport.Controls.stopped_normal
abbrev unique := @ContextualDependentCommonEndpoint.Controls.unique
abbrev large := ContextualDependentInversion.Controls.large

theorem context_normal : NormalContext (S := setting) large.raw :=
  .snoc (.snoc (.snoc .nil (normal _ (by rfl'))) (normal _ (by rfl'))) (normal _ (by rfl'))

def run (mask : Fin 3 → Bool) := select (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique TowerModel.complete
  ContextualDependentInversion.Controls.declarations_formed (root_reflection rigid)
  large.raw large.formed context_normal mask

theorem dependent_context_computed :
    (run ContextualDependentPruning.Controls.requested).map (fun selected => selected.source) =
      some ContextualDependentInversion.Controls.small := by rfl'

theorem exact_variable_image :
    (run ContextualDependentPruning.Controls.requested).map (fun selected =>
      List.ofFn (fun index => (selected.inclusion.forward index).val)) = some [0, 2] := by rfl'

theorem dependency_failure_is_distinct_from_budget_failure :
    run (fun index => decide (index.val = 0)) = none ∧
      (run ContextualDependentPruning.Controls.requested).isSome = true ∧
      ContextualDependentPruning.Controls.run 0 ContextualDependentPruning.Controls.requested = none := by
  exact ⟨by rfl', by rfl', ContextualDependentPruning.Controls.exhausted_type_check_is_not_a_refutation⟩

theorem missing_dependency_not_closed :
    ¬ Closed large.raw (fun index => decide (index.val = 0)) := by
  intro closed
  have bad := closed 0 (by decide) 2 (by decide +kernel)
  contradiction

theorem retained_dependencies_are_closed :
    Closed large.raw ContextualDependentPruning.Controls.requested := by
  obtain ⟨selected, _, _⟩ := Option.map_eq_some_iff.mp dependent_context_computed
  exact selected.closed

namespace Common

abbrev small := ContextualDependentInversion.Controls.small
abbrev left := ContextualDependentInversion.Controls.inclusion
def right : Inclusion large large :=
  ⟨idRen, Function.injective_id, by
    intro index
    change Typed Tower.rules large.raw (.var index) (subst (renSub idRen) (Ctx.lookup large.raw index))
    rw [subst_renSub, Presentation.rename_id]
    exact .var index⟩

theorem left_compatible : CtxRen small.raw large.raw left.forward := by
  intro index
  fin_cases index <;> rfl

theorem right_compatible : CtxRen large.raw large.raw right.forward := by
  intro index
  exact (rename_id _).symm

def selected := ContextualDependentCommonSelection.selectCommon (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique TowerModel.complete
  ContextualDependentInversion.Controls.declarations_formed (root_reflection rigid)
  left right left_compatible right_compatible context_normal

theorem selected_dependent_context : selected.source = small := by rfl'
theorem selected_from_actual_maps : List.ofFn (commonMask left.forward right.forward) = [true, false, true] := by rfl'

def first : TotalTerm small :=
  ⟨ContextualDependentInversion.Controls.expected, ⟨.var 0, .var 0⟩⟩
abbrev second : TotalTerm large := ⟨_, ContextualDependentInversion.Controls.target⟩

theorem equation : (frames setting.levels).E (first.reindex left.hom) (second.reindex right.hom) := by
  exact ⟨(first.reindex left.hom).1.isType.refl, .refl (.var 0)⟩

def recovered := ContextualDependentCommonSelection.recoverCommon (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra unique TowerModel.complete
  ContextualDependentInversion.Controls.declarations_formed rigid
  left right left_compatible right_compatible context_normal first second equation
  (normal _ (by rfl')) (normal _ (by rfl')) (normal _ (by rfl')) (normal _ (by rfl'))

def typeIndex : Fin selected.source.arity := ⟨1, by decide +kernel⟩
def valueIndex : Fin selected.source.arity := ⟨0, by decide +kernel⟩

theorem actual_annotation_and_value :
    recovered.value.1.code = .var typeIndex ∧ recovered.value.2.code = .var valueIndex := by
  constructor <;> rfl'

theorem recovered_endpoint_solves :
    (frames setting.levels).E (recovered.value.reindex selected.inclusion.hom) second := recovered.solves

end Common
end ContextualDependentNormalSelection.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
