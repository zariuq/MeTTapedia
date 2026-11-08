import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopeConsequence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruningControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopedDispatch
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability

/-!
# Eta, erasing beta, and an equation-induced parameter mask

Typed normal equality preserves support across both function and dependent
pair eta. Before normalization, a typed beta step can erase support. Equal
support alone is not an equality test. The final control computes the common
parameter mask from two actual variable maps and applies the existing typed
context selector to that mask.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalSupport.Controls

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentNormalChecking
open ContextualDependentScopeConsequence

abbrev setting := ConversionControls.setting

theorem rigid_constants (name : DeclName) : setting.roles name = .rigid := rfl

theorem stopped_normal {n : Nat} (term : Tower.Tm n)
    (stopped : ExecutableReduction.step Tower.rules (fun _ => none) term = none) :
    Normal (S := setting) term :=
  ContextualDependentReductionBudget.normal_of_stopped Tower.rules (fun _ => none)
    (fun _ _ _ impossible => impossible.elim) term stopped

theorem function_eta_support :
    Examples.TypedContextualControls.suppliedFunction.code.support =
      Examples.TypedContextualControls.etaFunction.code.support :=
  equal_support (S := setting) rigid_constants TowerModel.complete
    Examples.TypedContextualControls.familyContext.formed Examples.TypedContextualControls.function_eta
    (stopped_normal _ (by rfl')) (stopped_normal _ (by rfl'))

theorem eta_equality_has_distinct_syntax :
    Examples.TypedContextualControls.suppliedFunction.code ≠ Examples.TypedContextualControls.etaFunction.code := by
  decide +kernel

theorem pair_eta : Equal Tower.rules ConversionControls.pairContext.raw
    ConversionControls.suppliedPair.code ConversionControls.expandedPair.code ConversionControls.pairType.code :=
  ((Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ConversionControls.reducer 16 (⟨_, ConversionControls.suppliedPair⟩ : TotalTerm _)
      (⟨_, ConversionControls.expandedPair⟩ : TotalTerm _)).get (by decide +kernel)).down.2

theorem dependent_pair_eta_support :
    ConversionControls.suppliedPair.code.support = ConversionControls.expandedPair.code.support :=
  equal_support (S := setting) rigid_constants TowerModel.complete ConversionControls.pairContext.formed pair_eta
    (stopped_normal _ (by rfl')) (stopped_normal _ (by rfl'))

abbrev two := ContextualDependentInversion.Controls.withExtra
abbrev erased := ContextualDependentInversion.Controls.erasedArgument

theorem typed_beta_erases_a_dependency : Equal Tower.rules two.raw erased (.var 0) (.head (.sort Tower.zero)) :=
  .betaPi (Examples.TypedContextualControls.function_formed _) (.sort _) (.var 1) (.var 1)

theorem raw_supports_differ : erased.support ≠ (Tm.var (Head := Tower.Head) (0 : Fin 2)).support := by
  decide +kernel

theorem raw_inverse_fails_before_beta :
    ContextualDependentInversion.invert (ContextualDependentInversion.lookup
      ContextualDependentInversion.Controls.keepFirst) erased = none := by rfl'

theorem same_support_is_not_equality :
    (Tm.head .legacyGround : Tower.Tm 0).support = (Tm.head (.sort Tower.zero) : Tower.Tm 0).support ∧
      ¬ TypeEq Tower.rules .nil (.head .legacyGround) (.head (.sort Tower.zero)) := by
  refine ⟨rfl, ?_⟩
  intro same
  rcases TypeEq.head_injective TowerModel.facts same .nil with same | same
  · cases same
  · exact same.elim

namespace CommonParameters

def left : Ren 2 3 := fun index => ⟨index.val, by omega⟩
def right : Ren 2 3 := fun index => ⟨index.val + 1, by omega⟩

def thirdType : TypeOver two := ContextualDependentInversion.Controls.universeType.reindex (toEmpty two)
abbrev three := extend two thirdType

theorem equation : Equal Tower.rules three.raw
    (Presentation.rename left (.var 1)) (Presentation.rename right (.var 0)) (.head (.sort Tower.zero)) :=
  .refl (.var 1)

theorem computed_mask : List.ofFn (commonMask left right) = [true, false] := by decide +kernel

theorem used_parameters_forced :
    ∀ index ∈ (Tm.var (Head := Tower.Head) (0 : Fin 2)).support, commonMask left right index = true :=
  common_parameters_forced (S := setting) rigid_constants TowerModel.complete left right three.formed
    (.var 1) (.var 0) (.head (.sort Tower.zero)) equation
    (stopped_normal _ (by rfl')) (stopped_normal _ (by rfl'))

def narrowed := ContextualDependentPruning.select (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
  TowerModel.algebra ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
  ContextualDependentInversion.Controls.reducer 16 two.raw two.formed (commonMask left right)

theorem actual_selector_retains_only_common_parameter :
    narrowed.map (fun result => result.source.arity) = some 1 := by rfl'

theorem actual_selected_variable :
    narrowed.map (fun result => List.ofFn (fun index => (result.inclusion.forward index).val)) = some [0] := by rfl'

end CommonParameters

namespace FutureAssignment

open ContextualDependentScope

abbrev types := ContextualDependentInversion.Controls.typeContext
abbrev element := ContextualDependentInversion.Controls.parameterType
abbrev values := extend types element

def function : TypeOver values :=
  ⟨.pi (.var 1) (.var 2), .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm (.var 1) (.sort _) (.var 2) (.sort _) (.sorts _ _)⟩
abbrev outer := extend values function
def localType : TypeOver outer := ⟨.var 2, .sort Tower.zero, .sort _, .var 2⟩
def resultType : TypeOver (extend outer localType) := localType.reindex (projectionHom _ localType)
def equation : Active (extend outer localType) :=
  ⟨resultType, ⟨.var 2, .var 2⟩,
    ⟨.app (.var 1) (.var 0), Derivable.appElim (A := .var 3) (B := .var 4) (.var 1) (.var 0)⟩⟩
def problem : Scoped outer := .bind localType (.active equation)

theorem current_right_is_normal : Normal (S := setting) equation.right.code := stopped_normal _ (by rfl')

theorem current_inverse_is_unfinished :
    ContextualDependentInversion.invert (ContextualDependentInversion.lookup (wk : Ren 3 4)) equation.right.code = none := by
  rfl'

def solved := (ContextualDependentScopedDispatch.solveNewest (S := setting)
  TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
  ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
  ConversionControls.reducer 32 function [problem]).get (by decide +kernel)

theorem actual_solution_finishes : solved.update.remaining = [] := by rfl'

theorem argument_dependency_is_removed_by_assignment :
    solved.update.answer.substitution 0 = .lam (.var 1) := by rfl'

theorem type_and_value_obligations_remain : solved.update.target = values := by rfl'

/-- M = G x under a rigid x has a principal solution G := lambda x.M,
even though its current normal right side is outside the outer scope. -/
theorem original_scoped_problem_has_principal_answer :
    ContextualDependentScopedDispatch.Holds [problem] solved.update.answer ∧
      ∀ (Δ : Context Tower.rules) (solution : Δ ⟶ outer),
        ContextualDependentScopedDispatch.Holds [problem] solution →
          ∃ residual : Δ ⟶ solved.update.target,
            ∀ term : TotalTerm outer,
              (frames setting.levels).E (term.reindex solution)
                (term.reindex (residual ≫ solved.update.answer)) :=
  solved.completed actual_solution_finishes

theorem closed_obligations_preserved :
    (∃ solution : empty Tower.rules ⟶ outer, ContextualDependentScopedDispatch.Holds [problem] solution) ↔
      ∃ residual : empty Tower.rules ⟶ solved.update.target,
        (frames setting.levels).Models residual solved.update.remaining :=
  solved.fixed_point_solutions_iff (empty Tower.rules)

end FutureAssignment
end ContextualDependentNormalSupport.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
