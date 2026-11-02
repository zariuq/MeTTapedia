import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderScopeNoninterference
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtensionControls

/-!
# A passed alias exposes its old caller component

The old equation x = y connects two different written names. A valid new tell
mentions only y, yet restricts the possible values of x. New-equation support
avoids x but the singleton component around x was not closed. This is a
counterexample to textual-name isolation, not to scope-based sharing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderAliasBoundaryControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A zero one)
open FirstOrderConservativeExtension FirstOrderAskLocality FirstOrderScopeNoninterference
open FirstOrderConservativeExtension.Controls (picked label)

def component : Set Nat := {0}
def oldAlias : EquationStore (Term signature) := [(.var 0, .var 1)]
def tellAlias : RuleInstance (Term signature) := ⟨[], [], [(.var 1, .const 1)], [], []⟩
def before : Configuration (Term signature) Nat := ⟨oldAlias, {0}⟩
def after : Configuration (Term signature) Nat := picked.result label tellAlias before
def zeroAlias : Subst signature := (Subst.single (σ := signature) 1 (.const 0)).comp zero
def oneAlias : Subst signature := (Subst.single (σ := signature) 1 (.const 1)).comp one

theorem zero_models_old_alias : A.Models zeroAlias before.equations := by
  intro equation member
  have same : equation = (Term.var (σ := signature) 0, .var 1) := by
    simpa [before, oldAlias] using member
  subst equation
  rfl

theorem binding_alias_is_valid : picked.Valid A label tellAlias before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨oneAlias, ?_⟩
    intro equation member
    have same : equation = (Term.var (σ := signature) 0, .var 1) ∨
        equation = (Term.var (σ := signature) 1, .const 1) := by
      simpa [Selection.problem, Selection.equations, before, oldAlias, picked, tellAlias] using member
    rcases same with rfl | rfl <;> rfl
  · simp [tellAlias]

theorem actual_alias_binding_step : Step A label tellAlias before after :=
  ⟨picked, binding_alias_is_valid, rfl⟩

theorem added_equations_avoid_the_written_root :
    Avoids component (GuardFreeProcessOrders.added label tellAlias picked) := by
  apply (avoids_iff_eqVars (signature := signature) component _).mpr
  intro name member
  have atOne : name = 1 := by
    simpa [GuardFreeProcessOrders.added, Selection.equations, picked, tellAlias, eqVars, Term.freeVars]
      using member
  subst name
  simp [component]

theorem old_alias_component_is_not_closed : ¬ Closed component before.equations := by
  intro closed
  rcases closed (.var 0, .var 1) (by simp [before, oldAlias]) with inside | outside
  · have impossible := inside 1 (by simp [equationSupport, Term.freeVars])
    simp [component] at impossible
  · exact outside 0 (by simp [equationSupport, Term.freeVars]) (by simp [component])

theorem new_models_bind_the_old_root (assignment : Subst signature)
    (model : A.Models assignment after.equations) : assignment 0 = Term.const (σ := signature) 1 := by
  have sameAliases : assignment 0 = assignment 1 := model (.var 0, .var 1) (by
    simp [after, Selection.result, Selection.problem, Selection.equations, before, oldAlias, picked, tellAlias])
  have bound : assignment 1 = Term.const (σ := signature) 1 := model (.var 1, .const 1) (by
    simp [after, Selection.result, Selection.problem, Selection.equations, before, oldAlias, picked, tellAlias])
  exact sameAliases.trans bound

theorem old_root_value_cannot_extend :
    ¬ ConservativeOn component before.equations after.equations := by
  intro preserves
  obtain ⟨extended, model, agree⟩ := preserves zeroAlias zero_models_old_alias
  have oldZero : extended 0 = Term.const (σ := signature) 0 := agree 0 (by simp [component])
  have impossible := oldZero.symm.trans (new_models_bind_the_old_root extended model)
  cases impossible

theorem raw_name_avoidance_does_not_establish_noninterference :
    Step A label tellAlias before after ∧
      Avoids component (GuardFreeProcessOrders.added label tellAlias picked) ∧
      ¬ Closed component before.equations ∧
      ¬ ConservativeOn component before.equations after.equations :=
  ⟨actual_alias_binding_step, added_equations_avoid_the_written_root,
    old_alias_component_is_not_closed, old_root_value_cannot_extend⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderAliasBoundaryControls
