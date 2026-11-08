import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantPruningTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUnaryRecoveryControls

/-!
# Computed principal pruning keeps the result obligation

Over T:U0, the source contains F:T->T and the constraint F x = F y under
two rigid arguments. The actual rule replaces F by H:T and computes
F := lambda x.H. It retains side equations and preserves closed solutions
separately. The identity function does not satisfy the source constraint.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantPruning.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentScope
open ContextualDependentConstantShape ContextualDependentConstantConstraint

abbrev setting := ContextualDependentNormalSupport.Controls.setting
abbrev rigid := ContextualDependentNormalSupport.Controls.rigid_constants
abbrev normal := @ContextualDependentNormalSupport.Controls.stopped_normal
abbrev base := ContextualDependentInversion.Controls.typeContext
abbrev parameter := ContextualDependentInversion.Controls.parameterType

def whole : TypeOver base :=
  ⟨.pi (.var 0) (.var 1), .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm (.var 0) (.sort _) (.var 1) (.sort _) (.sorts _ _)⟩

def shape : Shape base := ⟨parameter, parameter, whole, rfl⟩
def result := ContextualDependentConstantPruningTower.prune (fun _ => (0 : Nat)) shape

theorem actual_rule_finishes : result.update.remaining = [] := by rfl'

theorem original_equation_is_the_two_argument_constraint :
    result.closed.equations.map (fun equation => (equation.1.2.code, equation.2.2.code)) =
      [(.lam (.lam (.app (.var 2) (.var 1))), .lam (.lam (.app (.var 2) (.var 0))))] := by rfl'

theorem actual_function_assignment : result.update.answer.substitution 0 = .lam (.var (1 : Fin 3)) := by rfl'

theorem result_metavariable_and_type_remain :
    result.update.target = ContextualDependentInversion.Controls.small ∧ result.update.target.arity = 2 := by
  exact ⟨by rfl', by rfl'⟩

theorem parameter_type_is_not_instantiated : result.update.answer.substitution 1 = .var (1 : Fin 2) := by rfl'

theorem computed_answer_solves_original_scoped_problem :
    ContextualDependentScopedDispatch.Holds [shape.problem] result.update.answer :=
  (result.completed actual_rule_finishes).1

theorem every_original_solution_factors {Δ : Context Tower.rules} (solution : Δ ⟶ shape.source)
    (solved : shape.problem.Holds solution) :
    ∃ residual : Δ ⟶ result.update.target, ∀ term : TotalTerm shape.source,
      (frames setting.levels).E (term.reindex solution) (term.reindex (residual ≫ result.update.answer)) :=
  (result.completed actual_rule_finishes).2 Δ solution
    (by intro constraint member; obtain rfl := List.mem_singleton.mp member; exact solved)

theorem closed_obligation_is_preserved :
    (∃ solution : empty Tower.rules ⟶ shape.source, ContextualDependentScopedDispatch.Holds [shape.problem] solution) ↔
      ∃ residual : empty Tower.rules ⟶ result.update.target, (frames setting.levels).Models residual result.update.remaining :=
  result.fixed_point_solutions_iff (empty Tower.rules)

def identity : Term base whole := ⟨.lam (.var 0), .lamIntro whole.formed whole.universeWitness (.var 0)⟩
def identitySolution := Elimination.instantiate base identity

theorem identity_fresh_beta : Equal Tower.rules (extend base parameter).raw
    (shape.fresh identity).code (.var 0) (parameter.reindex (projectionHom base parameter)).code :=
  .betaPi (whole.reindex (projectionHom base parameter)).formed whole.universeWitness (.var 0) (.var 0)

theorem identity_is_not_a_solution : ¬ shape.problem.Holds identitySolution := by
  intro solved
  have independent := (shape.problem_pair (𝟙 base) (identity.cast whole.reindex_id.symm)).mp solved
  change Independent shape identity at independent
  have fresh := (independent_iff_fresh (S := setting) shape identity).mp independent
  have first := identity_fresh_beta.rename (ContextualDependentUnaryScope.left_compatible (S := setting) base parameter)
  have second := identity_fresh_beta.rename (ContextualDependentUnaryScope.right_compatible (S := setting) base parameter)
  have second' : Equal Tower.rules (ContextualDependentUnaryScope.twice (S := setting) base parameter).raw
      (Presentation.rename (liftRen wk) (shape.fresh identity).code) (.var (0 : Fin 3))
      (Presentation.rename wk (parameter.reindex (projectionHom base parameter)).code) :=
    (ContextualDependentUnaryScope.codomain_images (S := setting) base parameter parameter) ▸ second
  have distinct := first.symm.trans (fresh.trans second')
  let argumentBody : Term (extend base parameter) (parameter.reindex (projectionHom base parameter)) := ⟨.var 0, .var 0⟩
  have impossible := ContextualDependentUnaryScope.inverse_forced (S := setting) rigid TowerModel.complete
    base parameter parameter argumentBody (normal _ (by rfl')) distinct
  change false = true at impossible
  cases impossible

def side : Equation (TotalTerm shape.source) :=
  (Elimination.last base whole, TotalTerm.reindex (⟨whole, identity⟩ : TotalTerm base) (projectionHom base whole))
def withSide := result.update.keepLeft [side, side]

theorem side_equations_are_transported_not_deleted :
    withSide.remaining.map (fun equation => (equation.1.2.code, equation.2.2.code)) =
      ([ (.lam (.var 1), .lam (.var 0)), (.lam (.var 1), .lam (.var 0)) ] : List (Tower.Tm 2 × Tower.Tm 2)) := by rfl'

theorem side_queue_preserves_closed_solutions :
    (∃ solution : empty Tower.rules ⟶ shape.source,
      (frames setting.levels).Models solution (List.append [side, side] result.closed.equations)) ↔
      ∃ residual : empty Tower.rules ⟶ withSide.target, (frames setting.levels).Models residual withSide.remaining :=
  withSide.fixed_point_solutions_iff (empty Tower.rules)

def functionTypeHere := whole.reindex (projectionHom base whole)
def later : TypeOver shape.source :=
  ⟨.id functionTypeHere.code (.var 0) (.var 0), whole.level, whole.universeWitness,
    .idForm functionTypeHere.formed whole.universeWitness (.var 0) (.var 0)⟩
def lifted := result.update.lift later

theorem later_identity_obligation_is_retyped_and_retained :
    lifted.target.raw = .snoc ContextualDependentInversion.Controls.small.raw
      (.id (.pi (.var 1) (.var 2)) (.lam (.var 1)) (.lam (.var 1)) : Tower.Tm 2) ∧
      lifted.target.arity = 3 := by constructor <;> rfl'

theorem lifting_does_not_add_a_false_equation : lifted.remaining = [] := by rfl'

def noJoins : ExecutableChecking.HeadChoices Tower.rules :=
  { ExecutableTowerChoices.choices with join := fun _ _ => none }

theorem unavailable_join_does_not_refute :
    ContextualDependentConstantPruningTower.solve (fun _ => (0 : Nat)) noJoins shape = none := by rfl'

end ContextualDependentConstantPruning.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
