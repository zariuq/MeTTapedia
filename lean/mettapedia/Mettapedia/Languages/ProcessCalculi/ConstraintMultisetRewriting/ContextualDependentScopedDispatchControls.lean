import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScopedDispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentParameterExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexWakeup

/-!
# Reordered rigid arguments with a dependent result

Over an arbitrary type T, the unknown function has type
Pi a:T. Pi b:T. Id T b b. The original scoped equation is
F y x = refl x. Exchanging the independent rigid parameters exposes an
eta-pattern; the actual dispatcher computes F := lambda a b. refl b.
Every solution of the original scoped equation factors through that answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentScopedDispatch.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentScope ContextualDependentUpdate

abbrev setting := ConversionControls.setting
abbrev base := ContextualDependentFlex.Wakeup.frame

def functionType : TypeOver base where
  code := .pi (.var 0) (.pi (.var 1) (.id (.var 2) (.var 0) (.var 0)))
  level := .sort (.max Tower.zero (.max Tower.zero Tower.zero))
  universeWitness := .sort _
  formed := .piForm (.var 0) (.sort _)
    (.piForm (.var 1) (.sort _) (.idForm (.var 2) (.sort _) (.var 0) (.var 0))
      (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)

abbrev frame := extend base functionType
def domain : TypeOver frame := ⟨.var 1, .sort Tower.zero, .sort _, .var 1⟩
abbrev localContext := ContextualDependentParameterExchange.context domain domain

def resultType : TypeOver localContext :=
  ⟨.id (.var 3) (.var 1) (.var 1), .sort Tower.zero, .sort _,
    .idForm (.var 3) (.sort _) (.var 1) (.var 1)⟩

def left : Term localContext resultType :=
  ⟨.app (.app (.var 2) (.var 0)) (.var 1), by
    have first : Typed Tower.rules localContext.raw (.app (.var 2) (.var 0))
        (.pi (.var 3) (.id (.var 4) (.var 0) (.var 0))) :=
      Derivable.appElim (A := .var 3) (B := .pi (.var 4) (.id (.var 5) (.var 0) (.var 0)))
        (.var 2) (.var 0)
    exact Derivable.appElim (A := .var 3) (B := .id (.var 4) (.var 0) (.var 0)) first (.var 1)⟩

def right : Term localContext resultType := ⟨.refl (.var 1), .reflIntro (.var 1)⟩
def active : Active localContext := ⟨resultType, left, right⟩
def original : Scoped frame := ContextualDependentParameterExchange.problem domain domain active
def reordered : Scoped frame := ContextualDependentParameterExchange.exchanged domain domain active

def run (fuel : Nat) (problem : List (Scoped frame)) :=
  solveNewest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
    ConversionControls.reducer fuel functionType problem

def originalResult : Result setting.levels [original] :=
  (solveExchanged (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
    ConversionControls.reducer 32 functionType domain domain active).get (by decide +kernel)

theorem actual_scoped_pattern_finishes : originalResult.update.remaining = [] := by rfl'

theorem computed_function : originalResult.update.answer.substitution 0 = .lam (.lam (.refl (.var 0))) := by rfl'

theorem original_scoped_equation_is_solved : Holds [original] originalResult.update.answer :=
  (originalResult.completed actual_scoped_pattern_finishes).1

theorem every_original_solution_factors {Δ : Context Tower.rules} (solution : Δ ⟶ frame)
    (solved : original.Holds solution) :
    ∃ residual : Δ ⟶ originalResult.update.target,
      ∀ term : TotalTerm frame,
        (frames setting.levels).E (term.reindex solution)
          (term.reindex (residual ≫ originalResult.update.answer)) :=
  (originalResult.completed actual_scoped_pattern_finishes).2 Δ solution
    (by intro constraint member; obtain rfl := List.mem_singleton.mp member; exact solved)

theorem parameter_type_stays_open : originalResult.update.target = base := by rfl'

theorem outer_metavariables_are_fixed :
    (ContextualDependentParameterExchange.swap domain domain).substitution 2 = .var 2 ∧
    (ContextualDependentParameterExchange.swap domain domain).substitution 3 = .var 3 := by
  constructor <;> rfl

def unordered : Result setting.levels [original] := (run 32 [original]).get (by decide +kernel)

theorem unordered_input_is_not_a_false_refutation : unordered.update.remaining.length = 1 := by rfl'

def noFuel : Result setting.levels [reordered] := (run 0 [reordered]).get (by decide +kernel)

theorem zero_budget_keeps_scoped_obligation : noFuel.update.remaining.length = 1 := by rfl'

def noJoins : ExecutableChecking.HeadChoices Tower.rules :=
  { ExecutableTowerChoices.choices with join := fun _ _ => none }

theorem unavailable_join_leaves_closing_unfinished : closeAll setting.levels noJoins [original] = none := by rfl'

def mixedScopes : Result setting.levels [original, reordered] :=
  (run 32 [original, reordered]).get (by decide +kernel)

theorem later_scoped_definition_wakes_earlier_scope : mixedScopes.update.remaining = [] := by rfl'

theorem mixed_original_scopes_are_solved : Holds [original, reordered] mixedScopes.update.answer :=
  (mixedScopes.completed later_scoped_definition_wakes_earlier_scope).1

theorem closed_solutions_preserved_separately :
    (∃ solution : empty Tower.rules ⟶ frame, Holds [original] solution) ↔
      ∃ residual : empty Tower.rules ⟶ originalResult.update.target,
        (frames setting.levels).Models residual originalResult.update.remaining :=
  originalResult.fixed_point_solutions_iff (empty Tower.rules)

end ContextualDependentScopedDispatch.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
