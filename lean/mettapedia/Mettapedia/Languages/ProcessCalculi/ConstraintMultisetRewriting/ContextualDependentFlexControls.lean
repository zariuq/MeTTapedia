import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversionControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices

/-!
# Computed flexible-function solving with retained constraints

The actual rule solves `lambda x. F x = lambda x. G x`, retaining G as a
variable and computing F's answer. It earns principality for this problem.
An additional equation on G remains residual. A recursive non-pattern stays
pending although a separately checked identity substitution solves it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFlex.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := ConversionControls.setting

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

theorem declarations_formed : DeclaredTypesFormed setting.R := by
  intro name type known
  cases known

abbrev base := Examples.TypedContextualControls.functionContext
def secondType : TypeOver base :=
  Examples.TypedContextualControls.functionType.reindex
    (projectionHom _ Examples.TypedContextualControls.functionType)
abbrev frame := extend base secondType
def viewedType : TypeOver frame := secondType.reindex (projectionHom _ secondType)

def left : Term frame viewedType :=
  ⟨.lam (.app (.var 1) (.var 0)), .lamIntro viewedType.formed viewedType.universeWitness
    (Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero))
      (B := .head (.sort Tower.zero)) (.var 1) (.var 0))⟩

def right : Term frame viewedType :=
  ⟨.lam (.app (.var 2) (.var 0)), .lamIntro viewedType.formed viewedType.universeWitness
    (Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero))
      (B := .head (.sort Tower.zero)) (.var 2) (.var 0))⟩

def recoveredFunction : Term base secondType :=
  ⟨.lam (.app (.var 1) (.var 0)), .lamIntro secondType.formed secondType.universeWitness
    (Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero))
      (B := .head (.sort Tower.zero)) (.var 1) (.var 0))⟩

def run (fuel : Nat) (rest : EquationStore (TotalTerm frame)) :=
  stepNewest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    declarations_formed ExecutableTowerChoices.choices ConversionControls.reducer fuel left right rest

theorem actual_pattern_finishes : (run 16 []).remaining = [] := by decide +kernel

theorem actual_pattern_answer :
    (⟨(run 16 []).target, (run 16 []).answer⟩ : (Δ : Context Tower.rules) × (Δ ⟶ frame)) =
      ⟨base, Elimination.instantiate base recoveredFunction⟩ := by
  calc
    _ = (⟨base, (𝟙 base) ≫ Elimination.instantiate base recoveredFunction⟩ :
        (Δ : Context Tower.rules) × (Δ ⟶ frame)) := by rfl'
    _ = _ := congrArg (fun answer : base ⟶ frame =>
      (⟨base, answer⟩ : (Δ : Context Tower.rules) × (Δ ⟶ frame))) (Category.id_comp _)

theorem actual_pattern_principal :
    (frames setting.levels).Principal [equation left right] (run 16 []).answer :=
  (run 16 []).completed actual_pattern_finishes

theorem zero_budget_keeps_the_equation :
    (⟨(run 0 []).target, (run 0 []).remaining⟩ : (Δ : Context Tower.rules) × EquationStore (TotalTerm Δ)) =
      ⟨frame, [equation left right]⟩ := by rfl'

def olderFunction : Term frame viewedType := ⟨.var 1, .var 1⟩
def identity : Term frame viewedType :=
  ⟨.lam (.var 0), .lamIntro viewedType.formed viewedType.universeWitness (.var 0)⟩
def sideCondition : Equation (TotalTerm frame) := (⟨_, olderFunction⟩, ⟨_, identity⟩)

theorem unrelated_obligation_survives : (run 16 [sideCondition]).remaining.length = 1 := by decide +kernel

def recursiveRight : Term frame viewedType :=
  ⟨.lam (.app (.var 1) (.app (.var 1) (.var 0))), .lamIntro viewedType.formed viewedType.universeWitness
    (Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero)) (B := .head (.sort Tower.zero))
      (.var 1) (Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero))
        (B := .head (.sort Tower.zero)) (.var 1) (.var 0)))⟩

def recursiveAttempt :=
  stepNewest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    declarations_formed ExecutableTowerChoices.choices ConversionControls.reducer 16 left recursiveRight []

theorem recursive_nonpattern_is_retained :
    (⟨recursiveAttempt.target, recursiveAttempt.remaining⟩ :
      (Δ : Context Tower.rules) × EquationStore (TotalTerm Δ)) =
      ⟨frame, [equation left recursiveRight]⟩ := by rfl'

def identityAtBase : Term base secondType :=
  ⟨.lam (.var 0), .lamIntro secondType.formed secondType.universeWitness (.var 0)⟩

/-- An independently required definition makes the recursive residual
solvable; the computed substitution and conversion pass both do real work. -/
def forcedIdentity :=
  defineThenConvert (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ConversionControls.reducer 16 identityAtBase [equation left recursiveRight]

theorem recursive_residual_solves_after_definition : forcedIdentity.remaining = [] := by decide +kernel

theorem forced_definition_is_principal :
    (frames setting.levels).Principal
      (Elimination.definition base identityAtBase :: [equation left recursiveRight]) forcedIdentity.answer :=
  forcedIdentity.completed recursive_residual_solves_after_definition

theorem recursive_nonpattern_has_a_solution :
    (frames setting.levels).Solvable [equation left recursiveRight] :=
  Frames.solvable_of_subset (fun _ member => List.mem_cons_of_mem _ member)
    (Frames.Principal.solvable forced_definition_is_principal)

end ContextualDependentFlex.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
