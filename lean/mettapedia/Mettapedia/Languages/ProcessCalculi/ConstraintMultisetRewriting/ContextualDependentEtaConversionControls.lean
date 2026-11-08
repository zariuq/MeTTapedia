import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.TypedContextualControls

/-!
# Actual bounded eta conversion and residual controls

The independent typed-contextual examples supply a function and its eta
expansion. The actual type-directed converter discharges their equation.
A dependent-pair example uses the same executable path. A non-pattern
application remains residual, and a zero budget retains even the eta equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEta.ConversionControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

instance : DecidableRel Tower.rules.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right

def reducer : ExecutableReduction.Reducer Tower.rules :=
  ExecutableReduction.normalize Tower.rules (fun _ => none)

abbrev setting := TowerModel.setting (fun _ => (0 : Nat))

instance : DecidableRel setting.R.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right

instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def scan (fuel : Nat) {Γ : Context Tower.rules} (problem : EquationStore (TotalTerm Γ)) :=
  Conversion.scan (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    reducer fuel problem

def functionProblem : EquationStore (TotalTerm Examples.TypedContextualControls.familyContext) :=
  [((⟨_, Examples.TypedContextualControls.suppliedFunction⟩ : TotalTerm _),
    ⟨_, Examples.TypedContextualControls.etaFunction⟩)]

theorem actual_function_eta_finishes : scan 16 functionProblem = [] := by decide +kernel

theorem zero_budget_retains_function : scan 0 functionProblem = functionProblem := by rfl'

def sumType : TypeOver (empty Tower.rules) :=
  ⟨.sigma (.head (.sort Tower.zero)) (.var 0),
    .sort (.max (.succ Tower.zero) Tower.zero), .sort _,
    .sigmaForm (.headType (.sort _)) (.sort _) (.var 0) (.sort _) (.sorts _ _)⟩

abbrev pairContext := extend (empty Tower.rules) sumType

def pairType : TypeOver pairContext := sumType.reindex (projectionHom _ sumType)

def suppliedPair : Term pairContext pairType := newest _ sumType

def expandedPair : Term pairContext pairType :=
  ⟨.pair (.fst (.var 0)) (.snd (.var 0)),
    .pairIntro pairType.formed pairType.universeWitness
      (.fstElim suppliedPair.typed) (.sndElim suppliedPair.typed)⟩

def pairProblem : EquationStore (TotalTerm pairContext) :=
  [((⟨_, suppliedPair⟩ : TotalTerm _), ⟨_, expandedPair⟩)]

theorem actual_dependent_pair_eta_finishes : scan 16 pairProblem = [] := by decide +kernel

abbrev functionContext := Examples.TypedContextualControls.functionContext

def sortType : TypeOver functionContext :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩

def appliedOnce : Term functionContext sortType := by
  refine ⟨.app (.var 0) (.head .legacyGround), ?_⟩
  change Typed Tower.rules functionContext.raw (.app (.var 0) (.head .legacyGround)) (.head (.sort Tower.zero))
  exact Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero)) (B := .head (.sort Tower.zero))
    (.var 0) (.headType .legacyGround)

def appliedTwice : Term functionContext sortType := by
  refine ⟨.app (.var 0) appliedOnce.code, ?_⟩
  change Typed Tower.rules functionContext.raw (.app (.var 0) appliedOnce.code) (.head (.sort Tower.zero))
  exact Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero)) (B := .head (.sort Tower.zero))
    (.var 0) appliedOnce.typed

/-- The flexible head is applied to a non-variable argument. No assignment
is guessed when conversion alone does not settle the equation. -/
def nonPattern : EquationStore (TotalTerm functionContext) :=
  [((⟨_, appliedTwice⟩ : TotalTerm _), ⟨_, appliedOnce⟩)]

theorem non_pattern_remains_residual : scan 16 nonPattern = nonPattern := by rfl'

/-- The retained non-pattern really has a solution: instantiate the function
by identity. Retention is not a disguised refutation. -/
def identityFunction : Term (empty Tower.rules) Examples.TypedContextualControls.functionType :=
  ⟨.lam (.var 0), .lamIntro Examples.TypedContextualControls.functionType.formed (.sort _) (.var 0)⟩

def identitySolution : empty Tower.rules ⟶ functionContext :=
  TypedContextual.pair (𝟙 _) (identityFunction.cast Examples.TypedContextualControls.functionType.reindex_id.symm)

theorem non_pattern_solution_checks :
    scan 16 ((frames setting.levels).applyStore identitySolution nonPattern) = [] := by decide +kernel

theorem non_pattern_is_solvable : (frames setting.levels).Solvable nonPattern := by
  refine ⟨empty Tower.rules, identitySolution, ?_⟩
  have reduced : (frames setting.levels).Models (𝟙 (empty Tower.rules))
      ((frames setting.levels).applyStore identitySolution nonPattern) := by
    apply (Conversion.scan_models (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra reducer 16 (𝟙 _) _).mp
    change (frames setting.levels).Models (𝟙 _) (scan 16 _)
    rw [non_pattern_solution_checks]
    exact Frames.models_nil _
  have solved := (Frames.models_applyStore (X := frames setting.levels)
    identitySolution (𝟙 _) nonPattern).mp reduced
  exact (Frames.models_congr (X := frames setting.levels)
    (fun term => ((frames setting.levels).act_comp ((frames setting.levels).id _) identitySolution term).trans
      ((frames setting.levels).act_id _)) nonPattern).mp solved

end ContextualDependentEta.ConversionControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
