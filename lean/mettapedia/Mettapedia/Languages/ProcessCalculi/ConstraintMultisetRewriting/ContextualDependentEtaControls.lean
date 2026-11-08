import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaBridge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstraintControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerConservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversionSkeleton

/-!
# Rigid eta controls and an actual beta-solution comparison

Opaque declared constants cannot be instantiated by a future solver. Their
function and dependent-pair eta equations therefore separate *solvability*
in the two frames, not just equality at one chosen substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEta.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

def functionName : DeclName := .str .anonymous "opaqueFunction"
def pairName : DeclName := .str .anonymous "opaquePair"

def arrow {n : Nat} : Tower.Tm n := .pi (.head .legacyGround) (.head .legacyGround)
def dependentSum {n : Nat} : Tower.Tm n := .sigma (.head (.sort Tower.zero)) (.var 0)

def rules : Rules Tower.Head := { Tower.rules with
  constantType := fun name =>
    if name = functionName then some arrow else if name = pairName then some dependentSum else none }

def levels : LevelModel rules Nat := { TowerModel.levels (fun _ => (0 : Nat)) with }

theorem arrow_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed rules Γ arrow (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm (.headType .legacyGround) (.sort _) (.headType .legacyGround) (.sort _) (.sorts _ _)

theorem sum_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed rules Γ dependentSum (.head (.sort (.max (.succ Tower.zero) Tower.zero))) :=
  .sigmaForm (.headType (.sort _)) (.sort _) (.var 0) (.sort _) (.sorts _ _)

theorem function_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ (.const functionName) arrow :=
  .const (by decide) (arrow_formed .nil) (.sort _)

theorem pair_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ (.const pairName) dependentSum :=
  .const (by decide) (sum_formed .nil) (.sort _)

def etaFunction {n : Nat} : Tower.Tm n := .lam (.app (.const functionName) (.var 0))
def etaPair {n : Nat} : Tower.Tm n := .pair (.fst (.const pairName)) (.snd (.const pairName))

theorem etaFunction_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ etaFunction arrow :=
  .lamIntro (arrow_formed Γ) (.sort _) (.appElim (function_typed _) (.var 0))

theorem etaPair_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ etaPair dependentSum :=
  .pairIntro (sum_formed Γ) (.sort _) (.fstElim (pair_typed Γ)) (.sndElim (pair_typed Γ))

theorem function_equal {n : Nat} (Γ : Tower.Ctx n) :
    Equal rules Γ (.const functionName) etaFunction arrow := by
  apply Derivable.etaPi (function_typed Γ) (etaFunction_typed Γ)
  exact .symm (.betaPi (arrow_formed _) (.sort _)
    (.appElim (function_typed _) (.var 0)) (.var 0))

theorem pair_equal {n : Nat} (Γ : Tower.Ctx n) :
    Equal rules Γ (.const pairName) etaPair dependentSum := by
  apply Derivable.etaSigma (pair_typed Γ) (etaPair_typed Γ)
  · exact .symm (.betaFst (sum_formed Γ) (.sort _) (.fstElim (pair_typed Γ)) (.sndElim (pair_typed Γ)))
  · exact .symm (.betaSnd (sum_formed Γ) (.sort _) (.fstElim (pair_typed Γ)) (.sndElim (pair_typed Γ)))

def arrowType : TypeOver (empty rules) :=
  ⟨arrow, .sort (.max Tower.zero Tower.zero), .sort _, arrow_formed .nil⟩

def sumType : TypeOver (empty rules) :=
  ⟨dependentSum, .sort (.max (.succ Tower.zero) Tower.zero), .sort _, sum_formed .nil⟩

def functionProblem : EquationStore (TotalTerm (empty rules)) :=
  [((⟨arrowType, ⟨.const functionName, function_typed .nil⟩⟩ : TotalTerm (empty rules)),
    ⟨arrowType, ⟨etaFunction, etaFunction_typed .nil⟩⟩)]

def pairProblem : EquationStore (TotalTerm (empty rules)) :=
  [((⟨sumType, ⟨.const pairName, pair_typed .nil⟩⟩ : TotalTerm (empty rules)),
    ⟨sumType, ⟨etaPair, etaPair_typed .nil⟩⟩)]

theorem function_eta_solved : (frames levels).Solvable functionProblem :=
  solvable_of_equivalent levels _ _ ⟨arrowType.isType.refl, function_equal .nil⟩

theorem pair_eta_solved : (frames levels).Solvable pairProblem :=
  solvable_of_equivalent levels _ _ ⟨sumType.isType.refl, pair_equal .nil⟩

theorem function_not_beta :
    ¬ Conv rules.headEq (.const functionName : Tower.Tm 0) etaFunction rules.computation := by
  apply TowerConversionSkeleton.not_conv_of_normal_erase_ne
  · intro target step
    cases step
  · intro target step
    cases step with
    | congLam inner =>
        cases inner with
        | congAppFun prior => cases prior
        | congAppArg prior => cases prior
  · intro same
    cases same

theorem pair_not_beta :
    ¬ Conv rules.headEq (.const pairName : Tower.Tm 0) etaPair rules.computation := by
  apply TowerConversionSkeleton.not_conv_of_normal_erase_ne
  · intro target step
    cases step
  · intro target step
    cases step with
    | congPairFst inner => cases inner with | congFst prior => cases prior
    | congPairSnd inner => cases inner with | congSnd prior => cases prior
  · intro same
    cases same

theorem raw_arrow_formed {n : Nat} (Γ : Tower.Ctx n) :
    FormationSensitive.Typing rules Γ arrow (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm (.headType .legacyGround) (.sort _) (.headType .legacyGround) (.sort _) (.sorts _ _)

theorem raw_sum_formed {n : Nat} (Γ : Tower.Ctx n) :
    FormationSensitive.Typing rules Γ dependentSum (.head (.sort (.max (.succ Tower.zero) Tower.zero))) :=
  .sigmaForm (.headType (.sort _)) (.sort _) (.var 0) (.sort _) (.sorts _ _)

theorem raw_function_typed {n : Nat} (Γ : Tower.Ctx n) :
    FormationSensitive.Typing rules Γ (.const functionName) arrow :=
  .const (by decide) (raw_arrow_formed .nil) (.sort _)

theorem raw_pair_typed {n : Nat} (Γ : Tower.Ctx n) :
    FormationSensitive.Typing rules Γ (.const pairName) dependentSum :=
  .const (by decide) (raw_sum_formed .nil) (.sort _)

def rawArrow : FormationSensitiveContextual.TypeOver (FormationSensitiveContextual.empty rules) :=
  ⟨arrow, .sort (.max Tower.zero Tower.zero), .sort _, raw_arrow_formed .nil⟩

def rawSum : FormationSensitiveContextual.TypeOver (FormationSensitiveContextual.empty rules) :=
  ⟨dependentSum, .sort (.max (.succ Tower.zero) Tower.zero), .sort _, raw_sum_formed .nil⟩

def rawFunctionProblem : EquationStore (Interface.Dependent.Entry (FormationSensitiveContextual.empty rules)) :=
  [((⟨rawArrow, ⟨.const functionName, raw_function_typed .nil⟩⟩ : Interface.Dependent.Entry _),
    ⟨rawArrow, ⟨etaFunction,
      .lamIntro rawArrow.formed (.sort _) (.appElim (raw_function_typed _) (.var 0))⟩⟩)]

def rawPairProblem : EquationStore (Interface.Dependent.Entry (FormationSensitiveContextual.empty rules)) :=
  [((⟨rawSum, ⟨.const pairName, raw_pair_typed .nil⟩⟩ : Interface.Dependent.Entry _),
    ⟨rawSum, ⟨etaPair,
      .pairIntro rawSum.formed (.sort _) (.fstElim (raw_pair_typed .nil)) (.sndElim (raw_pair_typed .nil))⟩⟩)]

theorem function_requires_eta : ¬ (Interface.Dependent.frames rules).Solvable rawFunctionProblem := by
  intro solved
  exact function_not_beta ((Interface.Dependent.solvable_empty_iff _).mp solved _ (List.mem_singleton_self _)).2

theorem pair_requires_eta : ¬ (Interface.Dependent.frames rules).Solvable rawPairProblem := by
  intro solved
  exact pair_not_beta ((Interface.Dependent.solvable_empty_iff _).mp solved _ (List.mem_singleton_self _)).2

/-- The previously qualified dependent wake-up problem retains its actual
solution through the comparison; all qualification premises are discharged. -/
theorem pending_beta_example_also_eta :
    (frames (TowerModel.levels (fun _ => (0 : Nat)))).Solvable
      (BetaBridge.problem (S := TowerModel.setting (fun _ => (0 : Nat)))
        TowerModel.facts TowerModel.roots TowerModel.heads Normalization.LevelTower.churchRosser
        (Interface.Dependent.definition (FormationSensitiveContextual.empty Tower.rules)
          ContextualDependentConstraints.Controls.ground :: ContextualDependentConstraints.Controls.suspended.store)) :=
  BetaBridge.solvable (S := TowerModel.setting (fun _ => (0 : Nat)))
    TowerModel.facts TowerModel.roots TowerModel.heads Normalization.LevelTower.churchRosser _
    ContextualDependentConstraints.Controls.original_has_a_solution

end ContextualDependentEta.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
