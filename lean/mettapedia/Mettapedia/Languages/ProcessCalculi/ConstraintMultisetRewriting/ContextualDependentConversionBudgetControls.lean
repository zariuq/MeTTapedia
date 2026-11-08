import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversionControls

/-!
# Conversion budgets preserve dependent answers and residual order

An accepted Sigma-eta equation remains accepted at every larger budget.
Neutral projection comparison retains its inferred dependent type. The
scanner removes certified equations without reordering or deduplicating the
remaining ones. A certificate-returning but unstable reducer separates
soundness from budget stability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConversionBudget.Controls

open Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

abbrev setting := ConversionControls.setting

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def leftPair : TotalTerm ConversionControls.pairContext :=
  ⟨ConversionControls.pairType, ConversionControls.suppliedPair⟩
def rightPair : TotalTerm ConversionControls.pairContext :=
  ⟨ConversionControls.pairType, ConversionControls.expandedPair⟩

def pairResult := Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
  TowerModel.algebra ConversionControls.reducer 16 leftPair rightPair
def pairCertificate := pairResult.get (by decide +kernel)

theorem all_larger_pair_eta (fuel : Nat) (enough : 16 ≤ fuel) :
    Conversion.compare (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ConversionControls.reducer fuel leftPair rightPair = some pairCertificate :=
  ContextualDependentEtaBudget.compare_mono (S := setting) (Γ := ConversionControls.pairContext)
    TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ConversionControls.reducer (normalizer_stable Tower.rules (fun _ => none))
    (by rfl' : pairResult = some pairCertificate) enough

def neutralResult := ExecutableConversion.neutral Tower.rules ConversionControls.reducer 16
  ConversionControls.pairContext.raw (.snd (.var 0)) (.snd (.var 0))
def neutralCertificate := neutralResult.get (by decide +kernel)

theorem inferred_type_is_the_first_projection : neutralCertificate.1 = .fst (.var 0) := by rfl'

theorem all_larger_neutral_types (fuel : Nat) (enough : 16 ≤ fuel) :
    ExecutableConversion.neutral Tower.rules ConversionControls.reducer fuel
      ConversionControls.pairContext.raw (.snd (.var 0)) (.snd (.var 0)) = some neutralCertificate :=
  normalizer_neutral_mono Tower.rules (fun _ => none)
    (by rfl' : neutralResult = some neutralCertificate) enough

def projectedType : TypeOver ConversionControls.pairContext :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩
def pending : Equation (TotalTerm ConversionControls.pairContext) :=
  (⟨projectedType, ⟨.fst (.var 0), .fstElim ConversionControls.suppliedPair.typed⟩⟩,
    ⟨projectedType, ⟨.head .legacyGround, .headType .legacyGround⟩⟩)
def problem : EquationStore (TotalTerm ConversionControls.pairContext) :=
  [(leftPair, rightPair), pending, (leftPair, rightPair), pending]

theorem scan_keeps_residual_order_and_duplicates : ConversionControls.scan 16 problem = [pending, pending] := by rfl'

theorem zero_budget_keeps_every_equation : ConversionControls.scan 0 problem = problem := by rfl'

theorem larger_scan_is_sublist (first second : Nat) (enough : first ≤ second) :
    (ConversionControls.scan second problem).Sublist (ConversionControls.scan first problem) :=
  ContextualDependentEtaBudget.scan_sublist (S := setting) (Γ := ConversionControls.pairContext)
    TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ConversionControls.reducer (normalizer_stable Tower.rules (fun _ => none)) enough problem

def withdrawingReducer : ExecutableReduction.Reducer Tower.rules :=
  fun fuel _ term => if fuel ≤ 2 then some ⟨term, .refl⟩ else none

theorem unstable_reducer_can_lose_acceptance :
    ExecutableConversion.acceptsTypes Tower.rules withdrawingReducer 1 .nil
      (.head .legacyGround) (.head .legacyGround) = true ∧
    ExecutableConversion.acceptsTypes Tower.rules withdrawingReducer 3 .nil
      (.head .legacyGround) (.head .legacyGround) = false := by decide +kernel

theorem withdrawing_reducer_is_not_stable :
    ¬ (∀ {n : Nat} (fuel : Nat) (term : Tower.Tm n),
      Keeps (withdrawingReducer fuel term) (withdrawingReducer (fuel + 1) term)) := by
  intro stable
  have kept := stable 2 (.head .legacyGround : Tower.Tm 0)
    (⟨.head .legacyGround, .refl⟩ : ExecutableReduction.Result Tower.rules (.head .legacyGround)) rfl
  cases kept

end ContextualDependentConversionBudget.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
