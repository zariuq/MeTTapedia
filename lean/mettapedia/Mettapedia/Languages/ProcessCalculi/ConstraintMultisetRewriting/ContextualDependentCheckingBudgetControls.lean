import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRecoveryBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentProjectionControls

/-!
# Stable complete judgment certificates and dependent recovery

The actual checker accepts a closed identity function and a dependent pair
eta equation. Their full certificates persist at every larger budget.
Neutral synthesis retains its dependent inferred type. Cumulative subtyping
also succeeds when type equality fails, exercising the fallback branch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCheckingBudget.Controls

open Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableChecking ContextualDependentEta ContextualDependentConversionBudget

abbrev setting := ConversionControls.setting

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

abbrev sort0 {n : Nat} : Tower.Tm n := .head (.sort Tower.zero)
abbrev sort1 {n : Nat} : Tower.Tm n := .head (.sort (.succ Tower.zero))
abbrev identity : Tower.Tm 0 := .lam (.var 0)
abbrev identityType : Tower.Tm 0 := .pi sort0 sort0

def fullResult := judgment Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer 24
  .nil identity identityType
def fullCertificate := fullResult.get (by decide +kernel)

theorem expected_type_metadata : fullCertificate.expectedType =
    .head (.sort (.max (.succ Tower.zero) (.succ Tower.zero))) := by rfl'

theorem full_judgment_persists (fuel : Nat) (enough : 24 ≤ fuel) :
    judgment Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer fuel
      .nil identity identityType = some fullCertificate :=
  judgment_success_mono Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer
    (normalizer_stable Tower.rules (fun _ => none)) (by rfl' : fullResult = some fullCertificate) enough

def synthesis := synth Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer 24
  ConversionControls.pairContext.raw (.snd (.var 0))
def synthesisCertificate := synthesis.get (by decide +kernel)

theorem synthesized_type_is_dependent : synthesisCertificate.1 = .fst (.var 0) := by rfl'

theorem dependent_synthesis_persists (fuel : Nat) (enough : 24 ≤ fuel) :
    synth Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer fuel
      ConversionControls.pairContext.raw (.snd (.var 0)) = some synthesisCertificate :=
  synth_success_mono Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer
    (normalizer_stable Tower.rules (fun _ => none)) (by rfl' : synthesis = some synthesisCertificate) enough

def pairEquality := equality Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer 24
  ConversionControls.pairContext.raw ConversionControls.suppliedPair.code ConversionControls.expandedPair.code
    ConversionControls.pairType.code
def pairCertificate := pairEquality.get (by decide +kernel)

theorem checked_eta_persists (fuel : Nat) (enough : 24 ≤ fuel) :
    equality Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer fuel
      ConversionControls.pairContext.raw ConversionControls.suppliedPair.code ConversionControls.expandedPair.code
        ConversionControls.pairType.code = some pairCertificate :=
  equality_success_mono Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer
    (normalizer_stable Tower.rules (fun _ => none)) (by rfl' : pairEquality = some pairCertificate) enough

def cumulativeResult := below Tower.rules ConversionControls.reducer 1 .nil (sort0 : Tower.Tm 0) sort1
def cumulativeCertificate := cumulativeResult.get (by decide +kernel)

theorem equality_fails_but_cumulativity_succeeds :
    ExecutableConversion.types Tower.rules ConversionControls.reducer 1 .nil (sort0 : Tower.Tm 0) sort1 = none ∧
      cumulativeResult.isSome = true := by decide +kernel

theorem cumulative_check_persists (fuel : Nat) (enough : 1 ≤ fuel) :
    below Tower.rules ConversionControls.reducer fuel .nil (sort0 : Tower.Tm 0) sort1 = some cumulativeCertificate :=
  below_success_mono Tower.rules ConversionControls.reducer (normalizer_stable Tower.rules (fun _ => none))
    (by rfl' : cumulativeResult = some cumulativeCertificate) enough

theorem wrong_function_annotation_is_not_accepted :
    (judgment Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer 24
      .nil identity sort0).isSome = false := by decide +kernel

theorem zero_budget_is_not_accepted :
    (judgment Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer 0
      .nil identity identityType).isSome = false := by decide +kernel

theorem projection_recovery_persists (fuel : Nat) (enough : 24 ≤ fuel) :
    ContextualDependentProjectionInversion.Controls.run fuel
      ContextualDependentProjectionInversion.Controls.both
      ContextualDependentProjectionInversion.Controls.wholeType
      ContextualDependentProjectionInversion.Controls.packedValue =
        some ContextualDependentProjectionInversion.Controls.wholeRecovery :=
  ContextualDependentRecoveryBudget.projection_recover_mono (S := setting)
    TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
    ConversionControls.reducer (normalizer_stable Tower.rules (fun _ => none))
    (by rfl' : ContextualDependentProjectionInversion.Controls.wholeResult =
      some ContextualDependentProjectionInversion.Controls.wholeRecovery) enough

end ContextualDependentCheckingBudget.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
