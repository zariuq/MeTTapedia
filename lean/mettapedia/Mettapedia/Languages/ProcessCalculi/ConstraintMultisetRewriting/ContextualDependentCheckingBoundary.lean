import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaConversionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentReductionBudgetControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.ExecutableTowerChoices

/-!
# The raw checker's completeness boundary and safe normalization

An application with an unannotated lambda argument is well typed but is
never accepted by this bidirectional checker: the argument cannot synthesize
its type. Normalizing arbitrary unchecked syntax is not a sound repair,
because beta reduction can discard an untypable argument. The unifier's
independently typed endpoints permit normalization without that shortcut.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCheckingBoundary

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ExecutableChecking ContextualDependentEta

abbrev setting := ConversionControls.setting
abbrev functionType := Examples.TypedContextualControls.functionType
abbrev functionCode {n : Nat} : Tower.Tm n := Examples.TypedContextualControls.functionCode
abbrev high := Examples.TypedContextualControls.high

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def identity : Term (empty Tower.rules) functionType :=
  ⟨.lam (.var 0), .lamIntro functionType.formed functionType.universeWitness (.var 0)⟩
def redex : Tower.Tm 0 := .app (.lam (.var 0)) identity.code

theorem redex_typed : Typed Tower.rules .nil redex functionCode := by
  have outerFormed := Derivable.piForm (R := Tower.rules)
    (Examples.TypedContextualControls.function_formed (.nil : Tower.Ctx 0)) (LevelTower.IsUniverse.sort _)
    (Examples.TypedContextualControls.function_formed (.snoc .nil (functionCode : Tower.Tm 0)))
    (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)
  exact Derivable.appElim (A := functionCode) (B := functionCode)
    (.lamIntro outerFormed (.sort _) (.var 0)) identity.typed

def typedRedex : Term (empty Tower.rules) functionType := ⟨redex, redex_typed⟩

theorem lambda_cannot_synthesize (fuel : Nat) {n : Nat} (Γ : Ctx Tower.Head n)
    (body : Tower.Tm (n + 1)) :
    synth Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer fuel Γ (.lam body) = none := by
  cases fuel <;> rfl

theorem redex_never_synthesizes (fuel : Nat) :
    synth Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer fuel .nil redex = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change synth Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer (fuel + 1)
      .nil (.app (.lam (.var 0)) (.lam (.var 0))) = none
    rw [synth]
    simp only [lambda_cannot_synthesize]
    rfl

theorem redex_never_checks (fuel : Nat) :
    check Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer fuel .nil redex functionCode = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [check]
    · simp only [redex_never_synthesizes]
      rfl
    all_goals simp [redex]

theorem redex_never_has_judgment (fuel : Nat) :
    judgment Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer fuel .nil redex functionCode = none := by
  simp [judgment, redex_never_checks]

theorem raw_checker_is_not_complete :
    ¬ (∀ (term type : Tower.Tm 0), Typed Tower.rules .nil term type →
      ∃ fuel, (judgment Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer fuel .nil term type).isSome = true) := by
  intro complete
  obtain ⟨fuel, accepted⟩ := complete redex functionCode redex_typed
  rw [redex_never_has_judgment] at accepted
  cases accepted

theorem typed_redex_normalizes :
    (ConversionControls.reducer 2 redex).map Subtype.val = some identity.code := by rfl'

def unsafeSource : Tower.Tm 0 :=
  .app (.lam (.head .legacyGround)) ContextualDependentReductionBudget.Controls.loop

theorem unchecked_source_normalizes :
    (ConversionControls.reducer 2 unsafeSource).map Subtype.val = some (.head .legacyGround) := by rfl'

theorem unchecked_source_has_no_type (type : Tower.Tm 0) : ¬ Typed Tower.rules .nil unsafeSource type := by
  intro typed
  have loopSN := StrongNormalization.SN.app_right (TowerInterpretation.tower_sn CtxFormed.nil typed)
  obtain ⟨fuel, result, accepted, _⟩ :=
    ContextualDependentReductionBudget.exists_budget_of_sn Tower.rules (fun _ => none) loopSN
  have exhausted := ContextualDependentReductionBudget.Controls.loop_exhausts_every_budget fuel
  change ExecutableReduction.normalize Tower.rules (fun _ => none) fuel
    ContextualDependentReductionBudget.Controls.loop = none at exhausted
  rw [exhausted] at accepted
  cases accepted

theorem normal_form_passes_raw_checker :
    (judgment Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer 24 .nil
      (.head .legacyGround) (.head (.sort Tower.zero))).isSome = true := by decide +kernel

end ContextualDependentCheckingBoundary
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
