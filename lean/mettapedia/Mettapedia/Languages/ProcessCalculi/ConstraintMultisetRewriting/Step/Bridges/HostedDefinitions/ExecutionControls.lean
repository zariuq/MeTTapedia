import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ExecutionReflection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Agreement

/-!
# Positive execution and the value endpoint's exact normal-form boundary

The compiler is run on the actual empty development, retaining the native
vector table. A beta redex reaches zero through its source program. A normal
identity lambda has no value-profile result, showing why normal functions
need the additional normal-form endpoint.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ExecutionControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

def built : Compiled [] := (compile []).get (by decide +kernel)

theorem empty_checked : Definitions.devCheck [] = true := by decide +kernel

def betaInput : Tower.Tm 0 := .app (.lam TowerVectorsModel.zeroC) TowerVectorsModel.ttC

theorem beta_has_actual_compiled_run :
    RuleInstances.Steps built.rules (queryCode betaInput)
      (doneC (encodeTm (TowerVectorsModel.zeroC : Tower.Tm 0))) :=
  Completeness.value_reached built (.single (.betaPi _ _)) .zero

def identity : Tower.Tm 0 := .lam (.var 0)

theorem variable_normal {n : Nat} (index : Fin n) (output : Tower.Tm n) :
    ¬ StrongNormalization.Reduces (Definitions.devPackage [] built.nativeRows) (.var index) output := by
  intro reduction
  cases reduction with
  | root edge =>
      obtain ⟨name, spine, _, _⟩ := Definitions.dev_root_spine empty_checked built.native edge
      simp [ConstructorSystem.spineHead] at spine

theorem identity_normal (output : Tower.Tm 0) :
    ¬ StrongNormalization.Reduces (Definitions.devPackage [] built.nativeRows) identity output := by
  intro reduction
  cases reduction with
  | root edge =>
      obtain ⟨name, spine, _, _⟩ := Definitions.dev_root_spine empty_checked built.native edge
      simp [identity, ConstructorSystem.spineHead] at spine
  | congLam edge => exact variable_normal _ _ edge

theorem identity_not_a_value : ¬ DirectedAnswers.Value identity := by
  intro value
  cases value

theorem normal_identity_has_no_value_profile_answer (result : MClosed) :
    ¬ RuleInstances.Steps built.rules (queryCode identity) (doneC result) := by
  intro run
  obtain ⟨value, reached, isValue, _⟩ := ExecutionReflection.success_reflects built identity result run
  rcases reached.cases_head with same | ⟨next, reduction, _⟩
  · exact identity_not_a_value (same ▸ isValue)
  · exact identity_normal next reduction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ExecutionControls
