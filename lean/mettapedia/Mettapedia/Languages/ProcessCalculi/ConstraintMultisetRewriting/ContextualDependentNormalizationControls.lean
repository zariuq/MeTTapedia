import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizationTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizedFlexControls

/-!
# Normalization changes real annotations and composes with the solver

The example reduces both a beta-redex annotation and a beta-redex value.
Unfinished normalization keeps the original endpoint. Heterogeneous and
repeated equations are retained, and normalization composes with the actual
flexible-variable rule to earn a principal answer for the original input.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalization.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := ConversionControls.setting
abbrev functionType := ContextualDependentCheckingBoundary.functionType
abbrev highLevel : UniverseLevel.LevelExpr Nat := .max (.succ Tower.zero) (.succ Tower.zero)
abbrev high := LevelTower.Head.sort highLevel

theorem type_identity_formed : Typed Tower.rules .nil
    (.pi (.head high) (.head high)) (.head (.sort (.max (.succ highLevel) (.succ highLevel)))) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

def annotation : TypeOver (empty Tower.rules) where
  code := .app (.lam (.var 0)) functionType.code
  level := high
  universeWitness := .sort _
  formed := Derivable.appElim (A := .head high) (B := .head high)
    (.lamIntro type_identity_formed (.sort _) (.var 0)) functionType.formed

theorem annotation_equal : TypeEq Tower.rules .nil annotation.code functionType.code :=
  ⟨high, .sort _, .betaPi type_identity_formed (.sort _) (.var 0) functionType.formed⟩

def original : TotalTerm (empty Tower.rules) :=
  ⟨annotation, ContextualDependentCheckingBoundary.typedRedex.convertType annotation annotation_equal.symm⟩
def canonical : TotalTerm (empty Tower.rules) :=
  ⟨functionType, ContextualDependentCheckingBoundary.identity⟩

def run (fuel : Nat) := reduceTerm (S := setting) (fun _ => none)
  TowerModel.facts TowerModel.roots TowerModel.heads fuel original
def result := (run 2).get (by decide +kernel)

theorem value_and_annotation_reduce :
    result.value.1.code = functionType.code ∧
      result.value.2.code = ContextualDependentCheckingBoundary.identity.code := by constructor <;> rfl'

theorem universe_metadata_retained : result.value.1.level = original.1.level := by rfl'

theorem raw_spelling_changes :
    original.1.code ≠ result.value.1.code ∧ original.2.code ≠ result.value.2.code := by decide +kernel

theorem typed_meaning_retained : (frames setting.levels).E original result.value := result.equivalent

theorem insufficient_budget_retains_endpoint :
    termAt (S := setting) (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads 1 original = original := by rfl'

def groundType : TypeOver (empty Tower.rules) :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩
def ground : TotalTerm (empty Tower.rules) := ⟨groundType, ⟨.head .legacyGround, .headType .legacyGround⟩⟩
def heterogeneous : Equation (TotalTerm (empty Tower.rules)) := (ground, canonical)
def mixed : EquationStore (TotalTerm (empty Tower.rules)) :=
  [(original, canonical), heterogeneous, (canonical, original)]

theorem equations_are_not_discarded :
    storeAt (S := setting) (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads 2 mixed =
      [(canonical, canonical), heterogeneous, (canonical, canonical)] := by rfl'

theorem unsafe_source_cannot_enter_as_typed :
    ¬ ∃ term : TotalTerm (empty Tower.rules), term.2.code = ContextualDependentCheckingBoundary.unsafeSource := by
  rintro ⟨⟨type, term⟩, same⟩
  have typed := term.typed
  rw [same] at typed
  exact ContextualDependentCheckingBoundary.unchecked_source_has_no_type type.code typed

abbrev sourceFrame := ContextualDependentFlex.NormalizedControls.frame
def sourceProblem : EquationStore (TotalTerm sourceFrame) :=
  [ContextualDependentFlex.equation ContextualDependentFlex.NormalizedControls.left
    ContextualDependentFlex.NormalizedControls.right]

def prepared := update (S := setting) (fun _ => none) TowerModel.facts TowerModel.roots TowerModel.heads 2 sourceProblem

theorem prepared_has_normalized_problem : prepared.remaining =
    [ContextualDependentFlex.equation ContextualDependentFlex.NormalizedControls.left
      ContextualDependentFlex.NormalizedControls.identityRight] := by rfl'

def solved : Update setting.levels prepared.remaining :=
  ContextualDependentFlex.NormalizedControls.opaqueRun.rephrase (by
    intro Δ solution
    rw [prepared_has_normalized_problem]
    exact Iff.rfl)

def combined := prepared.then solved

theorem actual_pipeline_finishes : combined.remaining = [] :=
  ContextualDependentFlex.NormalizedControls.direct_route_still_finishes

theorem actual_pipeline_principal_for_original :
    (frames setting.levels).Principal sourceProblem combined.answer := combined.completed actual_pipeline_finishes

end ContextualDependentNormalization.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
