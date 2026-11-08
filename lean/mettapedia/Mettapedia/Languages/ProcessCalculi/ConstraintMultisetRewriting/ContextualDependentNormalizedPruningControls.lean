import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizedPruning
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantDispatchControls

/-!
# A declaration whose apparent argument dependency beta-reduces away

The original function type is Pi x:T. (lambda z:T.T) x. Its result syntax
mentions x, so direct discovery declines it. An independently proved beta
equality types the source equation. Certified declaration normalization and
queue recognition then produce a principal answer for that original input.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalizedPruning.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := ContextualDependentConstantPruning.Controls.setting
abbrev base := ContextualDependentConstantPruning.Controls.base
abbrev domain := ContextualDependentConstantPruning.Controls.parameter
abbrev canonicalWhole := ContextualDependentConstantPruning.Controls.whole

theorem eraser_formed : Typed Tower.rules (extend base domain).raw
    (.pi (.var 1) (.head (.sort Tower.zero))) (.head (.sort (.max Tower.zero (.succ Tower.zero)))) :=
  .piForm (.var 1) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

def resultCode : Tower.Tm 2 := .app (.lam (.var 2)) (.var 0)

theorem result_formed : Typed Tower.rules (extend base domain).raw resultCode (.head (.sort Tower.zero)) :=
  Derivable.appElim (R := Tower.rules) (A := .var 1) (B := .head (.sort Tower.zero))
    (.lamIntro eraser_formed (.sort _) (.var 2)) (.var 0)

def whole : TypeOver base :=
  ⟨.pi (.var 0) resultCode, .sort (.max Tower.zero Tower.zero), .sort _,
    .piForm (.var 0) (.sort _) result_formed (.sort _) (.sorts _ _)⟩

theorem declaration_equal : TypeEq Tower.rules base.raw whole.code canonicalWhole.code :=
  ⟨whole.level, whole.universeWitness,
    .piCong (.refl (.var 0)) (.sort _) (.betaPi eraser_formed (.sort _) (.var 2) (.var 0)) (.sort _) (.sorts _ _)⟩

def comparison := extensionComparison whole canonicalWhole declaration_equal
abbrev source := extend base whole
abbrev canonicalCandidate := ContextualDependentConstantDispatch.Controls.candidate
def original : Equation (TotalTerm source) :=
  (canonicalCandidate.1.reindex comparison.hom, canonicalCandidate.2.reindex comparison.hom)

theorem declaration_dependency_is_erased :
    ContextualDependentInversion.invert (ContextualDependentInversion.lookup (wk : Ren 1 2)) resultCode = none := by rfl'

theorem direct_recognition_is_unfinished :
    ContextualDependentConstantDispatch.step (fun _ => (0 : Nat)) 64 whole [original] =
      Update.pending setting.levels [original] := by rfl'

def normalized := (ContextualDependentDeclarationNormalization.normalize (S := setting) (fun _ => none)
  TowerModel.facts TowerModel.roots TowerModel.heads 2 whole).get (by decide +kernel)

theorem actual_normal_annotation : normalized.annotation.code = canonicalWhole.code := by rfl'
theorem original_universe_metadata_retained : normalized.annotation.level = whole.level := normalized.level

def result := step (fun _ => (0 : Nat)) 64 whole [original]

theorem normalization_then_pruning_finishes : result.remaining = [] := by rfl'
theorem actual_answer_is_constant :
    ContextualDependentConstantDispatch.Controls.lambdaIndex (result.answer.substitution 0) = some 1 := by rfl'

theorem principal_for_original_declaration_and_queue :
    (frames setting.levels).Principal [original] result.answer := result.completed normalization_then_pruning_finishes

theorem closed_solutions_preserved :
    (∃ solution : empty Tower.rules ⟶ source, (frames setting.levels).Models solution [original]) ↔
      ∃ residual : empty Tower.rules ⟶ result.target, (frames setting.levels).Models residual result.remaining :=
  result.fixed_point_solutions_iff (empty Tower.rules)

theorem insufficient_budget_keeps_original :
    step (fun _ => (0 : Nat)) 1 whole [original] = Update.pending setting.levels [original] := by rfl'

def reflexive : Equation (TotalTerm source) := (Elimination.last base whole, Elimination.last base whole)

theorem failed_retry_keeps_original_context_and_queue :
    step (fun _ => (0 : Nat)) 64 whole [reflexive] = Update.pending setting.levels [reflexive] := by rfl'

theorem failed_retry_is_not_refutation : (frames setting.levels).Models (𝟙 source) [reflexive] := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact ((frames setting.levels).equivalence source).refl _

end ContextualDependentNormalizedPruning.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
