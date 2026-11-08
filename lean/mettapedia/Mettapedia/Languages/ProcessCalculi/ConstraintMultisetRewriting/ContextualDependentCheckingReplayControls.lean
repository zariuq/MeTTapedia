import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizedRecovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalCheckingTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizationControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability

/-!
# Recovery needs reduction and scope inversion, not a second checker search

The actual rule recovers the typed raw-checker counterexample at reduction
budget two and yields a principal answer for the original equation. A normal
value also recovers while its annotation is not normalized at that budget.
Proper cumulative subtyping is replayed even when the types are not equal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCheckingReplay.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := ConversionControls.setting

def run (fuel : Nat) (type : TypeOver (empty Tower.rules))
    (value : Term (extend (empty Tower.rules) type) (type.reindex (projectionHom _ type))) :=
  ContextualDependentNormalizedRecovery.recover (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    TowerModel.algebra ContextualDependentNormalCheckingTower.head_typing_unique TowerModel.complete
    ContextualDependentFlex.Controls.declarations_formed
    (ContextualDependentReductionReflection.RootReflectsInjections.of_all
      TypedEquality.StrongNormalization.RootReflectsRename.empty)
    (fun _ => none) (fun _ _ _ impossible => impossible.elim) fuel
    (ContextualDependentFlex.withoutNewest _ type) (CtxRen.wk _ _) type value

abbrev type := ContextualDependentFlex.NormalizedControls.type
abbrev frame := ContextualDependentFlex.NormalizedControls.frame
abbrev left := ContextualDependentFlex.NormalizedControls.left
abbrev right := ContextualDependentFlex.NormalizedControls.right

def recovered := (run 2 type right).get (by decide +kernel)

theorem actual_body : recovered.body.code = .lam (.var 0) := by rfl'

theorem original_endpoint_is_solved :
    (frames setting.levels).E
      (TotalTerm.reindex (⟨type, recovered.body⟩ : TotalTerm (empty Tower.rules))
        (projectionHom _ type)) (⟨_, right⟩ : TotalTerm frame) := recovered.solves

def update : Update setting.levels [ContextualDependentFlex.equation left right] :=
  (ContextualDependentUpdate.definition setting.levels recovered.body []).rephrase
    (ContextualDependentFlex.recovered_equivalent setting.levels left right
      (((frames setting.levels).equivalence frame).refl _) recovered.body recovered.solves [])

theorem principal_for_original_redex :
    (frames setting.levels).Principal [ContextualDependentFlex.equation left right] update.answer :=
  update.completed rfl

theorem separate_body_checker_has_not_finished :
    ExecutableChecking.check Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer 2 .nil
      recovered.body.code type.code = none := by rfl'

theorem zero_reduction_budget_is_unfinished : run 0 type right = none := by rfl'

theorem missing_scope_image_is_unfinished : run 1 type left = none := by rfl'

theorem reflexive_problem_still_has_a_solution :
    (frames setting.levels).Models (𝟙 frame) [ContextualDependentFlex.equation left left] := by
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  exact ((frames setting.levels).equivalence frame).refl _

namespace UnreducedAnnotation

abbrev annotation := ContextualDependentNormalization.Controls.annotation
def sourceValue : Term (empty Tower.rules) annotation :=
  ContextualDependentCheckingBoundary.identity.convertType annotation
    ContextualDependentNormalization.Controls.annotation_equal.symm
def value := sourceValue.reindex (projectionHom _ annotation)
def computed := (run 1 annotation value).get (by decide +kernel)

theorem annotation_has_not_normalized :
    ExecutableReduction.normalize Tower.rules (fun _ => none) 1 annotation.code = none := by rfl'

theorem normal_value_is_recovered : computed.body.code = .lam (.var 0) := by rfl'

theorem original_annotation_is_retained : Typed Tower.rules .nil computed.body.code annotation.code :=
  computed.body.typed

end UnreducedAnnotation

namespace Cumulative

def raised : TypeOver (empty Tower.rules) where
  code := .pi (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero)))
  level := .sort (.max (.succ Tower.zero) (.succ (.succ Tower.zero)))
  universeWitness := .sort _
  formed := .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

theorem below : Below Tower.rules .nil type.code raised.code :=
  .subPi type.formed type.universeWitness raised.formed raised.universeWitness
    (.refl (.headType (.sort Tower.zero))) (.sort (.succ Tower.zero))
    (.subUniv (by intro valuation; exact Nat.zero_le 1))

theorem replayed : BelowAlgorithm Tower.rules .nil type.code raised.code :=
  ContextualDependentSubtypeReplay.below_replay (S := setting) TowerModel.facts TowerModel.algebra
    TowerModel.complete .nil type.isType raised.isType below

theorem not_type_equality : ¬ TypeEq Tower.rules .nil type.code raised.code := by
  intro same
  have bodies := (TypeEq.pi_injective TowerModel.facts same .nil).2
  have sameHeads := TypeEq.head_injective TowerModel.facts bodies
    (.snoc .nil (IsType.pi_parts type.isType).1)
  rcases sameHeads with sameHeads | sameHeads
  · cases sameHeads
  · have impossible := sameHeads (fun _ => (0 : Nat))
    change 0 = 1 at impossible
    cases impossible

end Cumulative
end ContextualDependentCheckingReplay.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
