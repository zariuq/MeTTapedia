import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentContextNormalizationTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSelectionControls

/-!
# Normalizing actual dependent declarations retains their obligations

The context A:U0, x:(lambda B.B) A, p:Id ((lambda B.B) A) x x
normalizes to A:U0, x:A, p:Id A x x. All three variables and both copies of
the equation p = refl x remain. Typed inverse maps preserve solutions at
every later context, including the empty context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentContextNormalization.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

abbrev setting := ContextualDependentNormalSupport.Controls.setting
abbrev types := ContextualDependentInversion.Controls.typeContext

def redexType : TypeOver types where
  code := .app (.lam (.var 0)) (.var 0)
  level := .sort Tower.zero
  universeWitness := .sort _
  formed := by
    exact Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero)) (B := .head (.sort Tower.zero))
      (.lamIntro (Examples.TypedContextualControls.function_formed _) (.sort _) (.var 0)) (.var 0)

abbrev values := extend types redexType
def carrier := redexType.reindex (projectionHom types redexType)
def proofType : TypeOver values :=
  ⟨.id carrier.code (.var 0) (.var 0), .sort Tower.zero, .sort _,
    .idForm carrier.formed (.sort _) (.var 0) (.var 0)⟩
abbrev original := extend values proofType

def run (fuel : Nat) := normalize (S := setting) (fun _ => none) (fun _ _ _ impossible => impossible.elim)
  TowerModel.facts TowerModel.roots TowerModel.heads fuel original.raw original.formed
def result := (run 2).get (by decide +kernel)

theorem actual_normal_declarations : result.raw =
    .snoc (.snoc (.snoc .nil (.head (.sort Tower.zero))) (.var 0)) (.id (.var 1) (.var 0) (.var 0)) := by rfl'

theorem presentation_really_changes : result.raw ≠ original.raw := by decide +kernel

theorem all_obligations_retained : result.context.arity = original.arity ∧ result.context.arity = 3 := by
  exact ⟨rfl, rfl⟩

theorem both_maps_keep_the_variables :
    List.ofFn (result.iso.hom.substitution) = ([.var 0, .var 1, .var 2] : List (Tower.Tm 3)) ∧
    List.ofFn (result.iso.inv.substitution) = ([.var 0, .var 1, .var 2] : List (Tower.Tm 3)) := by constructor <;> rfl'

def equationType := proofType.reindex (projectionHom values proofType)
def left : Term original equationType := ⟨.var 0, .var 0⟩
def right : Term original equationType := ⟨.refl (.var 1), .reflIntro (.var 1)⟩
def problem : EquationStore (TotalTerm original) :=
  [(⟨_, left⟩, ⟨_, right⟩), (⟨_, left⟩, ⟨_, right⟩)]
def prepared := result.update problem

theorem equations_keep_order_and_multiplicity :
    prepared.remaining.map (fun equation => (equation.1.2.code, equation.2.2.code)) =
      ([ (.var 0, .refl (.var 1)), (.var 0, .refl (.var 1)) ] : List (Tower.Tm 3 × Tower.Tm 3)) := by rfl'

theorem every_future_solution_preserved (point : Context Tower.rules) :
    (∃ solution : point ⟶ original, (frames setting.levels).Models solution problem) ↔
      ∃ residual : point ⟶ prepared.target, (frames setting.levels).Models residual prepared.remaining :=
  prepared.fixed_point_solutions_iff point

theorem closed_solutions_preserved_separately :
    (∃ solution : empty Tower.rules ⟶ original, (frames setting.levels).Models solution problem) ↔
      ∃ residual : empty Tower.rules ⟶ prepared.target, (frames setting.levels).Models residual prepared.remaining :=
  every_future_solution_preserved (empty Tower.rules)

theorem insufficient_budget_unfinished : run 1 = none := by rfl'

theorem type_dependencies_still_block_selection :
    ContextualDependentNormalSelection.select (S := setting)
      TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentNormalCheckingTower.head_typing_unique TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed
      (ContextualDependentScopeConsequence.root_reflection ContextualDependentNormalSupport.Controls.rigid_constants)
      result.raw result.formed result.normal (fun index => decide (index.val = 0)) = none := by rfl'

theorem normalized_context_enters_dependency_selection :
    (ContextualDependentNormalSelection.select (S := setting)
      TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentNormalCheckingTower.head_typing_unique TowerModel.complete
      ContextualDependentInversion.Controls.declarations_formed
      (ContextualDependentScopeConsequence.root_reflection ContextualDependentNormalSupport.Controls.rigid_constants)
      result.raw result.formed result.normal (fun index => decide (index.val ≠ 0))).map
        (fun selected => selected.source) = some ContextualDependentInversion.Controls.small := by rfl'

theorem general_formed_context_has_sufficient_budget (Γ : Context Tower.rules) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      (normalize (S := setting) (fun _ => none) (fun _ _ _ impossible => impossible.elim)
        TowerModel.facts TowerModel.roots TowerModel.heads larger Γ.raw Γ.formed).isSome = true :=
  ContextualDependentContextNormalizationTower.context_eventually_normalizes (fun _ => (0 : Nat)) Γ

end ContextualDependentContextNormalization.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
