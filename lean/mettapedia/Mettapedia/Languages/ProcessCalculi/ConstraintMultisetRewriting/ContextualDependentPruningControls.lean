import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInversionControls

/-!
# Computed dependent telescope pruning

The selection algorithm itself constructs the smaller context and its typed
inclusion. It removes the unused middle declaration, retains the dependency
of x on A, and fails honestly when asked to keep x but drop A.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPruning.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

abbrev setting := ContextualDependentInversion.Controls.setting

instance : DecidableRel setting.R.headEq := fun left right =>
  LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right =>
  LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def requested (index : Fin 3) : Bool := decide (index.val ≠ 1)

def run (fuel : Nat) (mask : Fin 3 → Bool) :=
  select (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer fuel
    ContextualDependentInversion.Controls.large.raw ContextualDependentInversion.Controls.large.formed mask

theorem actual_context_constructed :
    (run 16 requested).map (fun result => result.source) =
      some ContextualDependentInversion.Controls.small := by rfl'

theorem actual_variable_map :
    (run 16 requested).map (fun result =>
      List.ofFn (fun index => (result.inclusion.forward index).val)) = some [0, 2] := by
  decide +kernel

/-- The algorithm carries the proof of exactly which declarations survived;
it cannot satisfy this by returning an arbitrary smaller context. -/
theorem retained_image_exact :
    ∃ result, run 16 requested = some result ∧
      ∀ target, (∃ index, result.inclusion.forward index = target) ↔ target.val ≠ 1 := by
  obtain ⟨result, selected, _⟩ := Option.map_eq_some_iff.mp actual_context_constructed
  refine ⟨result, selected, fun target => ?_⟩
  simpa only [requested, decide_eq_true_eq] using result.image target

theorem dropping_the_required_type_fails :
    run 16 (fun index => decide (index.val = 0)) = none := by rfl'

theorem retaining_everything_preserves_context :
    (run 16 (fun _ => true)).map (fun result => result.source) =
      some ContextualDependentInversion.Controls.large := by rfl'

theorem no_retained_variables_needs_no_inhabitants :
    (run 0 (fun _ => false)).map (fun result => result.source) = some (empty Tower.rules) := by rfl'

theorem exhausted_type_check_is_not_a_refutation : run 0 requested = none := by rfl'

end ContextualDependentPruning.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
