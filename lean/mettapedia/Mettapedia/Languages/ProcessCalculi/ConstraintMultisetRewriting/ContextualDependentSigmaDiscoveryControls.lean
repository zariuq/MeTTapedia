import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSigmaDiscovery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSigmaControls

/-!
# The projection solver discovers its pair decomposition

The source whole type alone drives shape discovery. The computed rule
reconstructs the dependent codomain, then composes with the existing
type-variable solver. Zero fuel and a function annotation retain the input.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSigma.DiscoveryControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := Controls.setting

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

def run (fuel : Nat) {Γ : Context Tower.rules} (whole : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ whole))) :=
  splitNewest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
    ConversionControls.reducer fuel whole problem

theorem actual_discovery :
    discover (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
      ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
      ConversionControls.reducer 16 Controls.shape.whole = some ⟨Controls.shape, rfl⟩ := by rfl'

theorem actual_split : run 16 Controls.shape.whole Controls.problem = Controls.splitUpdate := by rfl'

def computed : Update setting.levels Controls.problem :=
  (run 16 Controls.shape.whole Controls.problem).then
    (actual_split.symm ▸ Controls.solveSplit)

theorem actual_projection_finishes : computed.remaining = [] := by decide +kernel

theorem actual_projection_principal :
    (frames setting.levels).Principal Controls.problem computed.answer :=
  computed.completed actual_projection_finishes

theorem zero_budget_retains_input :
    (⟨(run 0 Controls.shape.whole Controls.problem).target,
      (run 0 Controls.shape.whole Controls.problem).remaining⟩ :
        (Δ : Context Tower.rules) × EquationStore (TotalTerm Δ)) =
      ⟨Controls.shape.packed, Controls.problem⟩ := by rfl'

theorem function_annotation_retains_input
    (problem : EquationStore (TotalTerm Examples.TypedContextualControls.functionContext)) :
    (⟨(run 16 Examples.TypedContextualControls.functionType problem).target,
      (run 16 Examples.TypedContextualControls.functionType problem).remaining⟩ :
        (Δ : Context Tower.rules) × EquationStore (TotalTerm Δ)) =
      ⟨Examples.TypedContextualControls.functionContext, problem⟩ := by rfl'

end ContextualDependentSigma.DiscoveryControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
