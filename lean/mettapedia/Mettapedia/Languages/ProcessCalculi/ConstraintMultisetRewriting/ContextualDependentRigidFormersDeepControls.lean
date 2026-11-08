import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersDeep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersSpineControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursCheckControls

/-!
# Deep decomposition on a concrete store

Over `A X : U0`, `Π (Π A X) A ≐ Π (Π A A) A` decomposes into `Π A X ≐ Π A A` and a family twin, and
`Π A X ≐ Π A A` decomposes again into `A ≐ A` and the twin `(λ_. X : Π A U0) ≐ (λ_. A : Π A U0)`,
which the pattern rule solves by `X := A`. One decomposition is not enough: the spine solver leaves the
store suspended. The deep solver commits with a principal answer.

Every run is the actual solver in the actual driver, evaluated by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidFormers.DeepControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentWorklist
open ContextualDependentGeneralPattern ContextualDependentGeneralPattern.Controls
open ContextualDependentPatternSolver ContextualDependentPatternSolver.Controls
open ContextualDependentDecisiveFragment ContextualDependentFragment ContextualDependentFragment.Controls
open ContextualDependentOccursCheck.Controls

/-- The deep solver of the tower controls, as a fuel-indexed family. -/
abbrev deepTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  deepFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => none) DispatchControls.tower_normalizes DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The deep solver at budget 16. -/
def deepOnly : Solver setting.levels := deepTower.solver 16

theorem twisted_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.pi (.pi (.var 1) (.var 1)) (.var 2))
    (.head (.sort Tower.zero))).isSome = true := by decide +kernel

theorem straight_checked : (ExecutableChecking.check setting.R ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer 16 twoTypes.raw (.pi (.pi (.var 1) (.var 2)) (.var 2))
    (.head (.sort Tower.zero))).isSome = true := by decide +kernel

/-- `Π (Π A X) A ≐ Π (Π A A) A` over `A X : U0`. -/
def nestedDomainsStore : EquationStore (TotalTerm twoTypes) :=
  [(⟨universeAt twoTypes, checkedType _ twisted_checked⟩, ⟨universeAt twoTypes, checkedType _ straight_checked⟩)]

/-- **The deep solver commits on it.** -/
theorem nested_domains_solved : (run deepOnly nestedDomainsStore 3).readout = .commit := by decide +kernel

theorem nested_domains_principal :
    ∃ state finished, run deepOnly nestedDomainsStore 3 = .solved state finished ∧
      (frames setting.levels).Principal nestedDomainsStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit nested_domains_solved
  exact ⟨state, finished, solved, drive_solved_principal deepOnly solved⟩

/-- **One decomposition is not enough**: the spine solver leaves it suspended. -/
theorem nested_domains_spine_suspended :
    (run ContextualDependentRigidFormers.SpineControls.spineOnly nestedDomainsStore 4).readout = .suspended := by
  decide +kernel

end ContextualDependentRigidFormers.DeepControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
