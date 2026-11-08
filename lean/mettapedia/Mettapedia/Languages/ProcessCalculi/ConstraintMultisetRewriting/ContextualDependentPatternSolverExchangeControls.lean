import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolverControls

/-!
# Exchange so that the right metavariable is solved

The context is `T : U0, F : (a b : T) → U0, H : T → U0`, where `H` is the newest metavariable and
does not mention `F`. The store `λ x y. F y x ≐ λ x y. Id T x y` constrains only `F`. The full
solver exchanges `H` and `F` and solves `F` with a principal answer; without the exchange the
pattern rule finds no pattern for the newest metavariable and the run is stuck.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternSolver.ExchangeControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls

/-- `T, F, H`. -/
abbrev threeMetas := extend ContextualDependentPrune.Controls.outerContext ContextualDependentPrune.Controls.prunedType

/-- The crossed equation for `F`, read in the context that also declares `H`. -/
def olderStore : EquationStore (TotalTerm threeMetas) :=
  (frames setting.levels).applyStore
    (projectionHom ContextualDependentPrune.Controls.outerContext ContextualDependentPrune.Controls.prunedType)
    crossedStore

theorem older_store_length : olderStore.length = 1 := by decide +kernel

theorem exchanged_and_solved : (run full olderStore 2).readout = .commit := by decide +kernel

theorem exchanged_principal :
    ∃ state finished, run full olderStore 2 = .solved state finished ∧
      (frames setting.levels).Principal olderStore state.answer := by
  obtain ⟨state, finished, solved⟩ := ContextualDependentWorklist.Controls.solved_of_commit exchanged_and_solved
  exact ⟨state, finished, solved, drive_solved_principal full solved⟩

theorem without_exchange_stuck : (run patternOnly olderStore 4).readout = .suspended := by decide +kernel

end ContextualDependentPatternSolver.ExchangeControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
