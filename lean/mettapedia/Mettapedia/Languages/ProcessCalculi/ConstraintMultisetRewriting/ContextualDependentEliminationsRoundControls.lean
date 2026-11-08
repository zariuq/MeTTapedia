import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEliminationsRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringInPlaceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusSolvable

/-!
# Controls for the eliminations round

R99's two unread census rows with a rigid base type, over `A X : U0`, run at budget 16 and eight rounds:

| Store | Placed solver | Eliminations solver |
|---|---|---|
| `λ g. fst (fst (g X)) ≐ λ g. fst (fst (g A))` | suspended | commit |
| `λ g. fst (g X) A ≐ λ g. fst (g A) A` | suspended | commit |
| `λ g. fst (g A) A ≐ λ g. fst (g A) (Π A A)` | suspended | refuted |

Both committed stores are solvable (R99's `nested_solvable`, `applied_solvable`), and the refuted one is unsolvable:
its decomposition has the piece `A ≐ Π A A` at `U0`, a clash of heads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEliminations.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls

/-- The eliminations solver of the tower controls, as a fuel-indexed family. -/
noncomputable def elimsTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  elimsFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The eliminations solver at budget 16. -/
noncomputable def elimsOnly : Solver setting.levels := elimsTower.solver 16

/-! ## Nested projections -/

theorem nested_placed_suspended :
    (run placedOnly ContextualDependentCensus.Controls.nestedStore 8).readout = .suspended := by decide +kernel

/-- **The eliminations solver commits on nested projections.** -/
theorem nested_committed :
    (run elimsOnly ContextualDependentCensus.Controls.nestedStore 8).readout = .commit := by decide +kernel

/-! ## An applied projection -/

theorem applied_placed_suspended :
    (run placedOnly ContextualDependentCensus.Controls.appliedStore 8).readout = .suspended := by decide +kernel

/-- **The eliminations solver commits on an applied projection.** -/
theorem applied_committed :
    (run elimsOnly ContextualDependentCensus.Controls.appliedStore 8).readout = .commit := by decide +kernel

/-! ## A refutation through the pieces -/

/-- `λ g. fst (g A) A ≐ λ g. fst (g A) (Π A A)`. -/
def clashStore : EquationStore (TotalTerm ContextualDependentInversion.Controls.withExtra) :=
  [(termIn ContextualDependentInversion.Controls.withExtra ContextualDependentCensus.Controls.appliedGenerator
      (.lam (.app (.fst (.app (.var 0) (.var 2))) (.var 2))) (by decide +kernel),
    termIn ContextualDependentInversion.Controls.withExtra ContextualDependentCensus.Controls.appliedGenerator
      (.lam (.app (.fst (.app (.var 0) (.var 2))) (.pi (.var 2) (.var 3)))) (by decide +kernel))]

theorem clash_placed_suspended : (run placedOnly clashStore 8).readout = .suspended := by decide +kernel

/-- **The eliminations solver refutes it**: the piece `A ≐ Π A A` clashes. -/
theorem clash_refuted : (run elimsOnly clashStore 8).readout = .refuted := by decide +kernel

/-! ## The row that stays unread -/

/-- **A spine at a flexible base type stays suspended**: `λ g. g X ≐ λ g. g A` at `(U0 → A) → A` has the base type
`A`, an outer declaration, which a solution may instantiate with a Π or Σ type; the reader requires a rigid base. -/
theorem flexibleBase_elims_suspended :
    (run elimsOnly ContextualDependentCensus.Controls.flexibleBaseStore 8).readout = .suspended := by decide +kernel

/-- **The four unread flexible rows stay stuck under the last family**: the store with a declaration between two
metavariables, the intersection, the pruning under rigid structure, and the cumulative argument. -/
theorem flexible_rows_elims_stuck :
    isStuck (run elimsOnly farStore 8) = true ∧ isStuck (run elimsOnly intersectionStore 8) = true ∧
      isStuck (run elimsOnly prunableStore 8) = true ∧ isStuck (run elimsOnly cumulativeStore 8) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The two rows are in the fragment, solvable, suspended by the placed solver, and committed by the eliminations
solver.** -/
theorem rows_read :
    (InFragmentStore ContextualDependentCensus.Controls.nestedStore ∧
        (frames setting.levels).Solvable ContextualDependentCensus.Controls.nestedStore ∧
        (run placedOnly ContextualDependentCensus.Controls.nestedStore 8).readout = .suspended ∧
        (run elimsOnly ContextualDependentCensus.Controls.nestedStore 8).readout = .commit) ∧
      (InFragmentStore ContextualDependentCensus.Controls.appliedStore ∧
        (frames setting.levels).Solvable ContextualDependentCensus.Controls.appliedStore ∧
        (run placedOnly ContextualDependentCensus.Controls.appliedStore 8).readout = .suspended ∧
        (run elimsOnly ContextualDependentCensus.Controls.appliedStore 8).readout = .commit) :=
  ⟨⟨ContextualDependentCensus.Controls.nested_in_fragment, ContextualDependentCensus.Controls.nested_solvable,
      nested_placed_suspended, nested_committed⟩,
    ⟨ContextualDependentCensus.Controls.applied_in_fragment, ContextualDependentCensus.Controls.applied_solvable,
      applied_placed_suspended, applied_committed⟩⟩

end ContextualDependentEliminations.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
