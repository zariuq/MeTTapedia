import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralInPlaceRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralOlderControls

/-!
# Controls for the in-place round

Over `A : U0, F : U0 → U0 → U0, b : F A A`, at budget 16 and eight rounds:

| Store | Older solver | In-place solver |
|---|---|---|
| `λ x y. F x y ≐ λ x y. F y x` | suspended | commit |
| that equation, then `λ x y. F x x ≐ λ x y. x` | suspended | refuted |

The later declaration `b : F A A` mentions `F`, so rotation cannot move `F` to the newest position. In place, the
store is separated at `b` (neither equation mentions `b`), general intersection prunes `F` to a constant `H` on the
strengthened store, and the answer is carried past `b`, whose type becomes `H`. In the second store the other equation
becomes `λ x y. H ≐ λ x y. x`, refuted as before.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral.InPlaceControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.OlderControls

/-- The in-place solver of the tower controls, as a fuel-indexed family. -/
noncomputable def inPlaceTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  inPlaceFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The in-place solver at budget 16. -/
noncomputable def inPlaceOnly : Solver setting.levels := inPlaceTower.solver 16

/-- **The in-place solver commits on the intersection below a declaration that mentions the metavariable.** -/
theorem mentioned_committed : (run inPlaceOnly mentionedStore 8).readout = .commit := by decide +kernel

/-- That equation, then `λ x y. F x x ≐ λ x y. x`, below `b : F A A`. -/
def mentionedDiagonalStore : EquationStore (TotalTerm withDependentAfter) :=
  [(termIn withDependentAfter binaryDependent (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn withDependentAfter binaryDependent (.lam (.lam (.app (.app (.var 3) (.var 0)) (.var 1)))) (by decide +kernel)),
   (termIn withDependentAfter binaryDependent (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 1)))) (by decide +kernel),
    termIn withDependentAfter binaryDependent (.lam (.lam (.var 1))) (by decide +kernel))]

theorem mentionedDiagonal_older_suspended : (run olderOnly mentionedDiagonalStore 8).readout = .suspended := by
  decide +kernel

/-- **The in-place solver refutes it.** -/
theorem mentionedDiagonal_refuted : (run inPlaceOnly mentionedDiagonalStore 8).readout = .refuted := by decide +kernel

theorem mentionedDiagonal_unsolvable : ¬ (frames setting.levels).Solvable mentionedDiagonalStore :=
  Outcome.readout_eq_refuted mentionedDiagonal_refuted

end ContextualDependentIntersectionGeneral.InPlaceControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
