import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralOlder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralControls

/-!
# Controls for the older round

At budget 16 and eight rounds:

| Store | General solver | Older solver |
|---|---|---|
| `λ x y. F x y ≐ λ x y. F y x` over `A, F, B : U0` | suspended | commit |
| that equation, then `λ x y. F x x ≐ λ x y. x`, over `A, F, B` | suspended | refuted |
| `λ x y. F x y ≐ λ x y. F y x` over `A, F, b : F A A` | suspended | suspended |

In the first two, `F : U0 → U0 → U0` is older than `B`, which does not mention it: rotation makes `F` the newest, and
general intersection prunes it to a constant. In the third, the later declaration `b : F A A` mentions `F`, rotation
fails, and the store stays suspended. By hand it is in the fragment and solvable (`F := λ x y. A`, keeping `b`); those
two facts are not checked here. It marks, at this budget, the intersection row that remains: pruning a metavariable
that a later declaration mentions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral.OlderControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.Controls

/-- The older solver of the tower controls, as a fuel-indexed family. -/
noncomputable def olderTower : ContextualDependentDecisiveDriver.Family setting.levels :=
  olderFamily (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat)))

/-- The older solver at budget 16. -/
noncomputable def olderOnly : Solver setting.levels := olderTower.solver 16

/-! ## An older metavariable -/

/-- `A : U0, F : U0 → U0 → U0, B : U0`. -/
def universeAfter : TypeOver withBinary := formIn withBinary (.head (.sort Tower.zero)) (by decide +kernel)

abbrev withAfter := extend withBinary universeAfter

def binaryAfter : TypeOver withAfter :=
  formIn withAfter (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
    (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. F y x`, with `B` declared after `F`. -/
def olderStore : EquationStore (TotalTerm withAfter) :=
  [(termIn withAfter binaryAfter (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn withAfter binaryAfter (.lam (.lam (.app (.app (.var 3) (.var 0)) (.var 1)))) (by decide +kernel))]

theorem older_general_suspended : (run generalOnly olderStore 8).readout = .suspended := by decide +kernel

/-- **The older solver commits on the intersection at an older metavariable.** -/
theorem older_committed : (run olderOnly olderStore 8).readout = .commit := by decide +kernel

/-- That equation, then `λ x y. F x x ≐ λ x y. x`. -/
def olderDiagonalStore : EquationStore (TotalTerm withAfter) :=
  [(termIn withAfter binaryAfter (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn withAfter binaryAfter (.lam (.lam (.app (.app (.var 3) (.var 0)) (.var 1)))) (by decide +kernel)),
   (termIn withAfter binaryAfter (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 1)))) (by decide +kernel),
    termIn withAfter binaryAfter (.lam (.lam (.var 1))) (by decide +kernel))]

theorem olderDiagonal_general_suspended : (run generalOnly olderDiagonalStore 8).readout = .suspended := by
  decide +kernel

/-- **The older solver refutes it.** -/
theorem olderDiagonal_refuted : (run olderOnly olderDiagonalStore 8).readout = .refuted := by decide +kernel

theorem olderDiagonal_unsolvable : ¬ (frames setting.levels).Solvable olderDiagonalStore :=
  Outcome.readout_eq_refuted olderDiagonal_refuted

/-! ## A later declaration that mentions the metavariable -/

/-- `A : U0, F : U0 → U0 → U0, b : F A A`. -/
def dependentAfter : TypeOver withBinary :=
  formIn withBinary (.app (.app (.var 0) (.var 1)) (.var 1)) (by decide +kernel)

abbrev withDependentAfter := extend withBinary dependentAfter

def binaryDependent : TypeOver withDependentAfter :=
  formIn withDependentAfter (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))
    (by decide +kernel)

/-- `λ x y. F x y ≐ λ x y. F y x`, with `b : F A A` declared after `F`. -/
def mentionedStore : EquationStore (TotalTerm withDependentAfter) :=
  [(termIn withDependentAfter binaryDependent (.lam (.lam (.app (.app (.var 3) (.var 1)) (.var 0)))) (by decide +kernel),
    termIn withDependentAfter binaryDependent (.lam (.lam (.app (.app (.var 3) (.var 0)) (.var 1)))) (by decide +kernel))]

/-- **The open row**: a later declaration mentions `F`, and the store stays suspended at this budget. -/
theorem mentioned_suspended : (run olderOnly mentionedStore 8).readout = .suspended := by decide +kernel

end ContextualDependentIntersectionGeneral.OlderControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
