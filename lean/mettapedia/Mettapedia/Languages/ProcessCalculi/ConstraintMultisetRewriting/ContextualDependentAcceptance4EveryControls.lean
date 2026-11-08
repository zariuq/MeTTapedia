import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4EveryClosure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4Gap

/-!
# Controls for the every-rule family

The tower's every-rule family commits on the pattern equation behind a dead binder that the dead-binder family leaves
suspended (`deadPattern_every_committed`, against `ContextualDependentIntersectionGeneral.DeadControls.deadPattern_gap`):
read without `p`, the equation strengthens past `b` and the in-place pattern rule solves `F := λ x y. x`. It drops two
dead binders one level each (`twoDead_every_committed`), commits on R119's intersection behind a dead binder
(`annotated_every_committed`), and refutes R119's unsolvable diagonal store (`annotatedDiagonal_every_refuted`). A dead
binder under a live binder is not read (`ContextualDependentAcceptance4.middle_gap`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance4

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentIntersectionGeneral.OlderControls
open ContextualDependentIntersectionGeneral.AnywhereControls ContextualDependentIntersectionGeneral.InPlaceControls
open ContextualDependentIntersectionGeneral.DeadControls

/-- **The every-rule family commits on the pattern equation behind a dead binder**, at budget 16. -/
theorem deadPattern_every_committed : (run (everyTower.solver 16) deadPatternStore 8).readout = .commit := by
  decide +kernel

/-- **And on R119's intersection behind a dead binder**, as the dead-binder family does. -/
theorem annotated_every_committed : (run (everyTower.solver 16) annotatedStore 8).readout = .commit := by
  decide +kernel

/-- `Π (p q : Id (F A A) b b). Π (x y : U0). U0`: two dead binders. -/
def twoDeadType : TypeOver withDependentAfter :=
  formIn withDependentAfter (.pi (.id (.app (.app (.var 1) (.var 2)) (.var 2)) (.var 0) (.var 0))
    (.pi (.id (.app (.app (.var 2) (.var 3)) (.var 3)) (.var 1) (.var 1))
      (.pi (.head (.sort Tower.zero)) (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))))))
    (by decide +kernel)

/-- `λ p q x y. F x y ≐ λ p q x y. x`. -/
def twoDeadStore : EquationStore (TotalTerm withDependentAfter) :=
  [(termIn withDependentAfter twoDeadType (.lam (.lam (.lam (.lam (.app (.app (.var 5) (.var 1)) (.var 0))))))
      (by decide +kernel),
    termIn withDependentAfter twoDeadType (.lam (.lam (.lam (.lam (.var 1))))) (by decide +kernel))]

/-- **Two dead binders in front of a pattern equation**: the family drops both, one level each. -/
theorem twoDead_every_committed : (run (everyTower.solver 16) twoDeadStore 8).readout = .commit := by
  decide +kernel

/-- **A refutation behind a dead binder is kept**: R119's unsolvable diagonal store is refuted. -/
theorem annotatedDiagonal_every_refuted :
    (run (everyTower.solver 16) annotatedDiagonalStore 8).readout = .refuted := by
  decide +kernel

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
