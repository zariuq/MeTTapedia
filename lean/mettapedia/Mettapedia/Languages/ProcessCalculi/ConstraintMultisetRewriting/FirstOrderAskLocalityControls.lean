import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderAskLocality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeupControls

/-!
# An unrelated binding preserves a shared-row absence verdict

The query is closed, but its observed row contains a shared variable. A tell
about another variable preserves the verdict; a tell about the row's variable
changes it. These controls use the original first-order action and occurrence
checks, rather than a separate term syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderAskLocality.Controls

open Mettapedia.Logic.LP
open EquationWakeupControls (signature A f x zeroTerm oneTerm label before after pending pendingSelection)

def component : Set Nat := {0}
def unrelated : EquationStore (Term signature) := [(.var 1, .const 2)]
def observation (assignment : Subst signature) : Prop :=
  (Check.absent (f zeroTerm)).Holds A assignment label before.present

theorem absence_reads_the_row_component : ReadsOnly component observation := by
  apply absent_reads_query_and_rows component label before.present (f zeroTerm)
  · intro name member
    simp [f, ConstraintMultisetRewriting.Controls.f, zeroTerm, Term.freeVars] at member
  · intro occurrence present name member
    have atZero : occurrence = 0 := by simpa [before] using present
    subst occurrence
    have same : name = 0 := by
      simpa [label, f, ConstraintMultisetRewriting.Controls.f, x, Term.freeVars] using member
    subst name
    simp [component]

theorem empty_store_is_closed : Closed component ([] : EquationStore (Term signature)) := by
  intro equation member
  cases member

theorem unrelated_avoids_component : Avoids component unrelated := by
  intro equation member name inSupport
  have same : equation = (.var 1, .const 2) := by simpa [unrelated] using member
  subst equation
  have atOne : name = 1 := by simpa [equationSupport, Term.freeVars] using inSupport
  subst name
  simp [component]

theorem unrelated_is_consistent : A.Consistent ([] ++ unrelated) := by
  refine ⟨Subst.single 1 (.const 2), ?_⟩
  intro equation member
  have same : equation = (.var 1, .const 2) := by simpa [unrelated] using member
  subst equation
  rfl

theorem unrelated_tell_keeps_both_verdicts :
    (A.Entails unrelated observation ↔ A.Entails [] observation) ∧
      (A.Entails unrelated (fun assignment => ¬ observation assignment) ↔
        A.Entails [] (fun assignment => ¬ observation assignment)) :=
  verdicts_local component [] unrelated empty_store_is_closed unrelated_avoids_component
    unrelated_is_consistent observation absence_reads_the_row_component

theorem query_is_closed : (f zeroTerm).freeVars = ∅ := by
  simp [f, ConstraintMultisetRewriting.Controls.f, zeroTerm, Term.freeVars]

theorem query_support_alone_is_insufficient : ¬ ReadsOnly (∅ : Set Nat) observation := by
  intro reads
  have oneHolds : observation ConstraintMultisetRewriting.Controls.one := by
    apply EquationWakeupControls.pending_can_fire_after.checks (.absent (f zeroTerm)) (by simp [pending])
    intro equation member
    have same : equation = (x, oneTerm) := by
      simpa [Selection.problem, Selection.equations, Selection.result, pendingSelection, pending,
        after, EquationWakeupControls.tellSelection, EquationWakeupControls.tell, before] using member
    subst equation
    rfl
  have zeroHolds : observation ConstraintMultisetRewriting.Controls.zero :=
    (reads ConstraintMultisetRewriting.Controls.zero ConstraintMultisetRewriting.Controls.one
      (fun name member => False.elim member)).mpr oneHolds
  exact zeroHolds 0 (by simp [before]) rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderAskLocality.Controls
