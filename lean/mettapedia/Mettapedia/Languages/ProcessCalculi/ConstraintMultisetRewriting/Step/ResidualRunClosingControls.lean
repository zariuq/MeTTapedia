import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResidualRunExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulFirstOrder

/-!
# Four admissions do not supply a closing isomorphism

The existing transport that drops tells keeps both orders admissible but
changes their resulting solution sets. It cannot supply the closing operation
needed by native run exchange. Admission and closure are separate conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ResidualRunClosingControls

open AnnotatedRuns
open ConstraintMultisetRewriting.Controls (A)
open AnnotatedRuns.Controls (label)
open AnnotatedRuns.RoundControls (tellOne tellTwo empty)
open AnnotatedRuns.LawfulControls (idle both tellOne_valid tellTwo_valid noTells_not_independent)

theorem idle_after_first : idle.Valid A label (tellOne.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨both, ?_⟩, by simp [idle]⟩,
    by simp [idle]⟩
  intro equation member
  have same : equation = (.var 0, .const 1) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result,
      empty, tellOne, idle] using member
  subst same
  rfl

theorem idle_after_second : idle.Valid A label (tellTwo.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨both, ?_⟩, by simp [idle]⟩,
    by simp [idle]⟩
  intro equation member
  have same : equation = (.var 1, .const 2) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result,
      empty, tellTwo, idle] using member
  subst same
  rfl

abbrev T := noTells A label
abbrev P := (firstOrder A label).toStep

def crossing : T.Crossing (.cons tellOne tellOne_valid (.nil _)) tellTwo tellTwo_valid :=
  .cons idle_after_second idle_after_first (.nil _ _)

theorem not_closes : ¬T.Closes := by
  intro closes
  exact noTells_not_independent ⟨tellOne_valid, tellTwo_valid, idle_after_first, idle_after_second,
    closes tellOne_valid tellTwo_valid idle_after_first idle_after_second⟩

theorem no_closing_operation : IsEmpty T.Closing :=
  ⟨fun close => not_closes (fun first second afterFirst afterSecond =>
    ⟨close first second afterFirst afterSecond⟩)⟩

theorem crossing_admissions_do_not_imply_interchange :
    Nonempty (T.Crossing (.cons tellOne tellOne_valid (.nil _)) tellTwo tellTwo_valid) ∧
      ¬T.Independent empty tellOne tellTwo :=
  ⟨⟨crossing⟩, noTells_not_independent⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ResidualRunClosingControls
