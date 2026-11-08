import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TransformQualification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecksControls

/-!
# The minimized absence example on the one-frame step

The absence test, as runs of the one-frame instance `AnnotatedRuns.firstOrder` of the interface.
Row `0` is `cancel(0)`; rows `1` and `2` are requests. The firing `ask` takes request `1` under the
guard "no row `cancel(u)` is present" and makes row `3`; `bind v` takes request `2` and tells
`u = v`. The configurations and selections are those of `FirstOrderChecks.Controls.OpenAbsence`.

* **Unknown `u`.** `ask_refused_unknown`: with `u` unknown, `cancel(0)` might be `cancel(u)`, so the
  guard is not asked at every solution and `ask` is refused.
* **Later `u = 1` and `u = 0`.** `ask_admitted_after_one`, `ask_refused_after_zero`; the run
  `bind 1; ask` exists (`later_equation_run`), and no run starts with `ask`.
* **Relevant insertion.** After `u = 1`, inserting `cancel(1)` refuses `ask`
  (`relevant_insertion_refuses`).
* **Unrelated update.** After `u = 1`, inserting `cancel(2)` keeps `ask` admitted
  (`unrelated_insertion_keeps`).
* **Absence as a query.** `ask_as_query_refused_unknown`, `ask_as_query_admitted_after_one`: the same
  firing with its guard moved into an empty-census predicate query
  (`TransformQualification.admits_absent_check_iff_query`) has the same verdicts.

Incomplete scans are a property of an executable check, not of the step, whose guard quantifies over
every present occurrence; the scan is sound exactly under coverage
(`Check.entails_absent_iff_of_covered`), and the partial scan of this example lacks it
(`FirstOrderChecks.Controls.OpenAbsence.the_partial_scan_lacks_coverage`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification.AbsenceExample

open Mettapedia.Logic.LP
open AnnotatedRuns (Firing firstOrder)
open ConstraintMultisetRewriting.Controls (signature f one zero)
open FirstOrderChecks.Controls.OpenAbsence

/-- The one-frame step over the example's labels. -/
abbrev P := firstOrder (S := Subst signature) (FirstOrder.action signature) rows

/-- Take request `1` when no `cancel(u)` is present; make row `3`. -/
def ask : Firing (Term signature) (Subst signature) Nat := ⟨askRule, [], askSelection⟩

/-- Take request `2` and tell `u = value`. -/
def bind (value : Nat) : Firing (Term signature) (Subst signature) Nat :=
  ⟨bindRule value, [], bindSelection⟩

/-- Make the row `o`, whose label is `rows o`. -/
def insert (o : Nat) : Firing (Term signature) (Subst signature) Nat :=
  ⟨⟨[], [], [], [], [rows o]⟩, [], ⟨[], [], [o]⟩⟩

theorem ask_refused_unknown : ¬ P.Admits (s := initial) ask :=
  fun admitted => the_unbound_guard_does_not_admit_the_step admitted.firing

theorem bind_admitted (value : Nat) : P.Admits (s := initial) (bind value) :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr (either_binding_step_is_available value)

theorem ask_admitted_after_one : P.Admits (s := afterBind 1) ask :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr binding_to_one_enables_the_step

theorem ask_refused_after_zero : ¬ P.Admits (s := afterBind 0) ask :=
  fun admitted => binding_to_zero_refuses_the_step admitted.firing

/-- **A later equation enables the firing**: `bind 1; ask` is a run of the step, while `ask` is
refused at the start and after `bind 0`. -/
theorem later_equation_run :
    ∃ r : P.Run initial, r.word.map Sigma.snd = [bind 1, ask] ∧
      ¬ P.Admits (s := initial) ask ∧ ¬ P.Admits (s := P.result (bind 0) (bind_admitted 0)) ask :=
  ⟨.cons (bind 1) (bind_admitted 1) (.cons ask ask_admitted_after_one (.nil _)), rfl,
    ask_refused_unknown, ask_refused_after_zero⟩

/-! ## Insertions after `u = 1` -/

theorem insert_models (o : Nat) :
    (FirstOrder.action signature).Models one
      ((insert o).selection.problem rows (insert o).rule (afterBind 1)) := by
  intro equation member
  simp [afterBind, Selection.result, Selection.problem, Selection.equations, insert,
    bindSelection, bindRule, initial, rows] at member
  rcases member with rfl | rfl <;> rfl

theorem insert_admitted_four : P.Admits (s := afterBind 1) (insert 4) :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨one, insert_models 4⟩, by simp [insert]⟩

theorem insert_admitted_five : P.Admits (s := afterBind 1) (insert 5) :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨one, insert_models 5⟩, by simp [insert]⟩

/-- The configuration after `u = 1` and the insertion of row `o`. -/
def inserted (o : Nat) : Configuration (Term signature) Nat :=
  (insert o).result rows (afterBind 1)

/-- **A relevant insertion refuses the firing**: `cancel(1)` arrives after `u = 1`. -/
theorem relevant_insertion_refuses : ¬ P.Admits (s := inserted 4) ask := by
  intro admitted
  have absent := admitted.firing.checks (.absent query) (by simp [ask, askRule]) one (by
    intro equation member
    simp [ask, inserted, insert, afterBind, Firing.result, Selection.result, Selection.problem,
      Selection.equations, askSelection, askRule, bindSelection, bindRule, initial, rows] at member
    rcases member with rfl | rfl | rfl <;> rfl)
  exact absent 4 (by decide) rfl

/-- **An unrelated update keeps the firing admitted**: `cancel(2)` arrives after `u = 1`. -/
theorem unrelated_insertion_keeps : P.Admits (s := inserted 5) ask := by
  refine (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨one, ?_⟩, ?_⟩
  · intro equation member
    simp [ask, inserted, insert, afterBind, Firing.result, Selection.result, Selection.problem,
      Selection.equations, askSelection, askRule, bindSelection, bindRule, initial, rows] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro check member assignment model
    have only : check = Check.absent query := by simpa [ask, askRule] using member
    subst check
    have bound : assignment 0 = Term.const (σ := signature) 1 := model (.var 0, .const 1) (by
      simp [ask, inserted, insert, afterBind, Firing.result, Selection.result, Selection.problem,
        Selection.equations, askSelection, askRule, bindSelection, bindRule, initial, rows])
    intro occurrence present same
    have choices : occurrence = 0 ∨ occurrence = 1 ∨ occurrence = 5 := by
      simp [inserted, insert, afterBind, Firing.result, Selection.result,
        MeTTaCalculus.OccurrenceCommits.fire, Selection.commit, bindSelection, initial] at present
      omega
    rcases choices with rfl | rfl | rfl
    · change f (assignment 0) = f (.const 0) at same
      rw [bound] at same
      have children := eq_of_heq (Term.app.inj same).2
      have impossible := congrFun children 0
      cases impossible
    · change f (assignment 0) = Term.const (σ := signature) 10 at same
      cases same
    · change f (assignment 0) = f (.const 2) at same
      rw [bound] at same
      have children := eq_of_heq (Term.app.inj same).2
      have impossible := congrFun children 0
      cases impossible

/-- **The insertions are firings of the step**, and they separate: after `bind 1`, the run through
`insert 5` continues with `ask`, and `ask` is refused after `insert 4`. -/
theorem insertions_separate :
    (∃ r : P.Run initial, r.word.map Sigma.snd = [bind 1, insert 5, ask]) ∧
      ¬ P.Admits (s := P.result (insert 4) (insert_admitted_four)) ask :=
  ⟨⟨.cons (bind 1) (bind_admitted 1) (.cons (insert 5) (insert_admitted_five)
      (.cons ask unrelated_insertion_keeps (.nil _))), rfl⟩, relevant_insertion_refuses⟩

/-! ## The same verdicts with absence as a predicate query -/

/-- The first-order equivalence is syntactic equality, which is decidable. -/
instance decideEquivalence (a b : Term signature) : Decidable ((FirstOrder.action signature).E a b) :=
  inferInstanceAs (Decidable (a = b))

/-- The ask firing with its guard moved into an empty-census predicate query. -/
def askAsQuery : Firing (Term signature) (Subst signature) Nat :=
  ⟨{ askRule with checks := [] }, [absenceQuery (FirstOrder.action signature) query], askSelection⟩

theorem ask_iff_askAsQuery (C : Configuration (Term signature) Nat) :
    P.Admits (s := C) ask ↔ P.Admits (s := C) askAsQuery :=
  admits_absent_check_iff_query (FirstOrder.action signature) rows { askRule with checks := [] }
    query [] askSelection C

theorem ask_as_query_refused_unknown : ¬ P.Admits (s := initial) askAsQuery :=
  fun admitted => ask_refused_unknown ((ask_iff_askAsQuery initial).mpr admitted)

theorem ask_as_query_admitted_after_one : P.Admits (s := afterBind 1) askAsQuery :=
  (ask_iff_askAsQuery (afterBind 1)).mp ask_admitted_after_one

#print axioms ask_refused_unknown
#print axioms bind_admitted
#print axioms ask_admitted_after_one
#print axioms ask_refused_after_zero
#print axioms later_equation_run
#print axioms insert_admitted_four
#print axioms insert_admitted_five
#print axioms relevant_insertion_refuses
#print axioms unrelated_insertion_keeps
#print axioms insertions_separate
#print axioms ask_iff_askAsQuery
#print axioms ask_as_query_refused_unknown
#print axioms ask_as_query_admitted_after_one

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification.AbsenceExample
