import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Cells
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulFirstOrder

/-!
# Cells of the one-frame instance: the hollow cube

* **The cube law holds for every closing choice** (`firstOrder_cubeLaw`): a residual is the firing
  itself, and transport moves nothing.
* **A jointly run word is executable** (`jointly_executable`).
* **The review's control C3** (`CellControls.hollow_cube`): the tells `X = Y`, `X = 1` and `Y = 2` are
  pairwise independent, so each pair is a 2-cell, and the three form no 3-cell: the three squares
  exist and the cube is hollow.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Transport)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
section Laws

variable (A : SubstitutionAction T S) (label : O → T)

/-- **The cube law of the one-frame instance**, for every choice of closing isomorphisms. -/
theorem firstOrder_cubeLaw (close : (firstOrderTransport A label).Closing) :
    (firstOrderTransport A label).CubeLaw close :=
  fun _ _ _ _ _ => rfl

/-- **A jointly run word of the one-frame instance is executable.** -/
theorem jointly_executable : ∀ {C : Configuration T O} {w : List (Firing T S O)},
    (firstOrderTransport A label).Jointly C w → w ≠ [] → Executable A label C w
  | _, [], _, nonempty => absurd rfl nonempty
  | _, f :: rest, run, _ => by
      obtain ⟨admitted, later⟩ := Transport.Jointly.uncons run
      have same : rest.map ((firstOrderTransport A label).residual f admitted) = rest := List.map_id rest
      rw [same] at later
      refine ⟨admitted, ?_⟩
      by_cases empty : rest = []
      · subst empty
        exact admitted.firing.consistent
      · exact jointly_executable later empty

end Laws

namespace CellControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run ones)
open RoundControls (tellSame tellOne tellTwo empty)
open LawfulControls (tellOne_valid tellTwo_valid tellTwo_valid_after tellOne_valid_after)

/-- Every variable to `2`. -/
def twos : Subst signature := fun _ => .const 2

theorem tellSame_valid : tellSame.Valid A label empty := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, by simp [tellSame]⟩,
    by simp [tellSame]⟩
  intro equation member
  have same : equation = (.var 0, .var 1) := by
    simpa [Selection.problem, Selection.equations, empty, tellSame] using member
  subst same
  rfl

theorem tellSame_after_one : tellSame.Valid A label (tellOne.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, by simp [tellSame]⟩,
    by simp [tellSame]⟩
  intro equation member
  have cases : equation = (.var 0, .const 1) ∨ equation = (.var 0, .var 1) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, tellOne,
      tellSame] using member
  rcases cases with rfl | rfl <;> rfl

theorem tellOne_after_same : tellOne.Valid A label (tellSame.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, by simp [tellOne]⟩,
    by simp [tellOne]⟩
  intro equation member
  have cases : equation = (.var 0, .var 1) ∨ equation = (.var 0, .const 1) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, tellOne,
      tellSame] using member
  rcases cases with rfl | rfl <;> rfl

theorem tellSame_after_two : tellSame.Valid A label (tellTwo.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨twos, ?_⟩, by simp [tellSame]⟩,
    by simp [tellSame]⟩
  intro equation member
  have cases : equation = (.var 1, .const 2) ∨ equation = (.var 0, .var 1) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, tellTwo,
      tellSame] using member
  rcases cases with rfl | rfl <;> rfl

theorem tellTwo_after_same : tellTwo.Valid A label (tellSame.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨twos, ?_⟩, by simp [tellTwo]⟩,
    by simp [tellTwo]⟩
  intro equation member
  have cases : equation = (.var 0, .var 1) ∨ equation = (.var 1, .const 2) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, tellTwo,
      tellSame] using member
  rcases cases with rfl | rfl <;> rfl

/-- `X = Y` and `X = 1` are independent. -/
theorem same_one : (firstOrderTransport A label).Independent empty tellSame tellOne :=
  (firstOrder_independent_iff A label).mpr
    ⟨tellSame_valid, tellOne_valid, tellOne_after_same, tellSame_after_one⟩

/-- `X = Y` and `Y = 2` are independent. -/
theorem same_two : (firstOrderTransport A label).Independent empty tellSame tellTwo :=
  (firstOrder_independent_iff A label).mpr
    ⟨tellSame_valid, tellTwo_valid, tellTwo_after_same, tellSame_after_two⟩

/-- `X = 1` and `Y = 2` are independent. -/
theorem one_two : (firstOrderTransport A label).Independent empty tellOne tellTwo :=
  LawfulControls.lawful_independent

/-- **The three tells form no 3-cell.** -/
theorem no_three_cell : ¬ (firstOrderTransport A label).Cell empty [tellSame, tellOne, tellTwo] :=
  fun cell => RoundControls.pairwise_consistent_not_joint [tellSame, tellOne, tellTwo] (List.Perm.refl _)
    (jointly_executable A label cell.jointly (List.cons_ne_nil _ _))

/-- **The review's control C3: a hollow cube.** Every pair of the three tells is independent, so
each pair is a 2-cell, and the three form no 3-cell. -/
theorem hollow_cube :
    ((firstOrderTransport A label).Independent empty tellSame tellOne ∧
        (firstOrderTransport A label).Cell empty [tellSame, tellOne]) ∧
      ((firstOrderTransport A label).Independent empty tellSame tellTwo ∧
        (firstOrderTransport A label).Cell empty [tellSame, tellTwo]) ∧
      ((firstOrderTransport A label).Independent empty tellOne tellTwo ∧
        (firstOrderTransport A label).Cell empty [tellOne, tellTwo]) ∧
      ¬ (firstOrderTransport A label).Cell empty [tellSame, tellOne, tellTwo] :=
  ⟨⟨same_one, same_one.cell⟩, ⟨same_two, same_two.cell⟩, ⟨one_two, one_two.cell⟩, no_three_cell⟩

end CellControls

#print axioms firstOrder_cubeLaw
#print axioms jointly_executable
#print axioms CellControls.same_one
#print axioms CellControls.same_two
#print axioms CellControls.no_three_cell
#print axioms CellControls.hollow_cube

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
