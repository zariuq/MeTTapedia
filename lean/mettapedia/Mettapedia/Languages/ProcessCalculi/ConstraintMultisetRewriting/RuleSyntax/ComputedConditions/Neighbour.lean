import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelEvaluation

/-!
# Control: two cells at one key, and the true function makes two values

The machine state of `KernelEvaluation` without any table row, with one more cell at the key of the first
operand (`twoCells`: register `11` holds `2` at identity `2` and `7` at identity `5`). The add step evaluated by
the true interpretation `addI` has two admitted firings there, reading one operand cell or the other: at
`add(2, 3) = 5` and at `add(7, 3) = 10` (`two_values_admitted`). Both rules are rules of the evaluated program
(`both_members`), and they tell the made value two different rows (`told_values_differ`).

So with the graph held by the program and the function right, the value made still depends on which rows the
rule's own patterns match. The state violates exactly one hypothesis of the machine theorems: one cell per key
(`Machine.not_invariants_of_two_cells` is the same failure on the bags of `Machine`). What is trusted is the
function together with the store's invariants.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Neighbour

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Presentation.Schematic (Tm SRule SState GroundLabels TrivialKnowledge X E rowSig toTerm inst lift)
open KernelStep (addStep addName cell cellE instr k v addOp e rowsBefore θ)
open KernelEvaluation (addI addPoints addChoice addStep_anchored)

/-- The rows of the machine state, with a second cell at key `11`, holding `7`, at identity `5`. -/
def rowsDup : ℕ → Expr
  | 5 => cellE (e 11) (e 7)
  | o => rowsBefore o

/-- **The state with two cells at one key**: identities `0` to `5`, no knowledge, no table row. -/
def twoCells : SState ℕ := ⟨PUnit.unit, [], Finset.range 6, fun o => toTerm (rowsDup o)⟩

theorem twoCells_ground : GroundLabels twoCells rowsDup := fun _ _ => rfl

/-- The match that reads the second cell: first operand `7`, new value `10`. -/
def θDup : ℕ → Expr
  | 6 => e 7
  | 8 => e 10
  | n => θ n

/-- The point of evaluation `add(7, 3) = 10`. -/
def dupPoints : List EvalPoint := [([e 7, e 3], e 10)]

/-- The choices reading the second cell at key `11` (identity `5`). -/
def dupChoice : Choice ℕ (Subst rowSig) := ⟨Subst.id rowSig, [0, 1], [4, 5, 3], [], [6, 7], []⟩

/-- Both evaluated rules are rules of the program the true interpretation evaluates. -/
theorem both_members :
    addStep.evalAt addPoints ∈ evaluated addI {addStep} ∧ addStep.evalAt dupPoints ∈ evaluated addI {addStep} :=
  ⟨KernelEvaluation.evalAt_member, ⟨addStep, rfl, dupPoints, rfl, fun q inside => by
    simp only [addStep, dupPoints, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
    subst inside
    exact ⟨rfl, rfl⟩, rfl⟩⟩

/-- The rule at the point `add 2 3 5` fires at the state with two cells, reading the first. -/
theorem first_point_admitted :
    (step X ℕ E {addStep.at rows (addStep.pointRows addPoints)}).Admits (s := twoCells)
      (pointFiring (A := Presentation.Schematic.A) addStep (addStep.pointRows addPoints) (Set.mem_singleton _)
        addChoice) := by
  refine (admits_iff _).mpr ⟨identity_fresh twoCells_ground rfl _ rfl, ⟨by decide, by decide, rfl, rfl, rfl, rfl⟩,
    ?_, ⟨PUnit.unit, lift θ, models_lift twoCells_ground (fun _ inside => absurd inside List.not_mem_nil) _ rfl θ
      ?_ ?_ ?_⟩, fun c inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pointFiring, addChoice, twoCells, Selection.commit] <;> decide
  · intro x inside
    simp only [pointFiring, addChoice, RuleWithCondition.at_take, addStep, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨by simp [twoCells], rfl⟩
  · intro x inside
    simp only [pointFiring, addChoice, RuleWithCondition.at_read, addStep, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> exact ⟨by simp [twoCells], rfl⟩
  · intro pair inside
    simp only [pointFiring, RuleWithCondition.at_tell, addStep, RuleWithCondition.calls,
      RuleWithCondition.pointRows, addPoints, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
      List.append_nil, List.mem_singleton] at inside
    subst inside
    show inst θ (callRow rows ⟨v 8, addName, [v 6, v 7]⟩) =
      inst θ (toTerm (groundRow addName [e 2, e 3] (e 5)))
    rw [Presentation.Schematic.inst_toTerm]
    rfl

/-- The rule at the point `add 7 3 10` fires at the same state, reading the second. -/
theorem second_point_admitted :
    (step X ℕ E {addStep.at rows (addStep.pointRows dupPoints)}).Admits (s := twoCells)
      (pointFiring (A := Presentation.Schematic.A) addStep (addStep.pointRows dupPoints) (Set.mem_singleton _)
        dupChoice) := by
  refine (admits_iff _).mpr ⟨identity_fresh twoCells_ground rfl _ rfl, ⟨by decide, by decide, rfl, rfl, rfl, rfl⟩,
    ?_, ⟨PUnit.unit, lift θDup, models_lift twoCells_ground (fun _ inside => absurd inside List.not_mem_nil) _ rfl
      θDup ?_ ?_ ?_⟩, fun c inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pointFiring, dupChoice, twoCells, Selection.commit] <;> decide
  · intro x inside
    simp only [pointFiring, dupChoice, RuleWithCondition.at_take, addStep, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨by simp [twoCells], rfl⟩
  · intro x inside
    simp only [pointFiring, dupChoice, RuleWithCondition.at_read, addStep, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> exact ⟨by simp [twoCells], rfl⟩
  · intro pair inside
    simp only [pointFiring, RuleWithCondition.at_tell, addStep, RuleWithCondition.calls,
      RuleWithCondition.pointRows, dupPoints, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
      List.append_nil, List.mem_singleton] at inside
    subst inside
    show inst θDup (callRow rows ⟨v 8, addName, [v 6, v 7]⟩) =
      inst θDup (toTerm (groundRow addName [e 7, e 3] (e 10)))
    rw [Presentation.Schematic.inst_toTerm]
    rfl

/-- **Two admitted evaluations at one state, telling two different new values** (`5` and `10`): the true
function, the graph held by the program, no table row stored; the difference is the operand cell read. -/
theorem two_values_admitted :
    (step X ℕ E {addStep.evalAt addPoints}).Admits (s := twoCells)
        (evalFiring addStep addPoints (Set.mem_singleton _) addChoice) ∧
      (step X ℕ E {addStep.evalAt dupPoints}).Admits (s := twoCells)
        (evalFiring addStep dupPoints (Set.mem_singleton _) dupChoice) :=
  ⟨(eval_iff_point twoCells addStep addPoints rfl (fun q inside => by
        simp only [addStep, addPoints, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
        subst inside
        rfl) (Set.mem_singleton _) (Set.mem_singleton _) addChoice twoCells_ground addStep_anchored).mpr
      first_point_admitted,
    (eval_iff_point twoCells addStep dupPoints rfl (fun q inside => by
        simp only [addStep, dupPoints, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
        subst inside
        rfl) (Set.mem_singleton _) (Set.mem_singleton _) dupChoice twoCells_ground addStep_anchored).mpr
      second_point_admitted⟩

/-- The two evaluated rules tell the made value two different rows. -/
theorem told_values_differ :
    (addStep.evalAt addPoints).body.tell = [(v 8, toTerm (e 5))] ∧
      (addStep.evalAt dupPoints).body.tell = [(v 8, toTerm (e 10))] ∧ toTerm (e 5) ≠ toTerm (e 10) :=
  ⟨rfl, rfl, fun same => absurd (Presentation.Schematic.toTerm_injective same) (by decide)⟩

#print axioms both_members
#print axioms two_values_admitted
#print axioms told_values_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Neighbour
