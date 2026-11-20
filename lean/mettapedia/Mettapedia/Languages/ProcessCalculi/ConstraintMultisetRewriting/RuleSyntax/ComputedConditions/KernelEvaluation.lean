import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Runs

/-!
# The instruction step evaluated by host code, with no table stored

A guard in host code that computes the new value of the add step and supplies it is, on the step, the
rule evaluated at the point it computes (`RuleWithCondition.evalAt`), a rule of the program the
interpretation evaluates (`evaluated`), here `addI` (`add(a, b) = a + b` on numerals).

* `evalAt_member`: the rule evaluated at `add(2, 3) = 5` is a rule of the evaluated program;
  `wrong_value_not_a_rule`: at `add(2, 3) = 6` it is not. The host's computation is the program's
  membership. What is trusted is the interpretation together with the store's invariants: with the true
  interpretation and two cells at one key, two values are admitted (`Neighbour.two_values_admitted`).
* `addStep_anchored`: the operands are bound by the operand cells.
* `point_admitted`, `eval_admitted`: at the machine state **without** the table row, the rule at the point
  (it tells the call row equal to `add 2 3 5`) and the evaluated rule (it asks the call row and tells the
  value) are admitted, by `models_lift` and `eval_iff_point`; the made destination value is `5`. These are
  statements at the one state `noTable`; the statements at every state a run reaches are in `Machine`.

## The state after the instruction

* `result_not_ground`: **the state after the admitted evaluation is not ground**: the made destination cell is
  labelled by the opened made row, a term with the unknown `8`, and the binding is kept as knowledge. So a
  theorem that asks a ground state does not apply after one instruction.
* `result_reads`: **it reads as rows** (`Machines.Reads`), by the closure of such states under the step
  (`matches_of_admitted`), so the theorems at states that read as rows apply there.
* `evalAt_not_restricted`: **the evaluated add step is not range restricted**: its new value is bound by the tell
  of the function's value and by no take or read pattern. The wider fragment holds it
  (`evalAt_fragment`).

## Controls

* **A wrong function, no row stored** (`wrongI`, `wrong_member`, `wrong_function_admits_wrong_value`,
  `wrong_value_told`): with an interpretation that answers `add(2, 3) = 6`, the add step evaluated at that point
  is a rule of the evaluated program, is admitted at the machine state with no table row, and tells the new
  value `6`. This is the control for the reading in which the program holds the graph and nothing is stored;
  `Controls.wrong_row_admits_wrong_value` is the control for a stored table.
* **A made value that nothing binds** (`kernelFiring_admitted`, `kernel_result_not_reads`): the rule that makes
  a new value bound by no take, read or tell (`KernelStep.kernelRule`) is admitted at the machine state, and its
  result reads as no rows: two solutions of its knowledge read the made cell differently. The rule that range
  restriction rejects is the rule whose results leave the states the run theorems are about.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelEvaluation

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Presentation.Schematic (Tm SRule SState GroundLabels TrivialKnowledge X E rowSig toTerm inst lift
  toTerm_injective mem_vars_var not_mem_vars_const vars_toTerm RangeRestricted written mem_written_of_produce)
open KernelStep (addStep addName cell instr k v addOp e rowsBefore θ mem_vars_cell)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Reads reads_of_ground)

/-- **Addition on numerals.** -/
def addI : Interpretation ℕ Expr := fun f args =>
  match f, args with
  | 3, [.sym a, .sym b] => some (.sym (a + b))
  | _, _ => none

/-- The point of evaluation `add(2, 3) = 5`. -/
def addPoints : List EvalPoint := [([e 2, e 3], e 5)]

/-- **The rule evaluated at `add(2, 3) = 5` is a rule of the evaluated program.** -/
theorem evalAt_member : addStep.evalAt addPoints ∈ evaluated addI {addStep} :=
  ⟨addStep, rfl, addPoints, rfl, fun q inside => by
    simp only [addStep, addPoints, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
    subst inside
    exact ⟨rfl, rfl⟩, rfl⟩

/-- **At a wrong value the evaluated rule is not a rule of the program.** -/
theorem wrong_value_not_a_rule : addStep.evalAt [([e 2, e 3], e 6)] ∉ evaluated addI {addStep} := by
  rintro ⟨ρ, inP, pts, length, answered, same⟩
  rw [Set.mem_singleton_iff] at inP
  subst inP
  obtain ⟨pt, rfl⟩ : ∃ pt, pts = [pt] := List.length_eq_one_iff.mp length
  have tells : ((addStep.evalAt [([e 2, e 3], e 6)]).body.tell : EquationStore Tm) =
      ((addStep.evalAt [pt]).body.tell : EquationStore Tm) := by rw [same]
  have checks : ((addStep.evalAt [([e 2, e 3], e 6)]).body.checks : List (Check Tm)) =
      ((addStep.evalAt [pt]).body.checks : List (Check Tm)) := by rw [same]
  simp only [RuleWithCondition.evalAt, addStep, List.zip_cons_cons, List.zip_nil_left, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    at tells
  have value : pt.2 = e 6 := (toTerm_injective tells).symm
  obtain ⟨answers, argLength⟩ := answered (⟨v 8, addName, [v 6, v 7]⟩, pt) (List.mem_singleton_self _)
  change addI addName pt.1 = some pt.2 at answers
  have argLength' : pt.1.length = 2 := argLength
  change [Check.equal (callRow rows ⟨v 8, addName, [v 6, v 7]⟩)
      (pointRow ⟨v 8, addName, [v 6, v 7]⟩ ([e 2, e 3], e 6))] ++ [] =
    [Check.equal (callRow rows ⟨v 8, addName, [v 6, v 7]⟩) (pointRow ⟨v 8, addName, [v 6, v 7]⟩ pt)] ++ []
    at checks
  rw [List.append_nil, List.append_nil] at checks
  have rowsEq := toTerm_injective (Check.equal.inj (List.cons.inj checks).1).2
  obtain ⟨-, argsAndValue⟩ := groundSpine_inj (by simp [argLength']) rowsEq
  obtain ⟨args, -⟩ := List.append_inj argsAndValue (by simp [argLength'])
  rw [← args, value] at answers
  exact absurd answers (by decide)

/-- **The operands are bound by the operand cells.** -/
theorem addStep_anchored : addStep.ArgumentsAnchored := by
  intro c inside t inArguments x inT
  rw [show addStep.conditions = [⟨v 8, addName, [v 6, v 7]⟩] from rfl, List.mem_singleton] at inside
  subst inside
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
  rcases inArguments with rfl | rfl
  · rw [mem_vars_var.mp inT]
    exact .inl ⟨cell (v 3) (v 6), by simp [addStep], mem_vars_cell.mpr (.inr (mem_vars_var.mpr rfl))⟩
  · rw [mem_vars_var.mp inT]
    exact .inl ⟨cell (v 4) (v 7), by simp [addStep], mem_vars_cell.mpr (.inr (mem_vars_var.mpr rfl))⟩

/-- **The machine state without the table row**: identities `0` to `4`. -/
def noTable : SState ℕ := ⟨PUnit.unit, [], Finset.range 5, fun o => toTerm (rowsBefore o)⟩

theorem noTable_ground : GroundLabels noTable rowsBefore := fun _ _ => rfl

/-- The choices: the identity opening, the control and destination cells taken, the instruction and the
operand cells read, the made identities `6` and `7`. -/
def addChoice : Choice ℕ (Subst rowSig) := ⟨Subst.id rowSig, [0, 1], [4, 2, 3], [], [6, 7], []⟩

/-- **The rule at the point is admitted at the state without the table row.** -/
theorem point_admitted :
    (step X ℕ E {addStep.at rows (addStep.pointRows addPoints)}).Admits (s := noTable)
      (pointFiring (A := Presentation.Schematic.A) addStep (addStep.pointRows addPoints) (Set.mem_singleton _)
        addChoice) := by
  refine (admits_iff _).mpr ⟨identity_fresh noTable_ground rfl _ rfl, ⟨by decide, by decide, rfl, rfl, rfl, rfl⟩,
    ?_, ⟨PUnit.unit, lift θ, models_lift noTable_ground (fun _ inside => absurd inside List.not_mem_nil) _ rfl θ
      ?_ ?_ ?_⟩, fun c inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pointFiring, addChoice, noTable, Selection.commit] <;> decide
  · intro x inside
    simp only [pointFiring, addChoice, RuleWithCondition.at_take, addStep, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨by simp [noTable], rfl⟩
  · intro x inside
    simp only [pointFiring, addChoice, RuleWithCondition.at_read, addStep, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> exact ⟨by simp [noTable], rfl⟩
  · intro pair inside
    simp only [pointFiring, RuleWithCondition.at_tell, addStep, RuleWithCondition.calls,
      RuleWithCondition.pointRows, addPoints, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
      List.append_nil, List.mem_singleton] at inside
    subst inside
    show inst θ (callRow rows ⟨v 8, addName, [v 6, v 7]⟩) =
      inst θ (toTerm (groundRow addName [e 2, e 3] (e 5)))
    rw [Presentation.Schematic.inst_toTerm]
    rfl

/-- **The evaluated rule is admitted at the state without the table row**: it asks the call row equal to
`add 2 3 5` and tells the new value `5`. -/
theorem eval_admitted :
    (step X ℕ E {addStep.evalAt addPoints}).Admits (s := noTable)
      (evalFiring addStep addPoints (Set.mem_singleton _) addChoice) :=
  (eval_iff_point noTable addStep addPoints rfl (fun q inside => by
      simp only [addStep, addPoints, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
      subst inside
      rfl) (Set.mem_singleton _) (Set.mem_singleton _) addChoice noTable_ground addStep_anchored).mpr
    point_admitted

/-! ## The state after the instruction -/

/-- The admitted evaluation of the add step, as a firing. -/
abbrev fired : Firing ℕ E {addStep.evalAt addPoints} PUnit.unit :=
  evalFiring addStep addPoints (Set.mem_singleton _) addChoice

/-- The state after it. -/
abbrev afterAdd : SState ℕ := fired.result X noTable

theorem afterAdd_present : (7 : ℕ) ∈ afterAdd.present := by
  show 7 ∈ fire noTable.present (fired.selection.commit (T := Unit))
  simp [fire, Selection.commit, evalFiring, addChoice]

theorem afterAdd_label : afterAdd.label 7 = (Subst.id rowSig).applyTerm (cell (v 1) (v 8)) := rfl

/-- **The state after the admitted evaluation is not ground**: the made destination cell is labelled by a term
with the unknown `8`. -/
theorem result_not_ground : ¬ ∃ rowsOf : ℕ → Expr, GroundLabels afterAdd rowsOf := by
  rintro ⟨rowsOf, ground⟩
  have labelled := ground 7 afterAdd_present
  rw [afterAdd_label, Subst.applyTerm_id] at labelled
  have inside : 8 ∈ (cell (v 1) (v 8)).freeVars := mem_vars_cell.mpr (.inr (mem_vars_var.mpr rfl))
  rw [labelled] at inside
  exact vars_toTerm _ _ inside

/-- **The state after the admitted evaluation reads as rows**: the instance, at the instruction step, of the
closure of states that read as rows under the step. -/
theorem result_reads : ∃ rows : ℕ → Expr, Reads afterAdd rows := by
  have reads : Reads noTable rowsBefore :=
    reads_of_ground noTable_ground (fun _ inside => absurd inside List.not_mem_nil)
  obtain ⟨θ', -, -, -, after⟩ := matches_of_admitted reads fired eval_admitted
  exact ⟨_, after (evalAt_makes addStep addPoints rfl fun t inProduce x vars =>
    KernelStep.addStep_restricted t (mem_written_of_produce inProduce) x vars)⟩

/-- **The evaluated add step is not range restricted**: the new value `8` is told equal to the function's value
and made, and it occurs in no take or read pattern. -/
theorem evalAt_not_restricted : ¬ RangeRestricted (addStep.evalAt addPoints) := by
  intro restricted
  obtain ⟨t, member, inT⟩ := restricted (cell (v 1) (v 8))
    (by simp [written, RuleWithCondition.evalAt, addStep]) 8 (mem_vars_cell.mpr (.inr (mem_vars_var.mpr rfl)))
  have inPatterns : t = cell (k 0) (v 0) ∨ t = cell (v 1) (v 2) ∨
      t = instr (v 0) (k addOp) (v 1) (v 3) (v 4) (v 5) ∨ t = cell (v 3) (v 6) ∨ t = cell (v 4) (v 7) := by
    simpa [RuleWithCondition.evalAt, addStep] using member
  rcases inPatterns with rfl | rfl | rfl | rfl | rfl
  · exact absurd (KernelStep.vars_cell_symbol inT) (by decide)
  · rcases KernelStep.vars_cell_unknowns inT with same | same <;> exact absurd same (by decide)
  · rw [instr, mem_vars_spine] at inT
    rcases inT with inHead | ⟨u, inArguments, inU⟩
    · exact absurd inHead not_mem_vars_const
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inArguments
      rcases inArguments with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd (mem_vars_var.mp inU) (by decide)
      · exact absurd inU not_mem_vars_const
      · exact absurd (mem_vars_var.mp inU) (by decide)
      · exact absurd (mem_vars_var.mp inU) (by decide)
      · exact absurd (mem_vars_var.mp inU) (by decide)
      · exact absurd (mem_vars_var.mp inU) (by decide)
  · rcases KernelStep.vars_cell_unknowns inT with same | same <;> exact absurd same (by decide)
  · rcases KernelStep.vars_cell_unknowns inT with same | same <;> exact absurd same (by decide)

/-! ## Control: a wrong function, no row stored -/

/-- **A wrong addition**: one more than the sum. -/
def wrongI : Interpretation ℕ Expr := fun f args =>
  match f, args with
  | 3, [.sym a, .sym b] => some (.sym (a + b + 1))
  | _, _ => none

/-- The point it computes: `add(2, 3) = 6`. -/
def wrongPoints : List EvalPoint := [([e 2, e 3], e 6)]

/-- The match with the new value `6`. -/
def θWrong : ℕ → Expr
  | 8 => e 6
  | n => θ n

/-- **The rule evaluated at the wrong point is a rule of the program the wrong function evaluates.** -/
theorem wrong_member : addStep.evalAt wrongPoints ∈ evaluated wrongI {addStep} :=
  ⟨addStep, rfl, wrongPoints, rfl, fun q inside => by
    simp only [addStep, wrongPoints, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
    subst inside
    exact ⟨rfl, rfl⟩, rfl⟩

/-- The rule at the wrong point fires at the machine state without any table row. -/
theorem wrong_point_admitted :
    (step X ℕ E {addStep.at rows (addStep.pointRows wrongPoints)}).Admits (s := noTable)
      (pointFiring (A := Presentation.Schematic.A) addStep (addStep.pointRows wrongPoints) (Set.mem_singleton _)
        addChoice) := by
  refine (admits_iff _).mpr ⟨identity_fresh noTable_ground rfl _ rfl, ⟨by decide, by decide, rfl, rfl, rfl, rfl⟩,
    ?_, ⟨PUnit.unit, lift θWrong, models_lift noTable_ground (fun _ inside => absurd inside List.not_mem_nil) _ rfl
      θWrong ?_ ?_ ?_⟩, fun c inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pointFiring, addChoice, noTable, Selection.commit] <;> decide
  · intro x inside
    simp only [pointFiring, addChoice, RuleWithCondition.at_take, addStep, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨by simp [noTable], rfl⟩
  · intro x inside
    simp only [pointFiring, addChoice, RuleWithCondition.at_read, addStep, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> exact ⟨by simp [noTable], rfl⟩
  · intro pair inside
    simp only [pointFiring, RuleWithCondition.at_tell, addStep, RuleWithCondition.calls,
      RuleWithCondition.pointRows, wrongPoints, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
      List.append_nil, List.mem_singleton] at inside
    subst inside
    show inst θWrong (callRow rows ⟨v 8, addName, [v 6, v 7]⟩) =
      inst θWrong (toTerm (groundRow addName [e 2, e 3] (e 6)))
    rw [Presentation.Schematic.inst_toTerm]
    rfl

/-- **With a wrong function and no table stored, the wrong value is admitted**: the firing of the program the
wrong function evaluates, at the machine state. -/
theorem wrong_function_admits_wrong_value :
    (step X ℕ E (evaluated wrongI {addStep})).Admits (s := noTable)
      (evalFiring addStep wrongPoints wrong_member addChoice) :=
  (eval_iff_point noTable addStep wrongPoints rfl (fun q inside => by
      simp only [addStep, wrongPoints, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
      subst inside
      rfl) wrong_member (Set.mem_singleton _) addChoice noTable_ground addStep_anchored).mpr wrong_point_admitted

/-- It tells the new value `6`. -/
theorem wrong_value_told : (addStep.evalAt wrongPoints).body.tell = [(v 8, toTerm (e 6))] := rfl

/-! ## Control: a made value that nothing binds -/

/-- The rule that makes a value nothing binds, fired at the machine state: the control and destination cells
taken, the operand cells read, the made identities `6` and `7`. -/
def kernelFiring : Firing ℕ E {KernelStep.kernelRule} PUnit.unit :=
  ⟨KernelStep.kernelRule, Set.mem_singleton _, PUnit.unit, Subst.id rowSig, ⟨[0, 1], [2, 3], [6, 7]⟩, []⟩

/-- **It is admitted**: nothing constrains the made unknowns. -/
theorem kernelFiring_admitted : (step X ℕ E {KernelStep.kernelRule}).Admits (s := noTable) kernelFiring := by
  refine (admits_iff _).mpr ⟨identity_fresh noTable_ground rfl _ rfl, ⟨by decide, by decide, rfl, rfl, rfl, rfl⟩,
    ?_, ⟨PUnit.unit, lift θ, models_lift noTable_ground (fun _ inside => absurd inside List.not_mem_nil) _ rfl θ
      ?_ ?_ ?_⟩, fun c inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [kernelFiring, noTable, Selection.commit] <;> decide
  · intro x inside
    simp only [kernelFiring, KernelStep.kernelRule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨by simp [noTable], rfl⟩
  · intro x inside
    simp only [kernelFiring, KernelStep.kernelRule, List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
      List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨by simp [noTable], rfl⟩
  · intro pair inside
    exact absurd inside List.not_mem_nil

/-- **Its result reads as no rows**: the made value `8` occurs in no take or read pattern and in no tell, so two
solutions of the result's knowledge read the made destination cell as two different rows. -/
theorem kernel_result_not_reads : ¬ ∃ rows : ℕ → Expr, Reads (kernelFiring.result X noTable) rows :=
  result_not_reads kernelFiring kernelFiring_admitted (t := cell (v 1) (v 8))
    (by simp [kernelFiring, KernelStep.kernelRule]) (x := 8) (mem_vars_cell.mpr (.inr (mem_vars_var.mpr rfl)))
    (fun u inside => by
      have inPatterns : u = cell (k 0) (v 0) ∨ u = cell (v 1) (v 2) ∨ u = cell (v 3) (v 6) ∨
          u = cell (v 4) (v 7) := by
        simpa [kernelFiring, KernelStep.kernelRule] using inside
      intro inU
      rcases inPatterns with rfl | rfl | rfl | rfl
      · exact absurd (KernelStep.vars_cell_symbol inU) (by decide)
      · rcases KernelStep.vars_cell_unknowns inU with same | same <;> exact absurd same (by decide)
      · rcases KernelStep.vars_cell_unknowns inU with same | same <;> exact absurd same (by decide)
      · rcases KernelStep.vars_cell_unknowns inU with same | same <;> exact absurd same (by decide))
    (fun eq inside => absurd inside List.not_mem_nil)

#print axioms result_not_ground
#print axioms result_reads
#print axioms evalAt_not_restricted
#print axioms wrong_member
#print axioms wrong_function_admits_wrong_value
#print axioms kernelFiring_admitted
#print axioms kernel_result_not_reads
#print axioms evalAt_member
#print axioms wrong_value_not_a_rule
#print axioms addStep_anchored
#print axioms point_admitted
#print axioms eval_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelEvaluation
