import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Intensional

/-!
# Controls: each hypothesis of the table read is needed

* **The stored rows must be points of the graph** (`table_to_points` asks the rows read to be points):
  `wrong_row_admits_wrong_value`. At the kernel instance's state with the row `add 2 3 6` stored instead of
  `add 2 3 5`, the table read is admitted and its result holds register `10` at `6`. The table read trusts
  the rows of the table: the trusted part of a stored table is that its rows are the graph
  (`StoredRuns.TrueTables`). This is the control for a STORED table. Where no table is stored and the
  function is evaluated, the control in that mechanism is a wrong function
  (`KernelEvaluation.wrong_function_admits_wrong_value`, `Machine.wrong_value_made`).
* **The rule must be blind to the stored table** (`points_to_stored`, `stored_to_points` ask `Blind`):
  `grab_sees_table`, `grab_not_at_points`, `grab_not_blind`. A rule that takes any row takes a stored
  table row at the state with the table stored, and has nothing to take at the state without it.
* **Interpretations compose only with disjoint domains** (`graph_override` asks it): `override_loses`.
  Two interpretations that answer one call with different values: the union of their graphs has both
  rows, the override one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Controls

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open OneFrame (Terms frames ext)
open Presentation.Schematic (Tm SRule SState GroundLabels TrivialKnowledge ReadsAs schematicStep X E toTerm inst
  equationsOf admitted_of_match rowSig)
open KernelStep (cellE e addName addTable addProgram addTable_fragment rowsBefore θ)

/-! ## A wrong row of the table gives a wrong value -/

/-- The kernel instance's rows with the wrong row `add 2 3 6`. -/
def rowsWrong : ℕ → Expr
  | 5 => groundRow addName [e 2, e 3] (e 6)
  | o => rowsBefore o

/-- The state with the wrong row. -/
def beforeWrong : SState ℕ := ⟨PUnit.unit, [], Finset.range 6, fun o => toTerm (rowsWrong o)⟩

/-- The match with the wrong value. -/
def θWrong : ℕ → Expr
  | 8 => e 6
  | n => θ n

/-- The rows read and kept. -/
def keptWrong : List Expr := [rowsWrong 2, rowsWrong 3, rowsWrong 4, rowsWrong 5]

/-- **A wrong row of the table is read as the function's value**: the table read is admitted and register
`10` holds `6`. -/
theorem wrong_row_admits_wrong_value :
    ∃ (g : Firing ℕ E {r | r ∈ addProgram} beforeWrong.frame)
      (admitted : (schematicStep ℕ addProgram).Admits (s := beforeWrong) g),
      g.rule = addTable ∧ ReadsAs ((schematicStep ℕ addProgram).result g admitted)
        ((([cellE (e 0) (e 41), cellE (e 10) (e 6)] : List Expr) : Multiset Expr) + keptWrong) := by
  have split : ((addTable.body.take.map (inst θWrong) : List Expr) : Multiset Expr) + (keptWrong : Multiset Expr) =
      beforeWrong.present.val.map rowsWrong := rfl
  have reads : ∀ q ∈ addTable.body.read, inst θWrong q ∈ (keptWrong : Multiset Expr) := by
    intro q member
    simp only [addTable, RuleWithCondition.tableRule_read, KernelStep.addStep, RuleWithCondition.calls,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals
      rw [Multiset.mem_coe]
      decide
  have equations : ∀ eq ∈ equationsOf addTable, inst θWrong eq.1 = inst θWrong eq.2 := by
    intro eq member
    simp [equationsOf, addTable, KernelStep.addStep, RuleWithCondition.tableRule] at member
  exact admitted_of_match (fun _ _ => rfl) (fun _ inside => absurd inside List.not_mem_nil)
    (List.mem_singleton_self _) addTable_fragment split reads equations

/-! ## A rule that is not blind sees the stored table -/

/-- **Take any row.** -/
def grab : RuleWithCondition ℕ Tm := ⟨⟨PUnit.unit, ⟨[.var 0], [], [], [], []⟩, []⟩, []⟩

/-- A point of a graph: `add 2 3 5`. -/
def point : Tm := toTerm (groundRow addName [e 2, e 3] (e 5))

/-- The graph of that one point. -/
def onePoint : Set Tm := {point}

/-- A state with no row, whose label function labels `0` by the point. -/
def noRows : SState ℕ := ⟨PUnit.unit, [], ∅, fun _ => point⟩

/-- The program at the graph. -/
abbrev grabProgram : Program (Terms Tm) := specialized rows onePoint {grab}

theorem grab_member : grab.at rows [] ∈ grabProgram :=
  at_mem_specialized (Set.mem_singleton grab) rfl (fun _ inside => absurd inside List.not_mem_nil)

/-- The firing that takes row `0`. -/
def grabFiring : Firing ℕ E grabProgram PUnit.unit :=
  pointFiring (A := Presentation.Schematic.A) grab [] grab_member ⟨Subst.id rowSig, [0], [], [], [], []⟩

theorem grab_stores : StoresGraph Presentation.Schematic.A onePoint noRows {0} :=
  ⟨by simp [noRows], fun _ _ => ⟨rfl, fixed_toTerm _⟩⟩

/-- **At the state with the table stored, the rule takes the stored row.** -/
theorem grab_sees_table :
    (step X ℕ E grabProgram).Admits (s := withTables noRows {0}) grabFiring := by
  refine (admits_iff _).mpr ⟨fun b g h => ⟨h, fun t mentioned => ?_, fun t _ => ?_⟩,
    ⟨List.nodup_singleton 0, List.nodup_nil, rfl, rfl, rfl, rfl⟩, ?_, ⟨PUnit.unit, fun _ => point, ?_⟩,
    fun c inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · rcases mentioned with inKnowledge | inKnowledge | ⟨o, -, rfl⟩
    · exact absurd inKnowledge List.not_mem_nil
    · exact absurd inKnowledge List.not_mem_nil
    · show h.applyTerm ((Subst.id rowSig).applyTerm point) = g.applyTerm point
      rw [Subst.applyTerm_id, point, Presentation.Schematic.applyTerm_toTerm,
        Presentation.Schematic.applyTerm_toTerm]
  · show h.applyTerm ((Subst.id rowSig).applyTerm t) = h.applyTerm t
    rw [Subst.applyTerm_id]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [grabFiring, pointFiring, withTables, State.withPresent, noRows,
      Selection.commit]
  · intro eq inside
    have information : grabFiring.information X (withTables noRows {0}) =
        [((Subst.id rowSig).applyTerm (.var 0), (Subst.id rowSig).applyTerm point)] := rfl
    rw [information, List.mem_singleton] at inside
    subst inside
    show Subst.applyTerm (fun _ => point : Subst rowSig) ((Subst.id rowSig).applyTerm (.var 0)) =
      Subst.applyTerm (fun _ => point : Subst rowSig) ((Subst.id rowSig).applyTerm point)
    rw [Subst.applyTerm_id, Subst.applyTerm_id]
    exact (Presentation.Schematic.applyTerm_toTerm _ (groundRow addName [e 2, e 3] (e 5))).symm

/-- **At the state without it, the rule has nothing to take.** -/
theorem grab_not_at_points : ¬ (step X ℕ E grabProgram).Admits (s := noRows) grabFiring := by
  intro admitted
  obtain ⟨-, -, enabled, -⟩ := (admits_iff _).mp admitted
  have present := enabled.taken_subset (show 0 ∈ ([0] : List ℕ).toFinset by simp)
  simp [noRows] at present

/-- **The rule is not blind**: it equates its take pattern with the point. -/
theorem grab_not_blind : ¬ Blind Presentation.Schematic.A onePoint grab.rule := by
  intro blind
  exact blind (fun _ => point) point rfl (.var 0) (by simp [grab]) (by
    show Subst.applyTerm (fun _ => point : Subst rowSig) (.var 0) = point
    rfl)

/-! ## Interpretations with one answer each compose; with two they do not -/

/-- Rows of a table that are their values. -/
def valueRows : Tabulation ℕ ℕ := ⟨fun _ _ v => v⟩

/-- Answers `1` at the empty arguments of `0`. -/
def answerOne : Interpretation ℕ ℕ := fun f args => if f = 0 ∧ args = [] then some 1 else none

/-- Answers `2` there. -/
def answerTwo : Interpretation ℕ ℕ := fun f args => if f = 0 ∧ args = [] then some 2 else none

/-- **Overriding loses the second answer**: the union of the graphs has the row `2`, the override does
not. -/
theorem override_loses :
    (2 : ℕ) ∈ graph valueRows answerOne ∪ graph valueRows answerTwo ∧
      (2 : ℕ) ∉ graph valueRows (fun f args => (answerOne f args).or (answerTwo f args)) := by
  refine ⟨.inr ⟨0, [], 2, rfl, rfl⟩, ?_⟩
  rintro ⟨f, args, v, defined, same⟩
  simp only [answerOne, answerTwo] at defined
  by_cases at0 : f = 0 ∧ args = []
  · rw [if_pos at0, if_pos at0, Option.some_or] at defined
    cases defined
    have two : (2 : ℕ) = 1 := same
    exact absurd two (by decide)
  · rw [if_neg at0, if_neg at0] at defined
    cases defined

#print axioms wrong_row_admits_wrong_value
#print axioms grab_sees_table
#print axioms grab_not_at_points
#print axioms grab_not_blind
#print axioms override_loses

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Controls
