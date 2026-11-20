import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Rows

/-!
# An arithmetic instruction step whose new value is the table's

A machine state as rows: cells `cell key value` (the control cell has key `0` and holds the program
counter), instruction rows `instr pc op dst src₁ src₂ next` (the program is in the store), and rows of
the table of `add`, `add a b r`.

**The step with its computed condition** (`addStep`): take the control cell at `pc` and the destination
cell, read the instruction at `pc` and the two operand cells, let `r := add(a, b)`, make the control cell
at `next` and the destination cell holding `r`. Its table read (`addTable`) reads the row `add a b r`.

* `addStep_restricted`, `addTable_fragment`: every made unknown is bound (the next counter by the
  instruction row, the new value by the condition), so the table read is in the presentation's
  fragment.
* `right_value_admitted`: at the state `before` (control at `40`, register `10` holding `9`,
  registers `11` and `12` holding `2` and `3`, the instruction at `40` adding them into register `10`
  and going to `41`, and the table row `add 2 3 5`), `RuleSyntax.step` admits a firing whose result
  reads as the control at `41` and register `10` holding `5`.
* `made_value_is_five`: **every** admitted firing at `before` makes the destination value `5`: the
  table row read fixes it. This is one state, with one cell at each key and one row of the table; with
  two cells at one key two values are made (`Neighbour.two_values_admitted`), and the statement at every
  state that represents a store is `Machine.machine_backward` with `Machine.storeRows_invariants`.
* `wrong_value_refused`: ANOTHER rule, the one with the value `6` written in (what a caller-supplied
  value amounts to), reads `add a b 6`, and no firing of it is admitted at `before`. It does not say that
  no firing of the instruction's own rule makes a wrong value: that is `Machine.machine_backward`, and its
  control, a wrong function evaluated by the same mechanism, is
  `KernelEvaluation.wrong_function_admits_wrong_value`.
* `kernelRule_not_restricted`: **a rule whose made values nothing binds** (the same takes and operand
  reads as the step, no instruction row and no table row, the next counter and the new value written in
  the made rows and bound by nothing; a simplified shape, not a transcription of any kernel's rule) is
  rejected by range restriction, the static check that refuses a made value nothing determines. What such
  a rule does when it fires: its result reads as no rows (`KernelEvaluation.kernel_result_not_reads`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelStep

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Presentation.Schematic (Tm SRule SState GroundLabels TrivialKnowledge ReadsAs schematicStep E X
  toTerm inst Bound written RangeRestricted RangeRestrictedPositive equationsOf MatchFires mem_vars_var
  not_mem_vars_const admitted_of_match match_of_admitted)

/-! ## Rows -/

/-- An unknown. -/
abbrev v (n : ℕ) : Tm := .var n

/-- A symbol. -/
abbrev k (n : ℕ) : Tm := .const (.sym n)

/-- The symbol of cells. -/
abbrev cellSym : ℕ := 1

/-- The symbol of instruction rows. -/
abbrev instrSym : ℕ := 2

/-- The function `add`, whose table's rows start with this symbol. -/
abbrev addName : ℕ := 3

/-- The opcode of an addition. -/
abbrev addOp : ℕ := 6

/-- A cell. -/
def cell (key value : Tm) : Tm := spine (k cellSym) [key, value]

/-- An instruction row. -/
def instr (pc op dst src₁ src₂ next : Tm) : Tm := spine (k instrSym) [pc, op, dst, src₁, src₂, next]

/-- A ground cell. -/
def cellE (key value : Expr) : Expr := groundSpine (.sym cellSym) [key, value]

/-- A ground instruction row. -/
def instrE (pc op dst src₁ src₂ next : Expr) : Expr :=
  groundSpine (.sym instrSym) [pc, op, dst, src₁, src₂, next]

/-- A number. -/
abbrev e (n : ℕ) : Expr := .sym n

/-! ## The step -/

/-- **The add step with its computed condition** `r := add(a, b)`. Unknowns: `0` the counter, `1` the
destination register, `2` its old value, `3` and `4` the source registers, `5` the next counter, `6`
and `7` the operands, `8` the new value. -/
def addStep : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[cell (k 0) (v 0), cell (v 1) (v 2)],
    [instr (v 0) (k addOp) (v 1) (v 3) (v 4) (v 5), cell (v 3) (v 6), cell (v 4) (v 7)], [], [],
    [cell (k 0) (v 5), cell (v 1) (v 8)]⟩, []⟩
  conditions := [⟨v 8, addName, [v 6, v 7]⟩]

/-- **Its table read**: it also reads `add a b r`. -/
abbrev addTable : SRule := addStep.tableRule rows

/-- The program of the table read. -/
abbrev addProgram : List SRule := [addTable]

/-- The unknowns of a cell are those of its key and of its value. -/
theorem mem_vars_cell {x : ℕ} {key value : Tm} :
    x ∈ (cell key value).freeVars ↔ x ∈ key.freeVars ∨ x ∈ value.freeVars := by
  rw [cell, mem_vars_spine]
  constructor
  · rintro (inHead | ⟨t, member, inT⟩)
    · exact absurd inHead not_mem_vars_const
    · rcases List.mem_cons.mp member with rfl | member
      · exact .inl inT
      · rcases List.mem_cons.mp member with rfl | member
        · exact .inr inT
        · exact absurd member List.not_mem_nil
  · rintro (inKey | inValue)
    · exact .inr ⟨key, List.mem_cons_self, inKey⟩
    · exact .inr ⟨value, List.mem_cons_of_mem _ List.mem_cons_self, inValue⟩

/-- An unknown of a cell with a symbol for a key is its value's. -/
theorem vars_cell_symbol {x n m : ℕ} (inside : x ∈ (cell (k n) (v m)).freeVars) : x = m := by
  rcases mem_vars_cell.mp inside with inKey | inValue
  · exact absurd inKey not_mem_vars_const
  · exact mem_vars_var.mp inValue

/-- The unknowns of a cell of two unknowns. -/
theorem vars_cell_unknowns {x n m : ℕ} (inside : x ∈ (cell (v n) (v m)).freeVars) : x = n ∨ x = m := by
  rcases mem_vars_cell.mp inside with inKey | inValue
  · exact .inl (mem_vars_var.mp inKey)
  · exact .inr (mem_vars_var.mp inValue)

/-- The next counter is an unknown of the instruction pattern. -/
theorem next_in_instr : 5 ∈ (instr (v 0) (k addOp) (v 1) (v 3) (v 4) (v 5)).freeVars := by
  rw [instr, mem_vars_spine]
  exact .inr ⟨v 5, by simp, mem_vars_var.mpr rfl⟩

theorem addStep_restricted : addStep.RangeRestrictedWith := by
  intro t member x inT
  have produced : t = cell (k 0) (v 5) ∨ t = cell (v 1) (v 8) := by
    simpa [written, addStep, checkTerms] using member
  rcases produced with rfl | rfl
  · obtain rfl := vars_cell_symbol inT
    exact .inl ⟨instr (v 0) (k addOp) (v 1) (v 3) (v 4) (v 5), by simp [addStep], next_in_instr⟩
  · rcases vars_cell_unknowns inT with rfl | rfl
    · exact .inl ⟨cell (v 1) (v 2), by simp [addStep], mem_vars_cell.mpr (.inl (mem_vars_var.mpr rfl))⟩
    · exact .inr ⟨⟨v 8, addName, [v 6, v 7]⟩, by simp [addStep], mem_vars_var.mpr rfl⟩

theorem addTable_fragment : RangeRestrictedPositive addTable :=
  addStep.fragment_tableRule rfl rfl addStep_restricted

theorem addProgram_fragment : ∀ r ∈ addProgram, RangeRestrictedPositive r := by
  intro r member
  rw [List.mem_singleton.mp member]
  exact addTable_fragment

/-! ## The state before the step -/

/-- The rows: control at `40`; register `10` holds `9`; registers `11` and `12` hold `2` and `3`; the
instruction at `40` adds registers `11` and `12` into register `10` and goes to `41`; the table row
`add 2 3 5`. -/
def rowsBefore : ℕ → Expr
  | 0 => cellE (e 0) (e 40)
  | 1 => cellE (e 10) (e 9)
  | 2 => cellE (e 11) (e 2)
  | 3 => cellE (e 12) (e 3)
  | 4 => instrE (e 40) (e addOp) (e 10) (e 11) (e 12) (e 41)
  | _ => groundRow addName [e 2, e 3] (e 5)

/-- **The state before the step**: identities `0` to `5`, no knowledge. -/
def before : SState ℕ := ⟨PUnit.unit, [], Finset.range 6, fun o => toTerm (rowsBefore o)⟩

theorem before_ground : GroundLabels before rowsBefore := fun _ _ => rfl

theorem before_trivial : TrivialKnowledge before.knowledge := fun _ inside => absurd inside List.not_mem_nil

/-- The match: counter `40`, destination `10` (old `9`), sources `11` and `12`, next `41`, operands `2`
and `3`, new value `5`. -/
def θ : ℕ → Expr
  | 0 => e 40
  | 1 => e 10
  | 2 => e 9
  | 3 => e 11
  | 4 => e 12
  | 5 => e 41
  | 6 => e 2
  | 7 => e 3
  | _ => e 5

/-- The rows the step reads and keeps. -/
def kept : List Expr := [rowsBefore 2, rowsBefore 3, rowsBefore 4, rowsBefore 5]

/-- **The rows after the step**: control at `41`, register `10` holding `5`, and the rows read. -/
def rowsAfter : Multiset Expr := (([cellE (e 0) (e 41), cellE (e 10) (e 5)] : List Expr) : Multiset Expr) + kept

/-- **The firing with the right value is admitted**, and its result reads as the control at `41` and
register `10` holding `5`. -/
theorem right_value_admitted :
    ∃ (g : Firing ℕ E {r | r ∈ addProgram} before.frame)
      (admitted : (schematicStep ℕ addProgram).Admits (s := before) g),
      g.rule = addTable ∧ ReadsAs ((schematicStep ℕ addProgram).result g admitted) rowsAfter := by
  have split : ((addTable.body.take.map (inst θ) : List Expr) : Multiset Expr) + (kept : Multiset Expr) =
      before.present.val.map rowsBefore := rfl
  have reads : ∀ q ∈ addTable.body.read, inst θ q ∈ (kept : Multiset Expr) := by
    intro q member
    simp only [addTable, RuleWithCondition.tableRule_read, addStep, RuleWithCondition.calls, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals
      rw [Multiset.mem_coe]
      decide
  have equations : ∀ eq ∈ equationsOf addTable, inst θ eq.1 = inst θ eq.2 := by
    intro eq member
    simp [equationsOf, addTable, addStep, RuleWithCondition.tableRule] at member
  exact admitted_of_match before_ground before_trivial (List.mem_singleton_self _) addTable_fragment split
    reads equations

/-! ## The made value is the table's -/

/-- The value at the end of every row present at `before`: none is `6`, and the only row starting with
the symbol of `add` ends with `5`. -/
theorem table_row_unique {o : ℕ} (present : o ∈ before.present) {a b w : Expr}
    (labelled : rowsBefore o = groundSpine (.sym addName) [a, b, w]) : a = e 2 ∧ b = e 3 ∧ w = e 5 := by
  have small : o < 6 := Finset.mem_range.mp present
  interval_cases o <;>
    simp [rowsBefore, cellE, instrE, groundRow, groundSpine] at labelled
  refine ⟨?_, ?_, ?_⟩ <;> simp_all

/-- **Every admitted firing at `before` makes the destination value `5`**: the row of `add`'s table it
reads fixes the value. -/
theorem made_value_is_five (g : Firing ℕ E {r | r ∈ addProgram} before.frame)
    (admitted : (schematicStep ℕ addProgram).Admits (s := before) g) :
    ∃ θ' : ℕ → Expr, θ' 8 = e 5 ∧
      ReadsAs ((schematicStep ℕ addProgram).result g admitted)
        ((before.present \ g.selection.taken.toFinset).val.map rowsBefore +
          (([cellE (e 0) (θ' 5), cellE (θ' 1) (e 5)] : List Expr) : Multiset Expr)) := by
  obtain ⟨θ', fires, readsAs⟩ := match_of_admitted before_ground addProgram_fragment g admitted
  have isTable : g.rule = addTable := List.mem_singleton.mp g.member
  have call : rows.row addName [v 6, v 7] (v 8) ∈ g.rule.body.read := by
    rw [isTable]
    simp [addTable, addStep, RuleWithCondition.calls, callRow]
  have inRest := fires.reads _ call
  obtain ⟨o, inside, labelled⟩ := List.mem_map.mp inRest
  have present : o ∈ before.present := (Finset.mem_sdiff.mp (Finset.mem_toList.mp inside)).1
  have spineForm : inst θ' (rows.row addName [v 6, v 7] (v 8)) =
      groundSpine (.sym addName) [θ' 6, θ' 7, θ' 8] := inst_spine θ' _ _
  rw [spineForm] at labelled
  obtain ⟨-, -, eight⟩ := table_row_unique present labelled
  refine ⟨θ', eight, ?_⟩
  have produce : g.rule.body.produce.map (inst θ') = [cellE (e 0) (θ' 5), cellE (θ' 1) (e 5)] := by
    rw [isTable]
    show [inst θ' (cell (k 0) (v 5)), inst θ' (cell (v 1) (v 8))] = _
    rw [cell, cell, inst_spine, inst_spine]
    show [groundSpine (e cellSym) [e 0, θ' 5], groundSpine (e cellSym) [θ' 1, θ' 8]] = _
    rw [eight]
    rfl
  rw [← produce]
  exact readsAs

/-- **The rule at a wrong value**: the value `6` written into the made row and into the condition, as a
caller-supplied value would instantiate it. -/
def addStepAt (value : Tm) : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[cell (k 0) (v 0), cell (v 1) (v 2)],
    [instr (v 0) (k addOp) (v 1) (v 3) (v 4) (v 5), cell (v 3) (v 6), cell (v 4) (v 7)], [], [],
    [cell (k 0) (v 5), cell (v 1) value]⟩, []⟩
  conditions := [⟨value, addName, [v 6, v 7]⟩]

/-- The program of its table read at `6`. -/
abbrev wrongProgram : List SRule := [(addStepAt (k 6)).tableRule rows]

theorem addStepAt_restricted : (addStepAt (k 6)).RangeRestrictedWith := by
  intro t member x inT
  have produced : t = cell (k 0) (v 5) ∨ t = cell (v 1) (k 6) := by
    simpa [written, addStepAt, checkTerms] using member
  rcases produced with rfl | rfl
  · obtain rfl := vars_cell_symbol inT
    exact .inl ⟨instr (v 0) (k addOp) (v 1) (v 3) (v 4) (v 5), by simp [addStepAt], next_in_instr⟩
  · have one : x = 1 := by
      rcases mem_vars_cell.mp inT with inKey | inValue
      · exact mem_vars_var.mp inKey
      · exact absurd inValue not_mem_vars_const
    subst one
    exact .inl ⟨cell (v 1) (v 2), by simp [addStepAt], mem_vars_cell.mpr (.inl (mem_vars_var.mpr rfl))⟩

theorem wrongProgram_fragment : ∀ r ∈ wrongProgram, RangeRestrictedPositive r := by
  intro r member
  rw [List.mem_singleton.mp member]
  exact (addStepAt (k 6)).fragment_tableRule rfl rfl addStepAt_restricted

/-- **The rule with a wrong value written in is refused**: no firing of the rule at the value `6` is
admitted at `before`; its row `add a b 6` is not in the table. A statement about that rule at this state,
not about the firings of the instruction's own rule. -/
theorem wrong_value_refused (g : Firing ℕ E {r | r ∈ wrongProgram} before.frame) :
    ¬ (schematicStep ℕ wrongProgram).Admits (s := before) g := by
  intro admitted
  obtain ⟨θ', fires, -⟩ := match_of_admitted before_ground wrongProgram_fragment g admitted
  have isTable : g.rule = (addStepAt (k 6)).tableRule rows := List.mem_singleton.mp g.member
  have call : rows.row addName [v 6, v 7] (k 6) ∈ g.rule.body.read := by
    rw [isTable]
    simp [addStepAt, RuleWithCondition.calls, callRow]
  obtain ⟨o, inside, labelled⟩ := List.mem_map.mp (fires.reads _ call)
  have present : o ∈ before.present := (Finset.mem_sdiff.mp (Finset.mem_toList.mp inside)).1
  have spineForm : inst θ' (rows.row addName [v 6, v 7] (k 6)) =
      groundSpine (.sym addName) [θ' 6, θ' 7, e 6] := inst_spine θ' _ _
  rw [spineForm] at labelled
  obtain ⟨-, -, six⟩ := table_row_unique present labelled
  exact absurd (Expr.sym.inj six) (by decide)

/-! ## A rule whose made values nothing binds -/

/-- **A rule whose made values nothing binds** (a simplified shape): take the control and destination
cells, read the operand cells, make the control cell at `5` and the destination cell holding `8`, both
bound by nothing. -/
def kernelRule : SRule := ⟨PUnit.unit, ⟨[cell (k 0) (v 0), cell (v 1) (v 2)],
  [cell (v 3) (v 6), cell (v 4) (v 7)], [], [], [cell (k 0) (v 5), cell (v 1) (v 8)]⟩, []⟩

/-- **Range restriction rejects it**: the new value `8` is made and bound by nothing. -/
theorem kernelRule_not_restricted : ¬ RangeRestricted kernelRule := by
  intro restricted
  obtain ⟨t, member, inT⟩ := restricted (cell (v 1) (v 8)) (by simp [written, kernelRule]) 8
    (mem_vars_cell.mpr (.inr (mem_vars_var.mpr rfl)))
  have inPatterns : t = cell (k 0) (v 0) ∨ t = cell (v 1) (v 2) ∨ t = cell (v 3) (v 6) ∨
      t = cell (v 4) (v 7) := by
    simpa [kernelRule] using member
  rcases inPatterns with rfl | rfl | rfl | rfl
  · exact absurd (vars_cell_symbol inT) (by decide)
  · rcases vars_cell_unknowns inT with same | same <;> exact absurd same (by decide)
  · rcases vars_cell_unknowns inT with same | same <;> exact absurd same (by decide)
  · rcases vars_cell_unknowns inT with same | same <;> exact absurd same (by decide)

/-- **The add step makes the same rows as the kernel's rule**; it differs only by what it reads: the
instruction row, which binds the next counter, and the table row, which binds the new value. -/
theorem addStep_makes_the_same_rows : addStep.rule.body.produce = kernelRule.body.produce := rfl

#print axioms inst_spine
#print axioms addStep_restricted
#print axioms addTable_fragment
#print axioms right_value_admitted
#print axioms table_row_unique
#print axioms made_value_is_five
#print axioms wrong_value_refused
#print axioms kernelRule_not_restricted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelStep
