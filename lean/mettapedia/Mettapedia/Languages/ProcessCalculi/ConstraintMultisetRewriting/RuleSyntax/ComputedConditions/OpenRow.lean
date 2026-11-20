import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Evaluation

/-!
# Control: a row that holds an unknown nothing determines

`eval_iff_point_reads` asks a state that reads as rows; `eval_iff_point` asks a ground state. Here is a state
that is neither, with the arguments anchored: a rule whose condition's argument IS bound by a read
(`probe_anchored`), at a state whose one row holds an unknown that its knowledge does not determine (`openRow`,
`openRow_not_ground`, `openRow_not_read`). The point reading fires: its tell binds the row's unknown to the
point's argument (`probe_point_admitted`). The evaluation is refused: the argument is not determined
(`probe_eval_refused`). So the two readings admit the same firings only where the state determines its rows; at
a row that holds an unknown the evaluation is the smaller of the two.

The same row is the control for the hypothesis `Fixed` of `tableFiring_admits_iff`: as a stored row of a table
it is a point that is not fixed, its table read is admitted and the rule at that point is refused
(`box_not_fixed`, `nullary_table_admitted`, `nullary_point_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.OpenRow

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Presentation.Schematic (Tm SRule SState GroundLabels X E rowSig toTerm toTerm_injective applyTerm_toTerm
  mem_vars_var not_mem_vars_const vars_toTerm inst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Reads)

/-- A box holding one term. -/
def box (t : Tm) : Tm := spine (.const (.sym 1)) [t]

theorem applyTerm_box (τ : Subst rowSig) (t : Tm) : τ.applyTerm (box t) = box (τ.applyTerm t) := by
  rw [box, applyTerm_spine]
  rfl

theorem mem_vars_box {x : ℕ} {t : Tm} : x ∈ (box t).freeVars ↔ x ∈ t.freeVars := by
  rw [box, mem_vars_spine]
  constructor
  · rintro (inHead | ⟨u, member, inU⟩)
    · exact absurd inHead not_mem_vars_const
    · rw [List.mem_singleton.mp member] at inU
      exact inU
  · intro inside
    exact .inr ⟨t, List.mem_singleton_self _, inside⟩

/-- **The rule**: read a box holding `a`, let `r := f(a)` (`f` the symbol `3`), make `9 r`. Unknowns: `0`
the argument, `1` the value. -/
def probe : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[], [box (.var 0)], [], [], [spine (.const (.sym 9)) [.var 1]]⟩, []⟩
  conditions := [⟨.var 1, 3, [.var 0]⟩]

/-- **Its argument is bound by the read.** -/
theorem probe_anchored : probe.ArgumentsAnchored := by
  intro c inside t inArguments x inT
  rw [show probe.conditions = [⟨.var 1, 3, [.var 0]⟩] from rfl, List.mem_singleton] at inside
  subst inside
  rw [List.mem_singleton.mp inArguments] at inT
  rw [mem_vars_var.mp inT]
  exact .inl ⟨box (.var 0), by simp [probe], mem_vars_box.mpr (mem_vars_var.mpr rfl)⟩

/-- **A state whose one row is a box holding the unknown `100`**, with no knowledge. -/
def openRow : SState ℕ := ⟨PUnit.unit, [], {0}, fun _ => box (.var 100)⟩

/-- The state is not ground. -/
theorem openRow_not_ground : ¬ ∃ rowsOf : ℕ → Expr, GroundLabels openRow rowsOf := by
  rintro ⟨rowsOf, ground⟩
  have labelled : box (.var 100) = toTerm (rowsOf 0) := ground 0 (by simp [openRow])
  have inside : 100 ∈ (box (.var 100)).freeVars := mem_vars_box.mpr (mem_vars_var.mpr rfl)
  rw [labelled] at inside
  exact vars_toTerm _ _ inside

/-- **The state reads as no rows**: its knowledge is empty, so the identity solves it and reads the row as
itself, a term with an unknown. -/
theorem openRow_not_read : ¬ ∃ rowsOf : ℕ → Expr, Reads openRow rowsOf := by
  rintro ⟨rowsOf, reads⟩
  have labelled : (Subst.id rowSig).applyTerm (box (.var 100)) = toTerm (rowsOf 0) :=
    reads.reads (Subst.id rowSig) (fun _ inside => absurd inside List.not_mem_nil) 0 (by simp [openRow])
  rw [Subst.applyTerm_id] at labelled
  have inside : 100 ∈ (box (.var 100)).freeVars := mem_vars_box.mpr (mem_vars_var.mpr rfl)
  rw [labelled] at inside
  exact vars_toTerm _ _ inside

/-- The choices: the identity opening, nothing taken, the row read, the made identity `1`. -/
def choice : Choice ℕ (Subst rowSig) := ⟨Subst.id rowSig, [], [0], [], [1], []⟩

/-- The identity opens a rule whose terms do not mention the unknown `100` freshly at `openRow`. -/
theorem fresh_openRow {P : Program (OneFrame.Terms Tm)} (f : Firing ℕ E P PUnit.unit)
    (identity : f.opening = Subst.id rowSig) (apart : ∀ t ∈ f.rule.terms, ∀ x ∈ t.freeVars, x ≠ 100) :
    f.Fresh X openRow := by
  intro b g h
  let u : Subst rowSig := fun x : ℕ => if x = 100 then g 100 else h x
  refine ⟨u, fun t mentioned => ?_, fun t inside => ?_⟩
  · rcases mentioned with inKnowledge | inKnowledge | ⟨o, -, rfl⟩
    · exact absurd inKnowledge List.not_mem_nil
    · exact absurd inKnowledge List.not_mem_nil
    · show u.applyTerm ((Subst.id rowSig).applyTerm (box (.var 100))) = g.applyTerm (box (.var 100))
      rw [Subst.applyTerm_id, applyTerm_box, applyTerm_box]
      rfl
  · show u.applyTerm (f.opening.applyTerm t) = h.applyTerm t
    rw [identity, Subst.applyTerm_id]
    refine Subst.applyTerm_congr fun x inX => ?_
    show (if x = 100 then g 100 else h x) = h x
    rw [if_neg (apart t inside x inX)]

/-- The unknowns of the call row are `0` and `1`. -/
theorem vars_call {x : ℕ} (inside : x ∈ (callRow rows (⟨.var 1, 3, [.var 0]⟩ : Condition ℕ Tm)).freeVars) :
    x ≠ 100 := by
  rcases (mem_vars_callRow _).mp inside with ⟨t, inArguments, inT⟩ | inValue
  · rw [List.mem_singleton.mp inArguments] at inT
    rw [mem_vars_var.mp inT]
    decide
  · rw [mem_vars_var.mp inValue]
    decide

theorem vars_made {x : ℕ} (inside : x ∈ (spine (.const (.sym 9)) [(.var 1 : Tm)]).freeVars) : x ≠ 100 := by
  rcases (mem_vars_spine _ _).mp inside with inHead | ⟨u, member, inU⟩
  · exact absurd inHead not_mem_vars_const
  · rw [List.mem_singleton.mp member] at inU
    rw [mem_vars_var.mp inU]
    decide

theorem vars_read {x : ℕ} (inside : x ∈ (box (.var 0)).freeVars) : x ≠ 100 := by
  rw [mem_vars_var.mp (mem_vars_box.mp inside)]
  decide

/-- **The point reading fires at the open row**: the tell of the call row binds the row's unknown to `7`. -/
theorem probe_point_admitted :
    (step X ℕ E {probe.at rows (probe.pointRows argumentPoints)}).Admits (s := openRow)
      (pointFiring (A := Presentation.Schematic.A) probe (probe.pointRows argumentPoints)
        (Set.mem_singleton _) choice) := by
  refine (admits_iff _).mpr ⟨fresh_openRow _ rfl ?_, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, fun check inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · intro t inside x inX
    have cases : t = box (.var 0) ∨ t = callRow rows ⟨.var 1, 3, [.var 0]⟩ ∨
        t = pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5) ∨ t = spine (.const (.sym 9)) [.var 1] := by
      simpa [Rule.terms, pointFiring, probe, RuleWithCondition.at, RuleWithCondition.calls,
        RuleWithCondition.pointRows, argumentPoints, checkTerms] using inside
    rcases cases with rfl | rfl | rfl | rfl
    · exact vars_read inX
    · exact vars_call inX
    · exact absurd inX (vars_toTerm _ _)
    · exact vars_made inX
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pointFiring, choice, openRow, Selection.commit]
  · let σ : Subst rowSig := fun x => if x = 1 then toTerm (.sym 5) else toTerm (.sym 7)
    refine ⟨PUnit.unit, σ, fun eq inside => ?_⟩
    have cases : eq = ((Subst.id rowSig).applyTerm (box (.var 0)), (Subst.id rowSig).applyTerm (box (.var 100))) ∨
        eq = ((Subst.id rowSig).applyTerm (callRow rows ⟨.var 1, 3, [.var 0]⟩),
          (Subst.id rowSig).applyTerm (pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5))) := by
      simp [Firing.information, Firing.matching, Firing.opened, Firing.row, RuleInstance.map, pointFiring, choice,
        openRow, Frames.applyStore, probe, argumentPoints, RuleWithCondition.pointRows, RuleWithCondition.calls,
        RuleWithCondition.at] at inside
      exact inside
    rcases cases with rfl | rfl
    · show σ.applyTerm ((Subst.id rowSig).applyTerm (box (.var 0))) =
        σ.applyTerm ((Subst.id rowSig).applyTerm (box (.var 100)))
      rw [Subst.applyTerm_id, Subst.applyTerm_id, applyTerm_box, applyTerm_box]
      rfl
    · show σ.applyTerm ((Subst.id rowSig).applyTerm (callRow rows ⟨.var 1, 3, [.var 0]⟩)) =
        σ.applyTerm ((Subst.id rowSig).applyTerm (pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5)))
      rw [Subst.applyTerm_id, Subst.applyTerm_id, argument_call σ (.sym 7) rfl rfl]
      exact (applyTerm_toTerm σ _).symm

/-- **The evaluation is refused at the open row**: the read binds the argument to the row's unknown, which
nothing determines; the ask fails at the solution sending it to `8`. -/
theorem probe_eval_refused :
    ¬ (step X ℕ E {probe.evalAt argumentPoints}).Admits (s := openRow)
      (evalFiring probe argumentPoints (Set.mem_singleton _) choice) := by
  intro admitted
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff _).mp admitted
  let σ : Subst rowSig := fun x => if x = 1 then toTerm (.sym 5) else toTerm (.sym 8)
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) σ
      ((evalFiring probe argumentPoints (Set.mem_singleton _) choice).information X openRow) := by
    intro eq inside
    have cases : eq = ((Subst.id rowSig).applyTerm (box (.var 0)), (Subst.id rowSig).applyTerm (box (.var 100))) ∨
        eq = ((Subst.id rowSig).applyTerm (.var 1), (Subst.id rowSig).applyTerm (toTerm (.sym 5))) := by
      simp [Firing.information, Firing.matching, Firing.opened, Firing.row, RuleInstance.map, evalFiring, choice,
        openRow, Frames.applyStore, probe, argumentPoints, RuleWithCondition.evalAt] at inside
      exact inside
    rcases cases with rfl | rfl
    · show σ.applyTerm ((Subst.id rowSig).applyTerm (box (.var 0))) =
        σ.applyTerm ((Subst.id rowSig).applyTerm (box (.var 100)))
      rw [Subst.applyTerm_id, Subst.applyTerm_id, applyTerm_box, applyTerm_box]
      rfl
    · show σ.applyTerm ((Subst.id rowSig).applyTerm (Term.var 1)) =
        σ.applyTerm ((Subst.id rowSig).applyTerm (toTerm (.sym 5)))
      rw [Subst.applyTerm_id, Subst.applyTerm_id, applyTerm_toTerm]
      rfl
  have member : Check.map (Subst.id rowSig).applyTerm
      (.equal (callRow rows ⟨.var 1, 3, [.var 0]⟩) (pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5))) ∈
      ((((probe.calls rows).zip (probe.pointRows argumentPoints)).map
        (fun q : Tm × Tm => Check.equal q.1 q.2)) ++ []).map (Check.map (Subst.id rowSig).applyTerm) :=
    List.mem_map_of_mem (List.mem_append_left _
      (List.mem_map_of_mem (f := fun q : Tm × Tm => Check.equal q.1 q.2)
        (a := (callRow rows ⟨.var 1, 3, [.var 0]⟩, pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5)))
        (by simp [RuleWithCondition.calls, RuleWithCondition.pointRows, probe, argumentPoints])))
  have asked := checks _ member PUnit.unit σ solved
  change σ.applyTerm ((Subst.id rowSig).applyTerm (callRow rows ⟨.var 1, 3, [.var 0]⟩)) =
    σ.applyTerm ((Subst.id rowSig).applyTerm (pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5))) at asked
  rw [Subst.applyTerm_id, Subst.applyTerm_id, argument_call σ (.sym 8) rfl rfl] at asked
  have rows' := toTerm_injective (asked.trans (applyTerm_toTerm σ _))
  exact absurd rows' (by decide)

/-! ## Control: a stored row of a table that is not fixed

`tableFiring_admits_iff` asks the points to be fixed by every substitution (`Fixed`). The open row is also a
row of the table of the function `1` of no argument, `1 x`, with its value an unknown: a point that is not
fixed (`box_not_fixed`). The rule `nullary` (let `r := 1()`, make `9 r`) reads it: the table read is admitted
(`nullary_table_admitted`), and the rule at that point, with the same choices, is refused
(`nullary_point_refused`): the point is then a term of the rule, and the rule's opening, the identity, is not
fresh for an unknown the state mentions. The other hypotheses of `tableFiring_admits_iff` hold
(`nullary_labels`). -/

/-- The substitutions that read every unknown as the row `5`, and as the row `6`. -/
def allFive : Subst rowSig := fun _ => toTerm (.sym 5)
def allSix : Subst rowSig := fun _ => toTerm (.sym 6)

/-- **The open row is not fixed.** -/
theorem box_not_fixed : ¬ Fixed Presentation.Schematic.A (box (.var 100)) := by
  intro fixed
  have same : allFive.applyTerm (box (.var 100)) = box (.var 100) := fixed allFive
  rw [applyTerm_box] at same
  have inside : 100 ∈ (box (.var 100)).freeVars := mem_vars_box.mpr (mem_vars_var.mpr rfl)
  rw [← same] at inside
  have ground : 100 ∈ (toTerm (.sym 5) : Tm).freeVars := mem_vars_box.mp inside
  exact vars_toTerm _ _ ground

/-- **The rule**: let `r := 1()`, make `9 r`. -/
def nullary : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[], [], [], [], [spine (.const (.sym 9)) [.var 1]]⟩, []⟩
  conditions := [⟨.var 1, 1, []⟩]

/-- The choices: the identity opening, the table row `0`, the made identity `1`. -/
def tableChoice : Choice ℕ (Subst rowSig) := ⟨Subst.id rowSig, [], [], [0], [1], []⟩

/-- The table row read is labelled by the point. -/
theorem nullary_labels : tableChoice.tables.map openRow.label = [box (.var 100)] := rfl

/-- **The table read of the open row is admitted.** -/
theorem nullary_table_admitted :
    (step X ℕ E {nullary.tableRule rows}).Admits (s := openRow)
      (tableFiring (A := Presentation.Schematic.A) nullary (Set.mem_singleton _) tableChoice) := by
  refine (admits_iff _).mpr ⟨fresh_openRow _ rfl ?_, ⟨List.nodup_nil, List.nodup_singleton 1, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, fun check inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · intro t inside x inX
    have cases : t = callRow rows ⟨.var 1, 1, []⟩ ∨ t = spine (.const (.sym 9)) [.var 1] := by
      simpa [Rule.terms, tableFiring, nullary, RuleWithCondition.tableRule, RuleWithCondition.calls,
        checkTerms] using inside
    rcases cases with rfl | rfl
    · rcases (mem_vars_callRow _).mp inX with ⟨u, inArguments, -⟩ | inValue
      · exact absurd inArguments List.not_mem_nil
      · rw [mem_vars_var.mp inValue]
        decide
    · exact vars_made inX
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [tableFiring, tableChoice, openRow, Selection.commit]
  · refine ⟨PUnit.unit, allFive, fun eq inside => ?_⟩
    have isRead : eq = ((Subst.id rowSig).applyTerm (box (.var 1)), (Subst.id rowSig).applyTerm (box (.var 100))) := by
      simp [Firing.information, Firing.matching, Firing.opened, Firing.row, RuleInstance.map, tableFiring,
        tableChoice, openRow, Frames.applyStore, nullary, RuleWithCondition.calls,
        RuleWithCondition.tableRule] at inside
      exact inside
    subst isRead
    show allFive.applyTerm ((Subst.id rowSig).applyTerm (box (.var 1))) =
      allFive.applyTerm ((Subst.id rowSig).applyTerm (box (.var 100)))
    rw [Subst.applyTerm_id, Subst.applyTerm_id, applyTerm_box, applyTerm_box]
    rfl

/-- **The rule at the point that is not fixed is refused, with the same choices**: its opening is not fresh
for the unknown the point shares with the state. -/
theorem nullary_point_refused :
    ¬ (step X ℕ E {nullary.at rows [box (.var 100)]}).Admits (s := openRow)
      (pointFiring (A := Presentation.Schematic.A) nullary [box (.var 100)] (Set.mem_singleton _)
        tableChoice) := by
  intro admitted
  obtain ⟨fresh, -⟩ := (admits_iff _).mp admitted
  obtain ⟨u, onState, onRule⟩ := fresh PUnit.unit allFive allSix
  have atState : u.applyTerm ((Subst.id rowSig).applyTerm (box (.var 100))) = allFive.applyTerm (box (.var 100)) :=
    onState (box (.var 100)) (.inr (.inr ⟨0, by simp [openRow], rfl⟩))
  have atRule : u.applyTerm ((Subst.id rowSig).applyTerm (box (.var 100))) = allSix.applyTerm (box (.var 100)) :=
    onRule (box (.var 100)) (by
      simp [Rule.terms, pointFiring, nullary, RuleWithCondition.at, RuleWithCondition.calls])
  have same := atState.symm.trans atRule
  rw [applyTerm_box, applyTerm_box] at same
  have grounded := congrArg (inst fun _ => Expr.sym 0) same
  rw [box, box, inst_spine, inst_spine] at grounded
  have lists := (groundSpine_inj (by simp) grounded).2
  have clash : (Expr.sym 5 : Expr) = .sym 6 := (List.cons.inj lists).1
  exact absurd clash (by decide)

#print axioms box_not_fixed
#print axioms nullary_table_admitted
#print axioms nullary_point_refused
#print axioms probe_anchored
#print axioms openRow_not_ground
#print axioms openRow_not_read
#print axioms probe_point_admitted
#print axioms probe_eval_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.OpenRow
