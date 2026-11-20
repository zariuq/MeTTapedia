import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Evaluation

/-!
# Evaluation along a run: the evaluated program on states that read as bags

`Evaluation` relates one evaluated firing to the point firing with the same choices. This module states what
the evaluated PROGRAM (`evaluated I P`) does along runs of every length. The class of states is the tree's
`Machines.ReadsBag` (solvable knowledge that determines the row of each present identity), which the step
keeps, where a ground state is left by the first firing.

## The evaluated rule is outside range restriction, and inside the wider fragment

A rule evaluated at points tells each value pattern equal to its value and makes rows that hold it, so the
unknowns of a value pattern are bound by a tell and by no take or read pattern: the rule is not range restricted
whenever a value pattern holds an unknown that matching does not bind (`KernelEvaluation.evalAt_not_restricted`).
It is in the wider fragment of `Determined` (`evalAt_fragment`) when the rule with conditions is **evaluable**
(`RuleWithCondition.Evaluable`: no collect pattern, only equation checks, every written unknown bound by matching
or by a condition's value, every argument anchored), and it makes determined rows as soon as the made unknowns
are so bound (`evalAt_makes`).

## The firings of the two programs, at every state

* `evaluated_to_specialized`: a rule evaluated where the interpretation answers has its point reading in the
  program at the interpretation's ground graph.
* `evaluated_to_graph`: **every admitted firing of the evaluated program is an admitted firing of the program at
  the graph, with the same choices**, at every state. No hypothesis on the state or on the rules.
* `graph_to_evaluated`: conversely, **at every state that reads as rows, every admitted firing of the program at
  the graph is an admitted firing of the evaluated program with the same choices**, for rules with anchored
  arguments: the tell of a point of the graph is solvable only at a point of the condition's own function with
  as many arguments as the condition has (`point_of_tell`).

## Along runs

* `EvalStep I ρ`: **the atomic evaluation on bags**: a firing by matching of the rule whose conditions hold at
  the interpretation, at the matched arguments.
* `evalStep_iff`: it is one rewrite of the bag by the rule evaluated at some points where the interpretation
  answers; `rewritesBy_evaluated_iff`: so rewriting by the evaluated program is the atomic evaluation of the
  program's rules.
* `evaluated_backward`, `evaluated_forward`, `evaluatedCorrespondence`: **at every state that reads as a bag, an
  admitted firing of the evaluated program is one atomic evaluation on the bag and its result reads as the
  evaluated bag; and every atomic evaluation is an admitted firing** (identities infinitely many). As an
  `OperationalCorrespondence` from the atomic evaluation on bags (`evaluation I P`) to the step of the evaluated
  program, related by `Machines.ReadsBag`, it holds along runs of every length and composes with every other
  correspondence of the tree. The backward half asks only that made unknowns are bound (`evaluated_backward`).
* `evaluated_run_reads`: along every run of the evaluated program from a state that reads as a bag, every state
  reads as a bag; so `graph_to_evaluated` applies at every state the run reaches.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open NamesOnTheStep (Expr)
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open Presentation.Schematic (Tm SRule SState X E rowSig toTerm toTerm_injective applyTerm_toTerm inst inst_toTerm
  inst_groundPart groundPart vars_toTerm Bound written isGuard equationsOf guardOf mem_written_of_produce
  exists_zip_of_mem mem_zip_map_left)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Reads ReadsBag Rewrites)

/-! ## Rows of tables, as ground rows -/

/-- **The number of arguments of a row.** -/
def spineLength : Expr → ℕ
  | .app f _ => spineLength f + 1
  | _ => 0

theorem spineLength_groundSpine : ∀ (h : Expr) (xs : List Expr),
    spineLength (groundSpine h xs) = spineLength h + xs.length
  | _, [] => rfl
  | h, x :: xs => (spineLength_groundSpine (.app h x) xs).trans (by
      show spineLength h + 1 + xs.length = spineLength h + (xs.length + 1)
      omega)

/-- **Ground rows headed by symbols are equal exactly when the symbols and the arguments are**, with no
hypothesis on the numbers of arguments. -/
theorem groundSpine_sym_inj {a b : ℕ} {us ws : List Expr}
    (same : groundSpine (.sym a) us = groundSpine (.sym b) ws) : a = b ∧ us = ws := by
  have heads := congrArg spineHead same
  rw [spineHead_groundSpine, spineHead_groundSpine] at heads
  have lengths := congrArg spineLength same
  rw [spineLength_groundSpine, spineLength_groundSpine] at lengths
  have sameLength : us.length = ws.length := by
    change 0 + us.length = 0 + ws.length at lengths
    omega
  have symbols : a = b := Expr.sym.inj heads
  subst symbols
  exact ⟨rfl, (groundSpine_inj sameLength same).2⟩

/-- **A ground row of a table determines its function, its arguments and its value.** -/
theorem groundRow_inj {f g : ℕ} {xs ys : List Expr} {p q : Expr} (same : groundRow f xs p = groundRow g ys q) :
    f = g ∧ xs = ys ∧ p = q := by
  obtain ⟨names, whole⟩ := groundSpine_sym_inj same
  have lengths : xs.length = ys.length := by
    have counted := congrArg List.length whole
    rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton] at counted
    omega
  obtain ⟨front, back⟩ := List.append_inj whole lengths
  exact ⟨names, front, (List.cons.inj back).1⟩

/-- The instance of a row of a table. -/
theorem inst_row (θ : ℕ → Expr) (f : ℕ) (args : List Tm) (v : Tm) :
    inst θ (rows.row f args v) = groundRow f (args.map (inst θ)) (inst θ v) := by
  show inst θ (spine (.const (.sym f)) (args ++ [v])) = _
  rw [inst_spine, List.map_append]
  rfl

theorem mem_zip_map_self {α β : Type*} (f : α → β) : ∀ {l : List α} {q : α × β}, q ∈ l.zip (l.map f) →
    q.1 ∈ l ∧ q.2 = f q.1
  | [], _, inside => by simp at inside
  | a :: l, q, inside => by
      rw [List.map_cons, List.zip_cons_cons] at inside
      rcases List.mem_cons.mp inside with rfl | later
      · exact ⟨List.mem_cons_self, rfl⟩
      · obtain ⟨inL, same⟩ := mem_zip_map_self f later
        exact ⟨List.mem_cons_of_mem _ inL, same⟩

/-! ## The evaluated rule in the wider fragment -/

namespace RuleWithCondition

/-- **A rule with conditions that evaluation can run**: no collect pattern, only equation checks, every unknown
it tells, asks or makes bound by matching or by a condition's value, and every argument anchored. -/
structure Evaluable (ρ : RuleWithCondition ℕ Tm) : Prop where
  noCollect : ρ.rule.collect = []
  guards : ρ.rule.body.checks.all isGuard = true
  restricted : ρ.RangeRestrictedWith
  anchored : ρ.ArgumentsAnchored

end RuleWithCondition

section Fragment

variable (ρ : RuleWithCondition ℕ Tm) (pts : List EvalPoint) (lengths : pts.length = ρ.conditions.length)

/-- The terms the evaluated rule tells, asks or makes: the rule's, the value tells, and the asked rows. -/
theorem mem_written_evalAt {t : Tm} :
    t ∈ written (ρ.evalAt pts) ↔ t ∈ written ρ.rule ∨
      t ∈ ((ρ.conditions.zip pts).map (fun q => (q.1.value, toTerm q.2.2))).map Prod.fst ∨
      t ∈ ((ρ.conditions.zip pts).map (fun q => (q.1.value, toTerm q.2.2))).map Prod.snd ∨
      t ∈ (((ρ.calls rows).zip (ρ.pointRows pts)).map (fun q => Check.equal q.1 q.2)).flatMap checkTerms := by
  simp only [written, RuleWithCondition.evalAt, List.map_append, List.flatMap_append, List.mem_append]
  tauto

include lengths in
/-- **What a rule with conditions binds, the evaluated rule determines**: by the same patterns, or by the tell
of the value. -/
theorem evalAt_determines {x : ℕ} (binds : ρ.Binds x) : Determines (ρ.evalAt pts) x := by
  rcases binds with bound | ⟨c, inConditions, inValue⟩
  · exact .bound bound
  · obtain ⟨pt, paired⟩ := exists_zip_of_mem lengths.symm inConditions
    have told : (c.value, toTerm pt.2) ∈ (ρ.evalAt pts).body.tell :=
      List.mem_append_left _ (List.mem_map_of_mem (f := fun q : Condition ℕ Tm × EvalPoint =>
        (q.1.value, toTerm q.2.2)) paired)
    exact .toldLeft told (fun y vars => absurd vars (vars_toTerm _ _)) inValue

include lengths in
/-- **The evaluated rule makes determined rows** when every unknown of a made row is bound by matching or by a
condition's value. -/
theorem evalAt_makes (made : ∀ t : Tm, t ∈ ρ.rule.body.produce → ∀ x ∈ t.freeVars, ρ.Binds x) :
    MakesDetermined (ρ.evalAt pts) :=
  fun t inProduce x vars => evalAt_determines ρ pts lengths (made t inProduce x vars)

include lengths in
/-- **The evaluated rule of an evaluable rule with conditions is in the wider fragment.** -/
theorem evalAt_fragment (evaluable : ρ.Evaluable) : DeterminedPositive (ρ.evalAt pts) := by
  refine ⟨evaluable.noCollect, ?_, ?_⟩
  · show ((((ρ.calls rows).zip (ρ.pointRows pts)).map (fun q : Tm × Tm => Check.equal q.1 q.2)) ++
      ρ.rule.body.checks).all isGuard = true
    rw [List.all_eq_true]
    intro check inside
    rcases List.mem_append.mp inside with ask | own
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp ask
      rfl
    · exact List.all_eq_true.mp evaluable.guards check own
  · intro t inside x vars
    rcases (mem_written_evalAt ρ pts).mp inside with own | value | point | rowCheck
    · exact evalAt_determines ρ pts lengths (evaluable.restricted t own x vars)
    · obtain ⟨pair, inValues, rfl⟩ := List.mem_map.mp value
      obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp inValues
      exact evalAt_determines ρ pts lengths (.inr ⟨q.1, (List.of_mem_zip inZip).1, vars⟩)
    · obtain ⟨pair, inValues, rfl⟩ := List.mem_map.mp point
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp inValues
      exact absurd vars (vars_toTerm _ _)
    · obtain ⟨check, inChecks, inCheck⟩ := List.mem_flatMap.mp rowCheck
      obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp inChecks
      simp only [checkTerms, List.mem_cons, List.not_mem_nil, or_false] at inCheck
      rcases inCheck with rfl | rfl
      · obtain ⟨c, inConditions, isCall⟩ := List.mem_map.mp (List.of_mem_zip inZip).1
        rw [← isCall] at vars
        rcases (mem_vars_callRow c).mp vars with ⟨u, inArguments, inU⟩ | inValue
        · exact evalAt_determines ρ pts lengths (evaluable.anchored c inConditions u inArguments x inU)
        · exact evalAt_determines ρ pts lengths (.inr ⟨c, inConditions, inValue⟩)
      · obtain ⟨point, -, isPoint⟩ := List.mem_map.mp (List.of_mem_zip inZip).2
        rw [← isPoint] at vars
        exact absurd vars (vars_toTerm _ _)

end Fragment

/-- **The rules of the program an interpretation evaluates are in the wider fragment**, for evaluable rules with
conditions. -/
theorem evaluated_fragment {I : Interpretation ℕ Expr} {P : Set (RuleWithCondition ℕ Tm)}
    (evaluable : ∀ ρ ∈ P, ρ.Evaluable) : ∀ r ∈ evaluated I P, DeterminedPositive r := by
  rintro r ⟨ρ, inP, pts, lengths, -, rfl⟩
  exact evalAt_fragment ρ pts lengths (evaluable ρ inP)

/-- **The rules of the evaluated program make determined rows**, when made unknowns are bound by matching or by
a condition's value. -/
theorem evaluated_makes {I : Interpretation ℕ Expr} {P : Set (RuleWithCondition ℕ Tm)}
    (made : ∀ ρ ∈ P, ∀ t : Tm, t ∈ ρ.rule.body.produce → ∀ x ∈ t.freeVars, ρ.Binds x) :
    ∀ r ∈ evaluated I P, MakesDetermined r := by
  rintro r ⟨ρ, inP, pts, lengths, -, rfl⟩
  exact evalAt_makes ρ pts lengths (made ρ inP)

/-! ## The firings of the evaluated program and of the program at the graph -/

section Programs

variable {O : Type} [DecidableEq O] {I : Interpretation ℕ Expr} {P : Set (RuleWithCondition ℕ Tm)}

/-- **A rule evaluated where an interpretation answers has its point reading in the program at the
interpretation's ground graph.** -/
theorem evaluated_to_specialized {ρ : RuleWithCondition ℕ Tm} (member : ρ ∈ P) {pts : List EvalPoint}
    (lengths : pts.length = ρ.conditions.length)
    (answers : ∀ q ∈ ρ.conditions.zip pts, I q.1.name q.2.1 = some q.2.2) :
    ρ.at rows (ρ.pointRows pts) ∈ specialized rows (groundGraph I) P := by
  refine at_mem_specialized member ?_ fun g inside => ?_
  · simp [RuleWithCondition.pointRows, lengths]
  · obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp inside
    exact pointRow_mem_groundGraph (answers q inZip)

omit [DecidableEq O] in
/-- Every firing of a program whose rule is `ρ` evaluated at points is the evaluated firing of its choices. -/
theorem eq_evalFiring {Q : Program (OneFrame.Terms Tm)} (f : Firing O E Q PUnit.unit)
    {ρ : RuleWithCondition ℕ Tm} {pts : List EvalPoint} (member : ρ.evalAt pts ∈ Q)
    (isRule : f.rule = ρ.evalAt pts) :
    f = evalFiring ρ pts member ⟨f.opening, f.selection.taken, f.selection.read, [], f.selection.made,
      f.seen⟩ := by
  obtain ⟨rule, inQ, ⟨⟩, opening, ⟨taken, read, made⟩, seen⟩ := f
  obtain rfl : rule = ρ.evalAt pts := isRule
  rfl

/-- **Every admitted firing of the evaluated program is an admitted firing of the program at the graph, with the
same choices**, at every state: it is the evaluated firing of a rule of the program at points where the
interpretation answers, and the point firing at those points' rows is admitted. -/
theorem evaluated_to_graph (s : SState O) (f : Firing O E (evaluated I P) PUnit.unit)
    (admitted : (step X O E (evaluated I P)).Admits (s := s) f) :
    ∃ (ρ : RuleWithCondition ℕ Tm) (pts : List EvalPoint) (c : Choice O (Subst rowSig))
      (mE : ρ.evalAt pts ∈ evaluated I P)
      (mP : ρ.at rows (ρ.pointRows pts) ∈ specialized rows (groundGraph I) P),
      ρ ∈ P ∧ f = evalFiring ρ pts mE c ∧
      (step X O E (specialized rows (groundGraph I) P)).Admits (s := s)
        (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c) := by
  obtain ⟨ρ, inP, pts, lengths, answered, isRule⟩ := f.member
  obtain ⟨c, hc⟩ : ∃ c : Choice O (Subst rowSig),
      c = ⟨f.opening, f.selection.taken, f.selection.read, [], f.selection.made, f.seen⟩ := ⟨_, rfl⟩
  have mE : ρ.evalAt pts ∈ evaluated I P := ⟨ρ, inP, pts, lengths, answered, rfl⟩
  have mP := evaluated_to_specialized inP lengths fun q inside => (answered q inside).1
  have same : f = evalFiring ρ pts mE c := by
    rw [hc]
    exact eq_evalFiring f mE isRule
  have admitted' : (step X O E (evaluated I P)).Admits (s := s) (evalFiring ρ pts mE c) := same ▸ admitted
  exact ⟨ρ, pts, c, mE, mP, inP, same,
    eval_to_point s ρ pts lengths (fun q inside => (answered q inside).2) mE mP c admitted'⟩

omit [DecidableEq O] in
/-- **A solvable tell of a point of the graph is at a point of the condition's own function**: if a solution
sends a call row to a row of the ground graph, that row is the row of a point of evaluation of the condition, with
as many arguments as the condition has, where the interpretation answers. -/
theorem point_of_tell {σ : Subst rowSig} {d : Condition ℕ Tm} {g : Tm} (onGraph : g ∈ groundGraph I)
    (told : σ.applyTerm (callRow rows d) = g) :
    ∃ pt : EvalPoint, I d.name pt.1 = some pt.2 ∧ pt.1.length = d.arguments.length ∧ g = pointRow d pt := by
  obtain ⟨f, args, v, answers, rfl⟩ := onGraph
  have ground := (inst_groundPart σ (callRow rows d) _ told).1
  rw [show callRow rows d = rows.row d.name d.arguments d.value from rfl, inst_row] at ground
  obtain ⟨names, arguments, -⟩ := groundRow_inj ground
  subst names
  refine ⟨(args, v), answers, ?_, rfl⟩
  have counted := congrArg List.length arguments
  rw [List.length_map] at counted
  exact counted.symm

omit [DecidableEq O] in
/-- Points of the graph, one for each condition and each the row of a point of evaluation of its condition, are
the rows of a list of points of evaluation where the interpretation answers. -/
theorem exists_points : ∀ (cs : List (Condition ℕ Tm)) (points : List Tm), points.length = cs.length →
    (∀ q ∈ cs.zip points, ∃ pt : EvalPoint, I q.1.name pt.1 = some pt.2 ∧
      pt.1.length = q.1.arguments.length ∧ q.2 = pointRow q.1 pt) →
    ∃ pts : List EvalPoint, pts.length = cs.length ∧
      (cs.zip pts).map (fun q => pointRow q.1 q.2) = points ∧
      ∀ q ∈ cs.zip pts, I q.1.name q.2.1 = some q.2.2 ∧ q.2.1.length = q.1.arguments.length
  | [], [], _, _ => ⟨[], rfl, rfl, fun _ inside => by simp at inside⟩
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | c :: cs, g :: points, lengths, each => by
      obtain ⟨pt, answers, argLength, same⟩ := each (c, g) List.mem_cons_self
      obtain ⟨pts, ptsLength, mapped, answered⟩ := exists_points cs points (Nat.succ.inj lengths)
        (fun q inside => each q (List.mem_cons_of_mem _ inside))
      refine ⟨pt :: pts, by rw [List.length_cons, List.length_cons, ptsLength], ?_, ?_⟩
      · rw [List.zip_cons_cons, List.map_cons, mapped]
        exact congrArg (fun row => row :: points) same.symm
      · intro q inside
        rw [List.zip_cons_cons] at inside
        rcases List.mem_cons.mp inside with rfl | later
        · exact ⟨answers, argLength⟩
        · exact answered q later

/-- **At every state that reads as rows, every admitted firing of the program at the graph is an admitted firing
of the evaluated program with the same choices**, for rules with anchored arguments. -/
theorem graph_to_evaluated (anchored : ∀ ρ ∈ P, ρ.ArgumentsAnchored) {s : SState O} {rowsOf : O → Expr}
    (reads : Reads s rowsOf) (h : Firing O E (specialized rows (groundGraph I) P) PUnit.unit)
    (admitted : (step X O E (specialized rows (groundGraph I) P)).Admits (s := s) h) :
    ∃ (ρ : RuleWithCondition ℕ Tm) (pts : List EvalPoint) (c : Choice O (Subst rowSig))
      (mE : ρ.evalAt pts ∈ evaluated I P)
      (mP : ρ.at rows (ρ.pointRows pts) ∈ specialized rows (groundGraph I) P),
      ρ ∈ P ∧ h = pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c ∧
      (step X O E (evaluated I P)).Admits (s := s) (evalFiring ρ pts mE c) := by
  obtain ⟨ρ, inP, points, length, onGraph, isRule⟩ := h.member
  obtain ⟨c, hc⟩ : ∃ c : Choice O (Subst rowSig),
      c = ⟨h.opening, h.selection.taken, h.selection.read, [], h.selection.made, h.seen⟩ := ⟨_, rfl⟩
  have member : ρ.at rows points ∈ specialized rows (groundGraph I) P := at_mem_specialized inP length onGraph
  have same : h = pointFiring (A := Presentation.Schematic.A) ρ points member c := by
    rw [hc]
    exact eq_pointFiring h member isRule []
  have admitted' : (step X O E (specialized rows (groundGraph I) P)).Admits (s := s)
      (pointFiring (A := Presentation.Schematic.A) ρ points member c) := same ▸ admitted
  obtain ⟨-, -, -, ⟨_, σ, solved⟩, -⟩ := (admits_iff _).mp admitted'
  -- each tell of a point is solved, so each point is a row of a point of evaluation of its condition
  have each : ∀ q ∈ ρ.conditions.zip points, ∃ pt : EvalPoint, I q.1.name pt.1 = some pt.2 ∧
      pt.1.length = q.1.arguments.length ∧ q.2 = pointRow q.1 pt := by
    intro q inside
    have inTell : (callRow rows q.1, q.2) ∈ (ρ.at rows points).body.tell :=
      List.mem_append_left _ (mem_zip_map_left (f := callRow rows) inside)
    have told : σ.applyTerm (c.opening.applyTerm (callRow rows q.1)) = σ.applyTerm (c.opening.applyTerm q.2) :=
      (pointFiring (A := Presentation.Schematic.A) ρ points member c).tell_solved (b := PUnit.unit) solved
        (List.mem_map_of_mem (f := fun pair : Tm × Tm =>
          (c.opening.applyTerm pair.1, c.opening.applyTerm pair.2)) inTell)
    have isGraph := onGraph q.2 (List.of_mem_zip inside).2
    obtain ⟨f, args, v, -, isRow⟩ := id isGraph
    rw [isRow, applyTerm_toTerm, applyTerm_toTerm, ← isRow, ← Subst.applyTerm_comp] at told
    exact point_of_tell isGraph told
  obtain ⟨pts, lengths, mapped, answered⟩ := exists_points ρ.conditions points length each
  subst mapped
  have mE : ρ.evalAt pts ∈ evaluated I P := ⟨ρ, inP, pts, lengths, answered, rfl⟩
  exact ⟨ρ, pts, c, mE, member, inP, same,
    (eval_iff_point_reads s ρ pts lengths (fun q inside => (answered q inside).2) mE member c reads
      (anchored ρ inP)).mpr admitted'⟩

end Programs

/-! ## The atomic evaluation on bags -/

/-- **The atomic evaluation on bags**: a firing by matching of the rule whose conditions are evaluated by
the interpretation at the matched arguments, atomically. -/
def EvalStep (I : Interpretation ℕ Expr) (ρ : RuleWithCondition ℕ Tm) (A A' : Multiset Expr) : Prop :=
  ∃ (θ : ℕ → Expr) (rest : Multiset Expr),
    (ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest = A ∧ (∀ q ∈ ρ.rule.body.read, inst θ q ∈ rest) ∧
    (∀ e ∈ equationsOf ρ.rule, inst θ e.1 = inst θ e.2) ∧
    (∀ c ∈ ρ.conditions, I c.name (c.arguments.map (inst θ)) = some (inst θ c.value)) ∧
    A' = (ρ.rule.body.produce.map (inst θ) : Multiset Expr) + rest

section Bags

variable {I : Interpretation ℕ Expr} (ρ : RuleWithCondition ℕ Tm) (pts : List EvalPoint)
  (lengths : pts.length = ρ.conditions.length)

include lengths in
/-- **The equations of the evaluated rule hold at an instantiation** exactly when the rule's own do, each value
pattern's instance is its point's value, and each call row's instance is its point's row. -/
theorem equations_evalAt_iff (θ : ℕ → Expr) :
    (∀ e ∈ equationsOf (ρ.evalAt pts), inst θ e.1 = inst θ e.2) ↔
      (∀ e ∈ equationsOf ρ.rule, inst θ e.1 = inst θ e.2) ∧
      ∀ q ∈ ρ.conditions.zip pts, inst θ q.1.value = q.2.2 ∧
        inst θ (callRow rows q.1) = groundRow q.1.name q.2.1 q.2.2 := by
  have askMem : ∀ q ∈ ρ.conditions.zip pts, Check.equal (callRow rows q.1) (pointRow q.1 q.2) ∈
      (ρ.evalAt pts).body.checks := by
    intro q inside
    have pair : (callRow rows q.1, pointRow q.1 q.2) ∈ (ρ.calls rows).zip (ρ.pointRows pts) := by
      rw [calls_zip_pointRows ρ pts lengths]
      exact List.mem_map_of_mem inside
    exact List.mem_append_left _ (List.mem_map_of_mem (f := fun q : Tm × Tm => Check.equal q.1 q.2) pair)
  constructor
  · intro all
    refine ⟨fun e inside => all e ?_, fun q inside => ⟨?_, ?_⟩⟩
    · rcases List.mem_append.mp inside with told | guarded
      · exact List.mem_append_left _ (List.mem_append_right _ told)
      · obtain ⟨check, inChecks, inGuard⟩ := List.mem_flatMap.mp guarded
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨check, List.mem_append_right _ inChecks, inGuard⟩)
    · have told := all (q.1.value, toTerm q.2.2) (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun q : Condition ℕ Tm × EvalPoint => (q.1.value, toTerm q.2.2)) inside)))
      exact told.trans (inst_toTerm θ q.2.2)
    · have asked := all (callRow rows q.1, pointRow q.1 q.2) (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, askMem q inside, List.mem_singleton_self _⟩))
      exact asked.trans (inst_toTerm θ _)
  · rintro ⟨own, conditions⟩ e inside
    rcases List.mem_append.mp inside with told | guarded
    · rcases List.mem_append.mp told with value | ownTell
      · obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp value
        exact (conditions q inZip).1.trans (inst_toTerm θ q.2.2).symm
      · exact own e (List.mem_append_left _ ownTell)
    · obtain ⟨check, inChecks, inGuard⟩ := List.mem_flatMap.mp guarded
      rcases List.mem_append.mp inChecks with ask | ownCheck
      · obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp ask
        rw [calls_zip_pointRows ρ pts lengths] at inPairs
        obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp inPairs
        have isPair : e = (callRow rows q.1, pointRow q.1 q.2) := List.mem_singleton.mp inGuard
        subst isPair
        exact (conditions q inZip).2.trans (inst_toTerm θ _).symm
      · exact own e (List.mem_append_right _ (List.mem_flatMap.mpr ⟨check, ownCheck, inGuard⟩))

end Bags

/-- **The atomic evaluation of a rule is one rewrite of the bag by the rule evaluated at points where the
interpretation answers**, with as many arguments as the conditions have. -/
theorem evalStep_iff (I : Interpretation ℕ Expr) (ρ : RuleWithCondition ℕ Tm) (B B' : Multiset Expr) :
    EvalStep I ρ B B' ↔ ∃ pts : List EvalPoint, pts.length = ρ.conditions.length ∧
      (∀ q ∈ ρ.conditions.zip pts, I q.1.name q.2.1 = some q.2.2 ∧ q.2.1.length = q.1.arguments.length) ∧
      Rewrites [ρ.evalAt pts] B B' := by
  constructor
  · rintro ⟨θ, rest, split, reads, equations, conditions, out⟩
    have paired : ∀ q ∈ ρ.conditions.zip (ρ.conditions.map fun c : Condition ℕ Tm =>
        ((c.arguments.map (inst θ), inst θ c.value) : EvalPoint)),
        q.1 ∈ ρ.conditions ∧ q.2 = (q.1.arguments.map (inst θ), inst θ q.1.value) := fun q inside =>
      mem_zip_map_self _ inside
    refine ⟨ρ.conditions.map fun c => (c.arguments.map (inst θ), inst θ c.value), List.length_map _,
      fun q inside => ?_, ρ.evalAt _, List.mem_singleton_self _, θ, rest, split, reads, ?_, out⟩
    · obtain ⟨inConditions, isPoint⟩ := paired q inside
      rw [isPoint]
      exact ⟨conditions q.1 inConditions, List.length_map _⟩
    · refine (equations_evalAt_iff ρ _ (List.length_map _) θ).mpr ⟨equations, fun q inside => ?_⟩
      obtain ⟨-, isPoint⟩ := paired q inside
      rw [isPoint]
      exact ⟨rfl, inst_row θ q.1.name q.1.arguments q.1.value⟩
  · rintro ⟨pts, lengths, answered, r, member, θ, rest, split, reads, equations, out⟩
    obtain rfl := List.mem_singleton.mp member
    obtain ⟨own, conditions⟩ := (equations_evalAt_iff ρ pts lengths θ).mp equations
    refine ⟨θ, rest, split, reads, own, fun c inConditions => ?_, out⟩
    obtain ⟨pt, paired⟩ := exists_zip_of_mem lengths.symm inConditions
    obtain ⟨value, asked⟩ := conditions (c, pt) paired
    obtain ⟨answers, -⟩ := answered (c, pt) paired
    have row : groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) = groundRow c.name pt.1 pt.2 :=
      (inst_row θ c.name c.arguments c.value).symm.trans asked
    obtain ⟨-, arguments, -⟩ := groundRow_inj row
    rw [arguments, value]
    exact answers

/-- **Rewriting of a bag by the evaluated program is the atomic evaluation of a rule of the program.** -/
theorem rewritesBy_evaluated_iff {I : Interpretation ℕ Expr} {P : Set (RuleWithCondition ℕ Tm)}
    {B B' : Multiset Expr} : RewritesBy (evaluated I P) B B' ↔ ∃ ρ ∈ P, EvalStep I ρ B B' := by
  constructor
  · rintro ⟨r, ⟨ρ, inP, pts, lengths, answered, rfl⟩, single⟩
    exact ⟨ρ, inP, (evalStep_iff I ρ B B').mpr ⟨pts, lengths, answered, single⟩⟩
  · rintro ⟨ρ, inP, evaluates⟩
    obtain ⟨pts, lengths, answered, single⟩ := (evalStep_iff I ρ B B').mp evaluates
    exact ⟨ρ.evalAt pts, ⟨ρ, inP, pts, lengths, answered, rfl⟩, single⟩

/-! ## The evaluated program along runs -/

section Runs

variable {O : Type} [DecidableEq O] {I : Interpretation ℕ Expr} {P : Set (RuleWithCondition ℕ Tm)}

/-- **An admitted firing of the evaluated program, at a state that reads as a bag, is one atomic evaluation on
the bag, and its result reads as the evaluated bag**, when made unknowns are bound by matching or by a
condition's value. The value made is the interpretation's value at the rows the state reads. -/
theorem evaluated_backward (made : ∀ ρ ∈ P, ∀ t : Tm, t ∈ ρ.rule.body.produce → ∀ x ∈ t.freeVars, ρ.Binds x)
    {s : SState O} {bag : Multiset Expr} (reads : ReadsBag s bag)
    (f : Firing O E (evaluated I P) s.frame) (admitted : (step X O E (evaluated I P)).Admits (s := s) f) :
    ∃ bag', (∃ ρ ∈ P, EvalStep I ρ bag bag') ∧ ReadsBag (f.result X s) bag' := by
  obtain ⟨bag', rewrites, reads'⟩ :=
    readsBag_backward_determined reads f admitted (evaluated_makes made f.rule f.member)
  exact ⟨bag', rewritesBy_evaluated_iff.mp ⟨f.rule, f.member, rewrites⟩, reads'⟩

/-- **Every atomic evaluation on the bag a state reads as is an admitted firing of the evaluated program whose
result reads as the evaluated bag**, for evaluable rules, when identities are infinitely many. -/
theorem evaluated_forward [Infinite O] (evaluable : ∀ ρ ∈ P, ρ.Evaluable) {s : SState O}
    {bag bag' : Multiset Expr} (reads : ReadsBag s bag) {ρ : RuleWithCondition ℕ Tm} (member : ρ ∈ P)
    (evaluates : EvalStep I ρ bag bag') :
    ∃ (f : Firing O E (evaluated I P) s.frame) (_ : (step X O E (evaluated I P)).Admits (s := s) f),
      ReadsBag (f.result X s) bag' := by
  obtain ⟨pts, lengths, answered, single⟩ := (evalStep_iff I ρ bag bag').mp evaluates
  obtain ⟨f, admitted, -, reads'⟩ := readsBag_forward_determined (P := evaluated I P) (r := ρ.evalAt pts)
    ⟨ρ, member, pts, lengths, answered, rfl⟩ (evalAt_fragment ρ pts lengths (evaluable ρ member)) reads single
  exact ⟨f, admitted, reads'⟩

/-- **The atomic evaluation of a program's rules on bags, as a system.** -/
def evaluation (I : Interpretation ℕ Expr) (P : Set (RuleWithCondition ℕ Tm)) : GSLT :=
  equalityGSLT (Multiset Expr) (fun B B' => ∃ ρ ∈ P, EvalStep I ρ B B')

/-- **The evaluated program and the atomic evaluation on bags, along runs**: one firing for one evaluation each
way, related by reading a state as a bag. -/
def evaluatedCorrespondence [Infinite O] (evaluable : ∀ ρ ∈ P, ρ.Evaluable) :
    OperationalCorrespondence (evaluation I P) (programSystem O (evaluated I P)) where
  related bag s := ReadsBag s bag
  readStep := by
    intro bag s s' reads stepped
    obtain ⟨f, admitted, rfl⟩ := stepped
    obtain ⟨bag', evaluates, reads'⟩ :=
      evaluated_backward (fun ρ inP t inProduce x vars =>
        (evaluable ρ inP).restricted t (mem_written_of_produce inProduce) x vars) reads f admitted
    exact Or.inr ⟨bag', evaluates, reads'⟩
  forward := by
    intro bag bag' s reads evaluates
    obtain ⟨ρ, member, single⟩ := evaluates
    obtain ⟨f, admitted, reads'⟩ := evaluated_forward evaluable reads member single
    exact ⟨_, (executionPath_nonempty_iff_multiStep (programSystem O (evaluated I P)) _ _).mpr
      (.step ⟨f, admitted, rfl⟩ (.refl _)), reads'⟩

/-- **Along every run of the evaluated program, from a state that reads as a bag, every state reads as a
bag.** -/
theorem evaluated_run_reads (made : ∀ ρ ∈ P, ∀ t : Tm, t ∈ ρ.rule.body.produce → ∀ x ∈ t.freeVars, ρ.Binds x)
    {s t : SState O} (run : Relation.ReflTransGen (Succ (step X O E (evaluated I P)).toStep) s t)
    (reads : ∃ bag, ReadsBag s bag) : ∃ bag, ReadsBag t bag :=
  readsBag_of_run (evaluated_makes made) run reads

end Runs

#print axioms groundRow_inj
#print axioms evalAt_fragment
#print axioms evaluated_fragment
#print axioms evaluated_to_specialized
#print axioms evaluated_to_graph
#print axioms point_of_tell
#print axioms graph_to_evaluated
#print axioms equations_evalAt_iff
#print axioms evalStep_iff
#print axioms rewritesBy_evaluated_iff
#print axioms evaluated_backward
#print axioms evaluated_forward
#print axioms evaluatedCorrespondence
#print axioms evaluated_run_reads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
