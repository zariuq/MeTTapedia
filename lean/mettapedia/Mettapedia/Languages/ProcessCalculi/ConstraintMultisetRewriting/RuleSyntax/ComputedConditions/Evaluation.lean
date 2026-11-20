import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Tables
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Rows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Determined

/-!
# Evaluating a condition: the call row asked, the value told

Host code evaluates a computed condition when the firing is chosen: it computes the function at the
arguments the match has determined and binds the value pattern. On the step this is **the rule
evaluated at points** (`RuleWithCondition.evalAt`): for each condition and a point of evaluation
(ground arguments and the value there), it **asks** that the call row be the point's row (a check: every
solution of the information must agree, and the ask binds nothing) and **tells** the value pattern
equal to the value. The rule at points of `Syntax` (`RuleWithCondition.at`) **tells** the whole call row
equal to the point's row: its arguments too.

So the two readings differ exactly in whether the arguments are told or asked. Both theorems below relate the
evaluation to the POINT reading (the rule at points of the graph, which reads no stored row); the stored row
is the further step `tableFiring_admits_iff`, which also asks the row present and not taken.

* `models_point_iff`, `models_eval_iff`: the solutions of the two informations; the point reading's
  solutions are the evaluation's solutions that also send each call's arguments to its point's.
* `evalFiring_admits_iff`: **the evaluated firing is admitted exactly when the point firing is admitted
  and the information of the evaluated firing determines the arguments** (asks each call row equal to
  its point).
* `eval_to_point`: **an admitted evaluation is an admitted point firing with the same choices**, at every
  state and for every rule. This half has no hypothesis on the state or on the arguments.
* `determined_of_reads`, `eval_iff_point_reads`: conversely, **at every state that reads as rows**
  (`Machines.Reads`: solvable knowledge that determines the row of each present identity), when every unknown
  of every argument is anchored (`ArgumentsAnchored`), an admitted point firing determines the arguments; so
  there **the two readings admit the same firings**, with information of the same solutions
  (`models_eval_iff_point`). States that read as rows are closed under the step of the evaluated program
  (`Runs`), so this holds at every state a run reaches, not only at the first.
* `determined_of_anchored`, `eval_iff_point`: the instances at ground states. A ground state is left by one
  firing (the made row is labelled by an opened term and the binding is kept as knowledge:
  `KernelEvaluation.result_not_ground`), so these two alone are about the first firing of a run.

## Which hypothesis on the arguments

`ArgumentsAnchored` asks every unknown of an argument to occur in a take or read pattern or in the value
pattern of SOME condition, its own included. It is what the theorems above assume. `WellModed` (`Rows`) is
stronger: each argument uses only unknowns of the take and read patterns or of the value patterns of EARLIER
conditions, which is what an evaluation that computes arguments before values can perform
(`anchored_of_wellModed`). The difference is real: `r := f(r)` is anchored, is not well moded, and its
evaluation is admitted at a fixed point of `f` (`selfCall_anchored`, `selfCall_not_wellModed`,
`selfCall_eval_admitted`).

## Controls

* `argumentOnly`, `argumentOnly_point_admitted`, `argumentOnly_eval_refused`: a rule whose condition's
  argument is mentioned by nothing else. At a ground state, the point reading is admitted (the tell of the
  point binds the argument: it enumerates the graph), and the evaluation is refused (nothing determines the
  argument, so the ask fails at some solution). It fails exactly `ArgumentsAnchored`.
* The state must read as rows: `OpenRow.probe_point_admitted`, `OpenRow.probe_eval_refused` (a row that holds
  an unknown nothing determines; the arguments are anchored).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Mettapedia.Logic.LP
open NamesOnTheStep (Expr)
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Presentation.Schematic (Tm SRule SState GroundLabels X E rowSig RowFunction args2 head tail fin_app app_inj
  toTerm toTerm_injective applyTerm_toTerm agree_of_applyTerm_eq mem_vars_var not_mem_vars_const Bound)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Reads)

/-! ## Spines under substitution -/

/-- **Substitution goes inside a spine.** -/
theorem applyTerm_spine (σ : Subst rowSig) : ∀ (h : Tm) (ts : List Tm),
    σ.applyTerm (spine h ts) = spine (σ.applyTerm h) (ts.map σ.applyTerm)
  | _, [] => rfl
  | h, t :: ts => by
      have first : σ.applyTerm (Term.app RowFunction.app (args2 h t)) =
          Term.app RowFunction.app (args2 (σ.applyTerm h) (σ.applyTerm t)) := by
        rw [Subst.applyTerm_app]
        congr 1
        funext i
        rcases fin_app i with rfl | rfl <;> rfl
      show σ.applyTerm (spine (Term.app RowFunction.app (args2 h t)) ts) =
        spine (Term.app RowFunction.app (args2 (σ.applyTerm h) (σ.applyTerm t))) (ts.map σ.applyTerm)
      rw [applyTerm_spine σ _ ts, first]

/-- **Spines of arguments of one length are equal exactly when heads and arguments are.** -/
theorem spine_inj : ∀ {h h' : Tm} {xs ys : List Tm}, xs.length = ys.length → spine h xs = spine h' ys →
    h = h' ∧ xs = ys
  | _, _, [], [], _, same => ⟨same, rfl⟩
  | _, _, [], _ :: _, lengths, _ => by simp at lengths
  | _, _, _ :: _, [], lengths, _ => by simp at lengths
  | _, _, x :: xs, y :: ys, lengths, same => by
      obtain ⟨heads, rest⟩ := spine_inj (Nat.succ.inj lengths) same
      have args := app_inj heads
      refine ⟨congrFun args head, ?_⟩
      have same' : x = y := congrFun args tail
      rw [same', rest]

theorem applyTerm_row (σ : Subst rowSig) (f : ℕ) (xs : List Tm) (p : Tm) :
    σ.applyTerm (rows.row f xs p) = rows.row f (xs.map σ.applyTerm) (σ.applyTerm p) := by
  show σ.applyTerm (spine (.const (.sym f)) (xs ++ [p])) =
    spine (.const (.sym f)) (xs.map σ.applyTerm ++ [σ.applyTerm p])
  rw [applyTerm_spine, List.map_append]
  rfl

theorem applyTerm_callRow (σ : Subst rowSig) (c : Condition ℕ Tm) :
    σ.applyTerm (callRow rows c) = rows.row c.name (c.arguments.map σ.applyTerm) (σ.applyTerm c.value) :=
  applyTerm_row σ c.name c.arguments c.value

/-- **A row of a table determines its arguments and its value.** -/
theorem row_inj {f : ℕ} {xs ys : List Tm} {p q : Tm} (lengths : xs.length = ys.length)
    (same : rows.row f xs p = rows.row f ys q) : xs = ys ∧ p = q := by
  have whole := (spine_inj (by simp [lengths]) same).2
  obtain ⟨front, back⟩ := List.append_inj whole lengths
  exact ⟨front, List.cons.inj back |>.1⟩

/-! ## The rule evaluated at points -/

/-- **A point of evaluation**: ground arguments and the ground value at them. -/
abbrev EvalPoint := List Expr × Expr

/-- The row of a point of evaluation of a condition. -/
def pointRow (c : Condition ℕ Tm) (pt : EvalPoint) : Tm := toTerm (groundRow c.name pt.1 pt.2)

theorem pointRow_eq (c : Condition ℕ Tm) (pt : EvalPoint) :
    pointRow c pt = rows.row c.name (pt.1.map toTerm) (toTerm pt.2) := toTerm_groundRow _ _ _

namespace RuleWithCondition

variable (ρ : RuleWithCondition ℕ Tm)

/-- The rows of points of evaluation, one per condition. -/
def pointRows (pts : List EvalPoint) : List Tm := (ρ.conditions.zip pts).map fun q => pointRow q.1 q.2

/-- **The rule evaluated at points**: it asks each call row equal to its point's row and tells each value
pattern equal to its point's value. -/
def evalAt (pts : List EvalPoint) : SRule where
  locals := ρ.rule.locals
  body := { ρ.rule.body with
    tell := (ρ.conditions.zip pts).map (fun q => (q.1.value, toTerm q.2.2)) ++ ρ.rule.body.tell
    checks := ((ρ.calls rows).zip (ρ.pointRows pts)).map (fun q => Check.equal q.1 q.2) ++
      ρ.rule.body.checks }
  collect := ρ.rule.collect

/-- **Every unknown of every argument is anchored**: it occurs in a take or read pattern, or in the value
pattern of some condition of the rule, its own included. Weaker than `WellModed`, which asks an earlier
condition (`anchored_of_wellModed`; control `selfCall_anchored`, `selfCall_not_wellModed`). -/
def ArgumentsAnchored : Prop :=
  ∀ c ∈ ρ.conditions, ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, ρ.Binds x

/-- Well-moded conditions are anchored. -/
theorem anchored_of_wellModedAfter :
    ∀ (bound : List Tm) (cs : List (Condition ℕ Tm)), WellModedAfter bound cs →
      (∀ u ∈ bound, ∀ x ∈ u.freeVars, Bound ρ.rule x ∨ ∃ c ∈ ρ.conditions, x ∈ c.value.freeVars) →
      cs ⊆ ρ.conditions → ∀ c ∈ cs, ∀ t ∈ c.arguments, ∀ x ∈ t.freeVars, ρ.Binds x
  | _, [], _, _, _, _, inside, _, _, _, _ => absurd inside List.not_mem_nil
  | bound, c :: cs, ⟨first, rest⟩, boundOK, sub, c', inside, t, inT, x, inX => by
      rcases List.mem_cons.mp inside with rfl | later
      · obtain ⟨u, inBound, inU⟩ := first t inT x inX
        exact boundOK u inBound x inU
      · refine anchored_of_wellModedAfter (bound ++ [c.value]) cs rest ?_
          (fun d inCs => sub (List.mem_cons_of_mem _ inCs)) c' later t inT x inX
        intro u inBound y inU
        rcases List.mem_append.mp inBound with old | new
        · exact boundOK u old y inU
        · rw [List.mem_singleton.mp new] at inU
          exact .inr ⟨c, sub List.mem_cons_self, inU⟩

theorem anchored_of_wellModed (wellModed : ρ.WellModed) : ρ.ArgumentsAnchored := by
  intro c inside t inT x inX
  refine anchored_of_wellModedAfter ρ _ ρ.conditions wellModed ?_ (fun _ member => member) c inside t inT x inX
  intro u inBound y inU
  exact .inl ⟨u, inBound, inU⟩

end RuleWithCondition

/-- **The program evaluated by an interpretation**: each rule at points of evaluation where the
interpretation answers, with arguments of the right number. -/
def evaluated (I : Interpretation ℕ Expr) (P : Set (RuleWithCondition ℕ Tm)) : Program (OneFrame.Terms Tm) :=
  {r | ∃ ρ ∈ P, ∃ pts : List EvalPoint, pts.length = ρ.conditions.length ∧
    (∀ q ∈ ρ.conditions.zip pts, I q.1.name q.2.1 = some q.2.2 ∧ q.2.1.length = q.1.arguments.length) ∧
    r = ρ.evalAt pts}

/-- The ground graph of an interpretation contains the rows of its points of evaluation. -/
theorem pointRow_mem_groundGraph {I : Interpretation ℕ Expr} {c : Condition ℕ Tm} {pt : EvalPoint}
    (answers : I c.name pt.1 = some pt.2) : pointRow c pt ∈ groundGraph I :=
  ⟨c.name, pt.1, pt.2, answers, rfl⟩

/-! ## The two firings with the same choices -/

variable {O : Type} [DecidableEq O]

/-- **The evaluated firing** with the given choices; it reads no table row. -/
def evalFiring {P : Program (OneFrame.Terms Tm)} (ρ : RuleWithCondition ℕ Tm) (pts : List EvalPoint)
    (member : ρ.evalAt pts ∈ P) (c : Choice O (Subst rowSig)) : Firing O E P PUnit.unit :=
  ⟨ρ.evalAt pts, member, PUnit.unit, c.opening, ⟨c.taken, c.read, c.made⟩, c.seen⟩

section Firings

variable (s : SState O) (ρ : RuleWithCondition ℕ Tm) (pts : List EvalPoint)
  (lengths : pts.length = ρ.conditions.length)
  (argLengths : ∀ q ∈ ρ.conditions.zip pts, q.2.1.length = q.1.arguments.length)
  {P Q : Program (OneFrame.Terms Tm)} (mE : ρ.evalAt pts ∈ P) (mP : ρ.at rows (ρ.pointRows pts) ∈ Q)
  (c : Choice O (Subst rowSig))

/-- The equations both firings share: the knowledge, the take and read equations, and the rule's own
tells, opened. -/
def baseInformation : EquationStore Tm :=
  (s.knowledge.map fun e => ((Subst.id rowSig).applyTerm e.1, (Subst.id rowSig).applyTerm e.2)) ++
    (ρ.rule.body.take.map c.opening.applyTerm).zipWith
      (fun p o => (p, (Subst.id rowSig).applyTerm (s.label o))) c.taken ++
    (ρ.rule.body.read.map c.opening.applyTerm).zipWith
      (fun p o => (p, (Subst.id rowSig).applyTerm (s.label o))) c.read

omit [DecidableEq O] in
theorem eval_information :
    (evalFiring ρ pts mE c).information X s = baseInformation s ρ c ++
      (((ρ.conditions.zip pts).map (fun q => (q.1.value, toTerm q.2.2)) ++ ρ.rule.body.tell).map
        fun pair => (c.opening.applyTerm pair.1, c.opening.applyTerm pair.2)) := rfl

omit [DecidableEq O] in
theorem point_information :
    (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).information X s =
      baseInformation s ρ c ++
      ((((ρ.calls rows).zip (ρ.pointRows pts)) ++ ρ.rule.body.tell).map
        fun pair => (c.opening.applyTerm pair.1, c.opening.applyTerm pair.2)) := rfl

omit [DecidableEq O] in
/-- One condition's call row is its point's row exactly when its arguments and its value are the
point's. -/
theorem callRow_point_iff (σ : Subst rowSig) {d : Condition ℕ Tm} {pt : EvalPoint}
    (argLength : pt.1.length = d.arguments.length) :
    σ.applyTerm (c.opening.applyTerm (callRow rows d)) = pointRow d pt ↔
      d.arguments.map (fun t => σ.applyTerm (c.opening.applyTerm t)) = pt.1.map toTerm ∧
        σ.applyTerm (c.opening.applyTerm d.value) = toTerm pt.2 := by
  rw [applyTerm_callRow, applyTerm_row, List.map_map, pointRow_eq]
  constructor
  · intro same
    exact row_inj (by simp [argLength]) same
  · rintro ⟨arguments, value⟩
    rw [show (σ.applyTerm ∘ c.opening.applyTerm) = fun t => σ.applyTerm (c.opening.applyTerm t) from rfl,
      arguments, value]

omit [DecidableEq O] in
/-- **The solutions of the point reading** are the solutions of the shared equations and the tells that
send each call row to its point's row. -/
theorem models_point_iff (σ : Subst rowSig) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) σ
        ((pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).information X s) ↔
      X.Models (a := PUnit.unit) (b := PUnit.unit) σ (baseInformation s ρ c) ∧
        (∀ e ∈ ρ.rule.body.tell, σ.applyTerm (c.opening.applyTerm e.1) = σ.applyTerm (c.opening.applyTerm e.2)) ∧
        ∀ q ∈ (ρ.calls rows).zip (ρ.pointRows pts), σ.applyTerm (c.opening.applyTerm q.1) = q.2 := by
  rw [point_information]
  show (∀ e ∈ _, _) ↔ _
  simp only [List.mem_append, List.mem_map]
  constructor
  · intro all
    refine ⟨fun e inside => all e (.inl inside), fun e inside => all _ (.inr ⟨e, .inr inside, rfl⟩),
      fun q inside => ?_⟩
    have holds := all _ (.inr ⟨q, .inl inside, rfl⟩)
    obtain ⟨q1, q2⟩ := q
    obtain ⟨point, -, rfl⟩ := List.mem_map.mp (List.of_mem_zip inside).2
    change σ.applyTerm (c.opening.applyTerm q1) =
      σ.applyTerm (c.opening.applyTerm (toTerm (groundRow point.1.name point.2.1 point.2.2))) at holds
    rw [applyTerm_toTerm, applyTerm_toTerm] at holds
    exact holds
  · rintro ⟨base, tells, calls⟩ e (inside | ⟨⟨q1, q2⟩, (inCalls | inTell), rfl⟩)
    · exact base e inside
    · obtain ⟨point, -, rfl⟩ := List.mem_map.mp (List.of_mem_zip inCalls).2
      show σ.applyTerm (c.opening.applyTerm q1) =
        σ.applyTerm (c.opening.applyTerm (toTerm (groundRow point.1.name point.2.1 point.2.2)))
      rw [applyTerm_toTerm, applyTerm_toTerm]
      exact calls _ inCalls
    · exact tells _ inTell

omit [DecidableEq O] in
/-- **The solutions of the evaluation** are the solutions of the shared equations, the rule's tells, and
the value tells. -/
theorem models_eval_iff (σ : Subst rowSig) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) σ ((evalFiring ρ pts mE c).information X s) ↔
      X.Models (a := PUnit.unit) (b := PUnit.unit) σ (baseInformation s ρ c) ∧
        (∀ e ∈ ρ.rule.body.tell, σ.applyTerm (c.opening.applyTerm e.1) = σ.applyTerm (c.opening.applyTerm e.2)) ∧
        ∀ q ∈ ρ.conditions.zip pts, σ.applyTerm (c.opening.applyTerm q.1.value) = toTerm q.2.2 := by
  rw [eval_information]
  show (∀ e ∈ _, _) ↔ _
  simp only [List.mem_append, List.mem_map]
  constructor
  · intro all
    refine ⟨fun e inside => all e (.inl inside), fun e inside => all _ (.inr ⟨e, .inr inside, rfl⟩),
      fun q inside => ?_⟩
    have holds := all _ (.inr ⟨(q.1.value, toTerm q.2.2), .inl ⟨q, inside, rfl⟩, rfl⟩)
    change σ.applyTerm (c.opening.applyTerm q.1.value) = σ.applyTerm (c.opening.applyTerm (toTerm q.2.2)) at holds
    rw [applyTerm_toTerm, applyTerm_toTerm] at holds
    exact holds
  · rintro ⟨base, tells, values⟩ e (inside | ⟨pair, (⟨q, inZip, rfl⟩ | inTell), rfl⟩)
    · exact base e inside
    · show σ.applyTerm (c.opening.applyTerm q.1.value) = σ.applyTerm (c.opening.applyTerm (toTerm q.2.2))
      rw [applyTerm_toTerm, applyTerm_toTerm]
      exact values q inZip
    · exact tells pair inTell

/-- Pairs of a list mapped, beside the pairs of the list, mapped. -/
theorem zip_map_zip {α β γ δ : Type} (f : α → γ) (g : α × β → δ) :
    ∀ (l : List α) (m : List β), l.length ≤ m.length →
      (l.map f).zip ((l.zip m).map g) = (l.zip m).map fun q => (f q.1, g q)
  | [], _, _ => rfl
  | _ :: _, [], short => by simp at short
  | a :: l, b :: m, short => by
      simp only [List.map_cons, List.zip_cons_cons]
      rw [zip_map_zip f g l m (Nat.le_of_succ_le_succ short)]

include lengths in
theorem calls_zip_pointRows : (ρ.calls rows).zip (ρ.pointRows pts) =
    (ρ.conditions.zip pts).map fun q => (callRow rows q.1, pointRow q.1 q.2) :=
  zip_map_zip (callRow rows) (fun q => pointRow q.1 q.2) ρ.conditions pts (le_of_eq lengths.symm)

/-- The terms of the rule at points: the rule's, the call rows and the points. -/
theorem mem_terms_at {points : List Tm} {t : Tm} :
    t ∈ (ρ.at rows points).terms ↔ t ∈ ρ.rule.terms ∨ t ∈ ((ρ.calls rows).zip points).map Prod.fst ∨
      t ∈ ((ρ.calls rows).zip points).map Prod.snd := by
  simp only [Rule.terms, RuleWithCondition.at_take, RuleWithCondition.at_read, RuleWithCondition.at_tell,
    RuleWithCondition.at_checks, RuleWithCondition.at_produce, RuleWithCondition.at_collect, List.map_append,
    List.mem_append]
  tauto

/-- The terms of the evaluated rule: the rule's, the value tells, and the asked rows. -/
theorem mem_terms_evalAt {t : Tm} :
    t ∈ (ρ.evalAt pts).terms ↔ t ∈ ρ.rule.terms ∨
      t ∈ ((ρ.conditions.zip pts).map (fun q => (q.1.value, toTerm q.2.2))).map Prod.fst ∨
      t ∈ ((ρ.conditions.zip pts).map (fun q => (q.1.value, toTerm q.2.2))).map Prod.snd ∨
      t ∈ (((ρ.calls rows).zip (ρ.pointRows pts)).map (fun q => Check.equal q.1 q.2)).flatMap checkTerms := by
  simp only [Rule.terms, RuleWithCondition.evalAt, List.map_append, List.flatMap_append, List.mem_append]
  tauto

/-- **The arguments are determined**: every solution of the evaluated firing's information sends each
call row to its point's row. -/
def Determined : Prop :=
  ∀ σ : Subst rowSig, X.Models (a := PUnit.unit) (b := PUnit.unit) σ ((evalFiring ρ pts mE c).information X s) →
    ∀ q ∈ (ρ.calls rows).zip (ρ.pointRows pts), σ.applyTerm (c.opening.applyTerm q.1) = q.2

omit [DecidableEq O] in
include lengths argLengths in
/-- **The point reading's solutions are the evaluation's solutions that send the calls to the points.** -/
theorem models_point_iff_eval (σ : Subst rowSig) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) σ
        ((pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).information X s) ↔
      X.Models (a := PUnit.unit) (b := PUnit.unit) σ ((evalFiring ρ pts mE c).information X s) ∧
        ∀ q ∈ (ρ.calls rows).zip (ρ.pointRows pts), σ.applyTerm (c.opening.applyTerm q.1) = q.2 := by
  rw [models_point_iff, models_eval_iff]
  constructor
  · rintro ⟨base, tells, calls⟩
    refine ⟨⟨base, tells, fun q inside => ?_⟩, calls⟩
    have call := calls (callRow rows q.1, pointRow q.1 q.2) (by
      rw [calls_zip_pointRows ρ pts lengths]
      exact List.mem_map_of_mem inside)
    exact ((callRow_point_iff c σ (argLengths q inside)).mp call).2
  · rintro ⟨⟨base, tells, -⟩, calls⟩
    exact ⟨base, tells, calls⟩

include lengths argLengths in
/-- **The evaluated firing is admitted exactly when the point firing is admitted and the evaluated firing's
information determines the arguments.** -/
theorem evalFiring_admits_iff :
    (step X O E P).Admits (s := s) (evalFiring ρ pts mE c) ↔
      (step X O E Q).Admits (s := s) (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c) ∧
        Determined s ρ pts mE c := by
  have models := models_point_iff_eval s ρ pts lengths argLengths mE mP c
  have freshIff : (evalFiring ρ pts mE c).Fresh X s ↔
      (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).Fresh X s := by
    have pointTerms : ∀ t ∈ (ρ.at rows (ρ.pointRows pts)).terms, t ∈ (ρ.evalAt pts).terms := by
      intro t inside
      rcases (mem_terms_at ρ).mp inside with ruleTerm | call | point
      · exact (mem_terms_evalAt ρ pts).mpr (.inl ruleTerm)
      · obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp call
        exact (mem_terms_evalAt ρ pts).mpr (.inr (.inr (.inr (List.mem_flatMap.mpr
          ⟨.equal q.1 q.2, List.mem_map_of_mem inZip, by simp [checkTerms]⟩))))
      · obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp point
        exact (mem_terms_evalAt ρ pts).mpr (.inr (.inr (.inr (List.mem_flatMap.mpr
          ⟨.equal q.1 q.2, List.mem_map_of_mem inZip, by simp [checkTerms]⟩))))
    have evalTerms : ∀ t ∈ (ρ.evalAt pts).terms, t ∈ (ρ.at rows (ρ.pointRows pts)).terms ∨
        (∃ q ∈ ρ.conditions.zip pts, t = q.1.value) ∨ ∃ e : Expr, t = toTerm e := by
      intro t inside
      rcases (mem_terms_evalAt ρ pts).mp inside with ruleTerm | value | point | rowCheck
      · exact .inl ((mem_terms_at ρ).mpr (.inl ruleTerm))
      · obtain ⟨pair, inValues, rfl⟩ := List.mem_map.mp value
        obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp inValues
        exact .inr (.inl ⟨q, inZip, rfl⟩)
      · obtain ⟨pair, inValues, rfl⟩ := List.mem_map.mp point
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp inValues
        exact .inr (.inr ⟨q.2.2, rfl⟩)
      · obtain ⟨check, inChecks, inCheck⟩ := List.mem_flatMap.mp rowCheck
        obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp inChecks
        simp only [checkTerms, List.mem_cons, List.not_mem_nil, or_false] at inCheck
        rcases inCheck with rfl | rfl
        · exact .inl ((mem_terms_at ρ).mpr (.inr (.inl (List.mem_map_of_mem inZip))))
        · exact .inl ((mem_terms_at ρ).mpr (.inr (.inr (List.mem_map_of_mem inZip))))
    constructor
    · intro fresh b g h
      obtain ⟨u, onState, onRule⟩ := fresh b g h
      exact ⟨u, onState, fun t inside => onRule t (pointTerms t inside)⟩
    · intro fresh b g h
      obtain ⟨u, onState, onRule⟩ := fresh b g h
      refine ⟨u, onState, fun t inside => ?_⟩
      rcases evalTerms t inside with atTerm | ⟨q, inZip, rfl⟩ | ⟨e, rfl⟩
      · exact onRule t atTerm
      · have callTerm : callRow rows q.1 ∈ (ρ.at rows (ρ.pointRows pts)).terms := by
          have pair : (callRow rows q.1, pointRow q.1 q.2) ∈ (ρ.calls rows).zip (ρ.pointRows pts) := by
            rw [calls_zip_pointRows ρ pts lengths]
            exact List.mem_map_of_mem inZip
          exact (mem_terms_at ρ).mpr (.inr (.inl (List.mem_map_of_mem (f := Prod.fst) pair)))
        have same : u.applyTerm (c.opening.applyTerm (callRow rows q.1)) = h.applyTerm (callRow rows q.1) :=
          onRule _ callTerm
        rw [applyTerm_callRow, applyTerm_row, applyTerm_callRow] at same
        exact (row_inj (by simp) same).2
      · show u.applyTerm (c.opening.applyTerm (toTerm e)) = h.applyTerm (toTerm e)
        rw [applyTerm_toTerm, applyTerm_toTerm, applyTerm_toTerm]
  show (evalFiring ρ pts mE c).Admits X s ↔
    (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).Admits X s ∧ _
  unfold Firing.Admits Firing.Shapes
  rw [freshIff]
  constructor
  · rintro ⟨shapes, enabled, ⟨_, σ₀, solved₀⟩, asks⟩
    have determined : Determined s ρ pts mE c := by
      intro σ solved q inside
      have holds := (asks PUnit.unit σ solved).1 (Check.map c.opening.applyTerm (.equal q.1 q.2))
        (List.mem_map_of_mem (List.mem_append_left _ (List.mem_map_of_mem inside)))
      have fixed : c.opening.applyTerm q.2 = q.2 ∧ σ.applyTerm q.2 = q.2 := by
        obtain ⟨q1, q2⟩ := q
        obtain ⟨point, -, rfl⟩ := List.mem_map.mp (List.of_mem_zip inside).2
        exact ⟨applyTerm_toTerm _ _, applyTerm_toTerm _ _⟩
      change σ.applyTerm (c.opening.applyTerm q.1) = σ.applyTerm (c.opening.applyTerm q.2) at holds
      rw [fixed.1, fixed.2] at holds
      exact holds
    refine ⟨⟨shapes, enabled, ⟨PUnit.unit, σ₀, (models σ₀).mpr ⟨solved₀, determined σ₀ solved₀⟩⟩, ?_⟩, determined⟩
    intro b σ solved
    have evalSolved := ((models σ).mp solved).1
    refine ⟨fun check inside => (asks b σ evalSolved).1 check ?_, (asks b σ evalSolved).2⟩
    change check ∈ ρ.rule.body.checks.map (Check.map c.opening.applyTerm) at inside
    change check ∈ ((((ρ.calls rows).zip (ρ.pointRows pts)).map (fun q => Check.equal q.1 q.2)) ++
      ρ.rule.body.checks).map (Check.map c.opening.applyTerm)
    rw [List.map_append]
    exact List.mem_append_right _ inside
  · rintro ⟨⟨shapes, enabled, ⟨_, σ₀, solved₀⟩, asks⟩, determined⟩
    refine ⟨shapes, enabled, ⟨PUnit.unit, σ₀, ((models σ₀).mp solved₀).1⟩, ?_⟩
    intro b σ solved
    have pointSolved := (models σ).mpr ⟨solved, determined σ solved⟩
    refine ⟨fun check inside => ?_, (asks b σ pointSolved).2⟩
    change check ∈ ((((ρ.calls rows).zip (ρ.pointRows pts)).map (fun q => Check.equal q.1 q.2)) ++
      ρ.rule.body.checks).map (Check.map c.opening.applyTerm) at inside
    rw [List.map_append, List.mem_append] at inside
    rcases inside with rowCheck | ruleCheck
    · obtain ⟨check₀, inRows, rfl⟩ := List.mem_map.mp rowCheck
      obtain ⟨q, inZip, rfl⟩ := List.mem_map.mp inRows
      show σ.applyTerm (c.opening.applyTerm q.1) = σ.applyTerm (c.opening.applyTerm q.2)
      have fixed : c.opening.applyTerm q.2 = q.2 ∧ σ.applyTerm q.2 = q.2 := by
        obtain ⟨q1, q2⟩ := q
        obtain ⟨point, -, rfl⟩ := List.mem_map.mp (List.of_mem_zip inZip).2
        exact ⟨applyTerm_toTerm _ _, applyTerm_toTerm _ _⟩
      rw [fixed.1, fixed.2]
      exact determined σ solved q inZip
    · exact (asks b σ pointSolved).1 check ruleCheck

omit [DecidableEq O] in
/-- Two substitutions that send a term to the same ground row agree on its unknowns. -/
theorem agree_on_ground {σ σ' θ : Subst rowSig} {p : Tm} {e : Expr}
    (one : σ.applyTerm (θ.applyTerm p) = toTerm e) (two : σ'.applyTerm (θ.applyTerm p) = toTerm e) :
    ∀ x ∈ p.freeVars, σ.applyTerm (θ x) = σ'.applyTerm (θ x) := by
  intro x inX
  rw [← Subst.applyTerm_comp] at one two
  exact agree_of_applyTerm_eq p (one.trans two.symm) x inX

include lengths argLengths in
/-- **Where every solution of the knowledge reads each present label as one ground row, an admitted point
firing of a rule with anchored arguments determines the arguments**: every solution of the evaluated firing's
information agrees with a solution of the point firing's on every anchored unknown, so it sends each call row
to its point's row. -/
theorem determined_of_read {rowsOf : O → Expr}
    (reads : ∀ τ : Subst rowSig, Presentation.Schematic.A.Models τ s.knowledge → ∀ o ∈ s.present,
      τ.applyTerm (s.label o) = toTerm (rowsOf o))
    (anchored : ρ.ArgumentsAnchored)
    (admitted : (step X O E Q).Admits (s := s)
      (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c)) :
    Determined s ρ pts mE c := by
  obtain ⟨-, ⟨_, _, takeLength, readLength, _, _⟩, enabled, ⟨_, σ', solved'⟩, -⟩ := (admits_iff _).mp admitted
  have models := models_point_iff_eval s ρ pts lengths argLengths mE mP c
  obtain ⟨evalSolved', calls'⟩ := (models σ').mp solved'
  intro σ solved q inside
  have rowAgree : ∀ {p : Tm} {o : O}, o ∈ s.present →
      σ.applyTerm (c.opening.applyTerm p) = σ.applyTerm ((Subst.id rowSig).applyTerm (s.label o)) →
      σ'.applyTerm (c.opening.applyTerm p) = σ'.applyTerm ((Subst.id rowSig).applyTerm (s.label o)) →
      ∀ x ∈ p.freeVars, σ.applyTerm (c.opening x) = σ'.applyTerm (c.opening x) := by
    intro p o present one two
    rw [Subst.applyTerm_id,
      reads σ (knowledge_of_information (s := s) (evalFiring ρ pts mE c) solved) o present] at one
    rw [Subst.applyTerm_id,
      reads σ' (knowledge_of_information (s := s)
        (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c) solved') o present] at two
    exact agree_on_ground one two
  have agree : ∀ x, ρ.Binds x → σ.applyTerm (c.opening x) = σ'.applyTerm (c.opening x) := by
    intro x binds
    rcases binds with ⟨p, inPatterns, inP⟩ | ⟨d, inConditions, inValue⟩
    · rcases List.mem_append.mp inPatterns with taken | read
      · obtain ⟨o, paired⟩ := Presentation.Schematic.exists_zip_of_mem takeLength taken
        have pairedOpen := Presentation.Schematic.mem_zip_map_left (f := c.opening.applyTerm) paired
        have present : o ∈ s.present :=
          enabled.taken_subset (List.mem_toFinset.mpr (List.of_mem_zip paired).2)
        exact rowAgree present ((evalFiring ρ pts mE c).take_solved (b := PUnit.unit) solved pairedOpen)
          ((pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).take_solved
            (b := PUnit.unit) solved' pairedOpen) x inP
      · obtain ⟨o, paired⟩ := Presentation.Schematic.exists_zip_of_mem readLength read
        have pairedOpen := Presentation.Schematic.mem_zip_map_left (f := c.opening.applyTerm) paired
        have present : o ∈ s.present :=
          enabled.kept_subset (List.mem_toFinset.mpr (List.of_mem_zip paired).2)
        exact rowAgree present ((evalFiring ρ pts mE c).read_solved (b := PUnit.unit) solved pairedOpen)
          ((pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).read_solved
            (b := PUnit.unit) solved' pairedOpen) x inP
    · obtain ⟨pt, paired⟩ := Presentation.Schematic.exists_zip_of_mem lengths.symm inConditions
      have one := ((models_eval_iff s ρ pts mE c σ).mp solved).2.2 (d, pt) paired
      have two := ((models_eval_iff s ρ pts mE c σ').mp evalSolved').2.2 (d, pt) paired
      exact agree_on_ground one two x inValue
  obtain ⟨q1, q2⟩ := q
  have inside' := inside
  rw [calls_zip_pointRows ρ pts lengths] at inside'
  obtain ⟨⟨d, pt⟩, inZip, same⟩ := List.mem_map.mp inside'
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  rw [← calls' _ inside]
  show σ.applyTerm (c.opening.applyTerm (callRow rows d)) = σ'.applyTerm (c.opening.applyTerm (callRow rows d))
  rw [← Subst.applyTerm_comp, ← Subst.applyTerm_comp]
  refine Subst.applyTerm_congr fun x inX => ?_
  rcases (mem_vars_callRow d).mp inX with ⟨t, inArguments, inT⟩ | inValue
  · exact agree x (anchored d (List.of_mem_zip inZip).1 t inArguments x inT)
  · exact agree x (.inr ⟨d, (List.of_mem_zip inZip).1, inValue⟩)

include lengths argLengths in
/-- **At a state that reads as rows, an admitted point firing of a rule with anchored arguments determines the
arguments.** -/
theorem determined_of_reads {rowsOf : O → Expr} (reads : Reads s rowsOf) (anchored : ρ.ArgumentsAnchored)
    (admitted : (step X O E Q).Admits (s := s)
      (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c)) :
    Determined s ρ pts mE c :=
  determined_of_read s ρ pts lengths argLengths mE mP c reads.reads anchored admitted

include lengths argLengths in
/-- **At a ground state, an admitted point firing of a rule with anchored arguments determines the
arguments.** The instance of `determined_of_read` at ground labels. -/
theorem determined_of_anchored {rowsOf : O → Expr} (ground : GroundLabels s rowsOf)
    (anchored : ρ.ArgumentsAnchored)
    (admitted : (step X O E Q).Admits (s := s)
      (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c)) :
    Determined s ρ pts mE c :=
  determined_of_read s ρ pts lengths argLengths mE mP c
    (fun τ _ o present => by rw [ground o present, applyTerm_toTerm]) anchored admitted

include lengths argLengths in
/-- **An admitted evaluation is an admitted point firing with the same choices**, at every state and for every
rule: no hypothesis on the state, and none on the arguments. -/
theorem eval_to_point (admitted : (step X O E P).Admits (s := s) (evalFiring ρ pts mE c)) :
    (step X O E Q).Admits (s := s) (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c) :=
  ((evalFiring_admits_iff s ρ pts lengths argLengths mE mP c).mp admitted).1

include lengths argLengths in
/-- **At every state that reads as rows the evaluation and the point reading admit the same firings**, for a
rule with anchored arguments. -/
theorem eval_iff_point_reads {rowsOf : O → Expr} (reads : Reads s rowsOf) (anchored : ρ.ArgumentsAnchored) :
    (step X O E P).Admits (s := s) (evalFiring ρ pts mE c) ↔
      (step X O E Q).Admits (s := s) (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c) := by
  rw [evalFiring_admits_iff s ρ pts lengths argLengths mE mP c]
  exact ⟨fun both => both.1, fun admitted =>
    ⟨admitted, determined_of_reads s ρ pts lengths argLengths mE mP c reads anchored admitted⟩⟩

include lengths argLengths in
/-- **At a ground state the evaluation and the point reading admit the same firings** for a rule with
anchored arguments. A ground state is the state before the first firing of a run; for the states a run
reaches, `eval_iff_point_reads`. -/
theorem eval_iff_point {rowsOf : O → Expr} (ground : GroundLabels s rowsOf)
    (anchored : ρ.ArgumentsAnchored) :
    (step X O E P).Admits (s := s) (evalFiring ρ pts mE c) ↔
      (step X O E Q).Admits (s := s) (pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c) := by
  rw [evalFiring_admits_iff s ρ pts lengths argLengths mE mP c]
  exact ⟨fun both => both.1, fun admitted =>
    ⟨admitted, determined_of_anchored s ρ pts lengths argLengths mE mP c ground anchored admitted⟩⟩

include lengths argLengths in
/-- **With the evaluated firing admitted, the two informations have the same solutions**: the results
differ only in how their knowledge is written. -/
theorem models_eval_iff_point (admitted : (step X O E P).Admits (s := s) (evalFiring ρ pts mE c))
    (σ : Subst rowSig) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) σ ((evalFiring ρ pts mE c).information X s) ↔
      X.Models (a := PUnit.unit) (b := PUnit.unit) σ
        ((pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).information X s) := by
  have determined := ((evalFiring_admits_iff s ρ pts lengths argLengths mE mP c).mp admitted).2
  rw [models_point_iff_eval s ρ pts lengths argLengths mE mP c]
  exact ⟨fun solved => ⟨solved, determined σ solved⟩, fun both => both.1⟩

/-- The two results have the same present rows and labels. -/
theorem eval_result_rows :
    ((evalFiring ρ pts mE c).result X s).present =
        ((pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).result X s).present ∧
      ((evalFiring ρ pts mE c).result X s).label =
        ((pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c).result X s).label :=
  ⟨rfl, rfl⟩

end Firings

/-! ## Solving the information of a firing by a match -/

section Match

variable {O : Type} {P : Program (OneFrame.Terms Tm)}

open Presentation.Schematic (lift applyTerm_lift TrivialKnowledge inst)

/-- An equation of the information matching a pattern with a selected row. -/
theorem mem_matching_rows {s : SState O} (f : Firing O E P PUnit.unit) {patterns : List Tm} {selected : List O}
    {e : Equation Tm} (member : e ∈ f.matching X s (patterns.map f.opening.applyTerm) selected) :
    ∃ p o, (p, o) ∈ patterns.zip selected ∧
      e = (f.opening.applyTerm p, (Subst.id rowSig).applyTerm (s.label o)) := by
  unfold Firing.matching at member
  rw [← List.map_uncurry_zip_eq_zipWith, List.zip_map_left, List.map_map] at member
  obtain ⟨⟨p, o⟩, inside, rfl⟩ := List.mem_map.mp member
  exact ⟨p, o, inside, rfl⟩

/-- **A match solves the information**: at a ground state with trivial knowledge, a firing that opens its
rule by the identity, whose take and read patterns' instances are the labels of the selected rows and
whose tells have equal instances, has its information solved by the match as a substitution. -/
theorem models_lift {s : SState O} {rowsOf : O → Expr} (ground : GroundLabels s rowsOf)
    (knowledge : TrivialKnowledge s.knowledge) (f : Firing O E P PUnit.unit) (identity : f.opening = Subst.id rowSig)
    (θ : ℕ → Expr)
    (takes : ∀ x ∈ f.rule.body.take.zip f.selection.taken, x.2 ∈ s.present ∧ inst θ x.1 = rowsOf x.2)
    (reads : ∀ x ∈ f.rule.body.read.zip f.selection.read, x.2 ∈ s.present ∧ inst θ x.1 = rowsOf x.2)
    (tells : ∀ e ∈ f.rule.body.tell, inst θ e.1 = inst θ e.2) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) (lift θ) (f.information X s) := by
  have known : X.applyStore ((E).weaken f.ext) s.knowledge = s.knowledge :=
    Frames.applyStore_id (X := X) s.knowledge
  intro e inside
  unfold Firing.information at inside
  rw [known] at inside
  simp only [List.mem_append] at inside
  rcases inside with ((old | taking) | reading) | told
  · show (lift θ).applyTerm e.1 = (lift θ).applyTerm e.2
    rw [knowledge e old]
  · obtain ⟨p, o, pair, rfl⟩ := mem_matching_rows f taking
    obtain ⟨present, matched⟩ := takes _ pair
    show (lift θ).applyTerm (f.opening.applyTerm p) =
      (lift θ).applyTerm ((Subst.id rowSig).applyTerm (s.label o))
    rw [identity, Subst.applyTerm_id, Subst.applyTerm_id, ground o present, applyTerm_toTerm, applyTerm_lift,
      matched]
  · obtain ⟨p, o, pair, rfl⟩ := mem_matching_rows f reading
    obtain ⟨present, matched⟩ := reads _ pair
    show (lift θ).applyTerm (f.opening.applyTerm p) =
      (lift θ).applyTerm ((Subst.id rowSig).applyTerm (s.label o))
    rw [identity, Subst.applyTerm_id, Subst.applyTerm_id, ground o present, applyTerm_toTerm, applyTerm_lift,
      matched]
  · obtain ⟨pair, inTell, rfl⟩ := List.mem_map.mp told
    show (lift θ).applyTerm (f.opening.applyTerm pair.1) = (lift θ).applyTerm (f.opening.applyTerm pair.2)
    rw [identity, Subst.applyTerm_id, Subst.applyTerm_id, applyTerm_lift, applyTerm_lift, tells pair inTell]

/-- **The identity opens a rule freshly at a ground state with no knowledge.** -/
theorem identity_fresh {s : SState O} {rowsOf : O → Expr} (ground : GroundLabels s rowsOf)
    (noKnowledge : s.knowledge = []) (f : Firing O E P PUnit.unit) (identity : f.opening = Subst.id rowSig) :
    f.Fresh X s := by
  intro b g h
  refine ⟨h, fun t mentioned => ?_, fun t _ => ?_⟩
  · rcases mentioned with inKnowledge | inKnowledge | ⟨o, present, rfl⟩
    · rw [noKnowledge] at inKnowledge
      exact absurd inKnowledge List.not_mem_nil
    · rw [noKnowledge] at inKnowledge
      exact absurd inKnowledge List.not_mem_nil
    · show h.applyTerm ((Subst.id rowSig).applyTerm (s.label o)) = g.applyTerm (s.label o)
      rw [Subst.applyTerm_id, ground o present, applyTerm_toTerm, applyTerm_toTerm]
  · show h.applyTerm (f.opening.applyTerm t) = h.applyTerm t
    rw [identity, Subst.applyTerm_id]

end Match

/-! ## Control: an argument nothing determines -/

section ArgumentOnly

/-- **A rule whose condition's argument nothing else mentions**: `1 := f(0)`, with `f` the symbol `3`,
making `9 r`. -/
def argumentOnly : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[], [], [], [], [spine (.const (.sym 9)) [.var 1]]⟩, []⟩
  conditions := [⟨.var 1, 3, [.var 0]⟩]

/-- Its one point of evaluation: `f(7) = 5`. -/
def argumentPoints : List EvalPoint := [([.sym 7], .sym 5)]

theorem argumentOnly_not_anchored : ¬ argumentOnly.ArgumentsAnchored := by
  intro anchored
  rcases anchored ⟨.var 1, 3, [.var 0]⟩ (List.mem_singleton_self _) (.var 0) (List.mem_singleton_self _) 0
      (mem_vars_var.mpr rfl) with ⟨t, member, -⟩ | ⟨d, inConditions, inValue⟩
  · exact absurd member (by simp [argumentOnly])
  · rw [List.mem_singleton.mp inConditions] at inValue
    exact absurd (mem_vars_var.mp inValue) (by decide)

/-- The empty store. -/
def emptyStore : SState ℕ := ⟨PUnit.unit, [], ∅, fun _ => toTerm (.sym 0)⟩

theorem emptyStore_ground : GroundLabels emptyStore (fun _ => .sym 0) := fun _ _ => rfl

/-- The choices: the identity opening, nothing taken or read, the made identity `0`. -/
def argumentChoice : Choice ℕ (Subst rowSig) := ⟨Subst.id rowSig, [], [], [], [0], []⟩

theorem argument_fresh {P : Program (OneFrame.Terms Tm)} (f : Firing ℕ E P PUnit.unit)
    (identity : f.opening = Subst.id rowSig) : f.Fresh X emptyStore := by
  intro b g h
  refine ⟨h, fun t mentioned => ?_, fun t _ => ?_⟩
  · rcases mentioned with inKnowledge | inKnowledge | ⟨o, present, _⟩
    · exact absurd inKnowledge List.not_mem_nil
    · exact absurd inKnowledge List.not_mem_nil
    · exact absurd present (Finset.notMem_empty o)
  · show h.applyTerm (f.opening.applyTerm t) = h.applyTerm t
    rw [identity, Subst.applyTerm_id]

/-- The call row at a solution sending `0` to `a` and `1` to `5`. -/
theorem argument_call (σ : Subst rowSig) (a : Expr) (zero : σ 0 = toTerm a) (one : σ 1 = toTerm (.sym 5)) :
    σ.applyTerm (callRow rows ⟨.var 1, 3, [.var 0]⟩) = toTerm (groundRow 3 [a] (.sym 5)) := by
  rw [applyTerm_callRow, toTerm_groundRow]
  show rows.row 3 [σ 0] (σ 1) = _
  rw [zero, one]
  rfl

/-- **The point reading fires**: the read of the point binds the argument to `7`. -/
theorem argumentOnly_point_admitted :
    (step X ℕ E {argumentOnly.at rows (argumentOnly.pointRows argumentPoints)}).Admits (s := emptyStore)
      (pointFiring (A := Presentation.Schematic.A) argumentOnly (argumentOnly.pointRows argumentPoints)
        (Set.mem_singleton _) argumentChoice) := by
  refine (admits_iff _).mpr ⟨argument_fresh _ rfl, ⟨List.nodup_nil, List.nodup_singleton 0, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, fun check inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pointFiring, argumentChoice, emptyStore, Selection.commit]
  · let σ : Subst rowSig := fun x => if x = 0 then toTerm (.sym 7) else toTerm (.sym 5)
    refine ⟨PUnit.unit, σ, fun e inside => ?_⟩
    simp [Firing.information, Firing.matching, Firing.opened, RuleInstance.map, pointFiring, argumentChoice,
      emptyStore, Frames.applyStore, argumentOnly, argumentPoints, RuleWithCondition.pointRows,
      RuleWithCondition.calls] at inside
    subst inside
    show σ.applyTerm ((Subst.id rowSig).applyTerm (callRow rows ⟨.var 1, 3, [.var 0]⟩)) =
      σ.applyTerm ((Subst.id rowSig).applyTerm (pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5)))
    rw [Subst.applyTerm_id, Subst.applyTerm_id, argument_call σ (.sym 7) rfl rfl]
    exact (applyTerm_toTerm σ _).symm

/-- **The evaluation does not fire**: nothing determines the argument, and the ask fails at the solution
sending it to `8`. -/
theorem argumentOnly_eval_refused :
    ¬ (step X ℕ E {argumentOnly.evalAt argumentPoints}).Admits (s := emptyStore)
      (evalFiring argumentOnly argumentPoints (Set.mem_singleton _) argumentChoice) := by
  intro admitted
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff _).mp admitted
  let σ : Subst rowSig := fun x => if x = 1 then toTerm (.sym 5) else toTerm (.sym 8)
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) σ
      ((evalFiring argumentOnly argumentPoints (Set.mem_singleton _) argumentChoice).information X emptyStore) := by
    intro e inside
    simp [Firing.information, Firing.matching, Firing.opened, RuleInstance.map, evalFiring, argumentChoice,
      emptyStore, Frames.applyStore, argumentOnly, argumentPoints, RuleWithCondition.evalAt] at inside
    subst inside
    show σ.applyTerm ((Subst.id rowSig).applyTerm (Term.var 1)) =
      σ.applyTerm ((Subst.id rowSig).applyTerm (toTerm (.sym 5)))
    rw [Subst.applyTerm_id, Subst.applyTerm_id, applyTerm_toTerm]
    rfl
  have member : Check.map (Subst.id rowSig).applyTerm
      (.equal (callRow rows ⟨.var 1, 3, [.var 0]⟩) (pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5))) ∈
      ((((argumentOnly.calls rows).zip (argumentOnly.pointRows argumentPoints)).map
        (fun q : Tm × Tm => Check.equal q.1 q.2)) ++ []).map (Check.map (Subst.id rowSig).applyTerm) :=
    List.mem_map_of_mem (List.mem_append_left _
      (List.mem_map_of_mem (f := fun q : Tm × Tm => Check.equal q.1 q.2)
        (a := (callRow rows ⟨.var 1, 3, [.var 0]⟩, pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5)))
        (by simp [RuleWithCondition.calls, RuleWithCondition.pointRows, argumentOnly, argumentPoints])))
  have asked := checks _ member PUnit.unit σ solved
  change σ.applyTerm ((Subst.id rowSig).applyTerm (callRow rows ⟨.var 1, 3, [.var 0]⟩)) =
    σ.applyTerm ((Subst.id rowSig).applyTerm (pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5))) at asked
  rw [Subst.applyTerm_id, Subst.applyTerm_id, argument_call σ (.sym 8) rfl rfl] at asked
  have rows' := toTerm_injective (asked.trans (applyTerm_toTerm σ _))
  exact absurd rows' (by decide)

end ArgumentOnly

/-! ## Control: an argument anchored by its own condition's value -/

section SelfCall

/-- **`r := f(r)`**, making `9 r`: the argument is the value. -/
def selfCall : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[], [], [], [], [spine (.const (.sym 9)) [.var 1]]⟩, []⟩
  conditions := [⟨.var 1, 3, [.var 1]⟩]

/-- One point of evaluation, a fixed point: `f(5) = 5`. -/
def selfPoints : List EvalPoint := [([.sym 5], .sym 5)]

/-- **Its argument is anchored**, by the value pattern of its own condition. -/
theorem selfCall_anchored : selfCall.ArgumentsAnchored := by
  intro c inside t inArguments x inT
  rw [show selfCall.conditions = [⟨.var 1, 3, [.var 1]⟩] from rfl, List.mem_singleton] at inside
  subst inside
  rw [List.mem_singleton.mp inArguments] at inT
  exact .inr ⟨⟨.var 1, 3, [.var 1]⟩, List.mem_singleton_self _, inT⟩

/-- **It is not well moded**: no take, read or earlier condition binds the argument. -/
theorem selfCall_not_wellModed : ¬ selfCall.WellModed := by
  intro wellModed
  obtain ⟨u, member, -⟩ := wellModed.1 (.var 1) (List.mem_singleton_self _) 1 (mem_vars_var.mpr rfl)
  exact absurd member (by simp [selfCall])

/-- The point reading fires at the empty store. -/
theorem selfCall_point_admitted :
    (step X ℕ E {selfCall.at rows (selfCall.pointRows selfPoints)}).Admits (s := emptyStore)
      (pointFiring (A := Presentation.Schematic.A) selfCall (selfCall.pointRows selfPoints)
        (Set.mem_singleton _) argumentChoice) := by
  refine (admits_iff _).mpr ⟨argument_fresh _ rfl, ⟨List.nodup_nil, List.nodup_singleton 0, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, fun check inside => absurd inside List.not_mem_nil, fun q inside => absurd inside List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pointFiring, argumentChoice, emptyStore, Selection.commit]
  · let σ : Subst rowSig := fun _ => toTerm (.sym 5)
    refine ⟨PUnit.unit, σ, fun eq inside => ?_⟩
    simp [Firing.information, Firing.matching, Firing.opened, RuleInstance.map, pointFiring, argumentChoice,
      emptyStore, Frames.applyStore, selfCall, selfPoints, RuleWithCondition.pointRows,
      RuleWithCondition.calls] at inside
    subst inside
    show σ.applyTerm ((Subst.id rowSig).applyTerm (callRow rows ⟨.var 1, 3, [.var 1]⟩)) =
      σ.applyTerm ((Subst.id rowSig).applyTerm (pointRow ⟨.var 1, 3, [.var 1]⟩ ([.sym 5], .sym 5)))
    rw [Subst.applyTerm_id, Subst.applyTerm_id, applyTerm_callRow]
    exact ((applyTerm_toTerm σ _).trans (toTerm_groundRow 3 [.sym 5] (.sym 5))).symm

/-- **The evaluation fires**, at a fixed point of the function: the anchoring hypothesis is met although no
order of evaluation computes the argument before the value. -/
theorem selfCall_eval_admitted :
    (step X ℕ E {selfCall.evalAt selfPoints}).Admits (s := emptyStore)
      (evalFiring selfCall selfPoints (Set.mem_singleton _) argumentChoice) :=
  (eval_iff_point emptyStore selfCall selfPoints rfl (fun q inside => by
      simp only [selfCall, selfPoints, List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at inside
      subst inside
      rfl) (Set.mem_singleton _) (Set.mem_singleton _) argumentChoice emptyStore_ground selfCall_anchored).mpr
    selfCall_point_admitted

end SelfCall

#print axioms selfCall_anchored
#print axioms selfCall_not_wellModed
#print axioms selfCall_eval_admitted
#print axioms determined_of_read
#print axioms determined_of_reads
#print axioms eval_to_point
#print axioms eval_iff_point_reads
#print axioms applyTerm_spine
#print axioms spine_inj
#print axioms row_inj
#print axioms RuleWithCondition.anchored_of_wellModed
#print axioms models_point_iff
#print axioms models_eval_iff
#print axioms models_point_iff_eval
#print axioms evalFiring_admits_iff
#print axioms determined_of_anchored
#print axioms eval_iff_point
#print axioms models_eval_iff_point
#print axioms mem_matching_rows
#print axioms models_lift
#print axioms identity_fresh
#print axioms argumentOnly_not_anchored
#print axioms argumentOnly_point_admitted
#print axioms argumentOnly_eval_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
