import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.KernelEvaluation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.GraphRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Intensional

/-!
# The stored table along runs

## The run theorems of `Intensional`, at an instance, and what they do not relate

`runs_points_to_stored` and `runs_stored_to_points` relate two restricted relations, relative to one finite set
of table identities fixed before the run. **Instance**: the add step is blind to every row headed by the symbol
of `add` (`addStep_blind`); the machine state `KernelEvaluation.noTable` stores that graph at the missing
identity `5`, which its label function labels `add 2 3 5` (`stores`); the admitted point firing is a step of
the source relation (`one_pointStep`); so the table reads have the run from the state with the row present
(`stored_run_exists`). **Control** (`graph_fires`, `no_pointStep`): at the empty store the program at a graph
of one point has an admitted firing, and for no choice of table identities is there a `PointStep` from that
state. The source relation is not the step of the program at the graph.

## Without table identities fixed before the run

On states that read as bags (`Machines.ReadsBag`) a stored table is rows of the bag, and no identity is chosen
before the run.

* `table_to_eval`: a table read at a store whose tables are true (`TrueTables`: every row of the store that is
  a row of the table of a called function is a row of the graph of the interpretation) is an evaluation at the
  same store, with the same result.
* `eval_to_table`: an evaluation at a bag is a table read at the bag beside the rows of the graph it uses,
  finitely many.
* `storedReadback`, an `OperationalReadback`: rewriting of bags by the table reads is read back as the atomic
  evaluation on the same bags, at stores whose tables are true, for rules that make no row of a table
  (`MakesNoTableRow`). `storedStepReadback` composes it with `stepCorrespondence`: the step of the program of
  table reads is read back as the atomic evaluation.
* `stored_run_to_evaluated`: every run of `RuleSyntax.step` at the program of table reads, from a state that
  reads as a store whose tables are true, ends at a state that reads as such a store, and the evaluated program
  has a run between states that read as the same two stores, from every state that reads as the first.
* `evaluated_run_to_stored`: every run of the evaluated program from a state that reads as a bag `B` to one
  that reads as `B'` gives finitely many rows `T` of the graph, the rows the run uses, such that the program of
  table reads has a run from every state that reads as `B + T` to a state that reads as `B' + T`.

* `stored_run_to_graph`, `graph_run_to_stored`: the same two statements with the program at the graph
  (`specialized rows (groundGraph I) P`) in place of the evaluated program, through `GraphRuns`.

The second direction is per run: the store is found from the run. The first direction is at every store. The
rows of the store have identities of their own in any state that reads as the bag (`exists_stored`).

**Controls.** For `TrueTables`: a wrong stored row gives a wrong value
(`Controls.wrong_row_admits_wrong_value`). For `MakesNoTableRow`: a rule that makes a row of the table
(`liar`) leaves, after one firing from the empty store, a store whose tables are not true
(`liar_breaks_tables`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.StoredRuns

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open NamesOnTheStep (Expr)
open Interface (Frames)
open Presentation.Schematic (Tm SRule SState X E rowSig toTerm toTerm_injective inst inst_toTerm equationsOf)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (ReadsBag Rewrites)
open KernelStep (addStep addName cellSym instrSym cell instr k v addOp e)
open KernelEvaluation (addPoints addChoice noTable)

/-! ## The run theorems of `Intensional` at an instance -/

/-- **The rows of the table of `add`**: every ground row headed by its symbol. -/
def addRows : Set Tm := {t | ∃ args value, t = toTerm (groundRow addName args value)}

theorem addRows_fixed : ∀ g ∈ addRows, Fixed Presentation.Schematic.A g := by
  rintro g ⟨args, value, rfl⟩
  exact fixed_toTerm _

/-- A substituted row headed by a symbol is a row of the table of that symbol only. -/
theorem head_apart (σ : Subst rowSig) (n : ℕ) (ts : List Tm) {f : ℕ} {args : List Expr} {value : Expr}
    (same : σ.applyTerm (spine (k n) ts) = toTerm (groundRow f args value)) : n = f := by
  have heads : spineHead (inst (fun _ => .sym 0) (σ.applyTerm (spine (k n) ts))) =
      spineHead (inst (fun _ => .sym 0) (toTerm (groundRow f args value))) := by rw [same]
  rw [applyTerm_spine, inst_spine, spineHead_groundSpine, inst_toTerm, groundRow,
    spineHead_groundSpine] at heads
  have symbols : (Expr.sym n : Expr) = .sym f := heads
  exact Expr.sym.inj symbols

/-- **The add step is blind to the table of `add`**: its patterns are cells and an instruction row. -/
theorem addStep_blind : Blind Presentation.Schematic.A addRows addStep.rule := by
  rintro σ g ⟨args, value, rfl⟩ p inside equated
  have patterns : p = cell (k 0) (v 0) ∨ p = cell (v 1) (v 2) ∨
      p = instr (v 0) (k addOp) (v 1) (v 3) (v 4) (v 5) ∨ p = cell (v 3) (v 6) ∨ p = cell (v 4) (v 7) := by
    simpa [addStep, checkRegion] using inside
  have same : σ.applyTerm p = toTerm (groundRow addName args value) := equated
  rcases patterns with rfl | rfl | rfl | rfl | rfl
  · exact absurd (head_apart σ cellSym _ same) (by decide)
  · exact absurd (head_apart σ cellSym _ same) (by decide)
  · exact absurd (head_apart σ instrSym _ same) (by decide)
  · exact absurd (head_apart σ cellSym _ same) (by decide)
  · exact absurd (head_apart σ cellSym _ same) (by decide)

/-- **The machine state without the table row stores the graph at the missing identity `5`**: its label
function labels `5` by `add 2 3 5`. -/
theorem stores : StoresGraph Presentation.Schematic.A addRows noTable {5} :=
  ⟨by simp [noTable], fun o inside => by
    rw [Finset.mem_singleton] at inside
    subst inside
    exact ⟨⟨[e 2, e 3], e 5, rfl⟩, fixed_toTerm _⟩⟩

theorem add_member : addStep.at rows (addStep.pointRows addPoints) ∈ specialized rows addRows {addStep} :=
  at_mem_specialized (Set.mem_singleton _) rfl (fun g inside => by
    rw [show addStep.pointRows addPoints = [toTerm (groundRow addName [e 2, e 3] (e 5))] from rfl,
      List.mem_singleton] at inside
    exact ⟨[e 2, e 3], e 5, inside⟩)

/-- The point firing of `KernelEvaluation`, as a firing of the program at the graph. -/
abbrev pointFired : Firing ℕ E (specialized rows addRows {addStep}) PUnit.unit :=
  pointFiring (A := Presentation.Schematic.A) addStep (addStep.pointRows addPoints) add_member addChoice

theorem pointFired_admitted :
    (step X ℕ E (specialized rows addRows {addStep})).Admits (s := noTable) pointFired :=
  (admits_iff _).mpr ((admits_iff _).mp KernelEvaluation.point_admitted)

/-- **A step of the source relation of `runs_points_to_stored`**, at the table identity `5`. -/
theorem one_pointStep :
    PointStep Presentation.Schematic.A rows addRows {addStep} {5} noTable
      ((step X ℕ E (specialized rows addRows {addStep})).result pointFired pointFired_admitted) :=
  ⟨pointFired, pointFired_admitted, ⟨addStep, Set.mem_singleton _, addStep.pointRows addPoints, rfl, rfl, [5],
    fun o inside => by
      rw [List.mem_singleton.mp inside]
      exact Finset.mem_singleton_self _, rfl⟩,
    fun o inside => by
      have made : o = 6 ∨ o = 7 := by simpa [pointFiring, addChoice] using inside
      rw [Finset.mem_singleton]
      omega, rfl⟩

/-- **The run theorem at an instance**: the table reads have a run from the state with the row `add 2 3 5`
present to the end state of the point run with that row present. -/
theorem stored_run_exists :
    Relation.ReflTransGen (StoredStep Presentation.Schematic.A rows {addStep} {5}) (withTables noTable {5})
      (withTables ((step X ℕ E (specialized rows addRows {addStep})).result pointFired pointFired_admitted)
        {5}) :=
  (runs_points_to_stored addRows_fixed (fun ρ inside => by
      rw [Set.mem_singleton_iff.mp inside]
      exact addStep_blind) stores (.single one_pointStep)).1

/-! ## Control: a firing of the program at the graph that is no step of the source relation -/

/-- The graph of one point, `f(7) = 5`. -/
def onePoint : Set Tm := {pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5)}

/-- The program at that graph of the rule `argumentOnly`. -/
abbrev graphProgram : Program (OneFrame.Terms Tm) := specialized rows onePoint {argumentOnly}

theorem graph_member : argumentOnly.at rows (argumentOnly.pointRows argumentPoints) ∈ graphProgram :=
  at_mem_specialized (Set.mem_singleton _) rfl (fun g inside => by
    rw [show argumentOnly.pointRows argumentPoints = [pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5)] from rfl,
      List.mem_singleton] at inside
    exact Set.mem_singleton_iff.mpr inside)

/-- **The program at the graph has an admitted firing at the empty store.** -/
theorem graph_fires :
    (step X ℕ E graphProgram).Admits (s := emptyStore)
      (pointFiring (A := Presentation.Schematic.A) argumentOnly (argumentOnly.pointRows argumentPoints)
        graph_member argumentChoice) :=
  (admits_iff _).mpr ((admits_iff _).mp argumentOnly_point_admitted)

/-- **No choice of table identities makes a step of the source relation there**: every label of the empty
store is the row `0`, which is no point of the graph. -/
theorem no_pointStep (tables : Finset ℕ) (t : SState ℕ) :
    ¬ PointStep Presentation.Schematic.A rows onePoint {argumentOnly} tables emptyStore t := by
  rintro ⟨h, -, ⟨ρ, inP, points, isRule, length, stored, -, labels⟩, -, -⟩
  rw [Set.mem_singleton_iff] at inP
  subst inP
  obtain ⟨ρ', inP', points', length', onGraph, isRule'⟩ := h.member
  rw [Set.mem_singleton_iff] at inP'
  subst inP'
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp (show points.length = 1 from length)
  obtain ⟨p', rfl⟩ := List.length_eq_one_iff.mp (show points'.length = 1 from length')
  have storedLength : stored.length = 1 := by
    rw [← List.length_map (f := emptyStore.label), labels]
    rfl
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp storedLength
  have isZero : toTerm (.sym 0) = p := List.head_eq_of_cons_eq labels
  have same : argumentOnly.at rows [p] = argumentOnly.at rows [p'] := isRule.symm.trans isRule'
  have tells : (argumentOnly.at rows [p]).body.tell = (argumentOnly.at rows [p']).body.tell := by rw [same]
  have points : p = p' := by
    simpa [RuleWithCondition.at, RuleWithCondition.calls, argumentOnly] using tells
  have onG : p' = pointRow ⟨.var 1, 3, [.var 0]⟩ ([.sym 7], .sym 5) :=
    Set.mem_singleton_iff.mp (onGraph p' (List.mem_singleton_self _))
  have clash : toTerm (.sym 0) = toTerm (groundRow 3 [.sym 7] (.sym 5)) := isZero.trans (points.trans onG)
  exact absurd (toTerm_injective clash) (by decide)

/-! ## The table read and the evaluation, on the same bags -/

section Bags

variable {I : Interpretation ℕ Expr} {P : Set (RuleWithCondition ℕ Tm)}

/-- **The tables a store holds are true**: every row of the store that is a row of the table of a function a
rule of the program calls is a row of the graph of the interpretation. -/
def TrueTables (I : Interpretation ℕ Expr) (P : Set (RuleWithCondition ℕ Tm)) (C : Multiset Expr) : Prop :=
  ∀ ρ ∈ P, ∀ c ∈ ρ.conditions, ∀ (args : List Expr) (value : Expr),
    groundRow c.name args value ∈ C → I c.name args = some value

/-- **The rules make no row of a table**: no instance of a made pattern is a row of the table of a function a
rule of the program calls. -/
def MakesNoTableRow (P : Set (RuleWithCondition ℕ Tm)) : Prop :=
  ∀ ρ ∈ P, ∀ (θ : ℕ → Expr), ∀ m ∈ ρ.rule.body.produce, ∀ ρ' ∈ P, ∀ c ∈ ρ'.conditions,
    ∀ (args : List Expr) (value : Expr), inst θ m ≠ groundRow c.name args value

/-- **A rewrite beside more rows is a rewrite.** -/
theorem rewrites_frame {rules : List SRule} {C C' : Multiset Expr} (fires : Rewrites rules C C')
    (F : Multiset Expr) : Rewrites rules (C + F) (C' + F) := by
  obtain ⟨r, member, θ, rest, rfl, reads, equations, rfl⟩ := fires
  exact ⟨r, member, θ, rest + F, (add_assoc _ _ _).symm,
    fun q inside => Multiset.mem_add.mpr (.inl (reads q inside)), equations, add_assoc _ _ _⟩

/-- **A run beside more rows is a run.** -/
theorem run_frame {program : Program (OneFrame.Terms Tm)} {C C' : Multiset Expr}
    (run : Relation.ReflTransGen (RewritesBy program) C C') (F : Multiset Expr) :
    Relation.ReflTransGen (RewritesBy program) (C + F) (C' + F) := by
  induction run with
  | refl => exact .refl
  | tail _ last ih =>
      obtain ⟨r, inP, single⟩ := last
      exact ih.tail ⟨r, inP, rewrites_frame single F⟩

/-- **A table read at a store whose tables are true is an evaluation at the same store, with the same
result.** -/
theorem table_to_eval {ρ : RuleWithCondition ℕ Tm} {C C' : Multiset Expr}
    (true : ∀ c ∈ ρ.conditions, ∀ (args : List Expr) (value : Expr),
      groundRow c.name args value ∈ C → I c.name args = some value)
    (fires : Rewrites [ρ.tableRule rows] C C') : EvalStep I ρ C C' := by
  obtain ⟨r, member, θ, rest, split, reads, equations, rfl⟩ := fires
  obtain rfl := List.mem_singleton.mp member
  refine ⟨θ, rest, split, fun q inside => reads q (List.mem_append_left _ inside), equations,
    fun c inside => ?_, rfl⟩
  have callIn := reads (callRow rows c) (List.mem_append_right _
    (show callRow rows c ∈ ρ.conditions.map (callRow rows) from List.mem_map_of_mem inside))
  rw [show inst θ (callRow rows c) = groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) from
    inst_row θ c.name c.arguments c.value] at callIn
  exact true c inside _ _ (by rw [← split]; exact Multiset.mem_add.mpr (.inr callIn))

/-- The rows of the tables an evaluation uses, at a match. -/
def usedRows (ρ : RuleWithCondition ℕ Tm) (θ : ℕ → Expr) : List Expr :=
  ρ.conditions.map fun c => groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value)

/-- **An evaluation at a bag is a table read at the bag beside the rows of the graph it uses**, finitely
many. -/
theorem eval_to_table {ρ : RuleWithCondition ℕ Tm} {B B' : Multiset Expr} (evaluates : EvalStep I ρ B B') :
    ∃ T : Multiset Expr, (∀ row ∈ T, toTerm row ∈ groundGraph I) ∧
      Rewrites [ρ.tableRule rows] (B + T) (B' + T) := by
  obtain ⟨θ, rest, rfl, reads, equations, conditions, rfl⟩ := evaluates
  refine ⟨(usedRows ρ θ : Multiset Expr), fun row inside => ?_, ρ.tableRule rows, List.mem_singleton_self _, θ,
    rest + (usedRows ρ θ : Multiset Expr), (add_assoc _ _ _).symm, fun q inside => ?_, equations,
    add_assoc _ _ _⟩
  · obtain ⟨c, inC, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp inside)
    exact ⟨c.name, _, _, conditions c inC, rfl⟩
  · rcases List.mem_append.mp (show q ∈ ρ.rule.body.read ++ ρ.conditions.map (callRow rows) from inside) with
      inRead | inCalls
    · exact Multiset.mem_add.mpr (.inl (reads q inRead))
    · obtain ⟨c, inC, rfl⟩ := List.mem_map.mp inCalls
      exact Multiset.mem_add.mpr (.inr (Multiset.mem_coe.mpr (List.mem_map.mpr
        ⟨c, inC, (inst_row θ c.name c.arguments c.value).symm⟩)))

/-- **A store whose tables are true, beside rows of the graph, is a store whose tables are true.** -/
theorem trueTables_add {B T : Multiset Expr} (true : TrueTables I P B)
    (graph : ∀ row ∈ T, toTerm row ∈ groundGraph I) : TrueTables I P (B + T) := by
  intro ρ member c inC args value inside
  rcases Multiset.mem_add.mp inside with inB | inT
  · exact true ρ member c inC args value inB
  · obtain ⟨f, args', value', answers, same⟩ := graph _ inT
    obtain ⟨rfl, rfl, rfl⟩ := groundRow_inj (toTerm_injective same)
    exact answers

/-- **Every table read at a store whose tables are true is an evaluation at the same store**, and the tables
of the result are true when the rules make no row of a table. -/
theorem table_step_to_eval (quiet : MakesNoTableRow P) {C C' : Multiset Expr} (true : TrueTables I P C)
    (fires : RewritesBy (tabled rows P) C C') : (∃ ρ ∈ P, EvalStep I ρ C C') ∧ TrueTables I P C' := by
  obtain ⟨r, inTabled, single⟩ := fires
  obtain ⟨ρ, member, rfl⟩ := mem_tabled.mp inTabled
  refine ⟨⟨ρ, member, table_to_eval (true ρ member) single⟩, ?_⟩
  obtain ⟨r, inList, θ, rest, split, -, -, rfl⟩ := single
  obtain rfl := List.mem_singleton.mp inList
  intro ρ' member' c inC args value inside
  rcases Multiset.mem_add.mp inside with made | old
  · obtain ⟨m, inProduce, same⟩ := List.mem_map.mp (Multiset.mem_coe.mp made)
    exact absurd same (quiet ρ member θ m inProduce ρ' member' c inC args value)
  · exact true ρ' member' c inC args value (by rw [← split]; exact Multiset.mem_add.mpr (.inr old))

/-- **The table reads at stores whose tables are true, read back as evaluations on the same bags**: every
rewrite by a table read is one evaluation. -/
def storedReadback (I : Interpretation ℕ Expr) (quiet : MakesNoTableRow P) :
    OperationalReadback (evaluation I P) (rewritingBy (tabled rows P)) where
  related B C := C = B ∧ TrueTables I P B
  readStep := by
    rintro B C C' ⟨rfl, true⟩ fires
    obtain ⟨evaluates, true'⟩ := table_step_to_eval quiet true fires
    exact .inr ⟨C', evaluates, rfl, true'⟩

/-- **Every run of the table reads from a store whose tables are true is a run of evaluations between the
same bags**, and the tables stay true. -/
theorem runs_table_to_eval (quiet : MakesNoTableRow P) {C C' : Multiset Expr} (true : TrueTables I P C)
    (run : Relation.ReflTransGen (RewritesBy (tabled rows P)) C C') :
    Relation.ReflTransGen (fun B B' => ∃ ρ ∈ P, EvalStep I ρ B B') C C' ∧ TrueTables I P C' := by
  induction run with
  | refl => exact ⟨.refl, true⟩
  | tail _ last ih =>
      obtain ⟨evaluations, trueMid⟩ := ih
      obtain ⟨evaluates, trueLast⟩ := table_step_to_eval quiet trueMid last
      exact ⟨evaluations.tail evaluates, trueLast⟩

/-- **Every run of evaluations is a run of the table reads beside finitely many rows of the graph**, the rows
the run uses. -/
theorem runs_eval_to_table {B B' : Multiset Expr}
    (run : Relation.ReflTransGen (fun B B' => ∃ ρ ∈ P, EvalStep I ρ B B') B B') :
    ∃ T : Multiset Expr, (∀ row ∈ T, toTerm row ∈ groundGraph I) ∧
      Relation.ReflTransGen (RewritesBy (tabled rows P)) (B + T) (B' + T) := by
  induction run with
  | refl => exact ⟨0, fun _ inside => absurd inside (Multiset.notMem_zero _), .refl⟩
  | @tail Bm Bn _ last ih =>
      obtain ⟨T₁, graph₁, run₁⟩ := ih
      obtain ⟨ρ, member, evaluates⟩ := last
      obtain ⟨T₂, graph₂, fires⟩ := eval_to_table evaluates
      refine ⟨T₁ + T₂, fun row inside => ?_, ?_⟩
      · rcases Multiset.mem_add.mp inside with in₁ | in₂
        exacts [graph₁ row in₁, graph₂ row in₂]
      · have lifted : Relation.ReflTransGen (RewritesBy (tabled rows P)) (B + T₁ + T₂) (Bm + T₁ + T₂) :=
          run_frame run₁ T₂
        have last' : RewritesBy (tabled rows P) (Bm + T₂ + T₁) (Bn + T₂ + T₁) :=
          ⟨ρ.tableRule rows, tableRule_mem_tabled member, rewrites_frame fires T₁⟩
        have eq₁ : B + (T₁ + T₂) = B + T₁ + T₂ := (add_assoc _ _ _).symm
        have eq₂ : Bm + T₂ + T₁ = Bm + T₁ + T₂ := add_right_comm _ _ _
        have eq₃ : Bn + T₂ + T₁ = Bn + (T₁ + T₂) := by rw [add_right_comm, add_assoc]
        rw [eq₁]
        rw [eq₂, eq₃] at last'
        exact lifted.tail last'

end Bags

/-! ## Along runs of `RuleSyntax.step` -/

section States

variable {O : Type} [DecidableEq O] {I : Interpretation ℕ Expr} {P : Set (RuleWithCondition ℕ Tm)}

/-- The table reads of evaluable rules are in the fragment of `Determined`. -/
theorem tabled_fragment (evaluable : ∀ ρ ∈ P, ρ.Evaluable) : ∀ r ∈ tabled rows P, DeterminedPositive r := by
  intro r inTabled
  obtain ⟨ρ, member, rfl⟩ := mem_tabled.mp inTabled
  exact determinedPositive_of_fragment (ρ.fragment_tableRule (evaluable ρ member).noCollect
    (evaluable ρ member).guards (evaluable ρ member).restricted)

/-- **The step of the program of table reads, read back as the atomic evaluation**: at states that read as
stores whose tables are true, every admitted table read is one evaluation of the bag. -/
def storedStepReadback [Infinite O] (I : Interpretation ℕ Expr) (evaluable : ∀ ρ ∈ P, ρ.Evaluable)
    (quiet : MakesNoTableRow P) : OperationalReadback (evaluation I P) (programSystem O (tabled rows P)) :=
  (storedReadback I quiet).comp (stepCorrespondence (O := O) (tabled_fragment evaluable)).toOperationalReadback

/-- **Every run of the program of table reads, from a state that reads as a store whose tables are true, is
matched by the evaluated program**: it ends at a state that reads as a store whose tables are true, and from
every state that reads as the first store the evaluated program has a run to a state that reads as the last. -/
theorem stored_run_to_evaluated [Infinite O] (evaluable : ∀ ρ ∈ P, ρ.Evaluable) (quiet : MakesNoTableRow P)
    {t t' : SState O} {C : Multiset Expr} (reads : ReadsBag t C) (true : TrueTables I P C)
    (run : (programSystem O (tabled rows P)).MultiStep t t') :
    ∃ C' : Multiset Expr, ReadsBag t' C' ∧ TrueTables I P C' ∧
      ∀ s : SState O, ReadsBag s C →
        ∃ s', (programSystem O (evaluated I P)).MultiStep s s' ∧ ReadsBag s' C' := by
  obtain ⟨(C' : Multiset Expr), bagRun, reads'⟩ :=
    (stepCorrespondence (O := O) (tabled_fragment evaluable)).toOperationalReadback.reflectMultiStep reads run
  obtain ⟨evaluations, true'⟩ := runs_table_to_eval (I := I) quiet true
    ((Meredith.multiStep_iff_reflTransGen (rewritingBy (tabled rows P)) C C').mp bagRun)
  refine ⟨C', reads', true', fun s readsS => ?_⟩
  exact (evaluatedCorrespondence (O := O) evaluable).liftMultiStep readsS
    ((Meredith.multiStep_iff_reflTransGen (evaluation I P) C C').mpr evaluations)

/-- **Every run of the evaluated program is a run of the table reads at a store that holds the rows the run
uses**: from a state that reads as `B` to one that reads as `B'`, there are finitely many rows `T` of the
graph such that from every state that reads as `B + T` the program of table reads has a run to a state that
reads as `B' + T`. -/
theorem evaluated_run_to_stored [Infinite O] (evaluable : ∀ ρ ∈ P, ρ.Evaluable) {s s' : SState O}
    {B : Multiset Expr} (reads : ReadsBag s B) (run : (programSystem O (evaluated I P)).MultiStep s s') :
    ∃ B' T : Multiset Expr, ReadsBag s' B' ∧ (∀ row ∈ T, toTerm row ∈ groundGraph I) ∧
      ∀ t : SState O, ReadsBag t (B + T) →
        ∃ t', (programSystem O (tabled rows P)).MultiStep t t' ∧ ReadsBag t' (B' + T) := by
  obtain ⟨(B' : Multiset Expr), bagRun, reads'⟩ :=
    (evaluatedCorrespondence (O := O) (I := I) evaluable).toOperationalReadback.reflectMultiStep reads run
  obtain ⟨T, graph, stored⟩ := runs_eval_to_table (I := I) (P := P)
    ((Meredith.multiStep_iff_reflTransGen (evaluation I P) B B').mp bagRun)
  refine ⟨B', T, reads', graph, fun t readsT => ?_⟩
  exact (stepCorrespondence (O := O) (tabled_fragment evaluable)).liftMultiStep readsT
    ((Meredith.multiStep_iff_reflTransGen (rewritingBy (tabled rows P)) (B + T) (B' + T)).mpr stored)

/-- **Every run of the program of table reads, from a state that reads as a store whose tables are true, is
matched by the program at the graph**, between states that read as the same stores. -/
theorem stored_run_to_graph [Infinite O] (evaluable : ∀ ρ ∈ P, ρ.Evaluable) (quiet : MakesNoTableRow P)
    {t t' : SState O} {C : Multiset Expr} (reads : ReadsBag t C) (true : TrueTables I P C)
    (run : (programSystem O (tabled rows P)).MultiStep t t') :
    ∃ C' : Multiset Expr, ReadsBag t' C' ∧ TrueTables I P C' ∧
      ∀ s : SState O, ReadsBag s C →
        ∃ s', (programSystem O (specialized rows (groundGraph I) P)).MultiStep s s' ∧ ReadsBag s' C' := by
  obtain ⟨(C' : Multiset Expr), bagRun, reads'⟩ :=
    (stepCorrespondence (O := O) (tabled_fragment evaluable)).toOperationalReadback.reflectMultiStep reads run
  obtain ⟨evaluations, true'⟩ := runs_table_to_eval (I := I) quiet true
    ((Meredith.multiStep_iff_reflTransGen (rewritingBy (tabled rows P)) C C').mp bagRun)
  refine ⟨C', reads', true', fun s readsS => ?_⟩
  exact (graphCorrespondence (O := O) (I := I) (fun ρ inP => (evaluable ρ inP).noCollect)
    (fun ρ inP => (evaluable ρ inP).guards) (fun ρ inP => (evaluable ρ inP).restricted)).liftMultiStep readsS
    ((Meredith.multiStep_iff_reflTransGen (evaluation I P) C C').mpr evaluations)

/-- **Every run of the program at the graph is a run of the table reads at a store that holds the rows the run
uses**: from a state that reads as `B` to one that reads as `B'`, there are finitely many rows `T` of the graph
such that from every state that reads as `B + T` the program of table reads has a run to a state that reads as
`B' + T`. -/
theorem graph_run_to_stored [Infinite O] (evaluable : ∀ ρ ∈ P, ρ.Evaluable) {s s' : SState O}
    {B : Multiset Expr} (reads : ReadsBag s B)
    (run : (programSystem O (specialized rows (groundGraph I) P)).MultiStep s s') :
    ∃ B' T : Multiset Expr, ReadsBag s' B' ∧ (∀ row ∈ T, toTerm row ∈ groundGraph I) ∧
      ∀ t : SState O, ReadsBag t (B + T) →
        ∃ t', (programSystem O (tabled rows P)).MultiStep t t' ∧ ReadsBag t' (B' + T) := by
  obtain ⟨B', reads', bagRun, -⟩ := graph_run_to_evaluated evaluable reads run
  obtain ⟨T, graph, stored⟩ := runs_eval_to_table (I := I) (P := P)
    ((Meredith.multiStep_iff_reflTransGen (evaluation I P) B B').mp bagRun)
  refine ⟨B', T, reads', graph, fun t readsT => ?_⟩
  exact (stepCorrespondence (O := O) (tabled_fragment evaluable)).liftMultiStep readsT
    ((Meredith.multiStep_iff_reflTransGen (rewritingBy (tabled rows P)) (B + T) (B' + T)).mpr stored)

end States

/-- **A store beside the rows a run uses is read from a state**, with an identity for each row. -/
theorem exists_stored (B T : Multiset Expr) : ∃ t : SState ℕ, ReadsBag t (B + T) :=
  Machines.exists_reads _

/-! ## Control: a rule that makes a row of the table -/

/-- The function `3` with the one value `3(7) = 5`. -/
def fiveAtSeven : Interpretation ℕ Expr := fun f args => if f = 3 ∧ args = [.sym 7] then some (.sym 5) else none

/-- **A rule that makes a row of the table of `3`**: make `3 7 6`, which is no row of the graph. -/
def liar : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[], [], [], [], [toTerm (groundRow 3 [.sym 7] (.sym 6))]⟩, []⟩
  conditions := []

/-- **After one firing of it from the empty store, the tables are not true**: the empty store's tables are
true, the rule's table read fires there, and the result holds the row `3 7 6`. -/
theorem liar_breaks_tables :
    TrueTables fiveAtSeven {argumentOnly, liar} 0 ∧
      ∃ C' : Multiset Expr, RewritesBy (tabled rows {argumentOnly, liar}) 0 C' ∧
        ¬ TrueTables fiveAtSeven {argumentOnly, liar} C' := by
  refine ⟨fun _ _ _ _ _ _ inside => absurd inside (Multiset.notMem_zero _),
    ((liar.rule.body.produce.map (inst fun _ => .sym 0) : List Expr) : Multiset Expr) + 0,
    ⟨liar.tableRule rows, tableRule_mem_tabled (Set.mem_insert_of_mem _ rfl), liar.tableRule rows,
      List.mem_singleton_self _, fun _ => .sym 0, 0, rfl, fun q inside => absurd inside List.not_mem_nil,
      fun eq inside => absurd inside List.not_mem_nil, rfl⟩, fun true => ?_⟩
  have value := true argumentOnly (Set.mem_insert _ _) ⟨.var 1, 3, [.var 0]⟩ (List.mem_singleton_self _)
    [.sym 7] (.sym 6) (by
      refine Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr (List.mem_map.mpr
        ⟨toTerm (groundRow 3 [.sym 7] (.sym 6)), List.mem_singleton_self _, inst_toTerm _ _⟩))))
  have five : fiveAtSeven 3 [.sym 7] = some (.sym 5) := by simp [fiveAtSeven]
  exact absurd (Option.some.inj (five.symm.trans value)) (by decide)

#print axioms addStep_blind
#print axioms stores
#print axioms one_pointStep
#print axioms stored_run_exists
#print axioms graph_fires
#print axioms no_pointStep
#print axioms table_to_eval
#print axioms eval_to_table
#print axioms trueTables_add
#print axioms storedReadback
#print axioms storedStepReadback
#print axioms runs_table_to_eval
#print axioms runs_eval_to_table
#print axioms stored_run_to_evaluated
#print axioms evaluated_run_to_stored
#print axioms stored_run_to_graph
#print axioms graph_run_to_stored
#print axioms liar_breaks_tables

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.StoredRuns
