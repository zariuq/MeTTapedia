import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# A call inside a call, run through the translation

The program is

* `(= (twice $f $x) (let $y ($f $x) ($f $y)))`: the inner call `($f $x)` runs first, its answer is
  bound to `$y`, and the outer call `($f $y)` takes it (the explicit form of `($f ($f $x))`);
* `(= (inc $n) (s $n))`.

The query is `(twice inc zero)`.

* `program_wellFormed`, `query_wellFormed`: both are well-formed (decided by the kernel).
* `runs`: the source run. The call to `twice` opens a copy at scope `0`; the `let` pushes its frame;
  the inner call `(inc zero)` is answered at scope `1` with the frame pending; the bind opens `$y` at
  scope `2`; the outer call `(inc (s zero))` is answered at scope `3`. At every call the equation
  whose left side does not fit makes a dead alternative.
* `final_answers`: the bag of answers at the end is `{(s (s zero))}`; `final_quiescent`: nothing
  can move there.
* **Through the translation** (`run_through_translation`): that configuration has a frontier whose
  states are reached from the translation's start by runs of the step, and whose bag of answers is
  the same. This is `arrow_runs_forward` with its hypotheses discharged: no hypothesis on runs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleTwice

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit

abbrev D := untyped.discipline
abbrev N := mettaNodes

/-! ## The program and the query -/

/-- `$f` and `$x` of `twice` (site `[200]`), `$y` of its `let` (site `[201]`), `$n` of `inc`
(site `[300]`). -/
def fArg : MData := mvar [200] 0
def xArg : MData := mvar [200] 1
def yBound : MData := mvar [201] 0
def nArg : MData := mvar [300] 0

/-- `(= (twice $f $x) (let $y ($f $x) ($f $y)))`. -/
def twiceEq : SourceLanguage.Equation mkeys [] () MTy :=
  ⟨[200], tuple [sym "twice", fArg, xArg],
    .let_ [201] yBound (.apply (tuple [fArg, xArg])) (.apply (tuple [fArg, yBound]))⟩

/-- `(= (inc $n) (s $n))`. -/
def incEq : SourceLanguage.Equation mkeys [] () MTy :=
  ⟨[300], tuple [sym "inc", nArg], .ret (tuple [sym "s", nArg])⟩

def program : SourceLanguage.Program mkeys [] () MTy := ⟨[twiceEq, incEq], fun t => .apply t⟩

/-- The call `(twice inc zero)`. -/
def call : MData := tuple [sym "twice", sym "inc", sym "zero"]

def query : Comp mkeys [] () MTy := .apply call

def supply : ℕ → MClosed := fun _ => csym "space"

theorem program_wellFormed : WellFormed program := by decide

theorem query_wellFormed : QueryWellFormed program [100] query := by decide

theorem program_arrows : ArrowProgram program := by
  intro e member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨trivial, trivial⟩
  · trivial

theorem query_arrows : ArrowComp query := trivial

/-! ## The data of the run -/

/-- The copy of `twice` at scope `0`, equated with the call. -/
def k1 : Constraint mkeys [] () := (instantiate (copyAt mkeys 0) twiceEq.lhs, call)

/-- The `let`'s pattern, inner call and outer call, in the copy at scope `0`. -/
def y0 : MData := instantiate (copyAt mkeys 0) yBound
def fx0 : MData := instantiate (copyAt mkeys 0) (tuple [fArg, xArg])
def fy0 : MData := instantiate (copyAt mkeys 0) (tuple [fArg, yBound])

/-- The pending frame of the `let`. -/
def frame0 : SourceLanguage.Frame mkeys [] () MTy := .bindTo [201] y0 (.apply fy0)

/-- The copy of `inc` at scope `1`, equated with the inner call, and its answer. -/
def k2 : Constraint mkeys [] () := (instantiate (copyAt mkeys 1) incEq.lhs, fx0)
def v1 : MData := instantiate (copyAt mkeys 1) (tuple [sym "s", nArg])

/-- The bind at scope `2`: the `let`'s `$y`, opened, equated with the inner answer. -/
def k3 : Constraint mkeys [] () := (instantiate (openAt mkeys [201] 2) y0, v1)
def fy2 : MData := instantiate (openAt mkeys [201] 2) fy0

/-- The copy of `inc` at scope `3`, equated with the outer call, and its answer. -/
def k4 : Constraint mkeys [] () := (instantiate (copyAt mkeys 3) incEq.lhs, fy2)
def v3 : MData := instantiate (copyAt mkeys 3) (tuple [sym "s", nArg])

/-- A solution of the whole store: `$f = inc`, `$x = zero`, and the copies of `$n` and `$y`. -/
def solution : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [200], 0), csym "inc"), (([0], [200], 1), csym "zero"), (([1], [300], 0), csym "zero"),
    (([2, 0], [201], 0), ctuple [csym "s", csym "zero"]),
    (([3], [300], 0), ctuple [csym "s", csym "zero"])] (csym "a")

theorem models_all : Models solution [k1, k2, k3, k4] := by
  intro e member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem live_of_subset {K : List (Constraint mkeys [] ())} (sub : K ⊆ [k1, k2, k3, k4]) : Solvable K :=
  ⟨Empty, noNames, solution, fun e member => models_all e (sub member)⟩

theorem live1 : Solvable [k1] := live_of_subset (List.sublist_append_left [k1] [k2, k3, k4]).subset
theorem live12 : Solvable [k1, k2] := live_of_subset (List.sublist_append_left [k1, k2] [k3, k4]).subset
theorem live123 : Solvable [k1, k2, k3] := live_of_subset (List.sublist_append_left [k1, k2, k3] [k4]).subset
theorem live1234 : Solvable [k1, k2, k3, k4] := live_of_subset (fun _ member => member)

/-! ## The source run -/

/-- The alternatives: `A` at the call to `twice`, `B` at the inner call, `C` and `D'` answering it,
`E` at the outer call, `F` and `G` answering it; `Xt`, `Xi` the dead ones. -/
abbrev A0 : Branch mkeys [] () MTy := ⟨[], .eval query, [], []⟩
abbrev At : Branch mkeys [] () MTy := ⟨[k1], .eval (.let_ [201] y0 (.apply fx0) (.apply fy0)), [], []⟩
abbrev Ai : Branch mkeys [] () MTy :=
  ⟨[(instantiate (copyAt mkeys 0) incEq.lhs, call)], .eval (incEq.rhs.inst (copyAt mkeys 0)), [], []⟩
abbrev Bt : Branch mkeys [] () MTy := ⟨[k1], .eval (.apply fx0), [frame0], []⟩
abbrev Ct : Branch mkeys [] () MTy :=
  ⟨[k1, (instantiate (copyAt mkeys 1) twiceEq.lhs, fx0)], .eval (twiceEq.rhs.inst (copyAt mkeys 1)), [frame0], []⟩
abbrev Ci : Branch mkeys [] () MTy := ⟨[k1, k2], .eval (.ret v1), [frame0], []⟩
abbrev Di : Branch mkeys [] () MTy := ⟨[k1, k2], .value v1, [frame0], []⟩
abbrev Ei : Branch mkeys [] () MTy := ⟨[k1, k2, k3], .eval (.apply fy2), [], []⟩
abbrev Ft : Branch mkeys [] () MTy :=
  ⟨[k1, k2, k3, (instantiate (copyAt mkeys 3) twiceEq.lhs, fy2)], .eval (twiceEq.rhs.inst (copyAt mkeys 3)), [], []⟩
abbrev Fi : Branch mkeys [] () MTy := ⟨[k1, k2, k3, k4], .eval (.ret v3), [], []⟩
abbrev Gi : Branch mkeys [] () MTy := ⟨[k1, k2, k3, k4], .value v3, [], []⟩

abbrev W0 : World mkeys [] () := ⟨0, 0, fun _ => 0⟩
abbrev W1 : World mkeys [] () := ⟨1, 0, fun _ => 0⟩
abbrev W2 : World mkeys [] () := ⟨2, 0, fun _ => 0⟩
abbrev W3 : World mkeys [] () := ⟨3, 0, fun _ => 0⟩
abbrev W4 : World mkeys [] () := ⟨4, 0, fun _ => 0⟩

/-- The configuration at the end. -/
def final : Config mkeys [] () MTy := ⟨W4, {Gi, Ft, Ct, Ai}⟩

theorem runs : Runs D program supply (Config.initial (fun _ => 0) query) final := by
  have m1 : ∃ e ∈ program.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, call)]) :=
    ⟨twiceEq, List.mem_cons_self .., live1⟩
  have m3 : ∃ e ∈ program.equations, Solvable ([k1] ++ [(instantiate (copyAt mkeys 1) e.lhs, fx0)]) :=
    ⟨incEq, List.mem_cons_of_mem _ (List.mem_cons_self ..), live12⟩
  have m6 : ∃ e ∈ program.equations,
      Solvable ([k1, k2, k3] ++ [(instantiate (copyAt mkeys 3) e.lhs, fy2)]) :=
    ⟨incEq, List.mem_cons_of_mem _ (List.mem_cons_self ..), live1234⟩
  -- the call to `twice`, at scope 0
  have s1 : SourceLanguage.Step D program supply (Config.initial (fun _ => 0) query) ⟨W1, {At, Ai}⟩ :=
    Step.of_eq (rest := 0) rfl (add_zero _).symm live_nil (.apply W0 [] call [] [] m1)
  -- the `let` pushes its frame
  have s2 : SourceLanguage.Step D program supply ⟨W1, {At, Ai}⟩ ⟨W1, {Bt, Ai}⟩ :=
    Step.of_eq (rest := {Ai}) rfl rfl live1 (.letStart W1 [k1] [201] y0 (.apply fx0) (.apply fy0) [] [])
  -- the inner call, at scope 1
  have s3 : SourceLanguage.Step D program supply ⟨W1, {Bt, Ai}⟩ ⟨W2, {Ct, Ci, Ai}⟩ :=
    Step.of_eq (rest := {Ai}) rfl rfl live1
      (Move.apply (D := D) (P := program) (supply := supply) W1 [k1] fx0 [frame0] [] m3)
  have s4 : SourceLanguage.Step D program supply ⟨W2, {Ct, Ci, Ai}⟩ ⟨W2, {Di, Ct, Ai}⟩ :=
    Step.of_eq (rest := {Ct, Ai}) (Multiset.cons_swap _ _ _) rfl live12
      (Move.ret (D := D) (P := program) (supply := supply) W2 [k1, k2] v1 [frame0] [])
  -- the bind, at scope 2
  have s5 : SourceLanguage.Step D program supply ⟨W2, {Di, Ct, Ai}⟩ ⟨W3, {Ei, Ct, Ai}⟩ :=
    Step.of_eq (rest := {Ct, Ai}) rfl rfl live12
      (Move.letBind (D := D) (P := program) (supply := supply) W2 [k1, k2] v1 [201] y0 (.apply fy0) [] [])
  -- the outer call, at scope 3
  have s6 : SourceLanguage.Step D program supply ⟨W3, {Ei, Ct, Ai}⟩ ⟨W4, {Ft, Fi, Ct, Ai}⟩ :=
    Step.of_eq (rest := {Ct, Ai}) rfl rfl live123 (.apply W3 [k1, k2, k3] fy2 [] [] m6)
  have s7 : SourceLanguage.Step D program supply ⟨W4, {Ft, Fi, Ct, Ai}⟩ final :=
    Step.of_eq (rest := {Ft, Ct, Ai}) (Multiset.cons_swap _ _ _) rfl live1234 (.ret W4 [k1, k2, k3, k4] v3 [] [])
  exact ((((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5).tail s6).tail s7

/-! ## The answers -/

/-- `(s (s zero))`. -/
def answer : MClosed := ctuple [csym "s", ctuple [csym "s", csym "zero"]]

theorem determines_final : Determines [k1, k2, k3, k4] v3 answer := by
  refine ⟨live1234, fun target τ solved => ?_⟩
  have h1 : tupleAt [symAt "twice", instantiate τ (foD [0] [200] 0), instantiate τ (foD [0] [200] 1)] =
      tupleAt [symAt "twice", symAt "inc", symAt "zero"] :=
    solved k1 (List.mem_cons_self ..)
  have h2 : tupleAt [symAt "inc", instantiate τ (foD [1] [300] 0)] =
      tupleAt [instantiate τ (foD [0] [200] 0), instantiate τ (foD [0] [200] 1)] :=
    solved k2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h3 : instantiate τ (foD [2, 0] [201] 0) = tupleAt [symAt "s", instantiate τ (foD [1] [300] 0)] :=
    solved k3 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have h4 : tupleAt [symAt "inc", instantiate τ (foD [3] [300] 0)] =
      tupleAt [instantiate τ (foD [0] [200] 0), instantiate τ (foD [2, 0] [201] 0)] :=
    solved k4 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  obtain ⟨_, _, x0⟩ := tuple3_inj h1
  obtain ⟨_, n1⟩ := tuple2_inj h2
  obtain ⟨_, n3⟩ := tuple2_inj h4
  show tupleAt [symAt "s", instantiate τ (foD [3] [300] 0)] = _
  rw [n3, h3, n1, x0]
  rfl

theorem dead_Ai : ¬ Solvable Ai.store :=
  dead_of_length (ts := [sym "inc", foD [0] [300] 0]) (ts' := [sym "twice", sym "inc", sym "zero"])
    (List.mem_singleton.mpr rfl) (by decide)

theorem dead_Ct : ¬ Solvable Ct.store :=
  dead_of_length (ts := [sym "twice", foD [1] [200] 0, foD [1] [200] 1]) (ts' := [foD [0] [200] 0, foD [0] [200] 1])
    (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)) (by decide)

theorem dead_Ft : ¬ Solvable Ft.store :=
  dead_of_length (ts := [sym "twice", foD [3] [200] 0, foD [3] [200] 1])
    (ts' := [foD [0] [200] 0, foD [2, 0] [201] 0])
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))))
    (by decide)

/-- **The bag of answers at the end**: `(s (s zero))`, once. -/
theorem final_answers : Config.answers (D := D) final = {{answer}} := by
  have finished : Branch.Finished (D := D) Gi := ⟨rfl, _, rfl⟩
  show Config.answers (D := D) ⟨W4, Gi ::ₘ Ft ::ₘ Ct ::ₘ {Ai}⟩ = _
  rw [answers_cons_finished finished live1234, answers_cons_dead dead_Ft, answers_cons_dead dead_Ct,
    answers_singleton_dead dead_Ai, answer_of_determines rfl determines_final]
  rfl

/-- Nothing can move at the end. -/
theorem final_quiescent : Config.Quiescent (D := D) program supply final :=
  Config.quiescent_of_finished fun b member live => by
    simp only [final, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨rfl, _, rfl⟩
    · exact absurd live dead_Ft
    · exact absurd live dead_Ct
    · exact absurd live dead_Ai

/-! ## Through the translation -/

/-- **Run through the translation.** The configuration that the source run reaches has a frontier,
whose states are reached from the translation's start by runs of the step of the translated program,
and whose bag of answers is `{(s (s zero))}`. -/
theorem run_through_translation :
    ∃ L, ArrowFrontier (D := D) N program final L ∧
      (∀ x ∈ L, Relation.ReflTransGen (Fires N program) (Hosting.start N program query) x.2.1) ∧
      frontierAnswers N L = {{answer}} := by
  obtain ⟨L, frontier, reached⟩ := arrow_runs_forward N (D := D) (P := program) (supply := supply)
    (fun _ => 0) query program_wellFormed program_arrows query_wellFormed query_arrows runs
  exact ⟨L, frontier, reached, (arrowFrontier_answers N frontier).symm.trans final_answers⟩

#print axioms program_wellFormed
#print axioms query_wellFormed
#print axioms runs
#print axioms final_answers
#print axioms final_quiescent
#print axioms run_through_translation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleTwice
