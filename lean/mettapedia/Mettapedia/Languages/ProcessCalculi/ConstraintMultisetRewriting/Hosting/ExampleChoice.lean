import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Unification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleBeta

/-!
# An equation under a binder, used at two arguments in the two alternatives of a choice, run through
the translation

The program is the one equation `(= (app (lam x. $F x) $a) ($F $a))`: a second-order pattern under
the binder `lam`. The query is

`(choice (app (lam x. (s x)) zero) (app (lam x. (pair x x)) one))`, both alternatives called.

* The source run (`runs`) reaches a configuration whose bag of answers is
  `{(pair one one)}, {(s zero)}` (`final_answers`), and nothing can move there (`final_quiescent`).
* **Through the translation** (`run_through_translation`): that configuration has a frontier whose
  states are reached from the start by runs of the step of the translated program, and the bag of
  their answers is the same.

Controls:
* `normal_form_refused`: the equation's schema is not admitted on an alternative whose call is a
  normal form of its right side, `(pair one one)`: the frames match modulo syntax only.
* `outside_still`: outside the fragment (`run`), the source makes a step (`outside_moves`) and the
  translated program has no firing at all: the translation does not host `run`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleChoice

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open SourceLanguage.ExampleBeta (betaEq program call1 call2 c0 v1 lamD)
open Classical

abbrev D := untyped.discipline
abbrev N := mettaNodes

/-- The query: a choice between the two calls. -/
def query : Comp mkeys [] () MTy := .choice (.apply call1) (.apply call2)

def supply : ℕ → MClosed := fun _ => csym "space"

def start : Config mkeys [] () MTy := Config.initial (fun _ => 0) query

/-- The copy of the equation at scope `1`, equated with the second call. -/
def c1 : Constraint mkeys [] () := (instantiate (copyAt mkeys 1) betaEq.lhs, call2)

def v2 : MData := hoD [1] [100] 0 (foD [1] [100] 1)

/-- A solution of both stores. -/
def σ : Assignment (fam mkeys) noNames := fun x =>
  match x with
  | ⟨[0], ⟨[100], 0, ([()], ())⟩⟩ => tupleAt [symAt "s", .var .zero]
  | ⟨[1], ⟨[100], 0, ([()], ())⟩⟩ => tupleAt [symAt "pair", .var .zero, .var .zero]
  | ⟨[0], ⟨[100], 1, ([], ())⟩⟩ => Rigid.includeTerm noNames (csym "zero")
  | ⟨[1], ⟨[100], 1, ([], ())⟩⟩ => Rigid.includeTerm noNames (csym "one")
  | ⟨_, ⟨_, _, (_, _)⟩⟩ => Rigid.includeTerm noNames (rename (Γ := []) (fun _ impossible => nomatch impossible) (csym "a"))

theorem live0 : Solvable [c0] := ⟨Empty, noNames, σ, fun e member => by
  simp only [List.mem_singleton] at member; subst member; rfl⟩

theorem live1 : Solvable [c1] := ⟨Empty, noNames, σ, fun e member => by
  simp only [List.mem_singleton] at member; subst member; rfl⟩

/-! ## The source run -/

abbrev W0 : World mkeys [] () := ⟨0, 0, fun _ => 0⟩
abbrev A1 : Branch mkeys [] () MTy := ⟨[], .eval (.apply call1), [], []⟩
abbrev A2 : Branch mkeys [] () MTy := ⟨[], .eval (.apply call2), [], []⟩
abbrev X1 : Branch mkeys [] () MTy := ⟨[c0], .eval (.ret v1), [], []⟩
abbrev Y1 : Branch mkeys [] () MTy := ⟨[c0], .value v1, [], []⟩
abbrev X2 : Branch mkeys [] () MTy := ⟨[c1], .eval (.ret v2), [], []⟩
abbrev Y2 : Branch mkeys [] () MTy := ⟨[c1], .value v2, [], []⟩

/-- The configuration at the end. -/
def final : Config mkeys [] () MTy := ⟨⟨2, 0, fun _ => 0⟩, {Y2, Y1}⟩

theorem runs : Runs D program supply start final := by
  have m1 : ∃ e ∈ program.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, call1)]) :=
    ⟨betaEq, List.mem_singleton_self _, live0⟩
  have m2 : ∃ e ∈ program.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 1) e.lhs, call2)]) :=
    ⟨betaEq, List.mem_singleton_self _, live1⟩
  -- choice
  have s1 : SourceLanguage.Step D program supply start ⟨W0, {A1, A2}⟩ :=
    Step.of_eq (rest := 0) rfl (add_zero _).symm live_nil (.choice W0 [] (.apply call1) (.apply call2) [] [])
  -- the first call, at scope 0
  have s2 : SourceLanguage.Step D program supply ⟨W0, {A1, A2}⟩ ⟨⟨1, 0, fun _ => 0⟩, {X1, A2}⟩ :=
    Step.of_eq (rest := {A2}) rfl rfl live_nil (.apply W0 [] call1 [] [] m1)
  have s3 : SourceLanguage.Step D program supply ⟨⟨1, 0, fun _ => 0⟩, {X1, A2}⟩
      ⟨⟨1, 0, fun _ => 0⟩, {Y1, A2}⟩ :=
    Step.of_eq (rest := {A2}) rfl rfl live0 (.ret _ [c0] v1 [] [])
  -- the second call, at scope 1
  have s4 : SourceLanguage.Step D program supply ⟨⟨1, 0, fun _ => 0⟩, {Y1, A2}⟩
      ⟨⟨2, 0, fun _ => 0⟩, {X2, Y1}⟩ :=
    Step.of_eq (rest := {Y1}) (Multiset.cons_swap _ _ _) rfl live_nil
      (.apply ⟨1, 0, fun _ => 0⟩ [] call2 [] [] m2)
  have s5 : SourceLanguage.Step D program supply ⟨⟨2, 0, fun _ => 0⟩, {X2, Y1}⟩ final :=
    Step.of_eq (rest := {Y1}) rfl rfl live1 (.ret _ [c1] v2 [] [])
  exact ((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5

/-! ## The answers -/

def answer1 : MClosed := ctuple [csym "s", csym "zero"]
def answer2 : MClosed := ctuple [csym "pair", csym "one", csym "one"]

theorem determines0 : Determines [c0] v1 answer1 := by
  refine ⟨live0, fun target σ' solved => ?_⟩
  have e0 := solved c0 (by simp)
  have h0 : tupleAt [symAt "app", lamAt (σ' (ho [0] [100] 0)), σ' (fo [0] [100] 1)] =
      tupleAt [symAt "app", lamAt (tupleAt [symAt "s", bv]), symAt "zero"] := by
    rw [← instantiate_foD σ' [0] [100] 1, ← instantiate_hoD_bv σ' [0] [100] 0]
    exact e0
  obtain ⟨_, f0, a0⟩ := tuple3_inj h0
  have body0 := lamAt_inj f0
  show instantiate σ' (hoD [0] [100] 0 (foD [0] [100] 1)) = _
  rw [instantiate_hoD, instantiate_foD, a0, body0]
  rfl

theorem determines1 : Determines [c1] v2 answer2 := by
  refine ⟨live1, fun target σ' solved => ?_⟩
  have e1 := solved c1 (by simp)
  have h1 : tupleAt [symAt "app", lamAt (σ' (ho [1] [100] 0)), σ' (fo [1] [100] 1)] =
      tupleAt [symAt "app", lamAt (tupleAt [symAt "pair", bv, bv]), symAt "one"] := by
    rw [← instantiate_foD σ' [1] [100] 1, ← instantiate_hoD_bv σ' [1] [100] 0]
    exact e1
  obtain ⟨_, f1, a1⟩ := tuple3_inj h1
  have body1 := lamAt_inj f1
  show instantiate σ' (hoD [1] [100] 0 (foD [1] [100] 1)) = _
  rw [instantiate_hoD, instantiate_foD, a1, body1]
  rfl

/-- **The bag of answers at the end**: `(pair one one)` and `(s zero)`, one each. -/
theorem final_answers : Config.answers (D := D) final = {{answer2}, {answer1}} := by
  have finished2 : Branch.Finished (D := D) Y2 := ⟨rfl, _, rfl⟩
  have finished1 : Branch.Finished (D := D) Y1 := ⟨rfl, _, rfl⟩
  show Config.answers (D := D) ⟨⟨2, 0, fun _ => 0⟩, Y2 ::ₘ {Y1}⟩ = _
  rw [answers_cons_finished finished2 live1, answers_singleton finished1 live0,
    answer_of_determines rfl determines1, answer_of_determines rfl determines0]
  rfl

/-- Nothing can move at the end. -/
theorem final_quiescent : Config.Quiescent (D := D) program supply final :=
  Config.quiescent_of_finished fun b member _ => by
    simp only [final, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact ⟨rfl, _, rfl⟩
    · exact ⟨rfl, _, rfl⟩

/-! ## Through the translation -/

theorem program_plain : PlainProgram program := by
  intro e member
  rw [List.mem_singleton.mp member]
  trivial

theorem query_plain : PlainComp query := ⟨trivial, trivial⟩

theorem query_unopened : ∀ t ∈ query.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [query, Comp.data, List.mem_append, List.mem_singleton] at member
  rcases member with rfl | rfl <;> simp [call1, call2, tuple, tupleArgs, sym, lamD, lamAt, tupleAt,
    tupleArgsAt, symAt, bv, support, supportArgs] at inside

/-- **Run through the translation.** The configuration that the source run reaches has a frontier,
whose states are reached from the start by runs of the step of the translated program, and whose bag
of answers is `{(pair one one)}, {(s zero)}`. -/
theorem run_through_translation :
    ∃ L, Frontier (D := D) N program final L ∧
      (∀ x ∈ L, Relation.ReflTransGen (Fires N program) (Hosting.start N program query) x.2.1) ∧
      frontierAnswers N L = {{answer2}, {answer1}} := by
  obtain ⟨L, frontier, reached⟩ := runs_forward N (D := D) (P := program) (supply := supply)
    (fun _ => 0) query program_plain query_plain query_unopened runs
  exact ⟨L, frontier, reached, (frontier_answers N frontier).symm.trans final_answers⟩

/-! ## Controls -/

/-- The normal form `(pair one one)` of the right side at the second call. -/
def normalForm : MData := tuple [sym "pair", sym "one", sym "one"]

theorem normalForm_unopened : ∀ t ∈ (Comp.apply normalForm : Comp mkeys [] () MTy).data,
    ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [Comp.data, List.mem_singleton] at member
  subst member
  simp [normalForm, tuple, tupleArgs, sym, support, supportArgs] at inside

/-- **The equation's schema does not fire on a normal form.** At the start of the query
`(apply (pair one one))`, the canonical firing of the equation's schema is not admitted: the copy of
`(app (lam x. $F x) $a)` does not unify with `(pair one one)` modulo syntax. -/
theorem normal_form_refused :
    ¬ (canonicalAt (Hosting.start N program (.apply normalForm)) (schema N betaEq)
      (schema_mem N program (List.mem_singleton_self _)) program.equations.length).Admits
        (Interface.Frames.contextual MSig) (Hosting.start N program (.apply normalForm)) := by
  rw [schema_admitted_iff N (start_represents N program (.apply normalForm) normalForm_unopened)
    (List.mem_singleton_self _)]
  rintro ⟨X, target, σ', solved⟩
  have same := (models_singleton σ' _).mp ((models_append σ' [] _).mp solved).2
  have heads : headSymbol (instantiate σ' (instantiate (copyAt mkeys 0) betaEq.lhs)) =
      headSymbol (instantiate σ' normalForm) := congrArg headSymbol same
  have left : headSymbol (instantiate σ' (instantiate (copyAt mkeys 0) betaEq.lhs)) = some "app" := rfl
  have right : headSymbol (instantiate σ' normalForm) = some "pair" := rfl
  rw [left, right] at heads
  simp at heads

/-- A program with no equations. -/
def noEquations : SourceLanguage.Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

/-- A query outside the fragment: text read as code. -/
def runQuery : Comp mkeys [] () MTy := .run (sym "x")

/-- Outside the fragment, the source moves: `run` reads the text as code. -/
theorem outside_moves :
    ∃ C', SourceLanguage.Step D noEquations supply (Config.initial (fun _ => 0) runQuery) C' := by
  have principal : Principal ([] : List (Constraint mkeys [] ())) (generator (fam mkeys)) := by
    refine ⟨fun e member => by simp at member, ?_⟩
    intro X target σ' _ name
    exact instantiate_generator σ' name
  exact ⟨_, Step.single live_nil (.run _ [] (sym "x") [] [] _ principal)⟩

/-- **Outside the fragment, the translation has no firing at all.** The start of `(run x)` represents
its alternative, whose row reads `eval(outside)`; no rule takes it. -/
theorem outside_still (s' : HostState MSig) :
    ¬ Fires N noEquations (Hosting.start N noEquations runQuery) s' := by
  have unopened : ∀ t ∈ runQuery.data, ∀ x ∈ support t, x.scopes = [] := by
    intro t member x inside
    simp only [runQuery, Comp.data, List.mem_singleton] at member
    subst member
    simp [sym, support, supportArgs] at inside
  have rep := start_represents N noEquations runQuery unopened
  rintro ⟨⟨rule, member, ext, opening, selection, seen⟩, admitted, _⟩
  rcases (mem_translate N).mp member with control | ⟨e, eMember, _⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨t, focus⟩ := shape_ret N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at reads
      obtain ⟨t, _, focus, _⟩ := shape_apply N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, focus⟩ := shape_choice N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨c, d, focus⟩ := shape_choice N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, _, _, focus⟩ := shape_bindStart N reads
      cases focus
    · obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N rep admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, _, _, frames⟩ := shape_bindValue N reads
      cases frames
  · cases eMember

#print axioms runs
#print axioms final_answers
#print axioms final_quiescent
#print axioms run_through_translation
#print axioms normal_form_refused
#print axioms outside_moves
#print axioms outside_still

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleChoice
