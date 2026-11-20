import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# An equation under a binder, used at two different arguments

The equation `(= (app (lam x. $F x) $a) ($F $a))` has a second-order pattern under the binder `lam`.
The query uses it twice in one run, at `(app (lam x. (s x)) zero)` and at
`(app (lam x. (pair x x)) one)`, and returns both results:

`(let $y (app (lam x. (s x)) zero) (let $z (app (lam x. (pair x x)) one) (pair $y $z)))`

Its one answer is `(pair (s zero) (pair one one))` (`beta_answers`). The answer depends on the binder
(each use matches `$F` to a different body) and on freshness at each use: both uses solve `$F` and
`$a`, at different values, in one store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleBeta

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

abbrev D := untyped.discipline

/-- `(lam x. body)` at the empty context. -/
abbrev lamD (body : Term (signature MSig (fam mkeys)) [()] ()) : MData := lamAt body

/-- The equation `(= (app (lam x. $F x) $a) ($F $a))` at site `[100]`. -/
def betaEq : Equation mkeys [] () MTy :=
  ⟨[100], tuple [sym "app", lamD (hoD [] [100] 0 bv), foD [] [100] 1], .ret (hoD [] [100] 0 (foD [] [100] 1))⟩

def program : Program mkeys [] () MTy := ⟨[betaEq], fun t => .apply t⟩

/-- The two calls. -/
def call1 : MData := tuple [sym "app", lamD (tupleAt [symAt "s", bv]), sym "zero"]
def call2 : MData := tuple [sym "app", lamD (tupleAt [symAt "pair", bv, bv]), sym "one"]

/-- The query. -/
def query : Comp mkeys [] () MTy :=
  .let_ [10] (foD [] [10] 0) (.apply call1)
    (.let_ [11] (foD [] [11] 0) (.apply call2) (.ret (tuple [sym "pair", foD [] [10] 0, foD [] [11] 0])))

def supply : ℕ → MClosed := fun _ => csym "space"

def start : Config mkeys [] () MTy := Config.initial (fun _ => 0) query

/-- The expected answer. -/
def answer : MClosed :=
  ctuple [csym "pair", ctuple [csym "s", csym "zero"], ctuple [csym "pair", csym "one", csym "one"]]

/-! ## The store of the run -/

def c0 : Constraint mkeys [] () := (instantiate (copyAt mkeys 0) betaEq.lhs, call1)
def v1 : MData := hoD [0] [100] 0 (foD [0] [100] 1)
def y1 : Constraint mkeys [] () := (instantiate (openAt mkeys [10] 1) (foD [] [10] 0), v1)
def c2 : Constraint mkeys [] () := (instantiate (copyAt mkeys 2) betaEq.lhs, call2)
def v2 : MData := hoD [2] [100] 0 (foD [2] [100] 1)
def y2 : Constraint mkeys [] () := (instantiate (openAt mkeys [11] 3) (foD [] [11] 0), v2)

def finalStore : List (Constraint mkeys [] ()) := [c0] ++ [y1] ++ [c2] ++ [y2]

/-- A solution of the final store. -/
def σ : Assignment (fam mkeys) noNames := fun x =>
  match x with
  | ⟨[0], ⟨[100], 0, ([()], ())⟩⟩ => tupleAt [symAt "s", .var .zero]
  | ⟨[2], ⟨[100], 0, ([()], ())⟩⟩ => tupleAt [symAt "pair", .var .zero, .var .zero]
  | ⟨[0], ⟨[100], 1, ([], ())⟩⟩ => Rigid.includeTerm noNames (csym "zero")
  | ⟨[2], ⟨[100], 1, ([], ())⟩⟩ => Rigid.includeTerm noNames (csym "one")
  | ⟨[1], ⟨[10], 0, ([], ())⟩⟩ => Rigid.includeTerm noNames (ctuple [csym "s", csym "zero"])
  | ⟨[3], ⟨[11], 0, ([], ())⟩⟩ => Rigid.includeTerm noNames (ctuple [csym "pair", csym "one", csym "one"])
  | ⟨_, ⟨_, _, (_, _)⟩⟩ => Rigid.includeTerm noNames (rename (Γ := []) (fun _ impossible => nomatch impossible) (csym "a"))

theorem finalStore_solved : Models σ finalStore := by
  intro e member
  simp only [finalStore, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem finalStore_live : Solvable finalStore := ⟨Empty, noNames, σ, finalStore_solved⟩

/-- Every store of the run is solved by `σ`: it is a part of the final store. -/
theorem live_of_sub {K : List (Constraint mkeys [] ())} (sub : ∀ e ∈ K, e ∈ finalStore) : Solvable K :=
  ⟨Empty, noNames, σ, fun e member => finalStore_solved e (sub e member)⟩

/-! ## The run -/

abbrev W : World mkeys [] () := ⟨0, 0, fun _ => 0⟩
abbrev k1 : Comp mkeys [] () MTy :=
  .let_ [11] (foD [] [11] 0) (.apply call2) (.ret (tuple [sym "pair", foD [] [10] 0, foD [] [11] 0]))
abbrev fs1 : List (Frame mkeys [] () MTy) := [.bindTo [10] (foD [] [10] 0) k1]
abbrev k2 : Comp mkeys [] () MTy := .ret (tuple [sym "pair", foD [1] [10] 0, foD [] [11] 0])
abbrev fs2 : List (Frame mkeys [] () MTy) := [.bindTo [11] (foD [] [11] 0) k2]

/-- The final configuration. -/
def final : Config mkeys [] () MTy :=
  ⟨⟨4, 0, fun _ => 0⟩, {⟨finalStore, .value (tuple [sym "pair", foD [1] [10] 0, foD [3] [11] 0]), [], []⟩}⟩

theorem runs : Runs D program supply start final := by
  have m1 : ∃ e ∈ program.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, call1)]) :=
    ⟨betaEq, List.mem_singleton_self _, live_of_sub (by simp [finalStore, c0])⟩
  have m2 : ∃ e ∈ program.equations,
      Solvable ([c0] ++ [y1] ++ [(instantiate (copyAt mkeys 2) e.lhs, call2)]) :=
    ⟨betaEq, List.mem_singleton_self _, live_of_sub (by simp [finalStore, c2])⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨4, 0, fun _ => 0⟩,
    {⟨[c0] ++ [y1] ++ [c2] ++ [y2], .eval (.ret (tuple [sym "pair", foD [1] [10] 0, foD [3] [11] 0])), [], []⟩}⟩) ?_
    (step_one (live_of_sub (by simp [finalStore])) (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, fun _ => 0⟩,
    {⟨[c0] ++ [y1] ++ [c2], .value v2, fs2, []⟩}⟩) ?_
    (step_one (live_of_sub (by simp [finalStore])) (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, fun _ => 0⟩,
    {⟨[c0] ++ [y1] ++ [c2], .eval (.ret v2), fs2, []⟩}⟩) ?_
    (step_one (live_of_sub (by simp [finalStore])) (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
    {⟨[c0] ++ [y1], .eval (.apply call2), fs2, []⟩}⟩) ?_
    (Step.of_eq (rest := 0) rfl rfl
      (live_of_sub (by simp [finalStore])) (.apply _ _ _ _ _ m2))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
    {⟨[c0] ++ [y1], .eval (.let_ [11] (foD [] [11] 0) (.apply call2) k2), [], []⟩}⟩) ?_
    (step_one (live_of_sub (by simp [finalStore])) (.letStart _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩, {⟨[c0], .value v1, fs1, []⟩}⟩) ?_
    (Step.of_eq (rest := 0) rfl (by simp [y1, v1, k2]; rfl) (live_of_sub (by simp [finalStore]))
      (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩, {⟨[c0], .eval (.ret v1), fs1, []⟩}⟩) ?_
    (step_one (live_of_sub (by simp [finalStore])) (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W, {⟨[], .eval (.apply call1), fs1, []⟩}⟩) ?_
    (Step.of_eq (rest := 0) rfl rfl
      (live_of_sub (by simp)) (.apply _ _ _ _ _ m1))
  exact Relation.ReflTransGen.single (step_one (live_of_sub (by simp)) (.letStart _ _ _ _ _ _ _ _))

/-! ## The answer -/

/-- Every solution of the final store reads the value as the expected answer. -/
theorem final_determines :
    Determines finalStore (tuple [sym "pair", foD [1] [10] 0, foD [3] [11] 0]) answer := by
  refine ⟨finalStore_live, fun target σ' solved => ?_⟩
  have e0 := solved c0 (by simp [finalStore])
  have e1 := solved y1 (by simp [finalStore])
  have e2 := solved c2 (by simp [finalStore])
  have e3 := solved y2 (by simp [finalStore])
  have h0 : tupleAt [symAt "app", lamAt (σ' (ho [0] [100] 0)), σ' (fo [0] [100] 1)] =
      tupleAt [symAt "app", lamAt (tupleAt [symAt "s", bv]), symAt "zero"] := by
    rw [← instantiate_foD σ' [0] [100] 1, ← instantiate_hoD_bv σ' [0] [100] 0]
    exact e0
  have h2 : tupleAt [symAt "app", lamAt (σ' (ho [2] [100] 0)), σ' (fo [2] [100] 1)] =
      tupleAt [symAt "app", lamAt (tupleAt [symAt "pair", bv, bv]), symAt "one"] := by
    rw [← instantiate_foD σ' [2] [100] 1, ← instantiate_hoD_bv σ' [2] [100] 0]
    exact e2
  obtain ⟨_, f0, a0⟩ := tuple3_inj h0
  obtain ⟨_, f2, a2⟩ := tuple3_inj h2
  have body0 := lamAt_inj f0
  have body2 := lamAt_inj f2
  have r1 : σ' (fo [1] [10] 0) = tupleAt [symAt "s", symAt "zero"] := by
    rw [← instantiate_foD σ' [1] [10] 0]
    refine e1.trans ?_
    show instantiate σ' (hoD [0] [100] 0 (foD [0] [100] 1)) = _
    rw [instantiate_hoD, instantiate_foD, a0, body0]
    rfl
  have r2 : σ' (fo [3] [11] 0) = tupleAt [symAt "pair", symAt "one", symAt "one"] := by
    rw [← instantiate_foD σ' [3] [11] 0]
    refine e3.trans ?_
    show instantiate σ' (hoD [2] [100] 0 (foD [2] [100] 1)) = _
    rw [instantiate_hoD, instantiate_foD, a2, body2]
    rfl
  show tupleAt [symAt "pair", instantiate σ' (foD [1] [10] 0), instantiate σ' (foD [3] [11] 0)] = _
  rw [instantiate_foD, instantiate_foD, r1, r2]
  rfl

/-- The final alternative is finished and live. -/
theorem final_branch_finished :
    Branch.Finished (D := D)
      ⟨finalStore, .value (tuple [sym "pair", foD [1] [10] 0, foD [3] [11] 0]), [], []⟩ := ⟨rfl, _, rfl⟩

/-- **The answer bag**: one answer, `(pair (s zero) (pair one one))`. -/
theorem beta_answers : Config.answers (D := D) final = {{answer}} := by
  have bag := answers_singleton (D := D) (w := ⟨4, 0, fun _ => 0⟩) final_branch_finished finalStore_live
  rw [answer_of_determines rfl final_determines] at bag
  exact bag

/-- Nothing can move at the end. -/
theorem final_quiescent : Config.Quiescent (D := D) program supply final := by
  intro b member _ w' bs moved
  have only : b = ⟨finalStore, .value (tuple [sym "pair", foD [1] [10] 0, foD [3] [11] 0]), [], []⟩ :=
    Multiset.mem_singleton.mp member
  subst only
  cases moved

/-- **The example**: a run of the query reaches a quiescent configuration whose bag of answers is
`{(pair (s zero) (pair one one))}`. -/
theorem beta_example :
    ∃ C, Runs D program supply start C ∧ Config.Quiescent (D := D) program supply C ∧
      Config.answers (D := D) C = {{answer}} :=
  ⟨final, runs, final_quiescent, beta_answers⟩

#print axioms beta_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleBeta
