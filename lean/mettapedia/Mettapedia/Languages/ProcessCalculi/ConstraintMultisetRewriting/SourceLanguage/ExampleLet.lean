import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# `let` shadows, and `let` crosses

Names are resolved to sites (the settled rule: an arrow's pattern names are its own, fresh at each
run, unless they are written as crossing an outer name).

* **Shadowing**: `(let $x 1 (let $x 2 $x))`; the inner `$x` is the inner arrow's own name. One answer,
  `2` (`shadow_example`).
* **Crossing that tests**: `(let $x 1 (let {$x} $x 2 $x))`; the inner pattern is the outer `$x`, so the
  inner arrow tests it: `1 ≐ 2` has no solution, and the bag is empty (`cross_test_example`).
* **Crossing that refines a variable of the query**: `(let {$x} $x 7 (pair ok $x))`; the query's own
  `$x` is bound by the arrow. One answer, `(pair ok 7)` (`cross_refine_example`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleLet

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

abbrev D := untyped.discipline

def program : Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

def supply : ℕ → MClosed := fun _ => csym "space"

/-- A solution sending every first-order name to `value` (and higher arities to `value` weakened). -/
def constant (value : MClosed) : Assignment (fam mkeys) noNames :=
  fun _ => Rigid.includeTerm noNames (rename (Γ := []) (fun _ impossible => nomatch impossible) value)

/-! ## Shadowing -/

def shadowQuery : Comp mkeys [] () MTy :=
  .let_ [10] (foD [] [10] 0) (.ret (num 1)) (.let_ [11] (foD [] [11] 0) (.ret (num 2)) (.ret (foD [] [11] 0)))

def shadowStore : List (Constraint mkeys [] ()) :=
  [(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)] ++
    [(instantiate (openAt mkeys [11] 1) (foD [] [11] 0), num 2)]

/-- A solution of the shadowing store. -/
def shadowSolution : Assignment (fam mkeys) noNames := fun x =>
  match x with
  | ⟨[0], ⟨[10], 0, ([], ())⟩⟩ => Rigid.includeTerm noNames (cnum 1)
  | ⟨[1], ⟨[11], 0, ([], ())⟩⟩ => Rigid.includeTerm noNames (cnum 2)
  | ⟨_, ⟨_, _, (_, _)⟩⟩ => Rigid.includeTerm noNames (rename (Γ := []) (fun _ impossible => nomatch impossible) (cnum 0))

theorem shadow_live : Solvable shadowStore :=
  ⟨Empty, noNames, shadowSolution, fun e member => by
    simp only [shadowStore, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl⟩

def shadowFinal : Config mkeys [] () MTy :=
  ⟨⟨2, 0, fun _ => 0⟩, {⟨shadowStore, .value (instantiate (openAt mkeys [11] 1) (foD [] [11] 0)), [], []⟩}⟩

theorem shadow_runs : Runs D program supply (Config.initial (fun _ => 0) shadowQuery) shadowFinal := by
  have live1 : Solvable ([] ++ [(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)] :
      List (Constraint mkeys [] ())) := solvable_of_append (two := [_]) shadow_live
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, fun _ => 0⟩,
    {⟨shadowStore, .eval (.ret (instantiate (openAt mkeys [11] 1) (foD [] [11] 0))), [], []⟩}⟩) ?_
    (step_one shadow_live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
    {⟨[(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)], .value (num 2),
      [.bindTo [11] (foD [] [11] 0) (.ret (foD [] [11] 0))], []⟩}⟩) ?_
    (step_one live1 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
    {⟨[(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)], .eval (.ret (num 2)),
      [.bindTo [11] (foD [] [11] 0) (.ret (foD [] [11] 0))], []⟩}⟩) ?_
    (step_one live1 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
    {⟨[(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)],
      .eval (.let_ [11] (foD [] [11] 0) (.ret (num 2)) (.ret (foD [] [11] 0))), [], []⟩}⟩) ?_
    (step_one live1 (.letStart _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
    {⟨[], .value (num 1), [.bindTo [10] (foD [] [10] 0)
      (.let_ [11] (foD [] [11] 0) (.ret (num 2)) (.ret (foD [] [11] 0)))], []⟩}⟩) ?_
    (step_one (solvable_of_append live1) (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
    {⟨[], .eval (.ret (num 1)), [.bindTo [10] (foD [] [10] 0)
      (.let_ [11] (foD [] [11] 0) (.ret (num 2)) (.ret (foD [] [11] 0)))], []⟩}⟩) ?_
    (step_one (solvable_of_append live1) (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one (solvable_of_append live1) (.letStart _ _ _ _ _ _ _ _))

theorem shadow_determines :
    Determines shadowStore (instantiate (openAt mkeys [11] 1) (foD [] [11] 0)) (cnum 2) := by
  refine ⟨shadow_live, fun target σ' solved => ?_⟩
  exact solved (instantiate (openAt mkeys [11] 1) (foD [] [11] 0), num 2) (by simp [shadowStore])

theorem shadow_example :
    ∃ C, Runs D program supply (Config.initial (fun _ => 0) shadowQuery) C ∧
      Config.Quiescent (D := D) program supply C ∧ Config.answers (D := D) C = {{cnum 2}} := by
  refine ⟨shadowFinal, shadow_runs, ?_, ?_⟩
  · intro b member _ w' bs moved
    have only : b = ⟨shadowStore, .value (instantiate (openAt mkeys [11] 1) (foD [] [11] 0)), [], []⟩ :=
      Multiset.mem_singleton.mp member
    subst only
    cases moved
  · have bag := answers_singleton (D := D) (w := ⟨2, 0, fun _ => 0⟩)
      (b := ⟨shadowStore, .value (instantiate (openAt mkeys [11] 1) (foD [] [11] 0)), [], []⟩)
      ⟨rfl, _, rfl⟩ shadow_live
    rw [answer_of_determines rfl shadow_determines] at bag
    exact bag

/-! ## Crossing that tests -/

def crossTestQuery : Comp mkeys [] () MTy :=
  .let_ [10] (foD [] [10] 0) (.ret (num 1)) (.let_ [11] (foD [] [10] 0) (.ret (num 2)) (.ret (foD [] [10] 0)))

def crossTestStore : List (Constraint mkeys [] ()) :=
  [(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)] ++
    [(instantiate (openAt mkeys [11] 1) (instantiate (openAt mkeys [10] 0) (foD [] [10] 0)), num 2)]

/-- The tested store has no solution: the crossing name is both `1` and `2`. -/
theorem crossTest_dead : ¬ Solvable crossTestStore := by
  rintro ⟨X, target, σ', solved⟩
  have one := solved (instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1) (by simp [crossTestStore])
  have two := solved (instantiate (openAt mkeys [11] 1) (instantiate (openAt mkeys [10] 0) (foD [] [10] 0)), num 2)
    (by simp [crossTestStore])
  have same : (instantiate σ' (num 1) : Term (signature MSig target) [] ()) = instantiate σ' (num 2) :=
    one.symm.trans two
  change (Term.op (Sum.inl (MOp.num 1)) Args.nil : Term (signature MSig target) [] ()) =
    Term.op (Sum.inl (MOp.num 2)) Args.nil at same
  injection same with _ _ hop _
  simp at hop

def crossTestFinal : Config mkeys [] () MTy :=
  ⟨⟨2, 0, fun _ => 0⟩, {⟨crossTestStore, .eval (.ret (instantiate (openAt mkeys [11] 1)
    (instantiate (openAt mkeys [10] 0) (foD [] [10] 0)))), [], []⟩}⟩

theorem crossTest_runs : Runs D program supply (Config.initial (fun _ => 0) crossTestQuery) crossTestFinal := by
  have live1 : Solvable ([] ++ [(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)] :
      List (Constraint mkeys [] ())) :=
    ⟨Empty, noNames, constant (cnum 1), fun e member => by
      simp only [List.nil_append, List.mem_singleton] at member
      subst member; rfl⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
    {⟨[(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)], .value (num 2),
      [.bindTo [11] (instantiate (openAt mkeys [10] 0) (foD [] [10] 0))
        (.ret (instantiate (openAt mkeys [10] 0) (foD [] [10] 0)))], []⟩}⟩) ?_
    (step_one live1 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
    {⟨[(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)], .eval (.ret (num 2)),
      [.bindTo [11] (instantiate (openAt mkeys [10] 0) (foD [] [10] 0))
        (.ret (instantiate (openAt mkeys [10] 0) (foD [] [10] 0)))], []⟩}⟩) ?_
    (step_one live1 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
    {⟨[(instantiate (openAt mkeys [10] 0) (foD [] [10] 0), num 1)],
      .eval ((Comp.let_ [11] (foD [] [10] 0) (.ret (num 2)) (.ret (foD [] [10] 0))).inst (openAt mkeys [10] 0)),
      [], []⟩}⟩) ?_
    (step_one live1 (.letStart _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
    {⟨[], .value (num 1), [.bindTo [10] (foD [] [10] 0)
      (.let_ [11] (foD [] [10] 0) (.ret (num 2)) (.ret (foD [] [10] 0)))], []⟩}⟩) ?_
    (step_one (solvable_of_append live1) (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
    {⟨[], .eval (.ret (num 1)), [.bindTo [10] (foD [] [10] 0)
      (.let_ [11] (foD [] [10] 0) (.ret (num 2)) (.ret (foD [] [10] 0)))], []⟩}⟩) ?_
    (step_one (solvable_of_append live1) (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one (solvable_of_append live1) (.letStart _ _ _ _ _ _ _ _))

theorem cross_test_example :
    ∃ C, Runs D program supply (Config.initial (fun _ => 0) crossTestQuery) C ∧
      Config.Quiescent (D := D) program supply C ∧ Config.answers (D := D) C = 0 := by
  refine ⟨crossTestFinal, crossTest_runs, ?_, ?_⟩
  · intro b member live
    have only : b = ⟨crossTestStore, .eval (.ret (instantiate (openAt mkeys [11] 1)
        (instantiate (openAt mkeys [10] 0) (foD [] [10] 0)))), [], []⟩ := Multiset.mem_singleton.mp member
    subst only
    exact absurd live crossTest_dead
  · exact answers_singleton_dead (D := D) crossTest_dead

/-! ## Crossing that refines a variable of the query -/

def crossRefineQuery : Comp mkeys [] () MTy :=
  .let_ [10] (foD [] [9] 0) (.ret (num 7)) (.ret (tuple [sym "pair", sym "ok", foD [] [9] 0]))

def crossRefineStore : List (Constraint mkeys [] ()) :=
  [(instantiate (openAt mkeys [10] 0) (foD [] [9] 0), num 7)]

theorem crossRefine_live : Solvable crossRefineStore :=
  ⟨Empty, noNames, constant (cnum 7), fun e member => by
    simp only [crossRefineStore, List.mem_singleton] at member
    subst member; rfl⟩

def crossRefineFinal : Config mkeys [] () MTy :=
  ⟨⟨1, 0, fun _ => 0⟩, {⟨crossRefineStore,
    .value (instantiate (openAt mkeys [10] 0) (tuple [sym "pair", sym "ok", foD [] [9] 0])), [], []⟩}⟩

theorem crossRefine_runs :
    Runs D program supply (Config.initial (fun _ => 0) crossRefineQuery) crossRefineFinal := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩, {⟨crossRefineStore,
    .eval (.ret (instantiate (openAt mkeys [10] 0) (tuple [sym "pair", sym "ok", foD [] [9] 0]))), [], []⟩}⟩) ?_
    (step_one crossRefine_live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
    {⟨[], .value (num 7), [.bindTo [10] (foD [] [9] 0) (.ret (tuple [sym "pair", sym "ok", foD [] [9] 0]))], []⟩}⟩) ?_
    (step_one live_nil (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
    {⟨[], .eval (.ret (num 7)), [.bindTo [10] (foD [] [9] 0)
      (.ret (tuple [sym "pair", sym "ok", foD [] [9] 0]))], []⟩}⟩) ?_
    (step_one live_nil (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (step_one live_nil (.letStart _ _ _ _ _ _ _ _))

theorem crossRefine_determines :
    Determines crossRefineStore (instantiate (openAt mkeys [10] 0) (tuple [sym "pair", sym "ok", foD [] [9] 0]))
      (ctuple [csym "pair", csym "ok", cnum 7]) := by
  refine ⟨crossRefine_live, fun target σ' solved => ?_⟩
  have bound := solved _ (List.mem_singleton_self _)
  have value : σ' (fo [] [9] 0) = Rigid.includeTerm target (cnum 7) := by
    rw [← instantiate_foD σ' [] [9] 0]
    exact bound
  show tupleAt [symAt "pair", symAt "ok", instantiate σ' (foD [] [9] 0)] = _
  rw [instantiate_foD, value]
  rfl

theorem cross_refine_example :
    ∃ C, Runs D program supply (Config.initial (fun _ => 0) crossRefineQuery) C ∧
      Config.Quiescent (D := D) program supply C ∧
        Config.answers (D := D) C = {{ctuple [csym "pair", csym "ok", cnum 7]}} := by
  refine ⟨crossRefineFinal, crossRefine_runs, ?_, ?_⟩
  · intro b member _ w' bs moved
    have only : b = ⟨crossRefineStore,
        .value (instantiate (openAt mkeys [10] 0) (tuple [sym "pair", sym "ok", foD [] [9] 0])), [], []⟩ :=
      Multiset.mem_singleton.mp member
    subst only
    cases moved
  · have bag := answers_singleton (D := D) (w := ⟨1, 0, fun _ => 0⟩)
      (b := ⟨crossRefineStore,
        .value (instantiate (openAt mkeys [10] 0) (tuple [sym "pair", sym "ok", foD [] [9] 0])), [], []⟩)
      ⟨rfl, _, rfl⟩ crossRefine_live
    rw [answer_of_determines rfl crossRefine_determines] at bag
    exact bag

#print axioms shadow_example
#print axioms cross_test_example
#print axioms cross_refine_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleLet
