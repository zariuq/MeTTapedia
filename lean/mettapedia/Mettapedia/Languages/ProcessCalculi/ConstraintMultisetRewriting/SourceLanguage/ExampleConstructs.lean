import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# `check`, `fail`, and shared cells (`delay`, `force`)

* **A check depends on the discipline** (`check_refused_numbers`, `check_admitted_numbers`,
  `check_admitted_untyped`): `(check Number a)` is refused by the discipline whose `Number` admits only
  integers (the bag is empty and the alternative ends refused), and passes under the trivial discipline
  (bag `{a}`); `(check Number 3)` passes under both.
* **`fail` drops an alternative** (`fail_example`): `(choice 1 fail)` has the bag `{1}`.
* **A shared cell runs once per alternative** (`need_example`): `(delay $c (choice 1 2) (let $y (force $c)
  (let $z (force $c) (pair $y $z))))` has the bag `{(pair 1 1), (pair 2 2)}`: both demands see the one
  choice the first demand made.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleConstructs

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

def supply : ℕ → MClosed := fun _ => csym "space"

/-- A program without equations. -/
def P (Ty : Type) : Program mkeys [] () Ty := ⟨[], fun t => .apply t⟩

/-- Every reading of a datum without names is the datum itself. -/
theorem reads_rigid (g g' : MClosed) :
    Reads ([] : List (Constraint mkeys [] ())) (Rigid.includeTerm (fam mkeys) g) g' ↔ g' = g :=
  Determines.reads_iff ⟨live_nil, fun _ _ _ => Rigid.instantiate_include _ g⟩ g'

/-! ## Checks -/

/-- The discipline whose `Number` admits only integers. -/
abbrev DN : Discipline MSig [] () := numbers.discipline
/-- The trivial discipline. -/
abbrev DT : Discipline MSig [] () := untyped.discipline

def checkA : Comp mkeys [] () MTy := .check (.value "Number") (.ret (sym "a"))
def check3 : Comp mkeys [] () MTy := .check (.value "Number") (.ret (num 3))

theorem check_refused_numbers :
    ∃ C, Runs DN (P MTy) supply (Config.initial (fun _ => 0) checkA) C ∧
      C.branches = {⟨[], .refused (sym "a") (.value "Number"), [], []⟩} ∧
      Config.Quiescent (D := DN) (P MTy) supply C ∧ Config.answers (D := DN) C = 0 := by
  refine ⟨⟨⟨0, 0, fun _ => 0⟩, {⟨[], .refused (sym "a") (.value "Number"), [], []⟩}⟩, ?_, rfl,
    fun b member _ _ _ => by rw [Multiset.mem_singleton.mp member]; exact Move.refused_still, ?_⟩
  · refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
        {⟨[], .value (sym "a"), [.checkAt (.value "Number")], []⟩}⟩) ?_
      (step_one live_nil (.refused _ _ _ _ _ _ (fun g reads => ?_)))
    · refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
          {⟨[], .eval (.ret (sym "a")), [.checkAt (.value "Number")], []⟩}⟩) ?_
        (step_one live_nil (.ret _ _ _ _ _))
      exact Relation.ReflTransGen.single (step_one live_nil (.checkStart _ _ _ _ _ _))
    · have same := (reads_rigid (csym "a") g).mp reads
      subst same
      rintro ⟨k, h⟩
      cases h
  · classical
    simp only [Config.answers]
    rw [Multiset.filter_singleton, if_neg (by rintro ⟨⟨_, _, h⟩, _⟩; cases h)]
    rfl

theorem check_admitted_untyped :
    ∃ C, Runs DT (P MTy) supply (Config.initial (fun _ => 0) checkA) C ∧
      Config.Quiescent (D := DT) (P MTy) supply C ∧ Config.answers (D := DT) C = {{csym "a"}} := by
  refine ⟨⟨⟨0, 0, fun _ => 0⟩, {⟨[], .value (sym "a"), [], []⟩}⟩, ?_, Config.quiescent_single, ?_⟩
  · refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
        {⟨[], .value (sym "a"), [.checkAt (.value "Number")], []⟩}⟩) ?_
      (step_one live_nil (.admitted _ _ _ _ _ _ (fun _ _ => trivial)))
    refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
        {⟨[], .eval (.ret (sym "a")), [.checkAt (.value "Number")], []⟩}⟩) ?_
      (step_one live_nil (.ret _ _ _ _ _))
    exact Relation.ReflTransGen.single (step_one live_nil (.checkStart _ _ _ _ _ _))
  · have bag := answers_singleton (D := DT) (w := ⟨0, 0, fun _ => 0⟩) (b := ⟨[], .value (sym "a"), [], []⟩)
      ⟨rfl, _, rfl⟩ live_nil
    rw [answer_of_determines (g := csym "a") rfl ⟨live_nil, fun _ _ _ => rfl⟩] at bag
    exact bag

theorem check_admitted_numbers :
    ∃ C, Runs DN (P MTy) supply (Config.initial (fun _ => 0) check3) C ∧
      Config.Quiescent (D := DN) (P MTy) supply C ∧ Config.answers (D := DN) C = {{cnum 3}} := by
  refine ⟨⟨⟨0, 0, fun _ => 0⟩, {⟨[], .value (num 3), [], []⟩}⟩, ?_, Config.quiescent_single, ?_⟩
  · refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
        {⟨[], .value (num 3), [.checkAt (.value "Number")], []⟩}⟩) ?_
      (step_one live_nil (.admitted _ _ _ _ _ _ (fun g reads => ?_)))
    · refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
          {⟨[], .eval (.ret (num 3)), [.checkAt (.value "Number")], []⟩}⟩) ?_
        (step_one live_nil (.ret _ _ _ _ _))
      exact Relation.ReflTransGen.single (step_one live_nil (.checkStart _ _ _ _ _ _))
    · have same := (reads_rigid (cnum 3) g).mp reads
      subst same
      exact ⟨3, rfl⟩
  · have bag := answers_singleton (D := DN) (w := ⟨0, 0, fun _ => 0⟩) (b := ⟨[], .value (num 3), [], []⟩)
      ⟨rfl, _, rfl⟩ live_nil
    rw [answer_of_determines (g := cnum 3) rfl ⟨live_nil, fun _ _ _ => rfl⟩] at bag
    exact bag

/-! ## `fail` -/

abbrev D0 : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

theorem fail_example :
    ∃ C, Runs D0 (P MTy) supply (Config.initial (fun _ => 0) (.choice (.ret (num 1)) .fail)) C ∧
      Config.Quiescent (D := D0) (P MTy) supply C ∧ Config.answers (D := D0) C = {{cnum 1}} := by
  refine ⟨⟨⟨0, 0, fun _ => 0⟩, {⟨[], .value (num 1), [], []⟩}⟩, ?_, Config.quiescent_single, ?_⟩
  · refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩, {⟨[], .eval (.ret (num 1)), [], []⟩}⟩) ?_
      (step_one live_nil (.ret _ _ _ _ _))
    refine Relation.ReflTransGen.tail (b := ⟨⟨0, 0, fun _ => 0⟩,
        ⟨[], .eval .fail, [], []⟩ ::ₘ ⟨[], .eval (.ret (num 1)), [], []⟩ ::ₘ 0⟩) ?_
      (Step.of_eq (D := D0) (P := P MTy) (supply := supply) (rest := ⟨[], .eval (.ret (num 1)), [], []⟩ ::ₘ 0)
        rfl (by rw [zero_add]; rfl) live_nil (.fail _ _ _ _))
    exact Relation.ReflTransGen.single
      (Step.of_eq (D := D0) (P := P MTy) (supply := supply) (rest := 0) rfl
        (by rw [add_zero]; exact Multiset.cons_swap _ _ _) live_nil (.choice _ _ _ _ _ _))
  · have bag := answers_singleton (D := D0) (w := ⟨0, 0, fun _ => 0⟩) (b := ⟨[], .value (num 1), [], []⟩)
      ⟨rfl, _, rfl⟩ live_nil
    rw [answer_of_determines (g := cnum 1) rfl ⟨live_nil, fun _ _ _ => rfl⟩] at bag
    exact bag

/-! ## A shared cell -/

def c : MData := foD [] [10] 0
def y : MData := foD [] [11] 0
def z : MData := foD [] [12] 0
def c0 : MData := foD [0] [10] 0

def k2 : Comp mkeys [] () MTy := .let_ [12] z (.force c0) (.ret (tuple [sym "pair", y, z]))
def body : Comp mkeys [] () MTy := .let_ [11] y (.force c) (.let_ [12] z (.force c) (.ret (tuple [sym "pair", y, z])))
def cellComp : Comp mkeys [] () MTy := .choice (.ret (num 1)) (.ret (num 2))
def needQuery : Comp mkeys [] () MTy := .delay [10] c cellComp body

def yAt (n : ℕ) : MData := foD [n] [11] 0
def zAt (n : ℕ) : MData := foD [n] [12] 0
def K1 (v : Int) : List (Constraint mkeys [] ()) := [(c0, num v)]
def K2 (v : Int) (n : ℕ) : List (Constraint mkeys [] ()) := K1 v ++ [(yAt n, num v)]
def K3 (v : Int) (n m : ℕ) : List (Constraint mkeys [] ()) := K2 v n ++ [(zAt m, c0)]
def fin (v : Int) (n m : ℕ) : Branch mkeys [] () MTy :=
  ⟨K3 v n m, .value (tuple [sym "pair", yAt n, zAt m]), [], []⟩

def f11 : Frame mkeys [] () MTy := .bindTo [11] y k2
def start (v : Int) : Branch mkeys [] () MTy := ⟨[], .eval (.ret (num v)), [.memo c0, f11], []⟩

def closeNeed (v : Int) (n m : ℕ) : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [10], 0), cnum v), (([n], [11], 0), cnum v), (([m], [12], 0), cnum v)] (csym "a")

theorem live_1 : Solvable (K3 1 1 2) := ⟨Empty, noNames, closeNeed 1 1 2, by decide⟩
theorem live_2 : Solvable (K3 2 3 4) := ⟨Empty, noNames, closeNeed 2 3 4, by decide⟩

/-- One alternative after the choice: it records the cell, binds `$y`, reads the recorded cell for `$z`. -/
theorem branch_runs (v : Int) (n : ℕ) (live : Solvable (K3 v n (n + 1))) :
    Runs D0 (P MTy) supply ⟨⟨n, 0, fun _ => 0⟩, {start v}⟩ ⟨⟨n + 2, 0, fun _ => 0⟩, {fin v n (n + 1)}⟩ := by
  have live2 : Solvable (K2 v n) := solvable_of_append live
  have live1 : Solvable (K1 v) := solvable_of_append live2
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, fun _ => 0⟩,
      {⟨K3 v n (n + 1), .eval (.ret (tuple [sym "pair", yAt n, zAt (n + 1)])), [], []⟩}⟩) ?_
    (step_one live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, fun _ => 0⟩,
      {⟨K2 v n, .value c0, [.bindTo [12] z (.ret (tuple [sym "pair", yAt n, z]))], []⟩}⟩) ?_
    (step_one live2 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, fun _ => 0⟩,
      {⟨K2 v n, .eval (.force c0), [.bindTo [12] z (.ret (tuple [sym "pair", yAt n, z]))], []⟩}⟩) ?_
    (step_one live2 (.forceDone _ _ _ _ _ (fun _ member => (by cases member))))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, fun _ => 0⟩, {⟨K2 v n, .eval (k2.inst (openAt mkeys [11] n)), [], []⟩}⟩) ?_
    (step_one live2 (.letStart _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n, 0, fun _ => 0⟩, {⟨K1 v, .value (num v), [f11], []⟩}⟩) ?_
    (step_one live1 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n, 0, fun _ => 0⟩, {⟨[], .value (num v), [.memo c0, f11], []⟩}⟩) ?_
    (step_one live_nil (.memo _ _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one live_nil (.ret _ _ _ _ _))

theorem need_runs :
    Runs D0 (P MTy) supply (Config.initial (fun _ => 0) needQuery)
      ⟨⟨5, 0, fun _ => 0⟩, fin 2 3 4 ::ₘ fin 1 1 2 ::ₘ 0⟩ := by
  have first : Runs D0 (P MTy) supply ⟨⟨1, 0, fun _ => 0⟩, {start 1} + (start 2 ::ₘ 0)⟩
      ⟨⟨3, 0, fun _ => 0⟩, {fin 1 1 2} + (start 2 ::ₘ 0)⟩ := (branch_runs 1 1 live_1).frame (start 2 ::ₘ 0)
  have second : Runs D0 (P MTy) supply ⟨⟨3, 0, fun _ => 0⟩, {start 2} + (fin 1 1 2 ::ₘ 0)⟩
      ⟨⟨5, 0, fun _ => 0⟩, {fin 2 3 4} + (fin 1 1 2 ::ₘ 0)⟩ := (branch_runs 2 3 live_2).frame (fin 1 1 2 ::ₘ 0)
  rw [Multiset.singleton_add, Multiset.singleton_add] at first second
  rw [Multiset.cons_swap (start 2) (fin 1 1 2)] at second
  refine (Relation.ReflTransGen.trans ?_ first).trans second
  -- before the choice: open the cell, start the arrow, force the pending cell, choose
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
      {⟨[], .eval cellComp, [.memo c0, f11], []⟩}⟩) ?_
    (Step.of_eq (D := D0) (P := P MTy) (supply := supply) (rest := 0) rfl
      (by rw [add_zero]; rfl) live_nil (.choice _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
      {⟨[], .eval (.force c0), [f11], [(c0, cellComp)]⟩}⟩) ?_
    (step_one (D := D0) (P := P MTy) (supply := supply) live_nil
      (.forcePending ⟨1, 0, fun _ => 0⟩ [] c0 c0 cellComp [f11] [] [] (fun _ _ _ => rfl)))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, fun _ => 0⟩,
      {⟨[], .eval (body.inst (openAt mkeys [10] 0)), [], [(c0, cellComp)]⟩}⟩) ?_
    (step_one live_nil (.letStart _ _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one live_nil (.delay _ _ _ _ _ _ _ _))

theorem fin_determines (v : Int) (n m : ℕ) (live : Solvable (K3 v n m)) :
    Determines (K3 v n m) (tuple [sym "pair", yAt n, zAt m]) (ctuple [csym "pair", cnum v, cnum v]) := by
  refine ⟨live, fun target σ solved => ?_⟩
  have cell := solved (c0, num v) (by simp [K3, K2, K1])
  have yv := solved (yAt n, num v) (by simp [K3, K2])
  have zc := solved (zAt m, c0) (by simp [K3])
  show tupleAt [symAt "pair", instantiate σ (yAt n), instantiate σ (zAt m)] = _
  rw [yv, zc, cell]
  rfl

theorem need_example :
    ∃ C, Runs D0 (P MTy) supply (Config.initial (fun _ => 0) needQuery) C ∧
      Config.Quiescent (D := D0) (P MTy) supply C ∧
      Config.answers (D := D0) C =
        {{ctuple [csym "pair", cnum 2, cnum 2]}, {ctuple [csym "pair", cnum 1, cnum 1]}} := by
  refine ⟨_, need_runs, Config.quiescent_of_finished fun b member _ => ?_, ?_⟩
  · simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨rfl, _, rfl⟩
  rw [answers_cons_finished (D := D0) (b := fin 2 3 4) ⟨rfl, _, rfl⟩ live_2,
    answers_cons_finished (D := D0) (b := fin 1 1 2) ⟨rfl, _, rfl⟩ live_1, answers_zero,
    answer_of_determines rfl (fin_determines 2 3 4 live_2), answer_of_determines rfl (fin_determines 1 1 2 live_1)]
  rfl

#print axioms need_example
#print axioms check_refused_numbers
#print axioms check_admitted_untyped
#print axioms check_admitted_numbers
#print axioms fail_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleConstructs
