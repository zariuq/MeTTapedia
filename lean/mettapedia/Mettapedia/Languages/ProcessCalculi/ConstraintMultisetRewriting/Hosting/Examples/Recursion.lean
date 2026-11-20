import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns

/-!
# A recursive function that uses its own result: two frames of one `let` pending at two depths

The program (well formed, with arrows; `program_wellFormed`, `program_arrows`):

* `(= (len Nil) Z)`
* `(= (len (Cons $h $t)) (let $r (len $t) (S $r)))`, the recursive call under a `let`

and the well-formed query `(len (Cons a (Cons b Nil)))` (`query_wellFormed`). The source run
(`runs10`, ten steps, three dead alternatives on the way) ends with the bag `{(S (S Z))}`
(`final_answers`). After four steps the live alternative has **two pending frames of the same `let`
(site `[205]`) at two depths of recursion**, at the levels `[1]` and `[0]` (`two_frames`); when the
base case returns `Z` to the inner one, that alternative is scoped at run time and hygienic
(`invariant_at_two_frames`): the levels keep the two copies of `$r` apart. The run theorem gives a
frontier reached by the step with the same bag (`run_through_translation`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.Recursion

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting

/-- The trivial discipline, with its type language on the nose. -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
abbrev N := mettaNodes

def supply : ℕ → MClosed := fun _ => csym "space"
abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

/-! ## The program and the query -/

def lenT (x : MData) : MData := tuple [sym "len", x]
def consT (a b : MData) : MData := tuple [sym "Cons", a, b]
def sT (x : MData) : MData := tuple [sym "S", x]
def nilT : MData := sym "Nil"
def zT : MData := sym "Z"

abbrev hC : MData := foD [] [204] 0
abbrev tC : MData := foD [] [204] 1
abbrev rL : MData := foD [] [205] 0

def eNil : SourceLanguage.Equation mkeys [] () MTy := ⟨[203], lenT nilT, .ret zT⟩
def eCons : SourceLanguage.Equation mkeys [] () MTy :=
  ⟨[204], lenT (consT hC tC), .let_ [205] rL (.apply (lenT tC)) (.ret (sT rL))⟩

def program : SourceLanguage.Program mkeys [] () MTy := ⟨[eNil, eCons], fun t => .apply t⟩

def L2 : MData := consT (sym "a") (consT (sym "b") nilT)
def query : Comp mkeys [] () MTy := .apply (lenT L2)

theorem program_wellFormed : WellFormed program := by decide

theorem query_wellFormed : QueryWellFormed program [3] query := by decide

theorem program_arrows : ArrowProgram program := by
  intro e member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · trivial
  · exact ⟨trivial, trivial⟩

theorem query_arrows : ArrowComp query := trivial

/-! ## The names the run opens -/

abbrev hN (n : ℕ) : MData := foD [n] [204] 0
abbrev tN (n : ℕ) : MData := foD [n] [204] 1
abbrev rN (n : ℕ) : MData := foD [n] [205] 0
abbrev r31 : MData := foD [3, 1] [205] 0
abbrev r40 : MData := foD [4, 0] [205] 0

/-- The frame of the `let` of the copy at scope `n`. -/
abbrev frameN (n : ℕ) : SourceLanguage.Frame mkeys [] () MTy := .bindTo [205] (rN n) (.ret (sT (rN n)))

abbrev K1 : List (Constraint mkeys [] ()) := [(lenT (consT (hN 0) (tN 0)), lenT L2)]
abbrev K3 : List (Constraint mkeys [] ()) := K1 ++ [(lenT (consT (hN 1) (tN 1)), lenT (tN 0))]
abbrev K5 : List (Constraint mkeys [] ()) := K3 ++ [(lenT nilT, lenT (tN 1))]
abbrev K7 : List (Constraint mkeys [] ()) := K5 ++ [(r31, zT)]
abbrev K9 : List (Constraint mkeys [] ()) := K7 ++ [(r40, sT r31)]

abbrev A0 : Branch mkeys [] () MTy := ⟨[], .eval query, [], []⟩
abbrev D1 : Branch mkeys [] () MTy := ⟨[] ++ [(lenT nilT, lenT L2)], .eval (.ret zT), [], []⟩
abbrev X1 : Branch mkeys [] () MTy :=
  ⟨K1, .eval (.let_ [205] (rN 0) (.apply (lenT (tN 0))) (.ret (sT (rN 0)))), [], []⟩
abbrev X2 : Branch mkeys [] () MTy := ⟨K1, .eval (.apply (lenT (tN 0))), [frameN 0], []⟩
abbrev D3 : Branch mkeys [] () MTy := ⟨K1 ++ [(lenT nilT, lenT (tN 0))], .eval (.ret zT), [frameN 0], []⟩
abbrev X3 : Branch mkeys [] () MTy :=
  ⟨K3, .eval (.let_ [205] (rN 1) (.apply (lenT (tN 1))) (.ret (sT (rN 1)))), [frameN 0], []⟩
abbrev X4 : Branch mkeys [] () MTy := ⟨K3, .eval (.apply (lenT (tN 1))), [frameN 1, frameN 0], []⟩
abbrev X5 : Branch mkeys [] () MTy := ⟨K5, .eval (.ret zT), [frameN 1, frameN 0], []⟩
abbrev D5 : Branch mkeys [] () MTy :=
  ⟨K3 ++ [(lenT (consT (hN 2) (tN 2)), lenT (tN 1))],
    .eval (.let_ [205] (rN 2) (.apply (lenT (tN 2))) (.ret (sT (rN 2)))), [frameN 1, frameN 0], []⟩
abbrev X6 : Branch mkeys [] () MTy := ⟨K5, .value zT, [frameN 1, frameN 0], []⟩
abbrev X7 : Branch mkeys [] () MTy := ⟨K7, .eval (.ret (sT r31)), [frameN 0], []⟩
abbrev X8 : Branch mkeys [] () MTy := ⟨K7, .value (sT r31), [frameN 0], []⟩
abbrev X9 : Branch mkeys [] () MTy := ⟨K9, .eval (.ret (sT r40)), [], []⟩
abbrev X10 : Branch mkeys [] () MTy := ⟨K9, .value (sT r40), [], []⟩

abbrev R5 : Multiset (Branch mkeys [] () MTy) := D5 ::ₘ D3 ::ₘ D1 ::ₘ 0

def C6 : Config mkeys [] () MTy := ⟨⟨3, 0, sp⟩, X6 ::ₘ R5⟩
def final : Config mkeys [] () MTy := ⟨⟨5, 0, sp⟩, X10 ::ₘ R5⟩

/-! ## Life and death -/

/-- One solution of the final store. -/
def σ9 : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [204], 0), csym "a"), (([0], [204], 1), ctuple [csym "Cons", csym "b", csym "Nil"]),
    (([1], [204], 0), csym "b"), (([1], [204], 1), csym "Nil"), (([3, 1], [205], 0), csym "Z"),
    (([4, 0], [205], 0), ctuple [csym "S", csym "Z"])] (csym "q")

theorem models9 : Models σ9 K9 := by
  intro e member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((((rfl | rfl) | rfl) | rfl) | rfl) <;> rfl

theorem live_of_sub {K : List (Constraint mkeys [] ())} (sub : ∀ e ∈ K, e ∈ K9) : Solvable K :=
  ⟨Empty, noNames, σ9, fun e member => models9 e (sub e member)⟩

theorem nil_ne_cons {X : Type} {target : X → MetaArity MSig} {a b c : Term (signature MSig target) [] ()} :
    (symAt "Nil" : Term (signature MSig target) [] ()) ≠ tupleAt [a, b, c] := by
  intro same
  cases same

theorem dead1 : ¬ Solvable D1.store := by
  rintro ⟨X, target, σ, solved⟩
  have e := solved _ (List.mem_singleton_self _)
  have e' : (tupleAt [symAt "len", symAt "Nil"] : Term (signature MSig target) [] ()) =
      tupleAt [symAt "len", tupleAt [symAt "Cons", symAt "a", tupleAt [symAt "Cons", symAt "b", symAt "Nil"]]] := e
  exact nil_ne_cons (tuple2_inj e').2

theorem dead3 : ¬ Solvable D3.store := by
  rintro ⟨X, target, σ, solved⟩
  have e1 := solved _ (List.mem_append_left _ (List.mem_singleton_self _))
  have e2 := solved _ (List.mem_append_right _ (List.mem_singleton_self _))
  change tupleAt [symAt "len", tupleAt [symAt "Cons", instantiate σ (hN 0), instantiate σ (tN 0)]] =
    tupleAt [symAt "len", tupleAt [symAt "Cons", symAt "a", tupleAt [symAt "Cons", symAt "b", symAt "Nil"]]] at e1
  change tupleAt [symAt "len", symAt "Nil"] = tupleAt [symAt "len", instantiate σ (tN 0)] at e2
  have t0 := (tuple3_inj (tuple2_inj e1).2).2.2
  exact nil_ne_cons ((tuple2_inj e2).2.trans t0)

theorem dead5 : ¬ Solvable D5.store := by
  rintro ⟨X, target, σ, solved⟩
  have e1 := solved _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))
  have e2 := solved _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have e3 := solved _ (List.mem_append_right _ (List.mem_singleton_self _))
  change tupleAt [symAt "len", tupleAt [symAt "Cons", instantiate σ (hN 0), instantiate σ (tN 0)]] =
    tupleAt [symAt "len", tupleAt [symAt "Cons", symAt "a", tupleAt [symAt "Cons", symAt "b", symAt "Nil"]]] at e1
  change tupleAt [symAt "len", tupleAt [symAt "Cons", instantiate σ (hN 1), instantiate σ (tN 1)]] =
    tupleAt [symAt "len", instantiate σ (tN 0)] at e2
  change tupleAt [symAt "len", tupleAt [symAt "Cons", instantiate σ (hN 2), instantiate σ (tN 2)]] =
    tupleAt [symAt "len", instantiate σ (tN 1)] at e3
  have t0 := (tuple3_inj (tuple2_inj e1).2).2.2
  have t1 := (tuple3_inj ((tuple2_inj e2).2.trans t0)).2.2
  exact nil_ne_cons (t1.symm.trans (tuple2_inj e3).2.symm)

/-! ## The source run -/

theorem live1 : Solvable K1 := live_of_sub (by simp)
theorem live3 : Solvable K3 := live_of_sub (by simp)
theorem live5 : Solvable K5 := live_of_sub (by simp)
theorem live7 : Solvable K7 := live_of_sub (by simp)
theorem live9 : Solvable K9 := live_of_sub (fun _ member => member)

theorem m1 : ∃ e ∈ program.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, lenT L2)]) :=
  ⟨eCons, List.mem_cons_of_mem _ (List.mem_singleton_self _), show Solvable K1 from live1⟩

theorem m3 : ∃ e ∈ program.equations, Solvable (K1 ++ [(instantiate (copyAt mkeys 1) e.lhs, lenT (tN 0))]) :=
  ⟨eCons, List.mem_cons_of_mem _ (List.mem_singleton_self _), show Solvable K3 from live3⟩

theorem m5 : ∃ e ∈ program.equations, Solvable (K3 ++ [(instantiate (copyAt mkeys 2) e.lhs, lenT (tN 1))]) :=
  ⟨eNil, List.mem_cons_self, show Solvable K5 from live5⟩

theorem runs6 : Runs D program supply (Config.initial sp query) C6 := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 0, sp⟩, X5 ::ₘ R5⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := R5) rfl (Multiset.singleton_add _ _).symm
      live5 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩, X4 ::ₘ D3 ::ₘ D1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := D3 ::ₘ D1 ::ₘ 0) rfl rfl
      live3 (.apply _ _ _ _ _ m5))
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩, D3 ::ₘ X3 ::ₘ D1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := X3) (rest := D3 ::ₘ D1 ::ₘ 0)
      (Multiset.cons_swap _ _ _) (Multiset.singleton_add _ _).symm live3
      (.letStart _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, X2 ::ₘ D1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := D1 ::ₘ 0) rfl rfl
      live1 (.apply _ _ _ _ _ m3))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, D1 ::ₘ X1 ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := X1) (rest := D1 ::ₘ 0)
      (Multiset.cons_swap _ _ _) (Multiset.singleton_add _ _).symm live1
      (.letStart _ _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := 0) rfl rfl live_nil (.apply _ _ _ _ _ m1))

theorem runs10 : Runs D program supply (Config.initial sp query) final := by
  refine Relation.ReflTransGen.tail (b := ⟨⟨5, 0, sp⟩, X9 ::ₘ R5⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := R5) rfl (Multiset.singleton_add _ _).symm
      live9 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨4, 0, sp⟩, X8 ::ₘ R5⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := R5) rfl (Multiset.singleton_add _ _).symm
      live7 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨4, 0, sp⟩, X7 ::ₘ R5⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := R5) rfl (Multiset.singleton_add _ _).symm
      live7 (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := C6) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (rest := R5) rfl (Multiset.singleton_add _ _).symm
      live5 (.letBind _ _ _ _ _ _ _ _))
  exact runs6

/-! ## The answers -/

def answer : MClosed := ctuple [csym "S", ctuple [csym "S", csym "Z"]]

theorem determines_final : Determines K9 (sT r40) answer := by
  refine ⟨live_of_sub (fun _ member => member), fun target σ solved => ?_⟩
  have e7 := solved (r31, zT) (by simp)
  have e9 := solved (r40, sT r31) (by simp)
  change instantiate σ (foD [3, 1] [205] 0) = instantiate σ zT at e7
  change instantiate σ (foD [4, 0] [205] 0) = tupleAt [symAt "S", instantiate σ (foD [3, 1] [205] 0)] at e9
  show tupleAt [symAt "S", instantiate σ (foD [4, 0] [205] 0)] = _
  rw [e9, e7]
  rfl

/-- **The source's bag at the end**: `{(S (S Z))}`. -/
theorem final_answers : Config.answers (D := D) final = {{answer}} := by
  show Config.answers (D := D) ⟨⟨5, 0, sp⟩, X10 ::ₘ D5 ::ₘ D3 ::ₘ D1 ::ₘ 0⟩ = _
  rw [answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ (live_of_sub (fun _ member => member)),
    answers_cons_dead (D := D) dead5, answers_cons_dead (D := D) dead3, answers_cons_dead (D := D) dead1,
    answers_zero, answer_of_determines rfl determines_final]
  rfl

/-! ## Two frames of one `let`, at two depths -/

/-- **The alternative after the base case has two pending frames of the `let` at site `[205]`**, the
copies at scopes `1` and `0` (levels `[1]` and `[0]`). -/
theorem two_frames : X6 ∈ C6.branches ∧
    X6.frames = [.bindTo [205] (foD [1] [205] 0) (.ret (sT (foD [1] [205] 0))),
      .bindTo [205] (foD [0] [205] 0) (.ret (sT (foD [0] [205] 0)))] :=
  ⟨show X6 ∈ X6 ::ₘ R5 from Multiset.mem_cons_self _ _, rfl⟩

/-- **The invariant holds there, and the alternative is hygienic.** -/
theorem invariant_at_two_frames : Scoping C6.world.scope X6 ∧ Hygienic X6 := by
  have equations := equations_of_wellFormed (D := D) (P := program) program_wellFormed program_arrows
  have sc := scoping_reachable (D := D) (supply := supply) sp query equations query_wellFormed.inScope
    (query_distinct (D := D) (P := program) query query_wellFormed) query_arrows C6 runs6 X6
    (show X6 ∈ X6 ::ₘ R5 from Multiset.mem_cons_self _ _)
  obtain ⟨Vis, L, Ls, inv⟩ := sc
  exact ⟨⟨Vis, L, Ls, inv⟩, hygienic_of_scopedAt inv⟩

/-- **Through the translation**: the bag `{(S (S Z))}` is that of a frontier reached by the step. -/
theorem run_through_translation :
    ∃ L : Multiset (Branch mkeys [] () D.Ty × HostState MSig × ℕ),
      frontierAnswers N L = {{answer}} ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N program) (Hosting.start N program query) x.2.1 := by
  obtain ⟨L, same, reached⟩ := arrow_answers N (D := D) (P := program) (supply := supply) sp query
    program_wellFormed program_arrows query_wellFormed query_arrows runs10
  exact ⟨L, same.symm.trans final_answers, reached⟩

#print axioms program_wellFormed
#print axioms query_wellFormed
#print axioms runs10
#print axioms final_answers
#print axioms two_frames
#print axioms invariant_at_two_frames
#print axioms run_through_translation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.Recursion
