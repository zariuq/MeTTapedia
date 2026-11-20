import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeld

/-!
# A held argument used twice, with a choice inside, when held text runs: four answers

The same surface program as `ExampleHeld`, under the reading where held text runs where a value is
wanted. Each of the two uses of `$x` runs `(two)` on its own, with its own choice, so the bag of
answers is `{(pair 1 1), (pair 1 2), (pair 2 1), (pair 2 2)}` (`runs_example`), against the single
`(pair (two) (two))` of the other reading.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeldRuns

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit ExampleHeld

abbrev P := core true

def two : MData := tuple [sym "two"]
def k0 : Comp mkeys [] () MTy := .let_ [1, 101, 1] S1 (.run X0) (.apply (tuple [sym "pair", S0, S1]))
def f0 : Frame mkeys [] () MTy := .bindTo [1, 101, 0] S0 k0
def K2 : List (Constraint mkeys [] ()) := K1 ++ [(two, two)]

/-- The alternative after the first choice, holding `v`. -/
def b2 (v : Int) : Branch mkeys [] () MTy := ⟨K2, .eval (.ret (num v)), [f0], []⟩

/-! ## One subtree: the second use, run at scopes from `n` -/

def Y0 (n : ℕ) : MData := foD [n, 0] [1, 101, 0] 0
def Y1 (s : ℕ) : MData := foD [s, 0] [1, 101, 1] 0
def K3 (v : Int) (n : ℕ) : List (Constraint mkeys [] ()) := K2 ++ [(Y0 n, num v)]
def f1 (n : ℕ) : Frame mkeys [] () MTy := .bindTo [1, 101, 1] S1 (.apply (tuple [sym "pair", Y0 n, S1]))
def K4 (v : Int) (n : ℕ) : List (Constraint mkeys [] ()) := K3 v n ++ [(two, two)]
def K5 (v : Int) (n : ℕ) (w : Int) (s : ℕ) : List (Constraint mkeys [] ()) := K4 v n ++ [(Y1 s, num w)]

def fin (v : Int) (n : ℕ) (w : Int) (s : ℕ) : Branch mkeys [] () MTy :=
  ⟨K5 v n w s, .value (tuple [sym "pair", Y0 n, Y1 s]), [], []⟩

def deadE (v : Int) (n : ℕ) : Branch mkeys [] () MTy :=
  ⟨K3 v n ++ [(tuple [sym "dup", foD [n + 1] [101] 0], two)],
    .eval ((dupE true).rhs.inst (copyAt mkeys (n + 1))), [f1 n], []⟩

/-- The dereferencing solution of the second use. -/
def θ (v : Int) (n : ℕ) : Assignment (fam mkeys) (fam mkeys) :=
  bindNames [(([0], [101], 0), two), (([n, 0], [1, 101, 0], 0), num v)]

abbrev sp : MClosed → Multiset (Row mkeys [] ()) := fun _ => 0

theorem unmatched_at (v : Int) (n : ℕ) (w : Int) (s : ℕ) (m : ℕ) :
    ∀ e ∈ P.equations,
      ¬ Solvable (K5 v n w s ++ [(instantiate (copyAt mkeys m) e.lhs, tuple [sym "pair", Y0 n, Y1 s])]) := by
  intro e member
  simp only [P, core, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact dead_of_length (ts := [sym "two"]) (ts' := [sym "pair", Y0 n, Y1 s])
      (List.mem_append_right _ (List.mem_singleton_self _)) (by simp)
  · exact dead_of_length (ts := [sym "dup", foD [m] [101] 0]) (ts' := [sym "pair", Y0 n, Y1 s])
      (List.mem_append_right _ (List.mem_singleton_self _)) (by simp)

/-- **The subtree**, given the facts that only a computation at concrete scopes decides. -/
theorem subtree (v : Int) (n : ℕ) (live1 : Solvable (K5 v n 1 (n + 2))) (live2 : Solvable (K5 v n 2 (n + 3)))
    (principal : Principal (K3 v n) (θ v n)) :
    Runs D P supply ⟨⟨n, 0, sp⟩, {b2 v}⟩
      ⟨⟨n + 4, 0, sp⟩, fin v n 1 (n + 2) ::ₘ fin v n 2 (n + 3) ::ₘ deadE v n ::ₘ 0⟩ := by
  have live4 : Solvable (K4 v n) := solvable_of_append live1
  have live3 : Solvable (K3 v n) := solvable_of_append live4
  have live2' : Solvable K2 := solvable_of_append live3
  have matched : ∃ e ∈ P.equations, Solvable (K3 v n ++ [(instantiate (copyAt mkeys (n + 1)) e.lhs, two)]) :=
    ⟨twoE, List.mem_cons.mpr (Or.inl rfl), live4⟩
  -- the second answer of the second choice
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 4, 0, sp⟩, fin v n 1 (n + 2) ::ₘ
      ⟨K5 v n 2 (n + 3), .eval (.apply (tuple [sym "pair", Y0 n, Y1 (n + 3)])), [], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) live2
      (.unmatched ⟨n + 4, 0, sp⟩ (K5 v n 2 (n + 3)) (tuple [sym "pair", Y0 n, Y1 (n + 3)]) [] []
        (unmatched_at v n 2 (n + 3) (n + 4))))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 3, 0, sp⟩, fin v n 1 (n + 2) ::ₘ
      ⟨K4 v n, .value (num 2), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) live4 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 3, 0, sp⟩, fin v n 1 (n + 2) ::ₘ
      ⟨K4 v n, .eval (.ret (num 2)), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) (Multiset.cons_swap _ _ _)
      (by rw [Multiset.singleton_add, Multiset.cons_swap]; rfl) live4 (.ret _ _ _ _ _))
  -- the first answer of the second choice
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 3, 0, sp⟩,
      ⟨K5 v n 1 (n + 2), .eval (.apply (tuple [sym "pair", Y0 n, Y1 (n + 2)])), [], []⟩ ::ₘ
      ⟨K4 v n, .eval (.ret (num 2)), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) rfl rfl live1
      (.unmatched ⟨n + 3, 0, sp⟩ (K5 v n 1 (n + 2)) (tuple [sym "pair", Y0 n, Y1 (n + 2)]) [] []
        (unmatched_at v n 1 (n + 2) (n + 3))))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, sp⟩,
      ⟨K4 v n, .value (num 1), [f1 n], []⟩ ::ₘ
      ⟨K4 v n, .eval (.ret (num 2)), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) rfl rfl live4 (.letBind _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, sp⟩,
      ⟨K4 v n, .eval (.ret (num 1)), [f1 n], []⟩ ::ₘ
      ⟨K4 v n, .eval (.ret (num 2)), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) rfl rfl live4 (.ret _ _ _ _ _))
  -- the second choice
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 2, 0, sp⟩,
      ⟨K4 v n, .eval (.choice (.ret (num 1)) (.ret (num 2))), [f1 n], []⟩ ::ₘ deadE v n ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) rfl rfl live4 (.choice _ _ _ _ _ _))
  -- the second use runs `(two)`
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, sp⟩, {⟨K3 v n, .eval (.apply two), [f1 n], []⟩}⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) (rest := 0) rfl rfl live3 (.apply _ _ _ _ _ matched))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, sp⟩, {⟨K3 v n, .eval (.run X0), [f1 n], []⟩}⟩) ?_
    (step_one live3 (.run _ _ _ _ _ (θ v n) principal))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n + 1, 0, sp⟩,
      {⟨K3 v n, .eval (.let_ [1, 101, 1] S1 (.run X0) (.apply (tuple [sym "pair", Y0 n, S1]))), [], []⟩}⟩) ?_
    (step_one live3 (.letStart _ _ _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨n, 0, sp⟩, {⟨K2, .value (num v), [f0], []⟩}⟩) ?_
    (step_one live2' (.letBind _ _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single (step_one live2' (.ret _ _ _ _ _))

theorem fin_determines (v : Int) (n : ℕ) (w : Int) (s : ℕ) (live : Solvable (K5 v n w s)) :
    Determines (K5 v n w s) (tuple [sym "pair", Y0 n, Y1 s]) (ctuple [csym "pair", cnum v, cnum w]) := by
  refine ⟨live, fun target σ solved => ?_⟩
  have y0 := solved (Y0 n, num v) (by simp [K5, K4, K3])
  have y1 := solved (Y1 s, num w) (by simp [K5])
  show tupleAt [symAt "pair", instantiate σ (Y0 n), instantiate σ (Y1 s)] = _
  rw [y0, y1]
  rfl

theorem deadE_dead (v : Int) (n : ℕ) : ¬ Solvable (deadE v n).store :=
  dead_of_length (ts := [sym "dup", foD [n + 1] [101] 0]) (ts' := [sym "two"])
    (List.mem_append_right _ (List.mem_singleton_self _)) (by simp)

/-! ## The concrete facts -/

def close (v : Int) (n : ℕ) (w : Int) (s : ℕ) : Assignment (fam mkeys) noNames :=
  closeNames [(([0], [101], 0), ctuple [csym "two"]), (([n, 0], [1, 101, 0], 0), cnum v),
    (([s, 0], [1, 101, 1], 0), cnum w)] (csym "a")

theorem live_1_2_1 : Solvable (K5 1 2 1 4) := ⟨Empty, noNames, close 1 2 1 4, by decide⟩
theorem live_1_2_2 : Solvable (K5 1 2 2 5) := ⟨Empty, noNames, close 1 2 2 5, by decide⟩
theorem live_2_6_1 : Solvable (K5 2 6 1 8) := ⟨Empty, noNames, close 2 6 1 8, by decide⟩
theorem live_2_6_2 : Solvable (K5 2 6 2 9) := ⟨Empty, noNames, close 2 6 2 9, by decide⟩

theorem principal_at (v : Int) (n : ℕ) (solved : Models (θ v n) (K3 v n)) : Principal (K3 v n) (θ v n) := by
  refine principal_bindNames solved ?_
  intro entry member X target σ models
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact K1_entails σ (fun e e_mem => models e (by simp [K3, K2, List.mem_append, e_mem]))
  · exact (instantiate_foD σ [n, 0] [1, 101, 0] 0).symm.trans (models (Y0 n, num v) (by simp [K3]))

theorem principal_1_2 : Principal (K3 1 2) (θ 1 2) := principal_at 1 2 (by decide)
theorem principal_2_6 : Principal (K3 2 6) (θ 2 6) := principal_at 2 6 (by decide)

/-! ## The whole run -/

/-- The first call and the first use, up to the first choice. -/
theorem prefix_runs :
    Runs D P supply start ⟨⟨2, 0, sp⟩, b2 1 ::ₘ b2 2 ::ₘ
      ⟨K1 ++ [(tuple [sym "dup", foD [1] [101] 0], two)], .eval ((dupE true).rhs.inst (copyAt mkeys 1)), [f0], []⟩ ::ₘ
      deadTwo true ::ₘ 0⟩ := by
  have liveK2 : Solvable K2 := solvable_of_append (solvable_of_append (K3 1 2 |>.length |> fun _ =>
    (solvable_of_append live_1_2_1 : Solvable (K4 1 2))))
  have liveK1 : Solvable K1 := solvable_of_append liveK2
  have principal1 : Principal K1 (bindNames [(([0], [101], 0), two)]) := by
    refine principal_bindNames (by decide) ?_
    intro entry member X target σ models
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst member
    exact K1_entails σ models
  have matched1 : ∃ e ∈ P.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e.lhs, call)]) :=
    ⟨dupE true, List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), liveK1⟩
  have matched2 : ∃ e ∈ P.equations, Solvable (K1 ++ [(instantiate (copyAt mkeys 1) e.lhs, two)]) :=
    ⟨twoE, List.mem_cons.mpr (Or.inl rfl), liveK2⟩
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 0, sp⟩,
      ⟨K2, .eval (.choice (.ret (num 1)) (.ret (num 2))), [f0], []⟩ ::ₘ
      ⟨K1 ++ [(tuple [sym "dup", foD [1] [101] 0], two)], .eval ((dupE true).rhs.inst (copyAt mkeys 1)), [f0], []⟩ ::ₘ
      deadTwo true ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) rfl rfl liveK2 (.choice _ _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, ⟨K1, .eval (.apply two), [f0], []⟩ ::ₘ deadTwo true ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) rfl rfl liveK1 (.apply _ _ _ _ _ matched2))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩, ⟨K1, .eval (.run X0), [f0], []⟩ ::ₘ deadTwo true ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) rfl rfl liveK1
      (.run _ _ _ _ _ (bindNames [(([0], [101], 0), two)]) principal1))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 0, sp⟩,
      ⟨K1, .eval ((dupE true).rhs.inst (copyAt mkeys 0)), [], []⟩ ::ₘ deadTwo true ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := P) (supply := supply) rfl rfl liveK1 (.letStart _ _ _ _ _ _ _ _))
  exact Relation.ReflTransGen.single
    (Step.of_eq (D := D) (P := P) (supply := supply) (rest := 0) rfl
      (by rw [add_zero, Multiset.cons_swap]; rfl) live_nil (.apply _ _ _ _ _ matched1))

/-- The dead alternative of the first use. -/
def deadD : Branch mkeys [] () MTy :=
  ⟨K1 ++ [(tuple [sym "dup", foD [1] [101] 0], two)], .eval ((dupE true).rhs.inst (copyAt mkeys 1)), [f0], []⟩

theorem deadD_dead : ¬ Solvable deadD.store :=
  dead_of_length (ts := [sym "dup", foD [1] [101] 0]) (ts' := [sym "two"])
    (List.mem_append_right _ (List.mem_singleton_self _)) (by decide)

/-- The final bag. -/
def finalBag : Multiset (Branch mkeys [] () MTy) :=
  fin 2 6 1 8 ::ₘ fin 2 6 2 9 ::ₘ deadE 2 6 ::ₘ
    fin 1 2 1 4 ::ₘ fin 1 2 2 5 ::ₘ deadE 1 2 ::ₘ deadD ::ₘ deadTwo true ::ₘ 0

def R1 : Multiset (Branch mkeys [] () MTy) := b2 2 ::ₘ deadD ::ₘ deadTwo true ::ₘ 0
def A : Multiset (Branch mkeys [] () MTy) := fin 1 2 1 4 ::ₘ fin 1 2 2 5 ::ₘ deadE 1 2 ::ₘ 0
def R2 : Multiset (Branch mkeys [] () MTy) :=
  fin 1 2 1 4 ::ₘ fin 1 2 2 5 ::ₘ deadE 1 2 ::ₘ deadD ::ₘ deadTwo true ::ₘ 0
def B : Multiset (Branch mkeys [] () MTy) := fin 2 6 1 8 ::ₘ fin 2 6 2 9 ::ₘ deadE 2 6 ::ₘ 0

theorem runs_all : Runs D P supply start ⟨⟨10, 0, sp⟩, finalBag⟩ := by
  have first : Runs D P supply ⟨⟨2, 0, sp⟩, {b2 1} + R1⟩ ⟨⟨6, 0, sp⟩, A + R1⟩ :=
    (subtree 1 2 live_1_2_1 live_1_2_2 principal_1_2).frame R1
  have second : Runs D P supply ⟨⟨6, 0, sp⟩, {b2 2} + R2⟩ ⟨⟨10, 0, sp⟩, B + R2⟩ :=
    (subtree 2 6 live_2_6_1 live_2_6_2 principal_2_6).frame R2
  have bridge : A + R1 = {b2 2} + R2 := by
    simp only [A, R1, R2, Multiset.cons_add, zero_add, Multiset.singleton_add]
    rw [Multiset.cons_swap (deadE 1 2) (b2 2), Multiset.cons_swap (fin 1 2 2 5) (b2 2),
      Multiset.cons_swap (fin 1 2 1 4) (b2 2)]
  have entry : ({b2 1} + R1 : Multiset (Branch mkeys [] () MTy)) = b2 1 ::ₘ R1 := Multiset.singleton_add _ _
  have exit : B + R2 = finalBag := by
    simp only [B, R2, finalBag, Multiset.cons_add, zero_add]
  rw [← bridge] at second
  rw [entry] at first
  rw [exit] at second
  exact (prefix_runs.trans first).trans second

/-! ## The answers -/

theorem fin_finished (v : Int) (n : ℕ) (w : Int) (s : ℕ) : Branch.Finished (D := D) (fin v n w s) :=
  ⟨rfl, _, rfl⟩

theorem runs_answers :
    Config.answers (D := D) (⟨⟨10, 0, sp⟩, finalBag⟩ : Config mkeys [] () MTy) =
      {{ctuple [csym "pair", cnum 2, cnum 1]}, {ctuple [csym "pair", cnum 2, cnum 2]},
        {ctuple [csym "pair", cnum 1, cnum 1]}, {ctuple [csym "pair", cnum 1, cnum 2]}} := by
  rw [finalBag, answers_cons_finished (fin_finished 2 6 1 8) live_2_6_1,
    answers_cons_finished (fin_finished 2 6 2 9) live_2_6_2,
    answers_cons_dead (D := D) (deadE_dead 2 6),
    answers_cons_finished (fin_finished 1 2 1 4) live_1_2_1,
    answers_cons_finished (fin_finished 1 2 2 5) live_1_2_2,
    answers_cons_dead (D := D) (deadE_dead 1 2),
    answers_cons_dead (D := D) deadD_dead,
    answers_cons_dead (D := D) (deadTwo_dead true), answers_zero,
    answer_of_determines rfl (fin_determines 2 6 1 8 live_2_6_1),
    answer_of_determines rfl (fin_determines 2 6 2 9 live_2_6_2),
    answer_of_determines rfl (fin_determines 1 2 1 4 live_1_2_1),
    answer_of_determines rfl (fin_determines 1 2 2 5 live_1_2_2)]
  rfl

/-- The run has ended: every live alternative is finished. -/
theorem final_quiescent :
    Config.Quiescent (D := D) P supply (⟨⟨10, 0, sp⟩, finalBag⟩ : Config mkeys [] () MTy) :=
  Config.quiescent_of_finished fun b member live => by
    simp only [finalBag, Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fin_finished 2 6 1 8
    · exact fin_finished 2 6 2 9
    · exact absurd live (deadE_dead 2 6)
    · exact fin_finished 1 2 1 4
    · exact fin_finished 1 2 2 5
    · exact absurd live (deadE_dead 1 2)
    · exact absurd live deadD_dead
    · exact absurd live (deadTwo_dead true)

/-- **The example**: under the reading where held text runs, the run ends with a bag of four
answers. -/
theorem runs_example :
    ∃ C, Runs D (elaborate (reading true) surface) supply
        (Config.initial (fun _ => 0) (elabQuery (reading true) surface querySurface)) C ∧
      Config.Quiescent (D := D) (elaborate (reading true) surface) supply C ∧
      Config.answers (D := D) C =
        {{ctuple [csym "pair", cnum 2, cnum 1]}, {ctuple [csym "pair", cnum 2, cnum 2]},
          {ctuple [csym "pair", cnum 1, cnum 1]}, {ctuple [csym "pair", cnum 1, cnum 2]}} := by
  rw [elaborate_runs, query_elaborated]
  exact ⟨_, runs_all, final_quiescent, runs_answers⟩

#print axioms runs_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleHeldRuns
